sig Text{}

abstract sig User {
	email: one Email,
	password: one Text,
	name: one Text,
	surname: one Text
}

sig Email{}

sig Farmer extends User {
	farm: one Farm
}

sig Farm {
	farmName: one Text,
	farmPosition: one Position,
	belongingArea: one Area,
	ownerName: one Farmer
}

sig Position{}

sig Agronomist extends User {
	area: one Area,
	plan: one Plan
}

sig Area{}

sig PolicyMaker extends User {}

sig Plan {
	visits: some Visit
}

sig Visit {
	day: one Day,
	initialHour: one Hour,
	endHour: one Hour,
	motivation: one Text,
	farm: one Farm
}

sig Day{}
sig Hour{}

sig ProductionData {
	data: set FarmerProduction
}

sig FarmerProduction {
	cropType: one CropType,
	weather: one WeatherForecast,
	cropQuantity: one CropQ,
	energy: one EnergyQ,
	fertilizer: one Fertilizer,
	water: one WaterQ,
	farm: one Farm,
	day: one Day
}

sig CropType{}
sig CropQ{}
sig EnergyQ{}
sig Fertilizer{}
sig WaterQ{}

sig BestPractices {
	bestPractice: set BestPractice
}

sig BestPractice {
	content: one Text,
	farmerData: one FarmerProduction,
	request: one BestPracticeRequest
}

sig BestPracticeRequest {
	recipientEmail: one Email,
	day: one Day,
	hour: one Hour
}

sig WeatherForecast {
	forecasts: some Forecast
}

sig Forecast {
	day: one Day,
	time: one Hour,
	position: one Position,
	weather: one Weather, //rain, sun, ...
	temperature: one TemperatureQ,
	humidity: one HumidityQ,
	wind: one WindQ
}

sig Weather{}
sig TemperatureQ{}
sig HumidityQ{}
sig WindQ{}

sig HelpAndSuggestions {
	list: set Conversation
}

sig Conversation{
	content: some Message,
	participantUsers: some Email
}

sig Message {
	text: one Text,
	email: one Email,
	day: one Day,
	time: one Hour
}

sig Forum {
	pages: set ForumPage
}

sig ForumPage {
	category: one Text,
	name: one Text,
	posts: set ForumThread
}

sig ForumThread {
	postTitle: one Text,
	creatorFarmer: one Farmer,
	object: one Text,
	messages: set Message
}

sig PersonalizedSuggestions {
	suggestions: set Suggestions,
	destinationFarmer: one Farmer
} 

sig Suggestions{}

fact {
	//Two user can't have the same email address
	no disj u1, u2: User | u1.email = u2.email
}

fact {
	//Every Area has at least one responsible agronomist
	all a: Area | 
		some b : Agronomist | b.area = a
}

fact {
	//Every farmer is associated to one and only one farm
	all f: Farmer, f2: Farm |
			(f.farm = f2 implies f2.ownerName = f) and 
			(f2.ownerName = f implies f.farm = f2)
}

fact {
	//Two farm can't be in the same position
	no disj f1, f2: Farm | f1.farmPosition = f2.farmPosition
}

fact {
	//Every farmer has a unique personalized suggestion
	all f: Farmer |
		one sug: PersonalizedSuggestions | sug.destinationFarmer = f
}

fact {
	//Every agronomist has a unique plan
	all p : Plan |
		one a : Agronomist | a.plan = p
}

fact {
	//Every mail in a message should belong to a user
	all e: Message.email |
		some u : User | u.email = e
}

fact {
	//Every mail in a conversation should belong to a user
	all e: Conversation.participantUsers |
		some u : User | u.email = e
}

fact {
	//Can't have different forecast for the same time and day
	no disj f1, f2: Forecast |
		f1.day = f2.day and f1.time = f2.time and f1.position = f2.position and
		(f1.temperature != f2.temperature or f1.weather != f2.weather or f1.humidity != f2.humidity or f1.wind != f2.wind)

}

fact { 
	//Message in a conversation must have email only from user participating to the conversation
	all conv: Conversation |
		all mess: conv.content | some participant: conv.participantUsers | mess.email = participant
}

fact {
	//All forum thread must participate to one Forum page
	all ft : ForumThread |
		one fp : ForumPage | ft in fp.posts 
}

fact {
	//The email of the Best practice request must belong to a farmer
	all bpr: BestPracticeRequest |
		one farmer: Farmer | farmer.email = bpr.recipientEmail
}

fact {
	//You can't have a Conversation with a policy maker
	no convEm: Conversation.participantUsers |
		some pm: PolicyMaker | pm.email = convEm
}

fact {
	//All conversation must participate to HelpAndSuggestions
	all c: Conversation |
		c in HelpAndSuggestions.list

}

fact {
	//All Visit must participate to a Plan
	all v: Visit |
		v in Plan.visits

}

fact {
	//A BestPracticeRequest must have mail corresponding to the BestPractice
	all bp: BestPractice |
		bp.request.recipientEmail = bp.farmerData.farm.ownerName.email
}

fact {
	//only farmers can participate to the forum
	all forumEm: ForumThread.messages.email |
		some f: Farmer | f.email = forumEm
}

fact {
	//every visits should belong to the area of competence of the agronomist
	all a: Agronomist |
		all visit: a.plan.visits | a.area = visit.farm.belongingArea
}

fact {
	//all FarmerProduction should belong to ProductionData
	all fp: FarmerProduction |
		one pd: ProductionData | fp in pd.data
}

//Every farmer has at least one connected agronomist
assert farmerHasAgronomist {
	all f: Farmer | 
		some a: Agronomist | a.area = f.farm.belongingArea
}
//check farmerHasAgronomist

//Every message in conversation must belong to a farmer or an agronomist
assert noPolicyMakerInConversation {
	all c: Conversation |
		all userEm : c.participantUsers | 
			(some f: Farmer | f.email = userEm) or (some a: Agronomist | a.email = userEm)
}
//check noPolicyMakerInConversation

//No message in a conversation has an email different from the participant to the conversation
assert noMessageFromStranger {
	no conv: Conversation |
		some message: conv.content |  
			message.email not in conv.participantUsers
}
//check noMessageFromStranger

//The first world has the aim to present all communication method present to the farmer
pred world1 {
	#Farmer = 2
	#Agronomist = 1
	#Visit = 2
	#PolicyMaker = 0
	#HelpAndSuggestions = 1
	#Conversation = 2
	#BestPracticeRequest = 0
	#BestPractice = 0
	#ForumThread = 1
	#ForumPage = 2
	#Suggestions = 1
	#Forecast = 0
	#ProductionData = 0
	#WeatherForecast = 0
	#Message = 3
}

//The second world puts the emphasis on the Agronomist and his instruments
pred world2 {
	#Farmer = 2
	#Agronomist = 3
	#Visit = 4
	#PolicyMaker = 0
	#HelpAndSuggestions = 0
	#Conversation = 0
	#BestPracticeRequest = 0
	#BestPractice = 0
	#ForumThread = 0
	#Suggestions = 0
	#Forecast = 0
	#ProductionData = 0
	#WeatherForecast = 0
	#Message = 0
	#Area = 2
	#Forum = 0
	#ForumPage = 0
}

//The third world show what is inherent with the policy maker
pred world3 {
	#Farmer = 2
	#Agronomist = 1
	#Visit = 1
	#PolicyMaker = 2
	#HelpAndSuggestions = 0
	#Conversation = 0
	#BestPracticeRequest = 2
	#BestPractice = 2
	#ForumThread = 0
	#Suggestions = 0
	#Forecast = 1
	#ProductionData = 1
	#FarmerProduction = 2
	#WeatherForecast = 1
	#Message = 0
	#Area = 1
	#Forum = 0
	#ForumPage = 0
	no disj bpr1, bpr2 : BestPracticeRequest | bpr1.recipientEmail = bpr2.recipientEmail
}

run world1 for 5
//run world2 for 5
//run world3 for 5