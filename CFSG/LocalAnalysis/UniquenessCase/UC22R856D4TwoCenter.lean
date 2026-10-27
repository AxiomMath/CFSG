module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.D4TwoSylowData
import CFSG.LocalAnalysis.UniquenessCase.UC22R856D4TwoPacked

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.R856NormalFour

open CFSG.Quasithin CFSG.AGLEmbedding.D4Two CFSG.LocalAnalysis.UniquenessCase.UC22.D4TwoPK

private def letter0 : Array GF8 := decA 784637722769341688359228641114377032468260287261079240705

private def letter1 : Array GF8 := decA 784637769537394082948124619780875689318562262762985095177

private def letter2 : Array GF8 := decA 784637816305446477537025790744851851048705491403813158929

private def letter3 : Array GF8 := decA 784637863073498872125921769411350507899007466905719013401

private def letter4 : Array GF8 := decA 784637909841551266714817748076920709712927878173809442849

private def letter5 : Array GF8 := decA 784637956609603661303713726743419366507889621454586642473

private def letter6 : Array GF8 := decA 784638003377656055892594128519342418874441314339049701425

private def letter7 : Array GF8 := decA 784638050145708450481490107185841075724743289840955555897

private def letter8 : Array GF8 := decA 784637722769341688359228641114377032468260287261079240705

private def letter9 : Array GF8 := decA 882717437384758581504316052229726481570818686354722914305

private def letter10 : Array GF8 := decA 980797152000175488515909935655728524920472569554759843841

private def letter11 : Array GF8 := decA 1078876866615592381660997346771077974023030968648403517441

private def letter12 : Array GF8 := decA 1176956581231009270722696324411551456087588442639951724545

private def letter13 : Array GF8 := decA 1275036295846426163357360185145493209995084930585943080961

private def letter14 : Array GF8 := decA 1373116010461843023835340371850748353224951594286076395521

private def letter15 : Array GF8 := decA 1471195725077259916980427782966097802327509993379720069121

private def letter16 : Array GF8 := decA 784637722769342036808372368155363618963858297392801513473

private def letter17 : Array GF8 := decA 784637723500092507024680100216219448826404048888859197441

private def row0 : Array GF8 := decA 784637722769341688359228641114377032468260287261079240705

private def row1 : Array GF8 := decA 4065893044541529364332420720331588301136249972176327802908

private def row2 : Array GF8 := decA 3043498543177228160058537397126113114787100248713896585280

private def row3 : Array GF8 := decA 3326787213986790019007313238736185879963696418588448522269

private def row4 : Array GF8 := decA 2487341865768109619925612847423583567546954560370481863283

private def row5 : Array GF8 := decA 4944732046853384356101147310721939057726222529421758937959

private def row6 : Array GF8 := decA 109532661656811321947421573700704357170468119951176563299

private def row7 : Array GF8 := decA 14018122895820235007688497108225178250059628271014670899

private def row8 : Array GF8 := decA 6264012265300370567429108306946777216694465452564747821223

private def row9 : Array GF8 := decA 1866245610234292315216865599937212263177930672157515666101

private def row10 : Array GF8 := decA 4494759967738060326429349298485780734489462375175402279322

private def row11 : Array GF8 := decA 6080965704973377666721226302752243379621783026397625277119

private def row12 : Array GF8 := decA 2813818883454239407861311626081080654636942518347333472840

private def row13 : Array GF8 := decA 39525675499558434710576682832989804488631008605053983680

private def row14 : Array GF8 := decA 5731040058301160232841194282329955813222706383131634280662

private def row15 : Array GF8 := decA 3728981961092906448438226533525848360162327070706007430222

private def row16 : Array GF8 := decA 2941786736219526277428156168948516357066483670907018006883

private def row17 : Array GF8 := decA 3641819356172958551886348463547455648698736381388188614648

private def row18 : Array GF8 := decA 672485830539892521244998947123579091489127876230379215239

private def row19 : Array GF8 := decA 5444125496125740409837185051168703178140679218018257627850

private def row20 : Array GF8 := decA 3160696571184736803935621832665085575187891660995298408494

private def row21 : Array GF8 := decA 54959924503115114373143254363996919316217124861909763540

private def row22 : Array GF8 := decA 5328527092158136550707367440699897936809484965938983767004

private def row23 : Array GF8 := decA 395639045975879900057434679112048442025437181380641516976

private def row24 : Array GF8 := decA 3739523629557438032859105844816076647519889672315983108167

private def row25 : Array GF8 := decA 4889297830925055379742047437178818049467046026462008180884

private def row26 : Array GF8 := decA 4151174823772136174467137837679965914895970851431507963758

private def row27 : Array GF8 := decA 1361884185812979977316451428878139164600194553056293908820

private def row28 : Array GF8 := decA 1967084550188755070639397305072384924813194139845320595302

private def row29 : Array GF8 := decA 1552621264661915539689201659236541803671312629112325047966

private def row30 : Array GF8 := decA 5740634014815549402761037012071788367575585398030594287640

private def row31 : Array GF8 := decA 1927106067493714809233249027435668139112854157071874261440

private def row32 : Array GF8 := decA 3677441646585442726845566226928152786110862381366047828574

private def row33 : Array GF8 := decA 3666561193941276748076050085599086247211755679450733418304

private def row34 : Array GF8 := decA 2476269117652918127502059899068814838003229181476565502903

private def row35 : Array GF8 := decA 1469324873851763078857292788205044515522827199111221512823

private def row36 : Array GF8 := decA 223256110621421504662755350050703991427110576548899670036

private def row37 : Array GF8 := decA 60307968373950618431584881055896255546823379367434694369

private def row38 : Array GF8 := decA 1092018909667614491129290451368866232209176676943431729088

private def row39 : Array GF8 := decA 5590376050823132955275977024595553216103600152368061640425

private def row40 : Array GF8 := decA 5136377459321831061046882540815701565048654900324524020116

private def row41 : Array GF8 := decA 6235031761004604436706986463083618150829531853441129270379

private def row42 : Array GF8 := decA 451654047762683280240612231500301605573663453071620514946

private def row43 : Array GF8 := decA 3716199370135049418713408031425867986924738521349321407203

private def row44 : Array GF8 := decA 5368433434048988906046571636606639438328610337341120306449

private def row45 : Array GF8 := decA 5369884638914520390628898563187196472374193308416946196106

private def row46 : Array GF8 := decA 3767542749271313626625876306711134086471169760327682852601

private def row47 : Array GF8 := decA 6268629047700964190062157264980947775655342183694360004864

private def row48 : Array GF8 := decA 5048037970343385931821281650752389945528536844875683861797

private def row49 : Array GF8 := decA 3599701906148113654421098099351820196840650213364120245338

private def row50 : Array GF8 := decA 6160291605958846160556016499219447485196611778157013113140

private def row51 : Array GF8 := decA 73562783501786324113103503650255979447928231341342663846

private def row52 : Array GF8 := decA 229585756892805205105319539974771083140812617448100247719

private def row53 : Array GF8 := decA 3279375942018164386475115815243735388408205905938147200599

private def row54 : Array GF8 := decA 3105988589954398780236017520877903420294892216511556132372

private def row55 : Array GF8 := decA 2150215748088745927933211033707168527170131338048104240710

private def row56 : Array GF8 := decA 3968719870391852146898940092316142838775461345985951505424

private def row57 : Array GF8 := decA 5367589810044246755674127736327120188479976115965362288320

private def row58 : Array GF8 := decA 1960320857508364424392159843179408592741195450613112536012

private def row59 : Array GF8 := decA 1929707532345976123509472006071600409081238031791641822670

private def row60 : Array GF8 := decA 88265911762698076739640931246719740501356254495588504927

private def row61 : Array GF8 := decA 2545702041205037652116251225950974607366089146117475270692

private def row62 : Array GF8 := decA 5006970660370630694042970269319364464067068226340604806323

private def row63 : Array GF8 := decA 71308285127886931184521392779419525785885591325118979933

private def row64 : Array GF8 := decA 808615848920513529772376142539824536965814107964283624617

private def row65 : Array GF8 := decA 3574186778376842825144318526072099226976002748070095926827

private def row66 : Array GF8 := decA 3960089338337560277981062828824865438999360986075686371328

private def row67 : Array GF8 := decA 4964882991057862963482292409085226583499772561750426987314

private def row68 : Array GF8 := decA 6074647795609543411491893076367141958380458177794163620180

private def row69 : Array GF8 := decA 6187497330806269099480318206676474026833179905097540827496

private def row70 : Array GF8 := decA 4876950725835734385535410210273313227858736553153102330900

private def row71 : Array GF8 := decA 4486536244761782978652249400510427902471696794749313618186

private def row72 : Array GF8 := decA 73255735988490978373966465548418847191335880191031870141

private def row73 : Array GF8 := decA 2063298402479492829081871565957897234878100405785828106349

private def row74 : Array GF8 := decA 4126739572079581949399522840837166884864706974885184740368

private def row75 : Array GF8 := decA 4051838769361536295340871741498651202924429170688088058743

private def row76 : Array GF8 := decA 5996542736256362038550535131570938339270215679702793986797

private def row77 : Array GF8 := decA 3775607063794719575495021693155670051119046040194299130038

private def row78 : Array GF8 := decA 96944464693647813432083854245947137827753718970482757

private def row79 : Array GF8 := decA 1377452965047746684175561618090108773212411557107360078777

private def row80 : Array GF8 := decA 2460184692242577000714410675627102528889590389017323833822

private theorem oneArr_literal : oneArr = row0 := by
  decide +kernel

private theorem letterArr_1_literal : letterArr 1 = letter1 := by
  decide +kernel

private theorem letterArr_3_literal : letterArr 3 = letter3 := by
  decide +kernel

private theorem letterArr_4_literal : letterArr 4 = letter4 := by
  decide +kernel

private theorem letterArr_5_literal : letterArr 5 = letter5 := by
  decide +kernel

private theorem letterArr_7_literal : letterArr 7 = letter7 := by
  decide +kernel

private theorem letterArr_9_literal : letterArr 9 = letter9 := by
  decide +kernel

private theorem letterArr_10_literal : letterArr 10 = letter10 := by
  decide +kernel

private theorem letterArr_11_literal : letterArr 11 = letter11 := by
  decide +kernel

private theorem letterArr_12_literal : letterArr 12 = letter12 := by
  decide +kernel

private theorem letterArr_14_literal : letterArr 14 = letter14 := by
  decide +kernel

private theorem letterArr_15_literal : letterArr 15 = letter15 := by
  decide +kernel

private theorem letterArr_16_literal : letterArr 16 = letter16 := by
  decide +kernel

private theorem letterArr_17_literal : letterArr 17 = letter17 := by
  decide +kernel

private def wordA9 : Array GF8 := decA 784637909841551266714817748076920709712927878173809442849

private theorem wordA_9_literal : wordArr [4] = wordA9 := by
  rw [wordArr_cons, wordArr_nil, oneArr_literal, letterArr_4_literal]
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private def wordA8 : Array GF8 := decA 784637909841562765536560740429478064067662216523553964065

private theorem wordA_8_literal : wordArr [16, 4] = wordA8 := by
  rw [wordArr_cons, wordA_9_literal, letterArr_16_literal]
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private def wordA7 : Array GF8 := decA 784637717654097456522826996644922561808695230774076506145

private theorem wordA_7_literal : wordArr [17, 16, 4] = wordA7 := by
  rw [wordArr_cons, wordA_8_literal, letterArr_17_literal]
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private def wordA6 : Array GF8 := decA 796897681981024747749982065559615335742464102777007112225

private theorem wordA_6_literal : wordArr [9, 17, 16, 4] = wordA6 := by
  rw [wordArr_cons, wordA_7_literal, letterArr_9_literal]
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private def wordA5 : Array GF8 := decA 796897877194433571261939002172869378980551253224186708001

private theorem wordA_5_literal : wordArr [17, 9, 17, 16, 4] = wordA5 := by
  rw [wordArr_cons, wordA_6_literal, letterArr_17_literal]
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private def wordA4 : Array GF8 := decA 5080806579208477500377515254658029242519861960862674714657

private theorem wordA_4_literal : wordArr [11, 17, 9, 17, 16, 4] = wordA4 := by
  rw [wordArr_cons, wordA_5_literal, letterArr_11_literal]
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private def wordA3 : Array GF8 := decA 5080806579208465822577881085858119433413314569885647372321

private theorem wordA_3_literal : wordArr [16, 11, 17, 9, 17, 16, 4] = wordA3 := by
  rw [wordArr_cons, wordA_4_literal, letterArr_16_literal]
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private def wordA2 : Array GF8 := decA 5080806581627249248300909533035366508701296933422644592673

private theorem wordA_2_literal : wordArr [17, 16, 11, 17, 9, 17, 16, 4] = wordA2 := by
  rw [wordArr_cons, wordA_3_literal, letterArr_17_literal]
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private def wordA1 : Array GF8 := decA 4065893076612275635829699798650338710831125406822602637345

private theorem wordA_1_literal : wordArr [10, 17, 16, 11, 17, 9, 17, 16, 4] = wordA1 := by
  rw [wordArr_cons, wordA_2_literal, letterArr_10_literal]
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem wordA_0_literal : wordArr [5, 10, 17, 16, 11, 17, 9, 17, 16, 4] = row1 := by
  rw [wordArr_cons, wordA_1_literal, letterArr_5_literal]
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem genA_literal : genA = row1 := by
  change wordArr [5, 10, 17, 16, 11, 17, 9, 17, 16, 4] = row1
  exact wordA_0_literal

private def wordB11 : Array GF8 := decA 784638050145708450481490107185841075724743289840955555897

private theorem wordB_11_literal : wordArr [7] = wordB11 := by
  rw [wordArr_cons, wordArr_nil, oneArr_literal, letterArr_7_literal]
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private def wordB10 : Array GF8 := decA 784638050145728312082682548522076505973829869857386004537

private theorem wordB_10_literal : wordArr [16, 7] = wordB10 := by
  rw [wordArr_cons, wordB_11_literal, letterArr_16_literal]
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private def wordB9 : Array GF8 := decA 784637717654105819302268657183777062976336694299355775033

private theorem wordB_9_literal : wordArr [17, 16, 7] = wordB9 := by
  rw [wordArr_cons, wordB_10_literal, letterArr_17_literal]
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private def wordB8 : Array GF8 := decA 784637951494367792247382010755913489985448731049407379793

private theorem wordB_8_literal : wordArr [5, 17, 16, 7] = wordB8 := by
  rw [wordArr_cons, wordB_9_literal, letterArr_5_literal]
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private def wordB7 : Array GF8 := decA 784637951494353810725489963236326706849578759902019549521

private theorem wordB_7_literal : wordArr [16, 5, 17, 16, 7] = wordB7 := by
  rw [wordArr_cons, wordB_8_literal, letterArr_16_literal]
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private def wordB6 : Array GF8 := decA 784637998262406205314113346368353082076135218851568379793

private theorem wordB_6_literal : wordArr [3, 16, 5, 17, 16, 7] = wordB6 := by
  rw [wordArr_cons, wordB_7_literal, letterArr_3_literal]
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private def wordB5 : Array GF8 := decA 4009008616244248024139664586467686371561654351817455921041

private theorem wordB_5_literal : wordArr [15, 3, 16, 5, 17, 16, 7] = wordB5 := by
  rw [wordArr_cons, wordB_6_literal, letterArr_15_literal]
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private def wordB4 : Array GF8 := decA 4009008348584638348681125312261497950368085895800711505809

private theorem wordB_4_literal : wordArr [17, 15, 3, 16, 5, 17, 16, 7] = wordB4 := by
  rw [wordArr_cons, wordB_5_literal, letterArr_17_literal]
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private def wordB3 : Array GF8 := decA 4614742176888634238960598653097940717358567691747130566545

private theorem wordB_3_literal : wordArr [14, 17, 15, 3, 16, 5, 17, 16, 7] = wordB3 := by
  rw [wordArr_cons, wordB_4_literal, letterArr_14_literal]
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private def wordB2 : Array GF8 := decA 4614742251498944006462989721591784269603516153504594618257

private theorem wordB_2_literal : wordArr [17, 14, 17, 15, 3, 16, 5, 17, 16, 7] = wordB2 := by
  rw [wordArr_cons, wordB_3_literal, letterArr_17_literal]
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private def wordB1 : Array GF8 := decA 4614742350813082673599032783438508680610019534445155641408

private theorem wordB_1_literal : wordArr [1, 17, 14, 17, 15, 3, 16, 5, 17, 16, 7] = wordB1 := by
  rw [wordArr_cons, wordB_2_literal, letterArr_1_literal]
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem wordB_0_literal : wordArr [12, 1, 17, 14, 17, 15, 3, 16, 5, 17, 16, 7] = row2 := by
  rw [wordArr_cons, wordB_1_literal, letterArr_12_literal]
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem genB_literal : genB = row2 := by
  change wordArr [12, 1, 17, 14, 17, 15, 3, 16, 5, 17, 16, 7] = row2
  exact wordB_0_literal

private theorem product_1_literal : mulArr row0 row1 = row1 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_2_literal : mulArr row0 row2 = row2 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_3_literal : mulArr row1 row1 = row3 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_4_literal : mulArr row1 row2 = row4 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_5_literal : mulArr row2 row1 = row5 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_6_literal : mulArr row2 row2 = row6 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_7_literal : mulArr row3 row2 = row7 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_8_literal : mulArr row4 row1 = row8 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_9_literal : mulArr row4 row2 = row9 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_10_literal : mulArr row5 row1 = row10 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_11_literal : mulArr row5 row2 = row11 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_12_literal : mulArr row6 row1 = row12 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_13_literal : mulArr row7 row1 = row13 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_14_literal : mulArr row7 row2 = row14 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_15_literal : mulArr row8 row1 = row15 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_16_literal : mulArr row8 row2 = row16 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_17_literal : mulArr row9 row1 = row17 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_18_literal : mulArr row10 row2 = row18 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_19_literal : mulArr row11 row2 = row19 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_20_literal : mulArr row12 row2 = row20 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_21_literal : mulArr row13 row1 = row21 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_22_literal : mulArr row13 row2 = row22 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_23_literal : mulArr row14 row1 = row23 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_24_literal : mulArr row15 row2 = row24 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_25_literal : mulArr row16 row2 = row25 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_26_literal : mulArr row17 row2 = row26 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_27_literal : mulArr row18 row1 = row27 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_28_literal : mulArr row18 row2 = row28 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_29_literal : mulArr row19 row1 = row29 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_30_literal : mulArr row20 row2 = row30 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_31_literal : mulArr row21 row2 = row31 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_32_literal : mulArr row22 row2 = row32 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_33_literal : mulArr row23 row2 = row33 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_34_literal : mulArr row24 row1 = row34 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_35_literal : mulArr row24 row2 = row35 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_36_literal : mulArr row25 row1 = row36 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_37_literal : mulArr row26 row2 = row37 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_38_literal : mulArr row27 row1 = row38 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_39_literal : mulArr row27 row2 = row39 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_40_literal : mulArr row28 row1 = row40 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_41_literal : mulArr row29 row2 = row41 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_42_literal : mulArr row30 row1 = row42 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_43_literal : mulArr row31 row1 = row43 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_44_literal : mulArr row31 row2 = row44 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_45_literal : mulArr row32 row1 = row45 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_46_literal : mulArr row33 row2 = row46 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_47_literal : mulArr row34 row1 = row47 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_48_literal : mulArr row34 row2 = row48 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_49_literal : mulArr row35 row1 = row49 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_50_literal : mulArr row36 row2 = row50 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_51_literal : mulArr row37 row1 = row51 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_52_literal : mulArr row38 row2 = row52 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_53_literal : mulArr row39 row2 = row53 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_54_literal : mulArr row40 row2 = row54 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_55_literal : mulArr row41 row2 = row55 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_56_literal : mulArr row42 row2 = row56 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_57_literal : mulArr row43 row1 = row57 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_58_literal : mulArr row43 row2 = row58 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_59_literal : mulArr row44 row1 = row59 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_60_literal : mulArr row45 row2 = row60 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_61_literal : mulArr row46 row1 = row61 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_62_literal : mulArr row47 row2 = row62 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_63_literal : mulArr row48 row2 = row63 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_64_literal : mulArr row49 row2 = row64 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_65_literal : mulArr row50 row2 = row65 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_66_literal : mulArr row51 row2 = row66 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_67_literal : mulArr row52 row2 = row67 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_68_literal : mulArr row54 row2 = row68 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_69_literal : mulArr row56 row2 = row69 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_70_literal : mulArr row57 row2 = row70 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_71_literal : mulArr row58 row2 = row71 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_72_literal : mulArr row59 row2 = row72 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_73_literal : mulArr row60 row2 = row73 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_74_literal : mulArr row61 row2 = row74 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_75_literal : mulArr row62 row2 = row75 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_76_literal : mulArr row64 row2 = row76 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_77_literal : mulArr row66 row2 = row77 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_78_literal : mulArr row70 row2 = row78 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_79_literal : mulArr row72 row2 = row79 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem product_80_literal : mulArr row74 row2 = row80 := by
  exact mulArr_of _ _ _ _ _ _ rfl rfl rfl (by decide +kernel)

private theorem center_test_0 :
    (commutes row0 row1 && commutes row0 row2) = true := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_1 :
    (commutes row1 row1 && commutes row1 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_2 :
    (commutes row2 row1 && commutes row2 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_3 :
    (commutes row3 row1 && commutes row3 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_4 :
    (commutes row4 row1 && commutes row4 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_5 :
    (commutes row5 row1 && commutes row5 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_6 :
    (commutes row6 row1 && commutes row6 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_7 :
    (commutes row7 row1 && commutes row7 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_8 :
    (commutes row8 row1 && commutes row8 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_9 :
    (commutes row9 row1 && commutes row9 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_10 :
    (commutes row10 row1 && commutes row10 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_11 :
    (commutes row11 row1 && commutes row11 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_12 :
    (commutes row12 row1 && commutes row12 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_13 :
    (commutes row13 row1 && commutes row13 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_14 :
    (commutes row14 row1 && commutes row14 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_15 :
    (commutes row15 row1 && commutes row15 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_16 :
    (commutes row16 row1 && commutes row16 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_17 :
    (commutes row17 row1 && commutes row17 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_18 :
    (commutes row18 row1 && commutes row18 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_19 :
    (commutes row19 row1 && commutes row19 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_20 :
    (commutes row20 row1 && commutes row20 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_21 :
    (commutes row21 row1 && commutes row21 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_22 :
    (commutes row22 row1 && commutes row22 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_23 :
    (commutes row23 row1 && commutes row23 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_24 :
    (commutes row24 row1 && commutes row24 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_25 :
    (commutes row25 row1 && commutes row25 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_26 :
    (commutes row26 row1 && commutes row26 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_27 :
    (commutes row27 row1 && commutes row27 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_28 :
    (commutes row28 row1 && commutes row28 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_29 :
    (commutes row29 row1 && commutes row29 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_30 :
    (commutes row30 row1 && commutes row30 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_31 :
    (commutes row31 row1 && commutes row31 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_32 :
    (commutes row32 row1 && commutes row32 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_33 :
    (commutes row33 row1 && commutes row33 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_34 :
    (commutes row34 row1 && commutes row34 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_35 :
    (commutes row35 row1 && commutes row35 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_36 :
    (commutes row36 row1 && commutes row36 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_37 :
    (commutes row37 row1 && commutes row37 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_38 :
    (commutes row38 row1 && commutes row38 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_39 :
    (commutes row39 row1 && commutes row39 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_40 :
    (commutes row40 row1 && commutes row40 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_41 :
    (commutes row41 row1 && commutes row41 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_42 :
    (commutes row42 row1 && commutes row42 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_43 :
    (commutes row43 row1 && commutes row43 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_44 :
    (commutes row44 row1 && commutes row44 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_45 :
    (commutes row45 row1 && commutes row45 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_46 :
    (commutes row46 row1 && commutes row46 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_47 :
    (commutes row47 row1 && commutes row47 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_48 :
    (commutes row48 row1 && commutes row48 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_49 :
    (commutes row49 row1 && commutes row49 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_50 :
    (commutes row50 row1 && commutes row50 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_51 :
    (commutes row51 row1 && commutes row51 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_52 :
    (commutes row52 row1 && commutes row52 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_53 :
    (commutes row53 row1 && commutes row53 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_54 :
    (commutes row54 row1 && commutes row54 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_55 :
    (commutes row55 row1 && commutes row55 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_56 :
    (commutes row56 row1 && commutes row56 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_57 :
    (commutes row57 row1 && commutes row57 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_58 :
    (commutes row58 row1 && commutes row58 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_59 :
    (commutes row59 row1 && commutes row59 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_60 :
    (commutes row60 row1 && commutes row60 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_61 :
    (commutes row61 row1 && commutes row61 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_62 :
    (commutes row62 row1 && commutes row62 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_63 :
    (commutes row63 row1 && commutes row63 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_64 :
    (commutes row64 row1 && commutes row64 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_65 :
    (commutes row65 row1 && commutes row65 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_66 :
    (commutes row66 row1 && commutes row66 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_67 :
    (commutes row67 row1 && commutes row67 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_68 :
    (commutes row68 row1 && commutes row68 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_69 :
    (commutes row69 row1 && commutes row69 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_70 :
    (commutes row70 row1 && commutes row70 row2) = true := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_71 :
    (commutes row71 row1 && commutes row71 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_72 :
    (commutes row72 row1 && commutes row72 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_73 :
    (commutes row73 row1 && commutes row73 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_74 :
    (commutes row74 row1 && commutes row74 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_75 :
    (commutes row75 row1 && commutes row75 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_76 :
    (commutes row76 row1 && commutes row76 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_77 :
    (commutes row77 row1 && commutes row77 row2) = true := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_78 :
    (commutes row78 row1 && commutes row78 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_79 :
    (commutes row79 row1 && commutes row79 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private theorem center_test_80 :
    (commutes row80 row1 && commutes row80 row2) = false := by
  exact center_of _ _ _ _ _ _ rfl rfl rfl _ (by decide +kernel)

private def acc0 : List (Array GF8) := [row0]
private def acc1 : List (Array GF8) := acc0 ++ [row1]
private def acc2 : List (Array GF8) := acc1 ++ [row2]
private def acc3 : List (Array GF8) := acc2 ++ [row3]
private def acc4 : List (Array GF8) := acc3 ++ [row4]
private def acc5 : List (Array GF8) := acc4 ++ [row5]
private def acc6 : List (Array GF8) := acc5 ++ [row6]
private def acc7 : List (Array GF8) := acc6 ++ [row7]
private def acc8 : List (Array GF8) := acc7 ++ [row8]
private def acc9 : List (Array GF8) := acc8 ++ [row9]
private def acc10 : List (Array GF8) := acc9 ++ [row10]
private def acc11 : List (Array GF8) := acc10 ++ [row11]
private def acc12 : List (Array GF8) := acc11 ++ [row12]
private def acc13 : List (Array GF8) := acc12 ++ [row13]
private def acc14 : List (Array GF8) := acc13 ++ [row14]
private def acc15 : List (Array GF8) := acc14 ++ [row15]
private def acc16 : List (Array GF8) := acc15 ++ [row16]
private def acc17 : List (Array GF8) := acc16 ++ [row17]
private def acc18 : List (Array GF8) := acc17 ++ [row18]
private def acc19 : List (Array GF8) := acc18 ++ [row19]
private def acc20 : List (Array GF8) := acc19 ++ [row20]
private def acc21 : List (Array GF8) := acc20 ++ [row21]
private def acc22 : List (Array GF8) := acc21 ++ [row22]
private def acc23 : List (Array GF8) := acc22 ++ [row23]
private def acc24 : List (Array GF8) := acc23 ++ [row24]
private def acc25 : List (Array GF8) := acc24 ++ [row25]
private def acc26 : List (Array GF8) := acc25 ++ [row26]
private def acc27 : List (Array GF8) := acc26 ++ [row27]
private def acc28 : List (Array GF8) := acc27 ++ [row28]
private def acc29 : List (Array GF8) := acc28 ++ [row29]
private def acc30 : List (Array GF8) := acc29 ++ [row30]
private def acc31 : List (Array GF8) := acc30 ++ [row31]
private def acc32 : List (Array GF8) := acc31 ++ [row32]
private def acc33 : List (Array GF8) := acc32 ++ [row33]
private def acc34 : List (Array GF8) := acc33 ++ [row34]
private def acc35 : List (Array GF8) := acc34 ++ [row35]
private def acc36 : List (Array GF8) := acc35 ++ [row36]
private def acc37 : List (Array GF8) := acc36 ++ [row37]
private def acc38 : List (Array GF8) := acc37 ++ [row38]
private def acc39 : List (Array GF8) := acc38 ++ [row39]
private def acc40 : List (Array GF8) := acc39 ++ [row40]
private def acc41 : List (Array GF8) := acc40 ++ [row41]
private def acc42 : List (Array GF8) := acc41 ++ [row42]
private def acc43 : List (Array GF8) := acc42 ++ [row43]
private def acc44 : List (Array GF8) := acc43 ++ [row44]
private def acc45 : List (Array GF8) := acc44 ++ [row45]
private def acc46 : List (Array GF8) := acc45 ++ [row46]
private def acc47 : List (Array GF8) := acc46 ++ [row47]
private def acc48 : List (Array GF8) := acc47 ++ [row48]
private def acc49 : List (Array GF8) := acc48 ++ [row49]
private def acc50 : List (Array GF8) := acc49 ++ [row50]
private def acc51 : List (Array GF8) := acc50 ++ [row51]
private def acc52 : List (Array GF8) := acc51 ++ [row52]
private def acc53 : List (Array GF8) := acc52 ++ [row53]
private def acc54 : List (Array GF8) := acc53 ++ [row54]
private def acc55 : List (Array GF8) := acc54 ++ [row55]
private def acc56 : List (Array GF8) := acc55 ++ [row56]
private def acc57 : List (Array GF8) := acc56 ++ [row57]
private def acc58 : List (Array GF8) := acc57 ++ [row58]
private def acc59 : List (Array GF8) := acc58 ++ [row59]
private def acc60 : List (Array GF8) := acc59 ++ [row60]
private def acc61 : List (Array GF8) := acc60 ++ [row61]
private def acc62 : List (Array GF8) := acc61 ++ [row62]
private def acc63 : List (Array GF8) := acc62 ++ [row63]
private def acc64 : List (Array GF8) := acc63 ++ [row64]
private def acc65 : List (Array GF8) := acc64 ++ [row65]
private def acc66 : List (Array GF8) := acc65 ++ [row66]
private def acc67 : List (Array GF8) := acc66 ++ [row67]
private def acc68 : List (Array GF8) := acc67 ++ [row68]
private def acc69 : List (Array GF8) := acc68 ++ [row69]
private def acc70 : List (Array GF8) := acc69 ++ [row70]
private def acc71 : List (Array GF8) := acc70 ++ [row71]
private def acc72 : List (Array GF8) := acc71 ++ [row72]
private def acc73 : List (Array GF8) := acc72 ++ [row73]
private def acc74 : List (Array GF8) := acc73 ++ [row74]
private def acc75 : List (Array GF8) := acc74 ++ [row75]
private def acc76 : List (Array GF8) := acc75 ++ [row76]
private def acc77 : List (Array GF8) := acc76 ++ [row77]
private def acc78 : List (Array GF8) := acc77 ++ [row78]
private def acc79 : List (Array GF8) := acc78 ++ [row79]
private def acc80 : List (Array GF8) := acc79 ++ [row80]

private theorem bfs_step_1_literal :
    bfsStep row1 row2 acc0 (0, true) = acc1 := by
  change acc0 ++ [mulArr row0 row1] = acc1
  exact congrArg (fun x => acc0 ++ [x]) product_1_literal

private theorem bfs_step_2_literal :
    bfsStep row1 row2 acc1 (0, false) = acc2 := by
  change acc1 ++ [mulArr row0 row2] = acc2
  exact congrArg (fun x => acc1 ++ [x]) product_2_literal

private theorem bfs_step_3_literal :
    bfsStep row1 row2 acc2 (1, true) = acc3 := by
  change acc2 ++ [mulArr row1 row1] = acc3
  exact congrArg (fun x => acc2 ++ [x]) product_3_literal

private theorem bfs_step_4_literal :
    bfsStep row1 row2 acc3 (1, false) = acc4 := by
  change acc3 ++ [mulArr row1 row2] = acc4
  exact congrArg (fun x => acc3 ++ [x]) product_4_literal

private theorem bfs_step_5_literal :
    bfsStep row1 row2 acc4 (2, true) = acc5 := by
  change acc4 ++ [mulArr row2 row1] = acc5
  exact congrArg (fun x => acc4 ++ [x]) product_5_literal

private theorem bfs_step_6_literal :
    bfsStep row1 row2 acc5 (2, false) = acc6 := by
  change acc5 ++ [mulArr row2 row2] = acc6
  exact congrArg (fun x => acc5 ++ [x]) product_6_literal

private theorem bfs_step_7_literal :
    bfsStep row1 row2 acc6 (3, false) = acc7 := by
  change acc6 ++ [mulArr row3 row2] = acc7
  exact congrArg (fun x => acc6 ++ [x]) product_7_literal

private theorem bfs_step_8_literal :
    bfsStep row1 row2 acc7 (4, true) = acc8 := by
  change acc7 ++ [mulArr row4 row1] = acc8
  exact congrArg (fun x => acc7 ++ [x]) product_8_literal

private theorem bfs_step_9_literal :
    bfsStep row1 row2 acc8 (4, false) = acc9 := by
  change acc8 ++ [mulArr row4 row2] = acc9
  exact congrArg (fun x => acc8 ++ [x]) product_9_literal

private theorem bfs_step_10_literal :
    bfsStep row1 row2 acc9 (5, true) = acc10 := by
  change acc9 ++ [mulArr row5 row1] = acc10
  exact congrArg (fun x => acc9 ++ [x]) product_10_literal

private theorem bfs_step_11_literal :
    bfsStep row1 row2 acc10 (5, false) = acc11 := by
  change acc10 ++ [mulArr row5 row2] = acc11
  exact congrArg (fun x => acc10 ++ [x]) product_11_literal

private theorem bfs_step_12_literal :
    bfsStep row1 row2 acc11 (6, true) = acc12 := by
  change acc11 ++ [mulArr row6 row1] = acc12
  exact congrArg (fun x => acc11 ++ [x]) product_12_literal

private theorem bfs_step_13_literal :
    bfsStep row1 row2 acc12 (7, true) = acc13 := by
  change acc12 ++ [mulArr row7 row1] = acc13
  exact congrArg (fun x => acc12 ++ [x]) product_13_literal

private theorem bfs_step_14_literal :
    bfsStep row1 row2 acc13 (7, false) = acc14 := by
  change acc13 ++ [mulArr row7 row2] = acc14
  exact congrArg (fun x => acc13 ++ [x]) product_14_literal

private theorem bfs_step_15_literal :
    bfsStep row1 row2 acc14 (8, true) = acc15 := by
  change acc14 ++ [mulArr row8 row1] = acc15
  exact congrArg (fun x => acc14 ++ [x]) product_15_literal

private theorem bfs_step_16_literal :
    bfsStep row1 row2 acc15 (8, false) = acc16 := by
  change acc15 ++ [mulArr row8 row2] = acc16
  exact congrArg (fun x => acc15 ++ [x]) product_16_literal

private theorem bfs_step_17_literal :
    bfsStep row1 row2 acc16 (9, true) = acc17 := by
  change acc16 ++ [mulArr row9 row1] = acc17
  exact congrArg (fun x => acc16 ++ [x]) product_17_literal

private theorem bfs_step_18_literal :
    bfsStep row1 row2 acc17 (10, false) = acc18 := by
  change acc17 ++ [mulArr row10 row2] = acc18
  exact congrArg (fun x => acc17 ++ [x]) product_18_literal

private theorem bfs_step_19_literal :
    bfsStep row1 row2 acc18 (11, false) = acc19 := by
  change acc18 ++ [mulArr row11 row2] = acc19
  exact congrArg (fun x => acc18 ++ [x]) product_19_literal

private theorem bfs_step_20_literal :
    bfsStep row1 row2 acc19 (12, false) = acc20 := by
  change acc19 ++ [mulArr row12 row2] = acc20
  exact congrArg (fun x => acc19 ++ [x]) product_20_literal

private theorem bfs_step_21_literal :
    bfsStep row1 row2 acc20 (13, true) = acc21 := by
  change acc20 ++ [mulArr row13 row1] = acc21
  exact congrArg (fun x => acc20 ++ [x]) product_21_literal

private theorem bfs_step_22_literal :
    bfsStep row1 row2 acc21 (13, false) = acc22 := by
  change acc21 ++ [mulArr row13 row2] = acc22
  exact congrArg (fun x => acc21 ++ [x]) product_22_literal

private theorem bfs_step_23_literal :
    bfsStep row1 row2 acc22 (14, true) = acc23 := by
  change acc22 ++ [mulArr row14 row1] = acc23
  exact congrArg (fun x => acc22 ++ [x]) product_23_literal

private theorem bfs_step_24_literal :
    bfsStep row1 row2 acc23 (15, false) = acc24 := by
  change acc23 ++ [mulArr row15 row2] = acc24
  exact congrArg (fun x => acc23 ++ [x]) product_24_literal

private theorem bfs_step_25_literal :
    bfsStep row1 row2 acc24 (16, false) = acc25 := by
  change acc24 ++ [mulArr row16 row2] = acc25
  exact congrArg (fun x => acc24 ++ [x]) product_25_literal

private theorem bfs_step_26_literal :
    bfsStep row1 row2 acc25 (17, false) = acc26 := by
  change acc25 ++ [mulArr row17 row2] = acc26
  exact congrArg (fun x => acc25 ++ [x]) product_26_literal

private theorem bfs_step_27_literal :
    bfsStep row1 row2 acc26 (18, true) = acc27 := by
  change acc26 ++ [mulArr row18 row1] = acc27
  exact congrArg (fun x => acc26 ++ [x]) product_27_literal

private theorem bfs_step_28_literal :
    bfsStep row1 row2 acc27 (18, false) = acc28 := by
  change acc27 ++ [mulArr row18 row2] = acc28
  exact congrArg (fun x => acc27 ++ [x]) product_28_literal

private theorem bfs_step_29_literal :
    bfsStep row1 row2 acc28 (19, true) = acc29 := by
  change acc28 ++ [mulArr row19 row1] = acc29
  exact congrArg (fun x => acc28 ++ [x]) product_29_literal

private theorem bfs_step_30_literal :
    bfsStep row1 row2 acc29 (20, false) = acc30 := by
  change acc29 ++ [mulArr row20 row2] = acc30
  exact congrArg (fun x => acc29 ++ [x]) product_30_literal

private theorem bfs_step_31_literal :
    bfsStep row1 row2 acc30 (21, false) = acc31 := by
  change acc30 ++ [mulArr row21 row2] = acc31
  exact congrArg (fun x => acc30 ++ [x]) product_31_literal

private theorem bfs_step_32_literal :
    bfsStep row1 row2 acc31 (22, false) = acc32 := by
  change acc31 ++ [mulArr row22 row2] = acc32
  exact congrArg (fun x => acc31 ++ [x]) product_32_literal

private theorem bfs_step_33_literal :
    bfsStep row1 row2 acc32 (23, false) = acc33 := by
  change acc32 ++ [mulArr row23 row2] = acc33
  exact congrArg (fun x => acc32 ++ [x]) product_33_literal

private theorem bfs_step_34_literal :
    bfsStep row1 row2 acc33 (24, true) = acc34 := by
  change acc33 ++ [mulArr row24 row1] = acc34
  exact congrArg (fun x => acc33 ++ [x]) product_34_literal

private theorem bfs_step_35_literal :
    bfsStep row1 row2 acc34 (24, false) = acc35 := by
  change acc34 ++ [mulArr row24 row2] = acc35
  exact congrArg (fun x => acc34 ++ [x]) product_35_literal

private theorem bfs_step_36_literal :
    bfsStep row1 row2 acc35 (25, true) = acc36 := by
  change acc35 ++ [mulArr row25 row1] = acc36
  exact congrArg (fun x => acc35 ++ [x]) product_36_literal

private theorem bfs_step_37_literal :
    bfsStep row1 row2 acc36 (26, false) = acc37 := by
  change acc36 ++ [mulArr row26 row2] = acc37
  exact congrArg (fun x => acc36 ++ [x]) product_37_literal

private theorem bfs_step_38_literal :
    bfsStep row1 row2 acc37 (27, true) = acc38 := by
  change acc37 ++ [mulArr row27 row1] = acc38
  exact congrArg (fun x => acc37 ++ [x]) product_38_literal

private theorem bfs_step_39_literal :
    bfsStep row1 row2 acc38 (27, false) = acc39 := by
  change acc38 ++ [mulArr row27 row2] = acc39
  exact congrArg (fun x => acc38 ++ [x]) product_39_literal

private theorem bfs_step_40_literal :
    bfsStep row1 row2 acc39 (28, true) = acc40 := by
  change acc39 ++ [mulArr row28 row1] = acc40
  exact congrArg (fun x => acc39 ++ [x]) product_40_literal

private theorem bfs_step_41_literal :
    bfsStep row1 row2 acc40 (29, false) = acc41 := by
  change acc40 ++ [mulArr row29 row2] = acc41
  exact congrArg (fun x => acc40 ++ [x]) product_41_literal

private theorem bfs_step_42_literal :
    bfsStep row1 row2 acc41 (30, true) = acc42 := by
  change acc41 ++ [mulArr row30 row1] = acc42
  exact congrArg (fun x => acc41 ++ [x]) product_42_literal

private theorem bfs_step_43_literal :
    bfsStep row1 row2 acc42 (31, true) = acc43 := by
  change acc42 ++ [mulArr row31 row1] = acc43
  exact congrArg (fun x => acc42 ++ [x]) product_43_literal

private theorem bfs_step_44_literal :
    bfsStep row1 row2 acc43 (31, false) = acc44 := by
  change acc43 ++ [mulArr row31 row2] = acc44
  exact congrArg (fun x => acc43 ++ [x]) product_44_literal

private theorem bfs_step_45_literal :
    bfsStep row1 row2 acc44 (32, true) = acc45 := by
  change acc44 ++ [mulArr row32 row1] = acc45
  exact congrArg (fun x => acc44 ++ [x]) product_45_literal

private theorem bfs_step_46_literal :
    bfsStep row1 row2 acc45 (33, false) = acc46 := by
  change acc45 ++ [mulArr row33 row2] = acc46
  exact congrArg (fun x => acc45 ++ [x]) product_46_literal

private theorem bfs_step_47_literal :
    bfsStep row1 row2 acc46 (34, true) = acc47 := by
  change acc46 ++ [mulArr row34 row1] = acc47
  exact congrArg (fun x => acc46 ++ [x]) product_47_literal

private theorem bfs_step_48_literal :
    bfsStep row1 row2 acc47 (34, false) = acc48 := by
  change acc47 ++ [mulArr row34 row2] = acc48
  exact congrArg (fun x => acc47 ++ [x]) product_48_literal

private theorem bfs_step_49_literal :
    bfsStep row1 row2 acc48 (35, true) = acc49 := by
  change acc48 ++ [mulArr row35 row1] = acc49
  exact congrArg (fun x => acc48 ++ [x]) product_49_literal

private theorem bfs_step_50_literal :
    bfsStep row1 row2 acc49 (36, false) = acc50 := by
  change acc49 ++ [mulArr row36 row2] = acc50
  exact congrArg (fun x => acc49 ++ [x]) product_50_literal

private theorem bfs_step_51_literal :
    bfsStep row1 row2 acc50 (37, true) = acc51 := by
  change acc50 ++ [mulArr row37 row1] = acc51
  exact congrArg (fun x => acc50 ++ [x]) product_51_literal

private theorem bfs_step_52_literal :
    bfsStep row1 row2 acc51 (38, false) = acc52 := by
  change acc51 ++ [mulArr row38 row2] = acc52
  exact congrArg (fun x => acc51 ++ [x]) product_52_literal

private theorem bfs_step_53_literal :
    bfsStep row1 row2 acc52 (39, false) = acc53 := by
  change acc52 ++ [mulArr row39 row2] = acc53
  exact congrArg (fun x => acc52 ++ [x]) product_53_literal

private theorem bfs_step_54_literal :
    bfsStep row1 row2 acc53 (40, false) = acc54 := by
  change acc53 ++ [mulArr row40 row2] = acc54
  exact congrArg (fun x => acc53 ++ [x]) product_54_literal

private theorem bfs_step_55_literal :
    bfsStep row1 row2 acc54 (41, false) = acc55 := by
  change acc54 ++ [mulArr row41 row2] = acc55
  exact congrArg (fun x => acc54 ++ [x]) product_55_literal

private theorem bfs_step_56_literal :
    bfsStep row1 row2 acc55 (42, false) = acc56 := by
  change acc55 ++ [mulArr row42 row2] = acc56
  exact congrArg (fun x => acc55 ++ [x]) product_56_literal

private theorem bfs_step_57_literal :
    bfsStep row1 row2 acc56 (43, true) = acc57 := by
  change acc56 ++ [mulArr row43 row1] = acc57
  exact congrArg (fun x => acc56 ++ [x]) product_57_literal

private theorem bfs_step_58_literal :
    bfsStep row1 row2 acc57 (43, false) = acc58 := by
  change acc57 ++ [mulArr row43 row2] = acc58
  exact congrArg (fun x => acc57 ++ [x]) product_58_literal

private theorem bfs_step_59_literal :
    bfsStep row1 row2 acc58 (44, true) = acc59 := by
  change acc58 ++ [mulArr row44 row1] = acc59
  exact congrArg (fun x => acc58 ++ [x]) product_59_literal

private theorem bfs_step_60_literal :
    bfsStep row1 row2 acc59 (45, false) = acc60 := by
  change acc59 ++ [mulArr row45 row2] = acc60
  exact congrArg (fun x => acc59 ++ [x]) product_60_literal

private theorem bfs_step_61_literal :
    bfsStep row1 row2 acc60 (46, true) = acc61 := by
  change acc60 ++ [mulArr row46 row1] = acc61
  exact congrArg (fun x => acc60 ++ [x]) product_61_literal

private theorem bfs_step_62_literal :
    bfsStep row1 row2 acc61 (47, false) = acc62 := by
  change acc61 ++ [mulArr row47 row2] = acc62
  exact congrArg (fun x => acc61 ++ [x]) product_62_literal

private theorem bfs_step_63_literal :
    bfsStep row1 row2 acc62 (48, false) = acc63 := by
  change acc62 ++ [mulArr row48 row2] = acc63
  exact congrArg (fun x => acc62 ++ [x]) product_63_literal

private theorem bfs_step_64_literal :
    bfsStep row1 row2 acc63 (49, false) = acc64 := by
  change acc63 ++ [mulArr row49 row2] = acc64
  exact congrArg (fun x => acc63 ++ [x]) product_64_literal

private theorem bfs_step_65_literal :
    bfsStep row1 row2 acc64 (50, false) = acc65 := by
  change acc64 ++ [mulArr row50 row2] = acc65
  exact congrArg (fun x => acc64 ++ [x]) product_65_literal

private theorem bfs_step_66_literal :
    bfsStep row1 row2 acc65 (51, false) = acc66 := by
  change acc65 ++ [mulArr row51 row2] = acc66
  exact congrArg (fun x => acc65 ++ [x]) product_66_literal

private theorem bfs_step_67_literal :
    bfsStep row1 row2 acc66 (52, false) = acc67 := by
  change acc66 ++ [mulArr row52 row2] = acc67
  exact congrArg (fun x => acc66 ++ [x]) product_67_literal

private theorem bfs_step_68_literal :
    bfsStep row1 row2 acc67 (54, false) = acc68 := by
  change acc67 ++ [mulArr row54 row2] = acc68
  exact congrArg (fun x => acc67 ++ [x]) product_68_literal

private theorem bfs_step_69_literal :
    bfsStep row1 row2 acc68 (56, false) = acc69 := by
  change acc68 ++ [mulArr row56 row2] = acc69
  exact congrArg (fun x => acc68 ++ [x]) product_69_literal

private theorem bfs_step_70_literal :
    bfsStep row1 row2 acc69 (57, false) = acc70 := by
  change acc69 ++ [mulArr row57 row2] = acc70
  exact congrArg (fun x => acc69 ++ [x]) product_70_literal

private theorem bfs_step_71_literal :
    bfsStep row1 row2 acc70 (58, false) = acc71 := by
  change acc70 ++ [mulArr row58 row2] = acc71
  exact congrArg (fun x => acc70 ++ [x]) product_71_literal

private theorem bfs_step_72_literal :
    bfsStep row1 row2 acc71 (59, false) = acc72 := by
  change acc71 ++ [mulArr row59 row2] = acc72
  exact congrArg (fun x => acc71 ++ [x]) product_72_literal

private theorem bfs_step_73_literal :
    bfsStep row1 row2 acc72 (60, false) = acc73 := by
  change acc72 ++ [mulArr row60 row2] = acc73
  exact congrArg (fun x => acc72 ++ [x]) product_73_literal

private theorem bfs_step_74_literal :
    bfsStep row1 row2 acc73 (61, false) = acc74 := by
  change acc73 ++ [mulArr row61 row2] = acc74
  exact congrArg (fun x => acc73 ++ [x]) product_74_literal

private theorem bfs_step_75_literal :
    bfsStep row1 row2 acc74 (62, false) = acc75 := by
  change acc74 ++ [mulArr row62 row2] = acc75
  exact congrArg (fun x => acc74 ++ [x]) product_75_literal

private theorem bfs_step_76_literal :
    bfsStep row1 row2 acc75 (64, false) = acc76 := by
  change acc75 ++ [mulArr row64 row2] = acc76
  exact congrArg (fun x => acc75 ++ [x]) product_76_literal

private theorem bfs_step_77_literal :
    bfsStep row1 row2 acc76 (66, false) = acc77 := by
  change acc76 ++ [mulArr row66 row2] = acc77
  exact congrArg (fun x => acc76 ++ [x]) product_77_literal

private theorem bfs_step_78_literal :
    bfsStep row1 row2 acc77 (70, false) = acc78 := by
  change acc77 ++ [mulArr row70 row2] = acc78
  exact congrArg (fun x => acc77 ++ [x]) product_78_literal

private theorem bfs_step_79_literal :
    bfsStep row1 row2 acc78 (72, false) = acc79 := by
  change acc78 ++ [mulArr row72 row2] = acc79
  exact congrArg (fun x => acc78 ++ [x]) product_79_literal

private theorem bfs_step_80_literal :
    bfsStep row1 row2 acc79 (74, false) = acc80 := by
  change acc79 ++ [mulArr row74 row2] = acc80
  exact congrArg (fun x => acc79 ++ [x]) product_80_literal

private theorem sylowElems_literal : sylowElems = acc80 := by
  rw [sylowElems, genA_literal, genB_literal]
  unfold bfsElems bfsPar
  rw [oneArr_literal]
  change List.foldl (bfsStep row1 row2) acc0 _ = acc80
  rw [List.foldl_cons, bfs_step_1_literal]
  rw [List.foldl_cons, bfs_step_2_literal]
  rw [List.foldl_cons, bfs_step_3_literal]
  rw [List.foldl_cons, bfs_step_4_literal]
  rw [List.foldl_cons, bfs_step_5_literal]
  rw [List.foldl_cons, bfs_step_6_literal]
  rw [List.foldl_cons, bfs_step_7_literal]
  rw [List.foldl_cons, bfs_step_8_literal]
  rw [List.foldl_cons, bfs_step_9_literal]
  rw [List.foldl_cons, bfs_step_10_literal]
  rw [List.foldl_cons, bfs_step_11_literal]
  rw [List.foldl_cons, bfs_step_12_literal]
  rw [List.foldl_cons, bfs_step_13_literal]
  rw [List.foldl_cons, bfs_step_14_literal]
  rw [List.foldl_cons, bfs_step_15_literal]
  rw [List.foldl_cons, bfs_step_16_literal]
  rw [List.foldl_cons, bfs_step_17_literal]
  rw [List.foldl_cons, bfs_step_18_literal]
  rw [List.foldl_cons, bfs_step_19_literal]
  rw [List.foldl_cons, bfs_step_20_literal]
  rw [List.foldl_cons, bfs_step_21_literal]
  rw [List.foldl_cons, bfs_step_22_literal]
  rw [List.foldl_cons, bfs_step_23_literal]
  rw [List.foldl_cons, bfs_step_24_literal]
  rw [List.foldl_cons, bfs_step_25_literal]
  rw [List.foldl_cons, bfs_step_26_literal]
  rw [List.foldl_cons, bfs_step_27_literal]
  rw [List.foldl_cons, bfs_step_28_literal]
  rw [List.foldl_cons, bfs_step_29_literal]
  rw [List.foldl_cons, bfs_step_30_literal]
  rw [List.foldl_cons, bfs_step_31_literal]
  rw [List.foldl_cons, bfs_step_32_literal]
  rw [List.foldl_cons, bfs_step_33_literal]
  rw [List.foldl_cons, bfs_step_34_literal]
  rw [List.foldl_cons, bfs_step_35_literal]
  rw [List.foldl_cons, bfs_step_36_literal]
  rw [List.foldl_cons, bfs_step_37_literal]
  rw [List.foldl_cons, bfs_step_38_literal]
  rw [List.foldl_cons, bfs_step_39_literal]
  rw [List.foldl_cons, bfs_step_40_literal]
  rw [List.foldl_cons, bfs_step_41_literal]
  rw [List.foldl_cons, bfs_step_42_literal]
  rw [List.foldl_cons, bfs_step_43_literal]
  rw [List.foldl_cons, bfs_step_44_literal]
  rw [List.foldl_cons, bfs_step_45_literal]
  rw [List.foldl_cons, bfs_step_46_literal]
  rw [List.foldl_cons, bfs_step_47_literal]
  rw [List.foldl_cons, bfs_step_48_literal]
  rw [List.foldl_cons, bfs_step_49_literal]
  rw [List.foldl_cons, bfs_step_50_literal]
  rw [List.foldl_cons, bfs_step_51_literal]
  rw [List.foldl_cons, bfs_step_52_literal]
  rw [List.foldl_cons, bfs_step_53_literal]
  rw [List.foldl_cons, bfs_step_54_literal]
  rw [List.foldl_cons, bfs_step_55_literal]
  rw [List.foldl_cons, bfs_step_56_literal]
  rw [List.foldl_cons, bfs_step_57_literal]
  rw [List.foldl_cons, bfs_step_58_literal]
  rw [List.foldl_cons, bfs_step_59_literal]
  rw [List.foldl_cons, bfs_step_60_literal]
  rw [List.foldl_cons, bfs_step_61_literal]
  rw [List.foldl_cons, bfs_step_62_literal]
  rw [List.foldl_cons, bfs_step_63_literal]
  rw [List.foldl_cons, bfs_step_64_literal]
  rw [List.foldl_cons, bfs_step_65_literal]
  rw [List.foldl_cons, bfs_step_66_literal]
  rw [List.foldl_cons, bfs_step_67_literal]
  rw [List.foldl_cons, bfs_step_68_literal]
  rw [List.foldl_cons, bfs_step_69_literal]
  rw [List.foldl_cons, bfs_step_70_literal]
  rw [List.foldl_cons, bfs_step_71_literal]
  rw [List.foldl_cons, bfs_step_72_literal]
  rw [List.foldl_cons, bfs_step_73_literal]
  rw [List.foldl_cons, bfs_step_74_literal]
  rw [List.foldl_cons, bfs_step_75_literal]
  rw [List.foldl_cons, bfs_step_76_literal]
  rw [List.foldl_cons, bfs_step_77_literal]
  rw [List.foldl_cons, bfs_step_78_literal]
  rw [List.foldl_cons, bfs_step_79_literal]
  rw [List.foldl_cons, bfs_step_80_literal]
  rfl

private def centerPred (x : Array GF8) : Bool := commutes x row1 && commutes x row2

private theorem center_acc_0 : acc0.filter centerPred = [row0] := by
  change ([row0] : List (Array GF8)).filter centerPred = _
  rw [List.filter_cons_of_pos (p := centerPred) (a := row0) center_test_0]
  rfl

private theorem center_acc_1 : acc1.filter centerPred = [row0] := by
  change (acc0 ++ [row1]).filter centerPred = _
  rw [List.filter_append, center_acc_0]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_1]; decide)]
  rfl

private theorem center_acc_2 : acc2.filter centerPred = [row0] := by
  change (acc1 ++ [row2]).filter centerPred = _
  rw [List.filter_append, center_acc_1]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_2]; decide)]
  rfl

private theorem center_acc_3 : acc3.filter centerPred = [row0] := by
  change (acc2 ++ [row3]).filter centerPred = _
  rw [List.filter_append, center_acc_2]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_3]; decide)]
  rfl

private theorem center_acc_4 : acc4.filter centerPred = [row0] := by
  change (acc3 ++ [row4]).filter centerPred = _
  rw [List.filter_append, center_acc_3]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_4]; decide)]
  rfl

private theorem center_acc_5 : acc5.filter centerPred = [row0] := by
  change (acc4 ++ [row5]).filter centerPred = _
  rw [List.filter_append, center_acc_4]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_5]; decide)]
  rfl

private theorem center_acc_6 : acc6.filter centerPred = [row0] := by
  change (acc5 ++ [row6]).filter centerPred = _
  rw [List.filter_append, center_acc_5]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_6]; decide)]
  rfl

private theorem center_acc_7 : acc7.filter centerPred = [row0] := by
  change (acc6 ++ [row7]).filter centerPred = _
  rw [List.filter_append, center_acc_6]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_7]; decide)]
  rfl

private theorem center_acc_8 : acc8.filter centerPred = [row0] := by
  change (acc7 ++ [row8]).filter centerPred = _
  rw [List.filter_append, center_acc_7]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_8]; decide)]
  rfl

private theorem center_acc_9 : acc9.filter centerPred = [row0] := by
  change (acc8 ++ [row9]).filter centerPred = _
  rw [List.filter_append, center_acc_8]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_9]; decide)]
  rfl

private theorem center_acc_10 : acc10.filter centerPred = [row0] := by
  change (acc9 ++ [row10]).filter centerPred = _
  rw [List.filter_append, center_acc_9]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_10]; decide)]
  rfl

private theorem center_acc_11 : acc11.filter centerPred = [row0] := by
  change (acc10 ++ [row11]).filter centerPred = _
  rw [List.filter_append, center_acc_10]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_11]; decide)]
  rfl

private theorem center_acc_12 : acc12.filter centerPred = [row0] := by
  change (acc11 ++ [row12]).filter centerPred = _
  rw [List.filter_append, center_acc_11]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_12]; decide)]
  rfl

private theorem center_acc_13 : acc13.filter centerPred = [row0] := by
  change (acc12 ++ [row13]).filter centerPred = _
  rw [List.filter_append, center_acc_12]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_13]; decide)]
  rfl

private theorem center_acc_14 : acc14.filter centerPred = [row0] := by
  change (acc13 ++ [row14]).filter centerPred = _
  rw [List.filter_append, center_acc_13]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_14]; decide)]
  rfl

private theorem center_acc_15 : acc15.filter centerPred = [row0] := by
  change (acc14 ++ [row15]).filter centerPred = _
  rw [List.filter_append, center_acc_14]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_15]; decide)]
  rfl

private theorem center_acc_16 : acc16.filter centerPred = [row0] := by
  change (acc15 ++ [row16]).filter centerPred = _
  rw [List.filter_append, center_acc_15]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_16]; decide)]
  rfl

private theorem center_acc_17 : acc17.filter centerPred = [row0] := by
  change (acc16 ++ [row17]).filter centerPred = _
  rw [List.filter_append, center_acc_16]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_17]; decide)]
  rfl

private theorem center_acc_18 : acc18.filter centerPred = [row0] := by
  change (acc17 ++ [row18]).filter centerPred = _
  rw [List.filter_append, center_acc_17]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_18]; decide)]
  rfl

private theorem center_acc_19 : acc19.filter centerPred = [row0] := by
  change (acc18 ++ [row19]).filter centerPred = _
  rw [List.filter_append, center_acc_18]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_19]; decide)]
  rfl

private theorem center_acc_20 : acc20.filter centerPred = [row0] := by
  change (acc19 ++ [row20]).filter centerPred = _
  rw [List.filter_append, center_acc_19]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_20]; decide)]
  rfl

private theorem center_acc_21 : acc21.filter centerPred = [row0] := by
  change (acc20 ++ [row21]).filter centerPred = _
  rw [List.filter_append, center_acc_20]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_21]; decide)]
  rfl

private theorem center_acc_22 : acc22.filter centerPred = [row0] := by
  change (acc21 ++ [row22]).filter centerPred = _
  rw [List.filter_append, center_acc_21]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_22]; decide)]
  rfl

private theorem center_acc_23 : acc23.filter centerPred = [row0] := by
  change (acc22 ++ [row23]).filter centerPred = _
  rw [List.filter_append, center_acc_22]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_23]; decide)]
  rfl

private theorem center_acc_24 : acc24.filter centerPred = [row0] := by
  change (acc23 ++ [row24]).filter centerPred = _
  rw [List.filter_append, center_acc_23]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_24]; decide)]
  rfl

private theorem center_acc_25 : acc25.filter centerPred = [row0] := by
  change (acc24 ++ [row25]).filter centerPred = _
  rw [List.filter_append, center_acc_24]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_25]; decide)]
  rfl

private theorem center_acc_26 : acc26.filter centerPred = [row0] := by
  change (acc25 ++ [row26]).filter centerPred = _
  rw [List.filter_append, center_acc_25]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_26]; decide)]
  rfl

private theorem center_acc_27 : acc27.filter centerPred = [row0] := by
  change (acc26 ++ [row27]).filter centerPred = _
  rw [List.filter_append, center_acc_26]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_27]; decide)]
  rfl

private theorem center_acc_28 : acc28.filter centerPred = [row0] := by
  change (acc27 ++ [row28]).filter centerPred = _
  rw [List.filter_append, center_acc_27]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_28]; decide)]
  rfl

private theorem center_acc_29 : acc29.filter centerPred = [row0] := by
  change (acc28 ++ [row29]).filter centerPred = _
  rw [List.filter_append, center_acc_28]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_29]; decide)]
  rfl

private theorem center_acc_30 : acc30.filter centerPred = [row0] := by
  change (acc29 ++ [row30]).filter centerPred = _
  rw [List.filter_append, center_acc_29]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_30]; decide)]
  rfl

private theorem center_acc_31 : acc31.filter centerPred = [row0] := by
  change (acc30 ++ [row31]).filter centerPred = _
  rw [List.filter_append, center_acc_30]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_31]; decide)]
  rfl

private theorem center_acc_32 : acc32.filter centerPred = [row0] := by
  change (acc31 ++ [row32]).filter centerPred = _
  rw [List.filter_append, center_acc_31]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_32]; decide)]
  rfl

private theorem center_acc_33 : acc33.filter centerPred = [row0] := by
  change (acc32 ++ [row33]).filter centerPred = _
  rw [List.filter_append, center_acc_32]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_33]; decide)]
  rfl

private theorem center_acc_34 : acc34.filter centerPred = [row0] := by
  change (acc33 ++ [row34]).filter centerPred = _
  rw [List.filter_append, center_acc_33]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_34]; decide)]
  rfl

private theorem center_acc_35 : acc35.filter centerPred = [row0] := by
  change (acc34 ++ [row35]).filter centerPred = _
  rw [List.filter_append, center_acc_34]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_35]; decide)]
  rfl

private theorem center_acc_36 : acc36.filter centerPred = [row0] := by
  change (acc35 ++ [row36]).filter centerPred = _
  rw [List.filter_append, center_acc_35]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_36]; decide)]
  rfl

private theorem center_acc_37 : acc37.filter centerPred = [row0] := by
  change (acc36 ++ [row37]).filter centerPred = _
  rw [List.filter_append, center_acc_36]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_37]; decide)]
  rfl

private theorem center_acc_38 : acc38.filter centerPred = [row0] := by
  change (acc37 ++ [row38]).filter centerPred = _
  rw [List.filter_append, center_acc_37]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_38]; decide)]
  rfl

private theorem center_acc_39 : acc39.filter centerPred = [row0] := by
  change (acc38 ++ [row39]).filter centerPred = _
  rw [List.filter_append, center_acc_38]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_39]; decide)]
  rfl

private theorem center_acc_40 : acc40.filter centerPred = [row0] := by
  change (acc39 ++ [row40]).filter centerPred = _
  rw [List.filter_append, center_acc_39]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_40]; decide)]
  rfl

private theorem center_acc_41 : acc41.filter centerPred = [row0] := by
  change (acc40 ++ [row41]).filter centerPred = _
  rw [List.filter_append, center_acc_40]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_41]; decide)]
  rfl

private theorem center_acc_42 : acc42.filter centerPred = [row0] := by
  change (acc41 ++ [row42]).filter centerPred = _
  rw [List.filter_append, center_acc_41]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_42]; decide)]
  rfl

private theorem center_acc_43 : acc43.filter centerPred = [row0] := by
  change (acc42 ++ [row43]).filter centerPred = _
  rw [List.filter_append, center_acc_42]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_43]; decide)]
  rfl

private theorem center_acc_44 : acc44.filter centerPred = [row0] := by
  change (acc43 ++ [row44]).filter centerPred = _
  rw [List.filter_append, center_acc_43]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_44]; decide)]
  rfl

private theorem center_acc_45 : acc45.filter centerPred = [row0] := by
  change (acc44 ++ [row45]).filter centerPred = _
  rw [List.filter_append, center_acc_44]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_45]; decide)]
  rfl

private theorem center_acc_46 : acc46.filter centerPred = [row0] := by
  change (acc45 ++ [row46]).filter centerPred = _
  rw [List.filter_append, center_acc_45]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_46]; decide)]
  rfl

private theorem center_acc_47 : acc47.filter centerPred = [row0] := by
  change (acc46 ++ [row47]).filter centerPred = _
  rw [List.filter_append, center_acc_46]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_47]; decide)]
  rfl

private theorem center_acc_48 : acc48.filter centerPred = [row0] := by
  change (acc47 ++ [row48]).filter centerPred = _
  rw [List.filter_append, center_acc_47]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_48]; decide)]
  rfl

private theorem center_acc_49 : acc49.filter centerPred = [row0] := by
  change (acc48 ++ [row49]).filter centerPred = _
  rw [List.filter_append, center_acc_48]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_49]; decide)]
  rfl

private theorem center_acc_50 : acc50.filter centerPred = [row0] := by
  change (acc49 ++ [row50]).filter centerPred = _
  rw [List.filter_append, center_acc_49]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_50]; decide)]
  rfl

private theorem center_acc_51 : acc51.filter centerPred = [row0] := by
  change (acc50 ++ [row51]).filter centerPred = _
  rw [List.filter_append, center_acc_50]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_51]; decide)]
  rfl

private theorem center_acc_52 : acc52.filter centerPred = [row0] := by
  change (acc51 ++ [row52]).filter centerPred = _
  rw [List.filter_append, center_acc_51]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_52]; decide)]
  rfl

private theorem center_acc_53 : acc53.filter centerPred = [row0] := by
  change (acc52 ++ [row53]).filter centerPred = _
  rw [List.filter_append, center_acc_52]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_53]; decide)]
  rfl

private theorem center_acc_54 : acc54.filter centerPred = [row0] := by
  change (acc53 ++ [row54]).filter centerPred = _
  rw [List.filter_append, center_acc_53]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_54]; decide)]
  rfl

private theorem center_acc_55 : acc55.filter centerPred = [row0] := by
  change (acc54 ++ [row55]).filter centerPred = _
  rw [List.filter_append, center_acc_54]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_55]; decide)]
  rfl

private theorem center_acc_56 : acc56.filter centerPred = [row0] := by
  change (acc55 ++ [row56]).filter centerPred = _
  rw [List.filter_append, center_acc_55]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_56]; decide)]
  rfl

private theorem center_acc_57 : acc57.filter centerPred = [row0] := by
  change (acc56 ++ [row57]).filter centerPred = _
  rw [List.filter_append, center_acc_56]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_57]; decide)]
  rfl

private theorem center_acc_58 : acc58.filter centerPred = [row0] := by
  change (acc57 ++ [row58]).filter centerPred = _
  rw [List.filter_append, center_acc_57]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_58]; decide)]
  rfl

private theorem center_acc_59 : acc59.filter centerPred = [row0] := by
  change (acc58 ++ [row59]).filter centerPred = _
  rw [List.filter_append, center_acc_58]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_59]; decide)]
  rfl

private theorem center_acc_60 : acc60.filter centerPred = [row0] := by
  change (acc59 ++ [row60]).filter centerPred = _
  rw [List.filter_append, center_acc_59]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_60]; decide)]
  rfl

private theorem center_acc_61 : acc61.filter centerPred = [row0] := by
  change (acc60 ++ [row61]).filter centerPred = _
  rw [List.filter_append, center_acc_60]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_61]; decide)]
  rfl

private theorem center_acc_62 : acc62.filter centerPred = [row0] := by
  change (acc61 ++ [row62]).filter centerPred = _
  rw [List.filter_append, center_acc_61]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_62]; decide)]
  rfl

private theorem center_acc_63 : acc63.filter centerPred = [row0] := by
  change (acc62 ++ [row63]).filter centerPred = _
  rw [List.filter_append, center_acc_62]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_63]; decide)]
  rfl

private theorem center_acc_64 : acc64.filter centerPred = [row0] := by
  change (acc63 ++ [row64]).filter centerPred = _
  rw [List.filter_append, center_acc_63]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_64]; decide)]
  rfl

private theorem center_acc_65 : acc65.filter centerPred = [row0] := by
  change (acc64 ++ [row65]).filter centerPred = _
  rw [List.filter_append, center_acc_64]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_65]; decide)]
  rfl

private theorem center_acc_66 : acc66.filter centerPred = [row0] := by
  change (acc65 ++ [row66]).filter centerPred = _
  rw [List.filter_append, center_acc_65]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_66]; decide)]
  rfl

private theorem center_acc_67 : acc67.filter centerPred = [row0] := by
  change (acc66 ++ [row67]).filter centerPred = _
  rw [List.filter_append, center_acc_66]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_67]; decide)]
  rfl

private theorem center_acc_68 : acc68.filter centerPred = [row0] := by
  change (acc67 ++ [row68]).filter centerPred = _
  rw [List.filter_append, center_acc_67]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_68]; decide)]
  rfl

private theorem center_acc_69 : acc69.filter centerPred = [row0] := by
  change (acc68 ++ [row69]).filter centerPred = _
  rw [List.filter_append, center_acc_68]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_69]; decide)]
  rfl

private theorem center_acc_70 : acc70.filter centerPred = [row0, row70] := by
  change (acc69 ++ [row70]).filter centerPred = _
  rw [List.filter_append, center_acc_69]
  rw [List.filter_cons_of_pos (p := centerPred) (a := row70) center_test_70]
  rfl

private theorem center_acc_71 : acc71.filter centerPred = [row0, row70] := by
  change (acc70 ++ [row71]).filter centerPred = _
  rw [List.filter_append, center_acc_70]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_71]; decide)]
  rfl

private theorem center_acc_72 : acc72.filter centerPred = [row0, row70] := by
  change (acc71 ++ [row72]).filter centerPred = _
  rw [List.filter_append, center_acc_71]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_72]; decide)]
  rfl

private theorem center_acc_73 : acc73.filter centerPred = [row0, row70] := by
  change (acc72 ++ [row73]).filter centerPred = _
  rw [List.filter_append, center_acc_72]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_73]; decide)]
  rfl

private theorem center_acc_74 : acc74.filter centerPred = [row0, row70] := by
  change (acc73 ++ [row74]).filter centerPred = _
  rw [List.filter_append, center_acc_73]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_74]; decide)]
  rfl

private theorem center_acc_75 : acc75.filter centerPred = [row0, row70] := by
  change (acc74 ++ [row75]).filter centerPred = _
  rw [List.filter_append, center_acc_74]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_75]; decide)]
  rfl

private theorem center_acc_76 : acc76.filter centerPred = [row0, row70] := by
  change (acc75 ++ [row76]).filter centerPred = _
  rw [List.filter_append, center_acc_75]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_76]; decide)]
  rfl

private theorem center_acc_77 : acc77.filter centerPred = [row0, row70, row77] := by
  change (acc76 ++ [row77]).filter centerPred = _
  rw [List.filter_append, center_acc_76]
  rw [List.filter_cons_of_pos (p := centerPred) (a := row77) center_test_77]
  rfl

private theorem center_acc_78 : acc78.filter centerPred = [row0, row70, row77] := by
  change (acc77 ++ [row78]).filter centerPred = _
  rw [List.filter_append, center_acc_77]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_78]; decide)]
  rfl

private theorem center_acc_79 : acc79.filter centerPred = [row0, row70, row77] := by
  change (acc78 ++ [row79]).filter centerPred = _
  rw [List.filter_append, center_acc_78]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_79]; decide)]
  rfl

private theorem center_acc_80 : acc80.filter centerPred = [row0, row70, row77] := by
  change (acc79 ++ [row80]).filter centerPred = _
  rw [List.filter_append, center_acc_79]
  rw [List.filter_cons_of_neg (by rw [centerPred, center_test_80]; decide)]
  rfl

theorem d4_two_center_candidates_length :
    (sylowElems.filter fun x => commutes x genA && commutes x genB).length = 3 := by
  rw [sylowElems_literal, genA_literal, genB_literal]
  change (acc80.filter centerPred).length = 3
  rw [center_acc_80]
  rfl

end CFSG.LocalAnalysis.UniquenessCase.UC22.R856NormalFour
