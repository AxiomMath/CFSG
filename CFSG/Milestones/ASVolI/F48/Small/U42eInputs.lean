module

public import CFSG.Certificates.CosetTablePresented
public meta import CFSG.Certificates.CosetTablePresented
public import CFSG.Milestones.ASVolI.F48.Small.EngCheck
public import CFSG.Milestones.ASVolI.F48.Small.U42LetterData
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutLists
public meta import Mathlib
public import Mathlib

public section

namespace CFSG.ASVolI

open CFSG.CosetTable CFSG.Quasithin

@[expose] def burnsideF48s_u42eLetter (c : Char) : Fin 5 × Bool :=
  (⟨"abpqf".toList.idxOf c.toLower % 5, Nat.mod_lt _ (by norm_num)⟩, c.isLower)

@[expose] def burnsideF48s_u42eWord (s : String) : List (Fin 5 × Bool) :=
  s.toList.map burnsideF48s_u42eLetter

@[expose] def burnsideF48s_u42eWords (l : List String) : List (List (Fin 5 × Bool)) :=
  l.map burnsideF48s_u42eWord

@[expose] def burnsideF48s_u42eR1S : List String :=
  ["pp", "ff", "bb", "afaf", "fpfapA", "afpfAp", "aaaaaa", "fpfbfpfb", "bpfpbpfp", "bAAbAAbAA",
    "bpbfbpAAfpa", "bAbabAbpApAp", "pApApApApApA"]
@[expose] def burnsideF48s_u42eR2S : List String :=
  ["bb", "qq", "ff", "qAqA", "fafa", "qbqbqb", "aaaaaa", "qafqaaf", "abfaaabAAf",
    "fbabAbfababAbA", "abAbAqbabAbaqbqAb", "babAbfbAAAbabAbqfq"]
@[expose] def burnsideF48s_u42eP1Str : String :=
  " a A b p f aa ab ap af AA Ab Ap Af ba bA bp bf pa pA pb pf fb fp aaa aab aap aaf aba abA \
    abp abf apa apA apb apf afb afp AAb AAp AAf Aba AbA Abp Abf ApA Apb Apf Afb Afp baa bab \
    bap baf bAA bAb bAp bAf bpa bpA bpb bpf bfb bfp pab pap pAb pAp pba pbA pbp pbf pfb pfp \
    fba fbA fbp fbf fpb aaab aaap aaaf aaba aabA aabp aabf aapa aapb aapf aafb aafp abaa \
    abab abap abaf abAA abAb abAp abAf abpa abpA abpb abpf abfb abfp apab apap apAb apAp \
    apba apbA apbp apbf apfb apfp afba afbA afbp afbf afpb AAba AAbA AAbp AAbf AApb AApf \
    AAfb AAfp Abaa Abab Abap Abaf AbAA AbAb AbAp AbAf Abpa AbpA Abpb Abpf Abfb Abfp ApAb \
    ApAp Apba ApbA Apbp Apbf Apfb Apfp Afba AfbA Afbp Afbf Afpb baaa baab baap baaf baba \
    babA babp babf bapa bapb bapf bafb bafp bAAb bAAp bAAf bAba bAbA bAbp bAbf bApA bApb \
    bApf bAfb bAfp bpab bpap bpAb bpAp bpba bpbA bpbp bpbf bpfb bpfp bfba bfbA bfbp bfbf \
    bfpb pabp papa papA papb papf pAbp pApA pApb pApf pbaa pbab pbap pbaf pbAA pbAb pbAp \
    pbAf pbpa pbpA pbpf pbfb pbfp pfba pfbA pfbp pfbf fbaa fbab fbaf fbAA fbAb fbAf fbpa \
    fbpA fbpb fbpf fpba fpbA fpbf aaaba aaabA aaabp aaabf aaapb aaapf aaafb aaafp aabab \
    aabap aabaf aabAA aabAb aabAp aabpa aabpA aabpb aabpf aabfb aabfp aapab aapap aapba \
    aapbA aapbp aapbf aapfb aapfp aafba aafbA aafbp aafbf aafpb abaaa abaap abaaf ababa \
    ababA ababp ababf abapa abapb abapf abafp abAAp abAAf abAba abAbA abAbp abAbf abApA \
    abApb abApf abAfp abpab abpap abpAb abpAp abpba abpbA abpbp abpbf abpfb abpfp abfba \
    abfbA abfbp abfbf abfpb apabp apapa apapA apapb apapf apAbp apApA apApb apApf apbaa \
    apbab apbap apbaf apbAA apbAb apbAp apbAf apbpa apbpA apbpf apbfb apbfp apfba apfbA \
    apfbp apfbf afbab afbaf afbAA afbAb afbpa afbpA afbpb afbpf afpba afpbA afpbf AAbab \
    AAbap AAbAb AAbAp AAbpa AAbpA AAbpb AAbpf AAbfb AAbfp AApba AApbA AApbp AApbf AApfb \
    AApfp AAfbp AAfpb Abaap Ababa AbabA Ababp Ababf Abapa Abapb Abapf Abafp AbAAp AbAba \
    AbAbA AbAbp AbAbf AbApA AbApb AbApf AbAfp Abpab Abpap AbpAb AbpAp Abpba AbpbA Abpbp \
    Abpbf Abpfb Abpfp Abfba AbfbA Abfbp Abfbf Abfpb ApAbp ApApb ApApf Apbaa Apbab Apbap \
    Apbaf ApbAA ApbAb ApbAp ApbAf Apbpa ApbpA Apbpf Apbfb Apbfp Apfba ApfbA Apfbp Apfbf \
    Afbab AfbAb Afbpa AfbpA Afbpb Afbpf Afpba AfpbA Afpbf baaab baaap baabp baapa baapb \
    baapf baafb baafp babaa babap babaf babAA babAb babAf babpA babpb babpf babfb babfp \
    bapab bapap bapbA bapbf bapfb bapfp bafbp bafpb bAAbp bAApb bAApf bAAfb bAAfp bAbaa \
    bAbab bAbaf bAbAA bAbAp bAbAf bAbpa bAbpb bAbpf bAbfb bAbfp bApAb bApAp bApba bApbf \
    bApfb bApfp bAfbp bAfpb bpabp bpapa bpapA bpapf bpAbp bpApA bpApf bpbaa bpbap bpbaf \
    bpbAA bpbAp bpbAf bpbpa bpbpA bpbpf bpbfb bpbfp bpfba bpfbA bpfbp bpfbf bfbaa bfbab \
    bfbaf bfbAA bfbAb bfbAf bfbpa bfbpA bfbpb bfbpf bfpba bfpbA bfpbf pabpa pabpA pabpb \
    pabpf papab papap papAb papAp papbA papbf papfb papfp pAbpa pAbpA pAbpb pAbpf pApAb \
    pApAp pApba pApbf pApfb pApfp pbaaa pbaab pbaap pbaaf pbaba pbabf pbapa pbapb pbapf \
    pbafb pbafp pbAAb pbAAp pbAAf pbAbA pbAbf pbApA pbApb pbApf pbAfb pbAfp pbpap pbpAp \
    pbpfb pbfba pbfbA pbfbp pbfbf pfbaa pfbab pfbaf pfbAA pfbAb pfbAf pfbpa pfbpA pfbpf \
    fbaap fbaba fbabA fbabp fbabf fbafp fbAAp fbAba fbAbA fbAbp fbAbf fbAfp fbpab fbpap \
    fbpAb fbpAp fbpba fbpbA fbpbf fpbaa fpbab fpbap fpbAA fpbAb fpbAp fpbfp aaabab aaabap \
    aaabAb aaabAp aaabfb aaabfp aaapba aaapbA aaapbp aaafbp aaafpb aababa aababA aababp \
    aababf aabapb aabapf aabafp aabAAp aabAba aabAbA aabAbp aabApA aabApb aabpab aabpAb \
    aabpbp aabfba aabfbA aabfbf aapbab aapbap aapbaf aapbAA aapbAb aapbAp aapbpa aapbpA \
    aapbpf aapfba aapfbA aapfbf aafbab aafbAb aafbpa aafbpA aafbpf aafpba aafpbA abaaab \
    abaaap abaapa abaapb abaapf abaafb abaafp ababaa ababap ababaf ababAA ababAb ababAf \
    ababpA ababpf ababfb ababfp abapap abapbA abapbf abapfp abafpb abAApb abAApf abAAfb \
    abAAfp abAbaa abAbab abAbaf abAbAA abAbAp abAbAf abAbpa abAbpb abAbpf abAbfp abApAp \
    abApba abApbf abApfp abAfpb abpabp abpapa abpapf abpAbp abpApA abpApf abpbaf abpbAf \
    abpbpa abpbpA abpbpf abpfba abpfbA abfbaa abfbab abfbaf abfbAA abfbAb abfbAf abfbpa \
    abfbpA abfbpf abfpba abfpbA apabpa apabpA apapap apapAb apapAp apapbA apapfp apAbpa \
    apAbpA apAbpf apApAb apApAp apApbf apApfb apApfp apbaap apbaaf apbaba apbabf apbapa \
    apbapb apbapf apbafp apbAAp apbAAf apbAbA apbAbf apbApA apbApb apbApf apbAfp apbpAp \
    apbpfb apbfba apbfbA apbfbf apfbab apfbaf apfbAA apfbAb apfbpa apfbpA apfbpf afbaba \
    afbabA afbabp afbabf afbafp afbAAp afbAba afbAbA afbAbp afbAbf afbpab afbpap afbpAb \
    afbpAp afbpba afbpbA afpbab afpbap afpbAA afpbAb afpbAp afpbfp AAbaba AAbabA AAbabp \
    AAbapb AAbAba AAbAbA AAbAbp AAbAbf AAbApb AAbpab AAbpAb AAbpbp AApbab AApbap AApbAb \
    AApbAp AApbpf Abaapb Ababaa Ababap Ababaf AbabAA AbabAb AbabAf AbabpA Ababpf Ababfp \
    Abapap AbapbA Abapbf Abapfp Abafpb AbAbaa AbAbab AbAbaf AbAbAA AbAbAp AbAbAf AbAbpa \
    AbAbpf AbAbfb AbAbfp AbApAp AbApbf AbApfp AbAfpb Abpabp Abpapf AbpAbp AbpApf Abpbaf \
    AbpbAf Abpbpa AbpbpA Abpbpf Abpfba AbpfbA Abfbab Abfbaf AbfbAb AbfbAf Abfbpa AbfbpA \
    Abfbpf Abfpba AbfpbA ApAbpa ApAbpA ApApfp Apbaba Apbabf Apbapa Apbapb Apbapf Apbafp \
    ApbAbf ApbApA ApbApf ApbAfp Apbpfb Apbfba ApbfbA Apbfbf Apfbab ApfbAb Apfbpa ApfbpA \
    Apfbpf Afbaba AfbabA Afbabp Afbabf AfbAba AfbAbA AfbAbp AfbAbf Afbpab Afbpap AfbpAb \
    AfbpAp Afbpba AfbpbA Afpbab Afpbap AfpbAb AfpbAp Afpbfp baaaba baaabA baapbA baapbf \
    baapfb baafba baafbA baafbp baafbf baafpb babaaa babaaf babapb babapf babAAp babAAf \
    babAba babAbA babAbf babpAp babpfb babpfp babfbA babfbp bapabp bapbAA bapbAf bapbfb \
    bafbpb bAApba bAApbf bAApfb bAAfbp bAAfpb bAbaap bAbaba bAbabA bAbabf bAbApb bAbApf \
    bAbpap bAbpfb bAbpfp bAbfba bAbfbp bApAbp bApbaa bApbaf bApbfb bAfbpb bpabpA bpabpb \
    bpapAp bpapfp bpAbpa bpAbpb bpApfp bpbaap bpbapb bpbafb bpbafp bpbAAp bpbApb bpbAfb \
    bpbAfp bpbpap bpbpAp bpbpfb bpfbaf bpfbAf bfbabp bfbabf bfbAbp bfbAbf bfbpab bfbpAb \
    bfpbab bfpbAb pabpab pabpAp pabpfp papApb papbAp papbfp pAbpap pAbpAb pAbpfp pApbap \
    pApbfp pbaapf pbaafb pbapab pbapbf pbafbp pbAApf pbAAfb pbApAb pbApbf pbAfbp pbpfba \
    pbpfbA pbpfbf pfbabA pfbafp pfbAba pfbAfp pfbpap pfbpAp fbaapb fbabaa fbabaf fbabAb \
    fbabAf fbabpA fbabpf fbabfb fbAApb fbAbab fbAbaf fbAbAA fbAbAf fbAbpa fbAbpf fbAbfb \
    fpbabf fpbapf fpbAbf fpbApf aaababA aaababp aaabapb aaabAba aaabAbp aaabApb aaapbab \
    aaapbAb aaapbpf aababaa aababAA aababAf aababpA aababpf aababfp aabapbf aabafpb aabAApb \
    aabAbaa aabAbab aabAbAA aabAbAp aabAbpa aabApAp aabApba aabpabp aabfbaf aabfbAf aapbabf \
    aapbafp aapbAbA aapbApA aapbApb aapfbab aapfbAb aafbaba aafbabA aafbAba aafbAbA aafbAbp \
    aafbAbf aafbpab aafbpAb aafpbab aafpbAb abaaaba abaaabA abaapbA abaapbf abaapfb abaafba \
    abaafbA abaafbp abaafbf abaafpb ababaaf ababapf ababAAp ababAAf ababAba ababAbf ababpAp \
    ababpfb ababpfp ababfbp abapbAA abapbAf abapbfb abAApba abAApfb abAAfpb abAbaap abAbaba \
    abAbApb abAbApf abAbpap abAbpfp abApbaa abApbaf abpabpA abpabpb abpapfp abpAbpa abpApfp \
    abpbafp abfbAbp abfbpAb apabpab apapApb apapbAp apAbpap apAbpAb apAbpfp apApbfp apbaapf \
    apbaafb apbapbf apbAAfb apbApbf apbpfbA apfbafp apfbAba apfbpap apfbpAp afbabaa afbabaf \
    afbabAf afbabpf afbAApb afbAbab afbAbaf afbAbAf afbAbpa afbAbpf afpbabf afpbapf afpbAbf \
    AAbabap AAbabpA AAbAbpa AAbAbpf AAbAbfp AAbApbf AAbpAbp AApbAbf Ababapb AbabAAp AbapbAf \
    AbAbApf AbAbpfb AbAbfbp AbApbfb Abpapfp AbpAbpb AbpbAfp Abfbabp Abfbpab Apbapbf Apbpfba \
    ApfbpAp Afpbabf bapbfbA bApbfba aaababpA aaabAbpa aabAbaap aafpbAbf"
@[expose] def burnsideF48s_u42eP2Str : String :=
  " a A b q f aa ab aq af AA Ab Aq Af ba bA bq bf qb qf fb fq aaa aab aaq aaf aba abA abq \
    abf aqb aqf afb afq AAb AAq AAf Aba AbA Abq Abf Aqb Aqf Afb Afq baa bab baq baf bAA bAb \
    bAq bAf bqb bqf bfb bfq qba qbA qbf qfb qfq fba fbA fbq fbf fqb fqf aaab aaba aabA aabq \
    aabf aaqb aafb abaa abab abaq abaf abAA abAb abAq abAf abqb abqf abfb abfq aqba aqbA \
    aqbf aqfb afba afbA afbq afbf afqb AAba AAbA AAbq AAbf AAqb AAfb Abaa Abab Abaq Abaf \
    AbAA AbAb AbAq AbAf Abqb Abqf Abfb Abfq Aqba AqbA Aqbf Aqfb Afba AfbA Afbq Afbf Afqb \
    baaa baab baaq baaf baba babA babq babf baqb baqf bafb bafq bAAb bAAq bAAf bAba bAbA \
    bAbq bAbf bAqb bAqf bAfb bAfq bqba bqbA bqbf bqfb bqfq bfba bfbA bfbq bfbf bfqb bfqf \
    qbaa qbab qbaf qbAA qbAb qbAf qfba qfbA qfbf fbaa fbab fbaq fbaf fbAA fbAb fbAq fbAf \
    fbqf fbfq fqba fqbA fqbf fqfb aaaba aaabA aaabf aabab aabaq aabaf aabAA aabAb aabAq \
    aabqb aabfb aabfq aaqba aaqbA aaqbf aafba aafbA aafbf abaaa abaaq abaaf ababa ababA \
    ababq ababf abaqb abaqf abafq abAAq abAAf abAba abAbA abAbq abAbf abAqb abAqf abAfq \
    abqba abqbA abqbf abqfb abfba abfbA abfbq abfbf abfqb abfqf aqbaa aqbab aqbaf aqbAA \
    aqbAb aqbAf aqfba aqfbA aqfbf afbab afbaq afbaf afbAA afbAb afbAq afbfq afqba afqbA \
    afqbf AAbab AAbaq AAbAb AAbAq AAbqb AAbfb AAbfq AAqba AAqbA AAqbf Abaaq Ababa AbabA \
    Ababq Ababf Abaqb Abaqf Abafq AbAAq AbAba AbAbA AbAbq AbAbf AbAqb AbAqf AbAfq Abqba \
    AbqbA Abqbf Abqfb Abfba AbfbA Abfbq Abfbf Abfqb Abfqf Aqbaa Aqbab Aqbaf AqbAA AqbAb \
    AqbAf Aqfba AqfbA Aqfbf Afbab Afbaq AfbAb AfbAq Afbfq Afqba AfqbA Afqbf baaab baabq \
    baaqb baafb babaa babab babaq babaf babAA babAb babAq babAf babqb babqf babfb babfq \
    baqba baqbA baqbf baqfb bafbq bafqb bAAbq bAAqb bAAfb bAbaa bAbab bAbaq bAbaf bAbAA \
    bAbAb bAbAq bAbAf bAbqb bAbqf bAbfb bAbfq bAqba bAqbA bAqbf bAqfb bAfbq bAfqb bqbaa \
    bqbab bqbaf bqbAA bqbAb bqbAf bqfba bqfbA bqfbf bfbaa bfbab bfbaq bfbaf bfbAA bfbAb \
    bfbAq bfbAf bfbqf bfbfq bfqba bfqbA bfqbf bfqfb qbaab qbaba qbabA qbabq qbabf qbafb \
    qbAAb qbAba qbAbA qbAbq qbAbf qbAfb qfbaa qfbab qfbaf qfbAA qfbAb qfbAf fbaaq fbaba \
    fbabA fbabq fbabf fbaqb fbaqf fbafq fbAAq fbAba fbAbA fbAbq fbAbf fbAqb fbAqf fbAfq \
    fbfqf fqbab fqbAb fqfba fqfbA fqfbf aaabab aaabAb aaabfb aababa aababA aababq aababf \
    aabaqb aabafq aabAAq aabAba aabAbA aabAbq aabAqb aabqba aabqbA aabfba aabfbA aabfbq \
    aabfbf aabfqb aaqbaa aaqbab aaqbAb aaqbAf aafbab aafbAb abaaab abaaqb abaafb ababaa \
    ababab ababaq ababaf ababAA ababAb ababAq ababAf ababqb ababqf ababfb ababfq abaqba \
    abaqbA abaqbf abaqfb abafqb abAAqb abAAfb abAbaa abAbab abAbaq abAbaf abAbAA abAbAb \
    abAbAq abAbAf abAbqb abAbqf abAbfq abAqba abAqbA abAqbf abAqfb abAfqb abqbaa abqbab \
    abqbaf abqbAA abqbAb abqbAf abqfba abqfbA abfbaa abfbab abfbaq abfbaf abfbAA abfbAb \
    abfbAq abfbAf abfbqf abfbfq abfqba abfqbA abfqbf abfqfb aqbaba aqbabA aqbabq aqbabf \
    aqbAba aqbAbA aqbAbq aqbAbf aqfbaa aqfbab aqfbAb aqfbAf afbaba afbabA afbabq afbabf \
    afbaqb afbafq afbAAq afbAba afbAbA afbAbq afbAbf afbAqb afqbab afqbAb AAbaba AAbabA \
    AAbabq AAbaqb AAbAba AAbAbA AAbAbq AAbAbf AAbAqb AAbqba AAbqbA AAbfbq AAbfqb AAqbab \
    AAqbAb Abaaqb Ababaa Ababab Ababaq Ababaf AbabAA AbabAb AbabAq AbabAf Ababqb Ababqf \
    Ababfq Abaqba AbaqbA Abaqbf Abaqfb Abafqb AbAAqb AbAbaa AbAbab AbAbaq AbAbaf AbAbAA \
    AbAbAb AbAbAq AbAbAf AbAbqb AbAbqf AbAbfb AbAbfq AbAqba AbAqbA AbAqbf AbAqfb AbAfqb \
    Abqbaa Abqbab Abqbaf AbqbAA AbqbAb AbqbAf Abqfba AbqfbA Abfbab Abfbaq Abfbaf AbfbAb \
    AbfbAq AbfbAf Abfbqf Abfbfq Abfqba AbfqbA Abfqbf Abfqfb Aqbaba AqbabA Aqbabq Aqbabf \
    AqbAba AqbAbA AqbAbq AqbAbf Aqfbab AqfbAb Afbaba AfbabA Afbabq Afbabf Afbaqb AfbAba \
    AfbAbA AfbAbq AfbAbf AfbAqb Afqbab AfqbAb baaaba baaabA baabqb baaqba baaqbA baaqbf \
    baafba baafbA baafbf babaaa babaaq babaaf bababA bababq bababf babaqb babaqf babafq \
    babAAq babAAf babAba babAbA babAbq babAbf babAqb babAqf babAfq babqbA babqbf babqfb \
    babfbA babfbq babfqb babfqf baqbaa baqbab baqbaf baqbAA baqbAf baqfba baqfbA baqfbf \
    bafqba bafqbA bafqbf bAAbqb bAAqba bAAqbA bAAqbf bAbaaq bAbaba bAbabA bAbabq bAbabf \
    bAbaqb bAbaqf bAbafq bAbAAq bAbAba bAbAbq bAbAbf bAbAqb bAbAqf bAbAfq bAbqba bAbqbf \
    bAbqfb bAbfba bAbfbq bAbfqb bAbfqf bAqbaa bAqbaf bAqbAA bAqbAb bAqbAf bAqfba bAqfbA \
    bAqfbf bAfqba bAfqbA bAfqbf bqbaab bqbabA bqbabf bqbafb bqbAAb bqbAba bqbAbf bqbAfb \
    bqfbaa bqfbab bqfbaf bqfbAA bqfbAb bqfbAf bfbaaq bfbabq bfbabf bfbaqb bfbaqf bfbafq \
    bfbAAq bfbAbq bfbAbf bfbAqb bfbAqf bfbAfq bfbfqf bfqbab bfqbAb bfqfba bfqfbA bfqfbf \
    qbaabq qbabaa qbabaf qbabAA qbabAb qbabAq qbabAf qbabqf qbabfb qbabfq qbafbq qbAAbq \
    qbAbaa qbAbab qbAbaq qbAbaf qbAbAA qbAbAf qbAbqf qbAbfb qbAbfq qbAfbq qfbaba qfbabA \
    qfbabq qfbabf qfbAba qfbAbA qfbAbq qfbAbf fbaaqb fbabaa fbabaq fbabaf fbabAb fbabAq \
    fbabAf fbabqb fbabqf fbabfb fbabfq fbaqba fbaqbA fbaqbf fbaqfb fbafqb fbAAqb fbAbab \
    fbAbaq fbAbaf fbAbAA fbAbAq fbAbAf fbAbqb fbAbqf fbAbfb fbAbfq fbAqba fbAqbA fbAqbf \
    fbAqfb fbAfqb fqbaba fqbabA fqbabf fqbAba fqbAbA fqbAbf fqfbab fqfbAb aaababA aaabAba \
    aababaa aababab aababaq aababAA aababAb aababAq aababAf aababqb aababfq aabaqba aabaqbA \
    aabaqbf aabafqb aabAAqb aabAbaa aabAbab aabAbaq aabAbAA aabAbAb aabAbAq aabAqba aabAqbA \
    aabqbab aabqbAA aabqbAb aabfbaq aabfbaf aabfbAq aabfbAf aabfqbA aaqbaba aaqbabA aaqbabq \
    aaqbAba aaqbAbA aaqbAbq aaqbAbf aafbaba aafbabA aafbAba aafbAbA aafbAbf abaaaba abaaabA \
    abaaqba abaaqbA abaaqbf abaafba abaafbA abaafbf ababaaq ababaaf abababA abababq abababf \
    ababaqb ababaqf ababafq ababAAq ababAAf ababAba ababAbA ababAbq ababAbf ababAqb ababAqf \
    ababAfq ababqbA ababqfb ababfbq ababfqb ababfqf abaqbaa abaqbab abaqbaf abaqbAA abaqbAf \
    abaqfba abaqfbA abaqfbf abafqba abafqbA abafqbf abAAqba abAAqbA abAbaaq abAbaba abAbabA \
    abAbabq abAbabf abAbaqb abAbaqf abAbafq abAbAAq abAbAba abAbAbq abAbAbf abAbAqb abAbAqf \
    abAbAfq abAbqba abAbqfb abAbfqf abAqbaa abAqbaf abAqbAA abAqbAb abAqbAf abAqfba abAqfbA \
    abAqfbf abAfqba abAfqbA abqbaab abqbabA abqbabf abqbafb abqbAAb abqbAba abqbAbf abqbAfb \
    abqfbab abqfbAA abqfbAb abfbaaq abfbabq abfbaqb abfbaqf abfbafq abfbAAq abfbAbq abfbAqb \
    abfbAqf abfbAfq abfqbab abfqbAb abfqfbA aqbabaa aqbabaf aqbabAA aqbabAb aqbabAq aqbabAf \
    aqbabqf aqbabfq aqbAbaa aqbAbab aqbAbaq aqbAbaf aqbAbAA aqbAbAf aqbAbqf aqbAbfb aqbAbfq \
    aqfbaba aqfbabA aqfbabq aqfbabf aqfbAba aqfbAbA aqfbAbq aqfbAbf afbabaa afbabaq afbabaf \
    afbabAb afbabAq afbabAf afbabqb afbabfq afbaqba afbaqbA afbaqbf afbafqb afbAAqb afbAbab \
    afbAbaq afbAbaf afbAbAq afbAbAf afbAbfq afbAqba afbAqbA afbAqbf afqbaba afqbabA afqbabf \
    afqbAba afqbAbA afqbAbf AAbabab AAbabaq AAbabAb AAbabAq AAbaqbA AAbAbab AAbAbaq AAbAbAb \
    AAbAbAq AAbAbqb AAbAbfq AAbAqba AAbAqbf AAqbaba AAqbabA AAqbabq AAqbabf AAqbAba AAqbAbA \
    AAqbAbq Abaaqba AbaaqbA Ababaaq Abababq Abababf Ababaqb Ababaqf Ababafq AbabAAq AbabAbA \
    AbabAbq AbabAbf AbabAqb AbabAqf AbabAfq Ababfqf Abaqbab Abaqbaf AbaqbAf Abaqfba AbaqfbA \
    Abaqfbf Abafqba AbafqbA AbAAqba AbAAqbA AbAbaaq AbAbaba AbAbabA AbAbabq AbAbabf AbAbaqb \
    AbAbaqf AbAbafq AbAbAAq AbAbAba AbAbAbq AbAbAbf AbAbAqb AbAbAqf AbAbAfq AbAbqba AbAbqfb \
    AbAbfbq AbAbfqb AbAbfqf AbAqbaa AbAqbaf AbAqbAb AbAqbAf AbAqfba AbAqfbA AbAqfbf AbAfqba \
    AbAfqbA AbAfqbf Abqbaab Abqbabf Abqbafb AbqbAAb AbqbAbf AbqbAfb Abqfbab AbqfbAb Abfbabq \
    Abfbaqb Abfbaqf Abfbafq AbfbAbq AbfbAqb AbfbAqf AbfbAfq Abfqbab AbfqbAb Aqbabaa Aqbabaf \
    AqbabAA AqbabAb AqbabAq AqbabAf Aqbabqf Aqbabfb Aqbabfq AqbAbaa AqbAbab AqbAbaq AqbAbaf \
    AqbAbAA AqbAbAf AqbAbqf AqbAbfq Aqfbaba AqfbabA Aqfbabq Aqfbabf AqfbAba AqfbAbA AqfbAbq \
    AqfbAbf Afbabaq AfbabAb AfbabAq Afbabfq Afbaqba AfbaqbA Afbaqbf AfbAbab AfbAbaq AfbAbAq \
    AfbAbqb AfbAbfq AfbAqba AfbAqbA AfbAqbf Afqbaba AfqbabA Afqbabf AfqbAba AfqbAbA AfqbAbf \
    baabqba baabqbA baaqbaa baaqbab baaqbAb baaqbAf baafbab baafbAb babaaqb babaafb bababAb \
    bababAq bababAf bababqf bababfq babaqba babaqbf babaqfb babafqb babAAqb babAAfb babAbab \
    babAbaq babAbaf babAbAA babAbAb babAbAq babAbqb babAbqf babAbfq babAqba babAqbA babAqbf \
    babAqfb babAfqb babqbAb babqbAf babqfba babfbAq babfqba baqbaba baqbabA baqbabq baqbabf \
    baqfbaa baqfbAb baqfbAf bafqbAb bAAbqba bAAbqbA bAAqbab bAAqbAb bAbaaqb bAbabaa bAbabab \
    bAbabaq bAbabAb bAbabAq bAbabAf bAbabqb bAbabqf bAbabfq bAbaqba bAbaqbA bAbaqbf bAbaqfb \
    bAbafqb bAbAAqb bAbAbab bAbAbaq bAbAbaf bAbAbqf bAbAbfq bAbAqbA bAbAqbf bAbAqfb bAbAfqb \
    bAbqbab bAbqbaf bAbqfbA bAbfbaq bAbfqbA bAqbAba bAqbAbA bAqbAbq bAqbAbf bAqfbab bAfqbab \
    bqbaabq bqbabAb bqbabAf bqbabfb bqbAAbq bqbAbab bqbAbaf bqbAbfb bqfbabf bqfbAbf bfbabqb \
    bfbabqf bfbabfb bfbabfq bfbaqbf bfbafqb bfbAbqb bfbAbqf bfbAbfb bfbAbfq bfbAqbf bfbAfqb \
    bfqbabA bfqbabf bfqbAba bfqbAbf bfqfbab bfqfbAb qbabAAq qbabAba qbabAbA qbabAbq qbabAbf \
    qbabAqb qbabAqf qbabAfq qbabfbA qbabfqf qbAbaaq qbAbaba qbAbabA qbAbabq qbAbabf qbAbaqb \
    qbAbaqf qbAbafq qbAbfba qbAbfqf qfbabaa qfbabAb qfbabAq qfbabAf qfbabqf qfbabfq qfbAbab \
    qfbAbaq qfbAbaf qfbAbAA qfbAbqf qfbAbfq fbabaaq fbabAba fbabAbq fbabAqb fbabAqf fbabAfq \
    fbabqbA fbaqbab fbaqbaf fbaqbAA fbafqbA fbAbabA fbAbabq fbAbaqb fbAbaqf fbAbafq fbAbAAq \
    fbAbqba fbAqbaa fbAqbAb fbAqbAf fbAfqba fqbabAb fqbAbab fqfbabA fqfbAba aaababAb \
    aaabAbab aababaaq aabababA aabababq aabababf aababaqb aababAAq aababAba aababAbq \
    aababAbf aababAqb aababAfq aabaqbaf aabafqbA aabAAqba aabAAqbA aabAbaaq aabAbaba \
    aabAbabq aabAbabf aabAbaqb aabAbAAq aabAbAbq aabAbAbf aabAbAqb aabAqbAb aabqbAAb \
    aaqbabaa aaqbabAA aaqbabAb aaqbabAq aaqbAbaa aaqbAbab aaqbAbaq aaqbAbaf aaqbAbAA \
    aaqbAbfq aafbabAb aafbAbab abaaqbaa abaaqbab abaaqbAb abaaqbAf abaafbab abaafbAb \
    ababaaqb ababaafb abababAq abababAf abababqf abababfq ababaqba ababaqbf ababaqfb \
    ababafqb ababAAqb ababAAfb ababAbab ababAbaq ababAbaf ababAbAq ababAbqb ababAbqf \
    ababAbfq ababAqba ababAqbA ababAqbf ababAqfb ababAfqb abaqbaba abaqbabA abaqbabf \
    abaqfbAb abaqfbAf abafqbAb abAAqbab abAbaaqb abAbabaa abAbabab abAbabaq abAbabAb \
    abAbabAq abAbabAf abAbabqb abAbabqf abAbabfq abAbaqba abAbaqbA abAbaqbf abAbaqfb \
    abAbafqb abAbAAqb abAbAbab abAbAbaq abAbAbaf abAbAbqf abAbAbfq abAbAqbA abAbAqbf \
    abAbAqfb abAbAfqb abAbqfbA abAqbAba abAqbAbA abAqbAbf abAqfbab abAfqbab abqbabAb \
    abqbabfb abqbAbaf abqfbabf abfbabqb abfbabqf abfbafqb abfbAbqb abfbAbqf abfbAfqb \
    abfqbabA abfqfbAb aqbabAAq aqbabAba aqbabAbA aqbabAbq aqbabAbf aqbabAqb aqbabAqf \
    aqbabAfq aqbabfqf aqbAbaaq aqbAbaba aqbAbabA aqbAbabq aqbAbabf aqbAbaqb aqbAbaqf \
    aqbAbafq aqbAbfqf aqfbabAb aqfbabAq aqfbabAf aqfbAbab aqfbAbaq aqfbAbaf aqfbAbAA \
    aqfbAbfq afbabaaq afbabAba afbabAbq afbabAqb afbabAfq afbabqbA afbaqbab afbaqbaf \
    afbaqbAA afbafqbA afbAbabA afbAbabq afbAbaqb afbAbafq afbAqbAb afbAqbAf afqbabAb \
    afqbAbab AAbababq AAbabaqb AAbabAbA AAbabAbq AAbabAbf AAbabAqb AAbAbabq AAbAbabf \
    AAbAbaqb AAbAbAbq AAbAbAqb AAqbabAb AAqbabAq AAqbabfq AAqbAbab AAqbAbaq Abaaqbaa \
    AbaaqbAb Ababaaqb Abababqf Abababfq Ababaqba Ababaqbf Ababaqfb Ababafqb AbabAAqb \
    AbabAbAb AbabAbAq AbabAbqb AbabAbqf AbabAbfq AbabAqba AbabAqbA AbabAqbf AbabAqfb \
    AbabAfqb Abaqbaba AbaqbabA Abaqbabf AbaqfbAb AbaqfbAf AbafqbAb AbAAqbab AbAbaaqb \
    AbAbabaq AbAbabAb AbAbabAq AbAbabAf AbAbabqb AbAbabqf AbAbabfq AbAbaqba AbAbaqbA \
    AbAbaqbf AbAbaqfb AbAbafqb AbAbAAqb AbAbAbaq AbAbAbaf AbAbAbqf AbAbAbfq AbAbAqbA \
    AbAbAqbf AbAbAqfb AbAbAfqb AbAqbAba AbAqbAbA AbAqbAbf AbAqfbab AbAfqbab AbqbAbfb \
    Abfbabqb AbfbAbqb AqbabAAq AqbabAba AqbabAbA AqbabAbq AqbabAbf AqbabAqb AqbabAqf \
    AqbabAfq Aqbabfqf AqbAbaaq AqbAbaba AqbAbabq AqbAbabf AqbAbaqb AqbAbaqf AqbAbafq \
    AqfbabAb AqfbabAq Aqfbabfq AqfbAbab AqfbAbaq AfbabAba AfbabAbq AfbabAqb Afbaqbab \
    Afbaqbaf AfbAbabq AfbAbaqb AfbAqbAb AfbAqbAf AfqbabAb AfqbAbab baabqbab baaqbabA \
    baaqbAba baaqbAbA baaqbAbq baaqbAbf babaaqba babaaqbA babaaqbf bababAbq bababAqb \
    bababAqf bababAfq bababfqf babaqbab babaqfbA babaqfbf babAAqba babAbabq babAbabf \
    babAbaqb babAbaqf babAbafq babAbAAq babAbAbq babAbAqb babAbAqf babAbqfb babAbfqf \
    babAqbAA babAqbAf babAqfba babAqfbA babAqfbf babAfqba babAfqbA babqbAfb babfbAqb \
    baqbabaa baqbabAA baqbabAb baqbabAq baqbabAf baqbabqf baqbabfq baqfbAba baqfbAbA \
    baqfbAbf bafqbAba bafqbAbA bafqbAbf bAAqbaba bAAqbabA bAAqbabq bAAqbabf bAAqbAba \
    bAbaaqbA bAbabaaq bAbababq bAbabaqb bAbabaqf bAbabAbq bAbabAbf bAbabAqb bAbabAqf \
    bAbabAfq bAbabfqf bAbaqbaf bAbaqfba bAbaqfbA bAbaqfbf bAbafqba bAbafqbA bAbAAqba \
    bAbAAqbA bAbAbabq bAbAbaqb bAbAbaqf bAbAbafq bAbAbfqf bAbAqbAb bAbAqfba bAbAqfbf \
    bAbqbafb bAbfbaqb bAqbAbaa bAqbAbab bAqbAbaq bAqbAbaf bAqbAbAA bAqbAbqf bAqbAbfq \
    bAqfbaba bAqfbabA bAqfbabf bAfqbaba bAfqbabA bAfqbabf bqbabAba bqbabAbA bqbabAbf \
    bqbabfbA bqbAbaba bqbAbabA bqbAbabf bqbAbfba bfqbabAb bfqbAbab qbabAbab qbabAbaq \
    qbabAbaf qbabAbAA qbabAbAb qbabAbAq qbabAbqf qbabAbfq qbabAqfb qbAbabaa qbAbabab \
    qbAbabaq qbAbabAb qbAbabAq qbAbabAf qbAbabqf qbAbabfq qbAbaqfb qfbabAba qfbabAbq \
    qfbabAqb qfbabAfq qfbAbabA qfbAbabq qfbAbaqb qfbAbafq fbabaaqb fbabAbaq fbabAbqb \
    fbabAbqf fbabAqbA fbabAqfb fbabAfqb fbaqbabA fbafqbAb fbAbabAq fbAbabqb fbAbabqf \
    fbAbaqba fbAbaqfb fbAbafqb fbAbAAqb fbAqbAba fbAfqbab fqbabAba fqbabAbA fqbabAbf \
    fqbAbaba fqbAbabA fqbAbabf fqfbabAb fqfbAbab aaababAbf aaabAbabf aababaaqb aabababAq \
    aabababAf aababaqba aababAbab aababAbaq aababAbaf aababAbfq aababAqbA aababAqbf \
    aababAfqb aabAAqbab aabAbabqb aaqbabAbq aaqbabAqb aaqbAbabA aaqbAbabq aaqbAbabf \
    aaqbAbaqb aaqbAbafq aafbAbabA abaaqbAbf ababaaqba ababaaqbf ababAbabf ababAbafq \
    ababAbAqf ababAbqfb ababAbfqf ababAqbAf ababAqfba ababAfqbA abaqbabAb abaqfbAba \
    abaqfbAbA abaqfbAbf abafqbAbf abAAqbaba abAAqbabA abAAqbabq abAAqbabf abAbabaaq \
    abAbababq abAbabAbq abAbabAbf abAbabAqb abAbabAqf abAbabAfq abAbaqbaf abAbaqfbA \
    abAbafqba abAbafqbA abAbAAqbA abAbAbabq abAbAbaqb abAbAbaqf abAbAbafq abAbAqbAb \
    abAbAqfba abAqbAbaf abAqbAbAA abAqfbabA abAfqbaba abAfqbabA abAfqbabf aqbabAbab \
    aqbabAbaq aqbabAbaf aqbabAbAA aqbabAbAb aqbabAbqf aqbabAbfq aqbabAqfb aqbAbabaq \
    aqbAbabAf aqbAbabqf aqbAbabfq aqfbabAbq aqfbabAqb aqfbAbabA aqfbAbabq aqfbAbaqb \
    aqfbAbafq afbabaaqb afbabAbaq afbabAqbA afbabAfqb afbaqbabA afbafqbAb afbAbabqb \
    afqbabAbA afqbabAbf afqbAbabA AAbabAbqb AAbAbabfq AAbAbaqba AAbAbaqbf AAqbabAbq \
    AAqbabAbf AAqbabAqb AAqbAbabq AAqbAbaqb AbaaqbAba AbaaqbAbA AbaaqbAbf Ababaqbab \
    AbabAbqfb AbabAqbAf Abaqbabaa AbAbabaqf AbAbabAbf AbAbabAfq AbAbaqbaf AbAbaqfbA \
    AbAbafqba AbAbAAqbA AbAqbAbab AbAqfbaba AbAqfbabA AbAfqbabf AqbabAbaf AqbabAbAq \
    AqbabAbqf AqbabAbfq AqbAbabqf AqbAbabfq AqbAbaqfb AqfbabAbq AqfbAbabq AqfbAbaqb \
    AfbabAbqb AfbAbaqba AfbAqbAba AfqbAbaba baaqbabAb baaqbAbaf baaqbAbfq babaaqbaa \
    babaaqbab bababAbqb babaqfbAb babAAqbab babAbabqf babAbabfq babAbaqbA babAbaqbf \
    babAbaqfb babAbafqb babAbAAqb baqbabAba baqbabAqb baqbabfqf baqfbAbab baqfbAbAA \
    bAAqbabfq bAAqbAbab bAbaaqbAb bAbabaaqb bAbabAbqf bAbabAbfq bAbabAqba bAbabAqbf \
    bAbabAqfb bAbabAfqb bAbaqfbAf bAbAbabqb bAbAqfbab bAqbAbaqb bAqfbabAb bqbabAbAb \
    bqbAbabab qbabAbafq qbabAbAqf qbAbabaqf qbAbabAfq aababAbabf aababAbafq aababAqbAf \
    aaqbAbabAf abaqfbAbab abAbabAbqf abAbabAbfq abAbabAqbf abAbabAqfb abAbabAfqb abAbAbabqb \
    abAbAqfbab aqbabAbafq aqbAbabaqf"
@[expose] def burnsideF48s_u42eC0S : List String :=
  ["", "AA", "aa"]
@[expose] def burnsideF48s_u42eN0S : List String :=
  ["", "a", "A", "f", "aa", "af", "AA", "Af", "aaa", "aaf", "AAf", "aaaf", "babAbab", "bAbabAb",
    "ababAbab", "abAbabAb", "AbAbabAb", "babAbabf", "bAbabAbf", "aababAbab", "ababAbabf",
    "abAbabAbf", "AbAbabAbf", "aababAbabf"]
@[expose] def burnsideF48s_u42eKSs : List (List String) :=
  [["", "AA", "aa", "aababAbab", "babAbab", "bAbabAb"],
    ["", "AA", "aa", "aaa", "a", "A"],
    ["", "AA", "aa", "abAbabAb", "AbAbabAb", "ababAbab"],
    ["", "AA", "aa", "aababAbabf", "bAbabAbf", "babAbabf"],
    ["", "AA", "aa", "f", "aaf", "AAf"],
    ["", "AA", "aa", "abAbabAbf", "ababAbabf", "AbAbabAbf"],
    ["", "AA", "aa", "aaaf", "Af", "af"]]
@[expose] def burnsideF48s_u42eTSs : List (List String) :=
  [[],
    [],
    [],
    ["", "a", "A", "f", "aa", "af", "AA", "Af", "aaa", "aaf", "AAf", "aaaf", "babAbab",
      "bAbabAb", "ababAbab", "abAbabAb", "AbAbabAb", "babAbabf", "bAbabAbf", "aababAbab",
      "ababAbabf", "abAbabAbf", "AbAbabAbf", "aababAbabf"],
    [],
    [],
    []]
@[expose] def burnsideF48s_u42eUSs : List (List String) :=
  [[],
    [],
    [],
    ["p", "p", "p", "p", "p", "p", "p", "p", "p", "p", "p", "aap", "aap", "aap", "aap", "aap",
      "aap", "aap", "aap", "aap", "aap", "aap", "aap", "aap", "aap", "aap", "aap", "aap",
      "aap", "apf", "apf", "apf", "apf", "apf", "apf", "apf", "apf", "apf", "apf", "apf",
      "apf", "apf", "apf", "apf", "apf", "apf", "apf", "apf", "apf", "pap", "pap", "pap",
      "pap", "pap", "pap", "pap", "pap", "pap", "pap", "pap", "pap", "pap", "pap", "pap",
      "pap", "pap", "pap", "pfp", "pfp", "pfp", "pfp", "pfp", "pfp", "pfp", "pfp", "pfp",
      "pfp", "pfp", "pfp", "pfp", "pfp", "pfp", "pfp", "pfp", "pfp", "pfp", "pfp", "aapap",
      "aapap", "aapap", "aapap", "aapap", "aapap", "aapap", "aapap", "aapap", "aapap",
      "aapap"],
    [],
    [],
    []]
@[expose] def burnsideF48s_u42eVSs : List (List String) :=
  [[],
    [],
    [],
    ["q", "q", "q", "q", "babAbabqf", "babAbabqf", "babAbabqf", "babAbabqf", "abAbabAbqf",
      "abAbabAbqf", "abAbabAbqf", "q", "q", "q", "q", "q", "q", "babAbabqf", "babAbabqf",
      "babAbabqf", "babAbabqf", "bAbabAbqf", "bAbabAbqf", "bAbabAbqf", "bAbabAbqf",
      "abAbabAbqf", "abAbabAbqf", "abAbabAbqf", "abAbabAbqf", "q", "q", "q", "q", "q", "q",
      "aq", "aq", "aq", "aq", "babAbabqf", "babAbabqf", "babAbabqf", "babAbabqf",
      "babAbabqf", "babAbabqf", "abAbabAbqf", "abAbabAbqf", "abAbabAbqf", "abAbabAbqf", "q",
      "q", "q", "q", "q", "q", "babAbabqf", "babAbabqf", "babAbabqf", "babAbabqf",
      "bAbabAbqf", "bAbabAbqf", "bAbabAbqf", "bAbabAbqf", "abAbabAbqf", "abAbabAbqf",
      "abAbabAbqf", "abAbabAbqf", "q", "q", "q", "q", "aq", "aq", "aq", "aq", "aq", "aq",
      "babAbabqf", "babAbabqf", "babAbabqf", "babAbabqf", "babAbabqf", "babAbabqf",
      "abAbabAbqf", "abAbabAbqf", "abAbabAbqf", "abAbabAbqf", "q", "q", "q", "q",
      "babAbabqf", "babAbabqf", "babAbabqf", "babAbabqf", "abAbabAbqf", "abAbabAbqf",
      "abAbabAbqf"],
    [],
    [],
    []]
@[expose] def burnsideF48s_u42eWSs : List (List String) :=
  [[],
    [],
    [],
    ["", "AA", "aababAbabf", "bAbabAbf", "", "AA", "aa", "aababAbabf", "", "AA", "aababAbabf",
      "", "AA", "aa", "aababAbabf", "bAbabAbf", "babAbabf", "", "AA", "aa", "aababAbabf",
      "", "AA", "aa", "aababAbabf", "", "AA", "aa", "aababAbabf", "", "AA", "aa",
      "aababAbabf", "bAbabAbf", "babAbabf", "", "AA", "aababAbabf", "babAbabf", "", "AA",
      "aa", "aababAbabf", "bAbabAbf", "babAbabf", "", "AA", "aababAbabf", "babAbabf", "",
      "AA", "aa", "aababAbabf", "bAbabAbf", "babAbabf", "", "AA", "aa", "aababAbabf", "",
      "AA", "aa", "aababAbabf", "", "AA", "aa", "aababAbabf", "", "AA", "aababAbabf",
      "bAbabAbf", "", "AA", "aa", "aababAbabf", "bAbabAbf", "babAbabf", "", "AA", "aa",
      "aababAbabf", "bAbabAbf", "babAbabf", "", "AA", "aababAbabf", "bAbabAbf", "", "AA",
      "aababAbabf", "bAbabAbf", "", "AA", "aa", "aababAbabf", "", "AA", "aababAbabf"],
    [],
    [],
    []]
@[expose] def burnsideF48s_u42eLS : List (List ℕ) :=
  [[0, 2, 1, 14, 12, 13, 11, 9, 10, 8, 6, 7, 5, 3, 4, 15, 24, 18, 21, 22, 16, 19, 23, 17, 20, 35,
      40, 43, 37, 41, 44, 38, 39, 42, 36, 25, 26, 29, 32, 27, 30, 33, 28, 31, 34],
    [0, 42, 38, 18, 32, 13, 22, 28, 10, 17, 8, 33, 19, 5, 31, 16, 15, 9, 3, 12, 24, 29, 6, 27, 20,
      34, 30, 23, 7, 21, 26, 14, 4, 11, 25, 35, 36, 41, 2, 43, 40, 37, 1, 39, 44],
    [0, 1, 2, 10, 11, 9, 13, 14, 12, 5, 3, 4, 8, 6, 7, 35, 40, 41, 39, 43, 44, 42, 37, 38, 36, 25,
      26, 27, 28, 29, 30, 31, 32, 33, 34, 15, 24, 22, 23, 18, 16, 17, 21, 19, 20],
    [15, 25, 35, 3, 5, 4, 9, 11, 10, 6, 8, 7, 12, 14, 13, 0, 16, 26, 36, 44, 24, 34, 30, 40, 20,
      1, 17, 27, 37, 42, 22, 32, 31, 41, 21, 2, 18, 28, 38, 43, 23, 33, 29, 39, 19],
    [0, 1, 2, 6, 8, 7, 3, 5, 4, 12, 14, 13, 9, 11, 10, 15, 16, 22, 19, 18, 24, 21, 17, 23, 20, 35,
      36, 42, 39, 38, 44, 41, 37, 43, 40, 25, 26, 32, 29, 28, 34, 31, 27, 33, 30]]
@[expose] def burnsideF48s_u42eLSi : List (List ℕ) :=
  [[0, 2, 1, 13, 14, 12, 10, 11, 9, 7, 8, 6, 4, 5, 3, 15, 20, 23, 17, 21, 24, 18, 19, 22, 16, 35,
      36, 39, 42, 37, 40, 43, 38, 41, 44, 25, 34, 28, 31, 32, 26, 29, 33, 27, 30],
    [0, 42, 38, 18, 32, 13, 22, 28, 10, 17, 8, 33, 19, 5, 31, 16, 15, 9, 3, 12, 24, 29, 6, 27, 20,
      34, 30, 23, 7, 21, 26, 14, 4, 11, 25, 35, 36, 41, 2, 43, 40, 37, 1, 39, 44],
    [0, 1, 2, 10, 11, 9, 13, 14, 12, 5, 3, 4, 8, 6, 7, 35, 40, 41, 39, 43, 44, 42, 37, 38, 36, 25,
      26, 27, 28, 29, 30, 31, 32, 33, 34, 15, 24, 22, 23, 18, 16, 17, 21, 19, 20],
    [15, 25, 35, 3, 5, 4, 9, 11, 10, 6, 8, 7, 12, 14, 13, 0, 16, 26, 36, 44, 24, 34, 30, 40, 20,
      1, 17, 27, 37, 42, 22, 32, 31, 41, 21, 2, 18, 28, 38, 43, 23, 33, 29, 39, 19],
    [0, 1, 2, 6, 8, 7, 3, 5, 4, 12, 14, 13, 9, 11, 10, 15, 16, 22, 19, 18, 24, 21, 17, 23, 20, 35,
      36, 42, 39, 38, 44, 41, 37, 43, 40, 25, 26, 32, 29, 28, 34, 31, 27, 33, 30]]
@[expose] def burnsideF48s_u42eR1 : List (List (Fin 5 × Bool)) := burnsideF48s_u42eWords burnsideF48s_u42eR1S

@[expose] def burnsideF48s_u42eR2 : List (List (Fin 5 × Bool)) := burnsideF48s_u42eWords burnsideF48s_u42eR2S

@[expose] def burnsideF48s_u42eP1W : List (List (Fin 5 × Bool)) := burnsideF48s_u42eWords (burnsideF48s_u42eP1Str.splitOn " ")

@[expose] def burnsideF48s_u42eP2W : List (List (Fin 5 × Bool)) := burnsideF48s_u42eWords (burnsideF48s_u42eP2Str.splitOn " ")

@[expose] def burnsideF48s_u42eC0W : List (List (Fin 5 × Bool)) := burnsideF48s_u42eWords burnsideF48s_u42eC0S

@[expose] def burnsideF48s_u42eN0W : List (List (Fin 5 × Bool)) := burnsideF48s_u42eWords burnsideF48s_u42eN0S

@[expose] def burnsideF48s_u42eKW (j : ℕ) : List (List (Fin 5 × Bool)) := burnsideF48s_u42eWords (burnsideF48s_u42eKSs.getD j [])

@[expose] def burnsideF48s_u42eTW (j : ℕ) : List (List (Fin 5 × Bool)) := burnsideF48s_u42eWords (burnsideF48s_u42eTSs.getD j [])

@[expose] def burnsideF48s_u42eU (j : ℕ) : List (List (Fin 5 × Bool)) := burnsideF48s_u42eWords (burnsideF48s_u42eUSs.getD j [])

@[expose] def burnsideF48s_u42eV (j : ℕ) : List (List (Fin 5 × Bool)) := burnsideF48s_u42eWords (burnsideF48s_u42eVSs.getD j [])

@[expose] def burnsideF48s_u42eW (j : ℕ) : List (List (Fin 5 × Bool)) := burnsideF48s_u42eWords (burnsideF48s_u42eWSs.getD j [])

abbrev burnsideF48s_u42eWs (k : ℕ) : List (List (Fin 5 × Bool)) :=
  burnsideF48s_eWs burnsideF48s_u42eR1 burnsideF48s_u42eR2 4 ((burnsideF48s_u42eU 3).getD k [])
    ((burnsideF48s_u42eV 3).getD k []) ((burnsideF48s_u42eW 3).getD k [])

abbrev burnsideF48s_u42eWsB (k : ℕ) : List (List (Fin (subsetOf 5 [0, 1, 2, 4]).length × Bool)) :=
  restrictWords (subsetOf 5 [0, 1, 2, 4]) (burnsideF48s_u42eWs k)

abbrev burnsideF48s_u42eEvL (w : List (Fin 5 × Bool)) : List ℕ :=
  burnsideF48s_eEvL 45 burnsideF48s_u42eLS burnsideF48s_u42eLSi w

@[expose] def burnsideF48s_u42eCheckGens (_ : Unit := ()) : Bool :=
  decide (burnsideF48s_u42eLS = burnsideF48s_u42eXY.map CFSG.Quasithin.H13.F431.U42Aut.evalAL) &&
    decide (burnsideF48s_u42eLSi = burnsideF48s_u42eXY.map fun w =>
      CFSG.Quasithin.H13.F431.U42Aut.evalAL (CFSG.Quasithin.H13.F431.U42Aut.invAL w))

@[expose] def burnsideF48s_u42eCheckRels (_ : Unit := ()) : Bool :=
  ((burnsideF48s_u42eR1 ++ burnsideF48s_u42eR2).all fun w =>
    decide (burnsideF48s_u42eEvL w = List.range 45)) &&
  ([0, 5, 8, 11, 17, 22, 27, 67, 73, 77, 83].all fun k => decide (burnsideF48s_u42eEvL
    (burnsideF48s_eCandRel 4 ((burnsideF48s_u42eU 3).getD k []) ((burnsideF48s_u42eV 3).getD k [])
      ((burnsideF48s_u42eW 3).getD k [])) = List.range 45)) &&
  !decide (burnsideF48s_u42eEvL (burnsideF48s_u42eWord "aa") = List.range 45) &&
  decide (burnsideF48s_u42eEvL (burnsideF48s_u42eWord "apapap") = U42F431.xL) &&
  decide (burnsideF48s_u42eEvL (burnsideF48s_u42eWord "bqpaqp") = U42F431.yL) &&
  decide (burnsideF48s_u42eEvL (burnsideF48s_u42eWord "bpbpfb") = CFSG.Quasithin.H13.F431.U42Aut.f45L) &&
  (List.range 7).all fun j => decide (((burnsideF48s_u42eKW j).map burnsideF48s_u42eEvL).Nodup)

@[expose] def burnsideF48s_u42eCheckLetters (_ : Unit := ()) : Bool :=
  ((burnsideF48s_u42eP1W ++ burnsideF48s_u42eR1).all fun w => w.all fun l => decide (l.1 ≠ 3)) &&
  ((burnsideF48s_u42eP2W ++ burnsideF48s_u42eR2).all fun w => w.all fun l => decide (l.1 ≠ 2)) &&
  ((burnsideF48s_u42eC0W ++ burnsideF48s_u42eN0W).all fun w => w.all fun l => decide (l.1 ≠ 2 ∧ l.1 ≠ 3)) &&
  (List.range 7).all fun j =>
    ((burnsideF48s_u42eU j).all fun w => w.all fun l => decide (l.1 ≠ 3)) &&
    ((burnsideF48s_u42eV j).all fun w => w.all fun l => decide (l.1 ≠ 2)) &&
    ((burnsideF48s_u42eKW j ++ burnsideF48s_u42eTW j ++ burnsideF48s_u42eW j).all fun w => w.all fun l => decide (l.1 ≠ 2 ∧ l.1 ≠ 3))

@[expose] def burnsideF48s_u42eCheckClosed (_ : Unit := ()) : Bool :=
  let P1L := burnsideF48s_u42eP1W.map burnsideF48s_u42eEvL
  let P2L := burnsideF48s_u42eP2W.map burnsideF48s_u42eEvL
  let C0L := burnsideF48s_u42eC0W.map burnsideF48s_u42eEvL
  decide (burnsideF48s_u42eP1W.length = 1152) && decide (burnsideF48s_u42eP2W.length = 1920) &&
  decide (burnsideF48s_u42eP1W.getD 0 [(0, true)] = []) &&
  decide (burnsideF48s_u42eP2W.getD 0 [(0, true)] = []) &&
  decide (burnsideF48s_u42eC0W = [[], burnsideF48s_u42eWord "AA", burnsideF48s_u42eWord "aa"]) &&
  decide ((burnsideF48s_u42eU 3).length = 98) &&
  burnsideF48s_eClosed P1L burnsideF48s_u42eLS [0, 1, 2, 4] &&
  burnsideF48s_eClosed P2L burnsideF48s_u42eLS [0, 1, 3, 4] &&
  (List.range 7).all fun j =>
    let KL := (burnsideF48s_u42eKW j).map burnsideF48s_u42eEvL
    decide ((burnsideF48s_u42eKW j).getD 0 [(0, true)] = []) && decide (0 < (burnsideF48s_u42eKW j).length) &&
    (C0L.all fun c => KL.contains c) && burnsideF48s_eClosedW KL KL &&
    decide ((burnsideF48s_u42eU j).length ≤ (burnsideF48s_u42eV j).length) && decide ((burnsideF48s_u42eU j).length ≤ (burnsideF48s_u42eW j).length)

@[expose] def burnsideF48s_u42eCheckCand (_ : Unit := ()) : Bool :=
  let P1L := burnsideF48s_u42eP1W.map burnsideF48s_u42eEvL
  let P2L := burnsideF48s_u42eP2W.map burnsideF48s_u42eEvL
  (List.range 7).all fun j =>
    burnsideF48s_eCandOK P1L P2L ((burnsideF48s_u42eKW j).map burnsideF48s_u42eEvL) ((burnsideF48s_u42eTW j).map burnsideF48s_u42eEvL)
      ((burnsideF48s_u42eU j).map burnsideF48s_u42eEvL) ((burnsideF48s_u42eV j).map burnsideF48s_u42eEvL) ((burnsideF48s_u42eW j).map burnsideF48s_u42eEvL)

@[expose] def burnsideF48s_u42eCheckClass (_ : Unit := ()) : Bool :=
  let P1L := burnsideF48s_u42eP1W.map burnsideF48s_u42eEvL
  let P2L := burnsideF48s_u42eP2W.map burnsideF48s_u42eEvL
  let C0L := burnsideF48s_u42eC0W.map burnsideF48s_u42eEvL
  let N0L := burnsideF48s_u42eN0W.map burnsideF48s_u42eEvL
  (N0L.all fun n => P1L.contains n && P2L.contains n && burnsideF48s_eNorm C0L n) &&
  P1L.all fun s => !burnsideF48s_eNorm C0L s || C0L.contains s || !C0L.contains (compL s s) ||
    !P2L.contains s ||
    N0L.any fun n => (List.range 7).any fun j =>
      ((burnsideF48s_u42eKW j).map burnsideF48s_u42eEvL).any fun k => compL n s == compL k n

end CFSG.ASVolI
