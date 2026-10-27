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

@[expose] def burnsideF48s_sp43eLetter (c : Char) : Fin 5 × Bool :=
  (⟨"abpqf".toList.idxOf c.toLower % 5, Nat.mod_lt _ (by norm_num)⟩, c.isLower)

@[expose] def burnsideF48s_sp43eWord (s : String) : List (Fin 5 × Bool) :=
  s.toList.map burnsideF48s_sp43eLetter

@[expose] def burnsideF48s_sp43eWords (l : List String) : List (List (Fin 5 × Bool)) :=
  l.map burnsideF48s_sp43eWord

@[expose] def burnsideF48s_sp43eR1S : List String :=
  ["pp", "ff", "bbb", "apAp", "fAfA", "BafBaf", "pafpaf", "abAAbaB", "BpBpBpBp", "AABpBAAbpb",
    "pBABAbpBpbA"]
@[expose] def burnsideF48s_sp43eR2S : List String :=
  ["ff", "bbb", "qqqq", "AfAf", "AAAqq", "afQafQ", "bfAbaf", "qAQAQA", "ABaaBAb", "bAQBQBaqq",
    "ababaababa", "bqfBAQbabfqq", "AbabfbabABfb"]
@[expose] def burnsideF48s_sp43eP1Str : String :=
  " a A b B p f aa ab aB ap af AA Ab AB Ap Af ba bA bp bf Ba BA Bp Bf pb pB pf fb fB aaa \
    aab aaB aap aaf aba abA abp abf aBa aBA aBp aBf apb apB apf afb afB AAb AAB AAp AAf Aba \
    AbA Abp Abf ABa ABA ABp ABf Apb ApB Apf Afb AfB baa bab baB bap bAA bAb bAB bAp bAf bpb \
    bpB bpf bfb bfB Baa Bab BaB Bap BAA BAb BAB BAp BAf Bpb BpB Bpf Bfb BfB pba pbA pbp pbf \
    pBa pBA pBp pBf pfb pfB fbA fbp fBA fBp aaab aaaB aaap aaaf aaba aabA aabp aabf aaBa \
    aaBp aaBf aapb aapB aapf aafb aafB abaa abab abaB abap abAb abAB abAp abpb abpB abpf \
    abfb abfB aBaa aBaB aBap aBAA aBAB aBAp aBAf aBpb aBpB aBpf aBfb apba apbA apbp apbf \
    apBa apBA apBp apBf apfb apfB afbA afbp afBA afBp AAbA AAbp AAbf AABa AABA AABp AABf \
    AApb AApB AApf AAfb AAfB Abaa Abap AbAA AbAb AbAp AbAf Abpb AbpB Abpf AbfB ABab ABaB \
    ABap ABAA ABAb ABAB ABAp ABAf ABpb ABpB ABpf ABfb ABfB Apba ApbA Apbp Apbf ApBa ApBA \
    ApBp ApBf Apfb ApfB AfbA Afbp AfBp baaa baab baaB baap baba babA babp babf baBA baBp \
    baBf bapb bapB bAAp bAAf bAba bAbA bAbp bAbf bABA bABp bABf bApb bApB bApf bpba bpbA \
    bpbp bpbf bpBa bpBp bpBf bpfb bpfB bfbp bfBA bfBp Baaa Baap Baba Babp BaBA BaBp BaBf \
    Bapb BapB BAAB BAAp BAAf BAba BAbp BABA BABp BABf BApb BApB BApf BAfb BpbA Bpbp Bpbf \
    BpBa BpBA BpBp BpBf Bpfb BpfB Bfbp BfBA BfBp pbaa pbaB pbap pbAA pbAb pbAB pbAp pbAf \
    pbpB pbpf pbfb pbfB pBaa pBab pBaB pBap pBAA pBAb pBAp pBAf pBpb pBpf pBfB pfbA pfbp \
    pfBA pfBp fbAA fbAb fbAB fbAp fbpb fBAA fBAp fBpb fBpB aaabA aaabp aaabf aaaBa aaaBp \
    aaaBf aaapb aaapB aaapf aaafb aaafB aabaa aabab aabap aabAb aabAB aabAp aabpb aabpB \
    aabpf aabfb aabfB aaBaa aaBaB aaBap aaBpb aaBpB aaBpf aaBfb aapba aapbA aapbp aapbf \
    aapBa aapBp aapBf aapfb aapfB aafbA aafbp aafBA aafBp abaab abaaB abaap ababa ababA \
    ababp ababf abaBA abaBp abaBf abapB abAba abAbA abAbp abAbf abABA abABp abABf abApb \
    abApB abpba abpbA abpbp abpbf abpBa abpBp abpBf abpfb abpfB abfbp abfBA abfBp aBaaa \
    aBaap aBaBA aBaBp aBaBf aBapb aBapB aBAAB aBAAp aBAAf aBABA aBABp aBABf aBApb aBApB \
    aBApf aBAfb aBpbA aBpbp aBpbf aBpBa aBpBA aBpBp aBpBf aBpfb aBpfB aBfbp apbaa apbaB \
    apbAb apbAB apbAp apbpB apbpf apbfb apbfB apBaa apBaB apBap apBAA apBAp apBAf apBpb \
    apBpf apfbA apfbp apfBA apfBp afbAA afbAb afbAp afbpb afBAA afBAp afBpb afBpB AAbAA \
    AAbAb AAbAp AAbAf AAbpb AAbpB AAbpf AAbfB AABab AABaB AABap AABAA AABAp AABAf AABpb \
    AABpB AABpf AABfb AABfB AApbA AApbp AApbf AApBa AApBA AApBp AApBf AApfb AApfB AAfbA \
    AAfbp AAfBp Abaaa Abaab Abaap Abapb AbapB AbAAp AbAAf AbAbA AbAbf AbApB AbApf Abpba \
    Abpbp Abpbf AbpBa AbpBp AbpBf Abpfb AbpfB AbfBp ABaba ABabp ABaBA ABaBp ABaBf ABapb \
    ABapB ABAAB ABAAp ABAAf ABAba ABAbp ABABp ABABf ABApb ABApf ABAfb ABpbp ABpbf ABpBa \
    ABpBp ABpBf ABpfb ABpfB ABfbp ABfBA ABfBp Apbaa Apbap ApbAA ApbAp ApbAf ApbpB Apbpf \
    ApbfB ApBab ApBaB ApBap ApBAA ApBAb ApBAf ApBpb ApBpf ApBfB ApfbA Apfbp ApfBp AfbAb \
    AfbAB AfbAp Afbpb AfBpb AfBpB baaab baaaB baaap baabA baabp baabf baaBp baapb baapB \
    babab babaB babap babAb babAB babAp babpf babfb babfB baBAA baBAB baBAp baBAf baBpb \
    baBpB baBpf baBfb bapbA bapbf bapBa bapBA bapBp bapBf bAApB bAApf bAAfb bAAfB bAbap \
    bAbAp bAbpf bABAb bABAB bABAp bABAf bABpB bABpf bABfb bABfB bApba bApbp bApbf bApBa \
    bApBA bApBp bApBf bApfb bpbaB bpbap bpbAB bpbAp bpbAf bpbpf bpbfb bpbfB bpBaa bpBab \
    bpBap bpBpb bpBpf bpfbA bpfbp bpfBA bpfBp bfbpb bfBAp bfBpb bfBpB Baaab BaaaB Baaap \
    Baapb Babab BabaB Babap BaBAB BaBAp BaBpf BaBfb BapbA Bapbf BapBA BapBp BapBf BAABa \
    BAABp BAABf BAApb BAApB BAApf BAAfb BAAfB BAbaa BAbap BAbpb BAbpB BABAb BABAB BABAp \
    BABpf BABfb BABfB BApba BApbA BApbp BApbf BApBa BApBf BApfb BApfB BAfbA BAfbp BpbAA \
    BpbAB BpbAp BpbAf Bpbpf Bpbfb BpbfB BpBab BpBap BpBAp BpBAf BpBpf BpfbA Bpfbp BpfBA \
    BpfBp BfBAA BfBAp BfBpb BfBpB pbaaa pbaab pbaap pbaBA pbaBp pbaBf pbAAp pbAAf pbAba \
    pbAbf pbABA pbABp pbABf pbApb pbApB pbApf pbpBa pbpBp pbpBf pbpfb pbpfB pbfbp pbfBA \
    pbfBp pBaaa pBaap pBaba pBabp pBaBA pBaBf pBapb pBapB pBAAB pBAAp pBAAf pBAba pBAbp \
    pBApf pBAfb pBpbA pBpbp pBpbf pBpfb pBpfB pBfBA pBfBp pfbAA pfbAb pfbAB pfbAp pfbpb \
    pfBAA pfBAp pfBpb pfBpB fbAAp fbAbp fbABA fbABp fbApb fbApB fbpbA fBAAB fBAAp fBApb \
    fBApB fBpbA fBpbp fBpBA aaabAb aaabAp aaabpb aaabpB aaabpf aaabfB aaaBaB aaaBap aaaBpb \
    aaaBpB aaaBpf aaaBfb aaapbA aaapbp aaapbf aaapBa aaapBp aaapBf aaapfb aaapfB aaafbA \
    aaafbp aaafBp aabaab aabaaB aabaap aababp aababf aabapB aabAba aabAbp aabABA aabABp \
    aabABf aabApb aabApB aabpbA aabpbp aabpbf aabpBp aabpBf aabpfb aabpfB aabfbp aabfBA \
    aabfBp aaBaap aaBaBf aaBpbA aaBpbp aaBpbf aaBpBA aaBpBp aaBpBf aaBpfb aaBpfB aaBfbp \
    aapbaa aapbAb aapbAB aapbAp aapbpB aapbpf aapbfb aapbfB aapBaa aapBap aapBpb aapBpf \
    aapfbA aapfbp aafbAA aafbAb aafbAp aafbpb aafBpb aafBpB abaabA abaabp abaabf abaaBp \
    abaapb abaapB ababAb ababAB ababAp ababpf ababfb ababfB abaBAA abaBAB abaBAp abaBAf \
    abaBpf abaBfb abapBa abapBA abapBf abAbap abAbAp abAbpf abABAb abABAB abABAp abABAf \
    abABpB abABpf abABfb abABfB abApba abApbp abApbf abApBa abApBA abApBp abApBf abpbap \
    abpbAB abpbAp abpbAf abpbpf abpbfb abpbfB abpBaa abpBap abpBpf abpfbA abpfbp abpfBA \
    abpfBp abfbpb abfBAp abfBpb abfBpB aBaaab aBaaaB aBaaap aBaBAp aBaBpf aBapbA aBapbf \
    aBapBA aBapBp aBapBf aBAABa aBAABp aBAABf aBAApb aBAApB aBAApf aBAAfb aBAAfB aBABAb \
    aBABAB aBABAp aBABpf aBABfb aBABfB aBApba aBApbA aBApbp aBApbf aBApBa aBApBf aBApfb \
    aBApfB aBAfbA aBAfbp aBpbAA aBpbAB aBpbAp aBpbAf aBpbpf aBpbfb aBpbfB aBpBap aBpBAp \
    aBpBAf aBpBpf aBpfbA aBpfbp aBpfBA aBpfBp apbaab apbaBA apbaBf apbAba apbAbf apbABA \
    apbABp apbABf apbApb apbApB apbpBa apbpBf apbpfb apbpfB apbfbp apbfBA apbfBp apBaaa \
    apBaap apBaBA apBaBf apBapb apBapB apBAAB apBAAp apBAAf apBApf apBAfb apBpbA apBpbf \
    apBpfb apBpfB apfbAA apfbAb apfbAp apfbpb apfBAA apfBpb apfBpB afbAAp afbAbp afbApb \
    afbApB afbpbA afBAAB afBAAp afBApb afBpbA afBpbp afBpBA AAbAAp AAbApf AAbpbp AAbpBp \
    AAbpBf AAbpfb AABabp AABaBf AABapb AABAAB AABAAp AABApf AABAfb AABpbp AABpBp AABfbp \
    AApbAA AApbAp AApbAf AApbpB AApbpf AApBab AApBap AApBAA AApBAf AApBpb AApfbp AApfBp \
    AAfbAB Abaaab Abaaap AbaabA Abaabp Abaabf Abaapb AbaapB Abapbf AbapBa AbapBf AbAApf \
    AbAAfB AbApfb AbpbaB Abpbap Abpbpf Abpbfb AbpBaa AbpBab AbpBap AbpBpf Abpfbp AbpfBA \
    AbpfBp ABabab ABabaB ABabap ABaBAB ABaBfb ABapBA ABapBp ABapBf ABAABp ABAApB ABAApf \
    ABAAfb ABAAfB ABAbap ABABpf ABABfb ABABfB ABApba ABApfb ABAfbp ABpbpf ABpbfb ABpBab \
    ABpBap ABpBpf ABpfbA ABpfBA ABfBAp ABfBpb Apbaaa Apbaab Apbaap ApbAAp ApbAAf ApbApf \
    ApbpBa ApbpBf ApbpfB ApBaba ApBabp ApBapB ApBAAB ApBAAf ApBAba ApBAfb ApBpbf ApBfBA \
    ApfbAB ApfbAp Apfbpb ApfBpb ApfBpB AfbABp AfbApB AfBpbp baaabp baaaBf baaapb baabAB \
    baabfb baapbp baapBf bababf babAbp babABp babApb babApB babpfb babpfB babfbp babfBp \
    baBAAB baBAAp baBABp baBApB baBApf baBAfb baBpbA baBpbf baBpfb baBpfB baBfbp bapbAB \
    bapbfb bapbfB bapBpf bAApfb bAApfB bAAfbp bAAfBp bAbapB bAbpfb bABAbp bABApf bABAfb \
    bABpBa bABpBp bABpfb bABfbp bABfBp bApbpB bApbpf bApBaB bpbaBA bpbaBp bpbaBf bpbABf \
    bpbApb bpbApf bpbpfB bpBaap bpBapB bpBpbf bpBpfb bpfbAb bpfbpb bpfBAp bpfBpb bpfBpB \
    bfbpbA bfBApb bfBApB bfBpbp BaaaBp BaaapB Baapbf BabaBf BaBABp BaBApb BaBpfB BaBfbp \
    BapbAb BapbfB BapBAf BAABpf BAApBp BAApBf BAApfb BAAfbp BAbaap BAbapb BAbpbf BAbpBa \
    BAbpBf BABpfb BABpfB BABfbp BABfBp BApbfB BApBab BApBfB BApfbA BApfbp BAfbAp BAfbpb \
    BpbAAp BpbABf BpbApb BpbApf BpbpfB BpBapB BpBApf BpBAfb BpfbAB BpfbAp BfBAAp BfBApB \
    BfBpbA pbaaab pbaBAA pbaBAB pbaBAf pbaBpf pbaBfb pbAApf pbAAfb pbAAfB pbABfb pbABfB \
    pbApbf pbpBaa pbpBpf pbpfBA pBaaaB pBaBAB pBaBfb pBAABf pBAAfb pBAbaa pBApfb pBAfbA \
    pBpbAA pBpbAf pBfBAA pfbABA pfBpBA fbABAp fbABpB fBpbAB aaabpbp aaaBpBp aaapbAp aaapbpf \
    aaapBap aaapfbp aabaabp aabABAb aabABpB aabABfB aabApba aabApbp aabpbAB aabpbAp aabpbpf \
    aabpbfb aabpfBA aabpfBp aabfbpb aaBpbAA aaBpbAp aaBpbAf aaBpbpf aaBpBAp aaBpBpf aapfbAp \
    aapfbpb abaBAAB abaBApf abaBAfb abABAbp abABfBp abpbABf abpbApf abpBapB abpfbpb abfBApb \
    aBaaaBp aBAABpf aBAAfbp aBABpfB aBABfBp aBApfbA aBAfbAp aBpBApf apbaBAf apbABfB apBaaaB \
    apBAAfb apBAfbA apBpbAA apBpbAf apfBpBA ABaBfbp"
@[expose] def burnsideF48s_sp43eP2Str : String :=
  " a A b B q Q f aa ab aB aq aQ af AA Ab AB Aq AQ Af ba bA bq bQ bf Ba BA Bq BQ Bf qa qA \
    qb qB qq qf Qa QA Qb QB Qf fb fB fq fQ aab aaB aaf aba abA abq abQ abf aBa aBA aBq aBQ \
    aBf aqa aqA aqb aqB aqf aQa aQA aQb aQB aQf afb afB afq afQ AAb AAB AAf Aba AbA Abq AbQ \
    Abf ABa ABA ABq ABQ ABf Aqa AqA Aqb AqB Aqf AQa AQA AQb AQB AQf Afb AfB Afq AfQ baa bab \
    baB baq baQ bAA bAb bAB bAq bAQ bAf bqa bqA bqb bqB bqq bqf bQa bQA bQb bQB bQf bfb bfB \
    bfq bfQ Baa Bab BaB Baq BaQ BAA BAb BAB BAq BAQ BAf Bqa BqA Bqb BqB Bqq Bqf BQa BQA BQb \
    BQB BQf Bfb BfB Bfq BfQ qab qaB qAb qAB qAf qba qbA qbq qbQ qbf qBa qBA qBq qBQ qBf qqb \
    qqB qqf qfb qfB qfq qfQ Qab QaB QAb QAB QAf Qba QbA Qbq QbQ Qbf QBa QBA QBq QBQ QBf Qfb \
    QfB fbA fbq fbQ fBA fBq fBQ fqA fqb fqB fQA fQb fQB aaba aabA aabq aabQ aabf aaBa aaBq \
    aaBQ aaBf aafb aafB abaa abab abaB abaq abaQ abAB abAq abAQ abqa abqA abqb abqB abqq \
    abqf abQa abQA abQb abQB abQf abfb abfB abfq abfQ aBaa aBaB aBaq aBaQ aBAA aBAB aBAq \
    aBAf aBqa aBqA aBqB aBqq aBqf aBQa aBQA aBQb aBQB aBQf aBfb aBfq aBfQ aqab aqaB aqAb \
    aqAB aqba aqbA aqbq aqbQ aqbf aqBa aqBA aqBq aqBf aqfb aqfB aQab aQaB aQAb aQAB aQba \
    aQbA aQbq aQbQ aQbf aQBa aQBA aQBq aQBQ aQBf aQfb aQfB afbA afbq afbQ afBA afBq afBQ \
    afqb afqB afQb afQB AAbA AAbq AAbQ AAbf AABa AABA AABq AABQ AABf AAfb AAfB Abaa AbaQ \
    AbAA AbAq AbAf Abqa AbqA Abqb Abqq Abqf AbQa AbQA AbQb AbQf AbfB Abfq AbfQ ABab ABaq \
    ABaQ ABAA ABAb ABAB ABAQ ABAf ABqa ABqA ABqb ABqB ABqq ABqf ABQa ABQA ABQb ABQf ABfb \
    ABfB ABfq ABfQ Aqab AqaB AqAb AqAB Aqba AqbA Aqbq AqbQ Aqbf AqBa AqBA AqBq AqBQ AqBf \
    Aqfb AqfB AQab AQaB AQAb AQAB AQba AQbA AQbQ AQbf AQBa AQBA AQBq AQBf AQfb AQfB AfbA \
    Afbq AfbQ AfBq AfBQ Afqb AfqB AfQb AfQB baab baba babA babq babQ babf baBA baBq baBf \
    baqa baqA baqf baQA baQB baQf bAAf bAbq bAbf bABf bAqa bAqb bAQa bAQA bAQb bAQf bAfq \
    bAfQ bqab bqaB bqAb bqAB bqAf bqba bqbA bqbQ bqbf bqBA bqBf bqqb bqqB bqqf bqfb bqfB \
    bqfq bqfQ bQab bQaB bQAb bQAf bQba bQbA bQbq bQbQ bQbf bQBa bQBA bQBf bQfB bfbq bfbQ \
    bfBA bfBQ bfqA bfqb bfqB bfQA bfQb bfQB BaBQ BaBf Baqa BaqA Baqf BaQA BaQB BaQf BAAB \
    BAAf BABA BABq BABQ BABf BAqa BAqb BAQa BAQA BAQf BAfb BAfq BAfQ BqaB BqAb BqAB BqAf \
    Bqba BqbA Bqbf BqBA BqBq BqBQ BqBf Bqqb BqqB Bqqf Bqfb BqfB Bqfq BqfQ BQab BQaB BQAb \
    BQAf BQba BQBa BQBA BQBf BQfB Bfbq BfbQ BfBA BfBQ BfqA Bfqb BfQA BfQb BfQB qaba qabq \
    qabQ qabf qaBA qaBq qaBQ qaBf qAbf qABf qAfb qAfB qbab qbaB qbaq qbAb qbAQ qbAf qbqq \
    qbqf qbQb qbfB qbfq qbfQ qBaa qBaq qBAA qBAB qBAQ qBAf qBqq qBqf qBQf qBfb qBfq qBfQ \
    qqbA qqbq qqbQ qqbf qqBa qqBq qqBQ qqBf qqfb qqfB qfbq qfbQ qfBq qfBQ qfqb qfqB Qabf \
    QaBf QAba QAbq QAbQ QAbf QABq QABQ QABf QAfb QAfB Qbaa Qbab Qbaq QbAA QbAQ QbAf Qbqq \
    Qbqf QbQf Qbfq QbfQ QBaB QBaq QBAB QBAQ QBAf QBqB QBqq QBqf QBQf QBfb QBfB QBfq QBfQ \
    QfbA Qfbq QfbQ QfBA QfBq QfBQ fbAA fbAb fbAB fbAQ fbqA fbqb fbqB fbqq fbQA fbQb fBAA \
    fBAQ fBqA fBqq fBQA fBQB fqAb fqAB fqbA fqBA fQAb fQAB fQbA fQBA aabaa aabab aabaq aabAB \
    aabAq aabqa aabqq aabqf aabQa aabQb aabQB aabQf aabfb aabfB aabfq aabfQ aaBaa aaBqa \
    aaBqB aaBqq aaBqf aaBQa aaBQf aaBfb aaBfq aaBfQ aafbA aafbq aafbQ aafBA aafBq aafBQ \
    ababa ababA ababq ababQ ababf abaBA abaBf abaqa abaqA abaqf abaQA abaQf abABf abAqa \
    abAqb abAQA abAQf abqab abqAb abqAB abqba abqbA abqbf abqBA abqBf abqqb abqqB abqqf \
    abqfb abqfB abqfq abQaB abQba abQbA abQbq abQbQ abQbf abQBa abQBA abQBf abfbq abfBA \
    abfBQ abfqb abfQA abfQB aBaBQ aBaBf aBaqa aBaqA aBaqf aBaQA aBaQf aBAAB aBAAf aBABA \
    aBABq aBABQ aBABf aBAfb aBqaB aBqAB aBqBA aBqBQ aBqBf aBqqb aBqqB aBqqf aBqfb aBqfq \
    aBQab aBQaB aBQAb aBQba aBQBa aBQBA aBQBf aBQfB aBfbq aBfbQ aBfqb aBfQA aBfQb aqaba \
    aqabQ aqabf aqaBA aqaBq aqaBQ aqaBf aqAbf aqABf aqbab aqbaB aqbAb aqbAQ aqbqq aqbqf \
    aqbQb aqbfB aqbfq aqBaa aqBAB aqBAQ aqBqf aqBfb aqBfq aqfbq aqfbQ aqfBq aqfBQ aQAbf \
    aQABf aQbaa aQbab aQbAQ aQbqq aQbQf aQbfq aQBAB aQBAQ aQBqB aQBqq aQBQf aQBfb aQBfB \
    aQBfq afbAb afbqb afbQb afBQB afqbA afqBA afQbA afQBA AAbAA AAbAf AAbqA AAbqq AAbqf \
    AAbQb AABab AABaQ AABAA AABAQ AABAf AABqA AABqb AABqB AABqq AABqf AABQA AABQf AABfb \
    AABfB AABfq AAfbA AAfbQ AAfBq Abqab AbqAb Abqba AbqbA AbqbQ Abqbf Abqqb AbqqB AbqfB \
    Abqfq AbQAb AbQba AbQbA AbQbq AbQbf AbQfB AbfBQ AbfQA AbfQB ABaqa ABaQA ABaQB ABaQf \
    ABABq ABABQ ABABf ABAQA ABAQf ABAfb ABqAb ABqba ABqbA ABqbf ABqBA ABqBq ABqBQ ABqBf \
    ABqqb ABqqB ABqfb ABqfB ABqfq ABQab ABQaB ABQba ABQfB ABfbq ABfbQ ABfBA ABfBQ ABfqb \
    ABfQA ABfQB Aqbab AqbaB Aqbqq AqBAB AqBqq AqBQf AqBfb AQaBf AQAba AQAbq AQAbQ AQAbf \
    AQABq AQABf AQbab AQBAB AQBqB AQBqf AQBfb AQfbq AQfbQ AQfBA AQfBq AQfBQ AfbAB Afbqq \
    AfbQb AfBqq baabA baabQ baabf babab babaB babAq babAQ babqa babqA babqB babqf babQa \
    babQA babQb babQf babfb babfB babfq babfQ baBAf baBfb baqab baqaB baQBA baQBf bAAfb \
    bAAfB bAbqb bAbqf bAbfq bABfb bABfB bAqab bAqba bAqbA bAqbQ bAqbf bAQAb bAQAB bAQfb \
    bAQfB bAfqB bqaba bqabq bqaBf bqAbf bqABf bqbAb bqbAf bqbfB bqBAA bqBAQ bqBAf bqBfq \
    bqqbq bqqbQ bqqbf bqqBq bqqBf bqqfB bqfbq bqfBq bqfBQ bqfqb bqfqB bQabf bQAfB bQbaa \
    bQbab bQbAA bQbAQ bQbAf bQbqq bQbqf bQbQf bQbfq bQbfQ bQBAB bQBfb bQBfB bfbqb bfbqB \
    bfBQB bfQAB bfQBA BaBQf BaBfb Baqab BaqaB BaQBa BaQBA BaQBf BAABq BAABf BAAfb BAAfB \
    BABAb BABAB BABqA BABqf BABQa BABQA BABQb BABQf BABfb BABfB BABfq BABfQ BAqba BAQAb \
    BAQAB BAQfb BAQfB BAfbQ Bqbab BqBAA BqBAf BqBqq BqBQf BqBfq BqBfQ BqqbQ Bqqbf BqqBq \
    BqqBQ BqqBf Bqfqb BqfqB BQbaa BQbaq BQBfb BQBfB BfbqA Bfbqb BfbqB Bfbqq BfBQA BfqAb \
    BfqbA BfQBA qaBqB qaBfQ qABfb qbaba qbabf qbAbq qbQba qbQbq qbQbQ qbQbf qbfBQ qbfQA \
    qbfQB qBAAB qBAAf qBABA qBABq qBABf qBAQf qBAfb qBqfq qBfbQ qqbqq qqbqf qqbQb qqBqq \
    qqBQf qqBfb qqBfq qqfBq qfbQb QaBfb QAbQb QABfb QABfq Qbaab Qbaba QbabQ Qbabf Qbqqf \
    Qbqfq QBaBQ QBABA QBABf QBAQf QBAfq QBqBA QBqBQ QBqBf QBfbq QBfqb QfbAA Qfbqq fbqAb \
    fbqAB fbqBA fbqqB fbQbA fbQbq fBAAB fQBAB aabABf aabAqb aabqab aabqqb aabqqf aabQba \
    aabQbf aabQBf aabfQB aaBqqB aaBqqf aaBfqb ababab ababaB ababqA ababqB ababqf ababQa \
    ababQb ababfb ababfB abaBAf abaBfb abaqab abaqaB abABfB abAqab abAqbQ abAqbf abAQAb \
    abAQAB abAQfb abAQfB abqaba abqABf abqbAb abqbfB abqqbq abqqBq abqqBf abqfBQ abqfqb \
    abqfqB abQbaa abQbab abQbAQ abQbqq abQbqf abQbfq abQbfQ abQBAB abQBfb abQBfB abfbqB \
    abfBQB abfQAB aBaqaB aBAABq aBAABf aBAAfb aBAAfB aBABqA aBABqf aBABQa aBABQA aBABQf \
    aBABfq aBABfQ aBAfbQ aBqqbQ aBqqBQ aBqfqb aBfbqA aBfbqB aBfqbA aqbabf aqbQbq aqBABq \
    aqBfbQ aQbaab aQbaba aQbabQ aQbabf aQBABA aQBABf aQBqBA aQBqBQ aQBqBf aQBfbq AAbqqb \
    AAbQbf AABaQB AABqBA AABqBf AABqqB AABfqb Abqabq AbqbAb AbqbfB Abqqbf AbqqBq AbqfqB \
    AbfBQB ABaqab ABaqaB ABaQBf ABABqA ABABqf ABABQa ABABfB ABAQAb ABAQAB ABAQfb ABAQfB \
    ABAfbQ ABqbab ABqBAA ABqBAf ABqBqq ABqqbQ ABqqBf ABqfqb ABqfqB ABfbqA ABfbqB Aqbaba \
    Aqbabf AqBABA AqBABq AqBABf AqBfbQ AQaBfb AQbabf AQBqBQ AfbqqB baabQf babAqa babAQA \
    babAQf babqfb babqfB babfBQ babfqb babfQA babfQB baBAfb baBfbQ baqaba baqabf baqaBf \
    baQBfB bAQAbQ bAQAbf bAQfBA bAQfBq bqABfb bqbAbq bqbfBQ bqqbqq bqqBfb bqqfBq bQbaba \
    bQbabQ bQbqqf bQBfbq BaBfbq BaQBfB BABfbq BABfBQ BABfQB BAqbaB BAQABf BAQfBA BqqBqq \
    BqqBQf BqqBfq qaBqBQ qABfbq qbabab qbQbqf qbQbfq qbQbfQ qBAABq qBAfbQ qqbQbf QbaabQ \
    QBABfb QBqBQf fQBABA aabABfB aabQBfb abaBAfb aQBABfb"
@[expose] def burnsideF48s_sp43eKS : List String :=
  ["", "f", "aaa", "aaaf"]
@[expose] def burnsideF48s_sp43eTS : List String :=
  ["", "f", "aaa", "aaaf"]
@[expose] def burnsideF48s_sp43eUS : List String :=
  ["p", "p", "p", "p", "p", "p", "p", "p", "pf", "pf", "pf", "pf", "pf", "pf", "pf", "pf",
    "aaap", "aaap", "aaap", "aaap", "aaap", "aaap", "aaap", "aaap", "aaapf", "aaapf", "aaapf",
    "aaapf", "aaapf", "aaapf", "aaapf", "aaapf"]
@[expose] def burnsideF48s_sp43eVS : List String :=
  ["aqA", "aqA", "aqA", "aqA", "qfq", "qfq", "qfq", "qfq", "aqA", "aqA", "aqA", "aqA", "qfq",
    "qfq", "qfq", "qfq", "aqA", "aqA", "aqA", "aqA", "qfq", "qfq", "qfq", "qfq", "aqA", "aqA",
    "aqA", "aqA", "qfq", "qfq", "qfq", "qfq"]
@[expose] def burnsideF48s_sp43eWS : List String :=
  ["", "f", "aaa", "aaaf", "", "f", "aaa", "aaaf", "", "f", "aaa", "aaaf", "", "f", "aaa",
    "aaaf", "", "f", "aaa", "aaaf", "", "f", "aaa", "aaaf", "", "f", "aaa", "aaaf", "", "f",
    "aaa", "aaaf"]
@[expose] def burnsideF48s_sp43eLS : List (List ℕ) :=
  [[43, 1, 36, 3, 29, 20, 34, 18, 8, 26, 11, 23, 13, 16, 33, 17, 30, 21, 4, 12, 6, 15, 22, 28,
      10, 35, 39, 41, 40, 0, 38, 42, 37, 44, 2, 32, 5, 31, 19, 9, 24, 27, 25, 7, 14],
    [41, 2, 36, 6, 27, 20, 34, 22, 5, 21, 26, 14, 31, 10, 16, 28, 11, 25, 4, 17, 8, 33, 29, 12,
      24, 19, 13, 18, 32, 7, 30, 23, 15, 9, 3, 35, 1, 39, 44, 40, 37, 43, 38, 0, 42],
    [2, 1, 0, 8, 6, 7, 4, 5, 3, 14, 12, 13, 10, 11, 9, 15, 23, 17, 20, 24, 18, 21, 22, 16, 19, 25,
      33, 27, 30, 34, 28, 31, 32, 26, 29, 35, 43, 37, 40, 44, 38, 41, 42, 36, 39],
    [43, 21, 12, 33, 0, 31, 23, 41, 9, 8, 19, 42, 20, 25, 44, 17, 10, 15, 4, 28, 30, 1, 22, 36, 6,
      38, 39, 7, 16, 27, 2, 34, 11, 3, 35, 5, 24, 13, 37, 26, 32, 29, 40, 18, 14],
    [0, 1, 2, 8, 7, 6, 5, 4, 3, 14, 13, 12, 11, 10, 9, 15, 24, 21, 18, 23, 20, 17, 22, 19, 16, 35,
      44, 41, 38, 43, 40, 37, 42, 39, 36, 25, 34, 31, 28, 33, 30, 27, 32, 29, 26]]
@[expose] def burnsideF48s_sp43eLSi : List (List ℕ) :=
  [[29, 1, 34, 3, 18, 36, 20, 43, 8, 39, 24, 10, 19, 12, 44, 21, 13, 15, 7, 38, 5, 17, 22, 11,
      40, 42, 9, 41, 23, 4, 16, 37, 35, 14, 6, 25, 2, 32, 30, 26, 28, 27, 31, 0, 33],
    [43, 36, 1, 34, 18, 8, 3, 29, 20, 33, 13, 16, 23, 26, 11, 32, 14, 19, 27, 25, 5, 9, 7, 31, 24,
      17, 10, 4, 15, 22, 30, 12, 28, 21, 6, 35, 2, 40, 42, 37, 39, 0, 44, 41, 38],
    [2, 1, 0, 8, 6, 7, 4, 5, 3, 14, 12, 13, 10, 11, 9, 15, 23, 17, 20, 24, 18, 21, 22, 16, 19, 25,
      33, 27, 30, 34, 28, 31, 32, 26, 29, 35, 43, 37, 40, 44, 38, 41, 42, 36, 39],
    [4, 21, 30, 33, 18, 35, 24, 27, 9, 8, 16, 32, 2, 37, 44, 17, 28, 15, 43, 10, 12, 1, 22, 6, 36,
      13, 39, 29, 19, 41, 20, 5, 40, 3, 31, 34, 23, 38, 25, 26, 42, 7, 11, 0, 14],
    [0, 1, 2, 8, 7, 6, 5, 4, 3, 14, 13, 12, 11, 10, 9, 15, 24, 21, 18, 23, 20, 17, 22, 19, 16, 35,
      44, 41, 38, 43, 40, 37, 42, 39, 36, 25, 34, 31, 28, 33, 30, 27, 32, 29, 26]]
@[expose] def burnsideF48s_sp43eR1 : List (List (Fin 5 × Bool)) := burnsideF48s_sp43eWords burnsideF48s_sp43eR1S

@[expose] def burnsideF48s_sp43eR2 : List (List (Fin 5 × Bool)) := burnsideF48s_sp43eWords burnsideF48s_sp43eR2S

@[expose] def burnsideF48s_sp43eP1W : List (List (Fin 5 × Bool)) := burnsideF48s_sp43eWords (burnsideF48s_sp43eP1Str.splitOn " ")

@[expose] def burnsideF48s_sp43eP2W : List (List (Fin 5 × Bool)) := burnsideF48s_sp43eWords (burnsideF48s_sp43eP2Str.splitOn " ")

@[expose] def burnsideF48s_sp43eKW : List (List (Fin 5 × Bool)) := burnsideF48s_sp43eWords burnsideF48s_sp43eKS

@[expose] def burnsideF48s_sp43eTW : List (List (Fin 5 × Bool)) := burnsideF48s_sp43eWords burnsideF48s_sp43eTS

@[expose] def burnsideF48s_sp43eU : List (List (Fin 5 × Bool)) := burnsideF48s_sp43eWords burnsideF48s_sp43eUS

@[expose] def burnsideF48s_sp43eV : List (List (Fin 5 × Bool)) := burnsideF48s_sp43eWords burnsideF48s_sp43eVS

@[expose] def burnsideF48s_sp43eW : List (List (Fin 5 × Bool)) := burnsideF48s_sp43eWords burnsideF48s_sp43eWS

abbrev burnsideF48s_sp43eWs (k : ℕ) : List (List (Fin 5 × Bool)) :=
  burnsideF48s_eWs burnsideF48s_sp43eR1 burnsideF48s_sp43eR2 4 (burnsideF48s_sp43eU.getD k [])
    (burnsideF48s_sp43eV.getD k []) (burnsideF48s_sp43eW.getD k [])

abbrev burnsideF48s_sp43eWsB (k : ℕ) : List (List (Fin (subsetOf 5 [0, 1, 2, 4]).length × Bool)) :=
  restrictWords (subsetOf 5 [0, 1, 2, 4]) (burnsideF48s_sp43eWs k)

abbrev burnsideF48s_sp43eEvL (w : List (Fin 5 × Bool)) : List ℕ :=
  burnsideF48s_eEvL 45 burnsideF48s_sp43eLS burnsideF48s_sp43eLSi w

@[expose] def burnsideF48s_sp43eCheckGens (_ : Unit := ()) : Bool :=
  decide (burnsideF48s_sp43eLS = burnsideF48s_sp43eXY.map CFSG.Quasithin.H13.F431.U42Aut.evalAL) &&
    decide (burnsideF48s_sp43eLSi = burnsideF48s_sp43eXY.map fun w =>
      CFSG.Quasithin.H13.F431.U42Aut.evalAL (CFSG.Quasithin.H13.F431.U42Aut.invAL w))

@[expose] def burnsideF48s_sp43eCheckRels (_ : Unit := ()) : Bool :=
  ((burnsideF48s_sp43eR1 ++ burnsideF48s_sp43eR2).all fun w =>
    decide (burnsideF48s_sp43eEvL w = List.range 45)) &&
  ([0, 4, 8, 12, 16, 20, 24, 28].all fun k => decide (burnsideF48s_sp43eEvL
    (burnsideF48s_eCandRel 4 (burnsideF48s_sp43eU.getD k []) (burnsideF48s_sp43eV.getD k [])
      (burnsideF48s_sp43eW.getD k [])) = List.range 45)) &&
  decide (burnsideF48s_sp43eEvL (burnsideF48s_sp43eWord "pbpBp") = U42F431.xL) &&
  decide (burnsideF48s_sp43eEvL (burnsideF48s_sp43eWord "aQABpBp") = U42F431.yL) &&
  decide (burnsideF48s_sp43eEvL (burnsideF48s_sp43eWord "abapBQpfb") = CFSG.Quasithin.H13.F431.U42Aut.f45L) &&
  decide ((burnsideF48s_sp43eKW.map burnsideF48s_sp43eEvL).Nodup)

@[expose] def burnsideF48s_sp43eCheckLetters (_ : Unit := ()) : Bool :=
  ((burnsideF48s_sp43eP1W ++ burnsideF48s_sp43eR1 ++ burnsideF48s_sp43eU).all fun w =>
    w.all fun l => decide (l.1 ≠ 3)) &&
  ((burnsideF48s_sp43eP2W ++ burnsideF48s_sp43eR2 ++ burnsideF48s_sp43eV).all fun w =>
    w.all fun l => decide (l.1 ≠ 2)) &&
  ((burnsideF48s_sp43eKW ++ burnsideF48s_sp43eTW ++ burnsideF48s_sp43eW).all fun w =>
    w.all fun l => decide (l.1 ≠ 2 ∧ l.1 ≠ 3))

@[expose] def burnsideF48s_sp43eCheckClosed (_ : Unit := ()) : Bool :=
  let P1L := burnsideF48s_sp43eP1W.map burnsideF48s_sp43eEvL
  let P2L := burnsideF48s_sp43eP2W.map burnsideF48s_sp43eEvL
  decide (burnsideF48s_sp43eP1W.length = 1296) && decide (burnsideF48s_sp43eP2W.length = 1296) &&
  decide (burnsideF48s_sp43eP1W.getD 0 [(0, true)] = []) &&
  decide (burnsideF48s_sp43eP2W.getD 0 [(0, true)] = []) &&
  decide (burnsideF48s_sp43eKW = [[], burnsideF48s_sp43eWord "f", burnsideF48s_sp43eWord "aaa", burnsideF48s_sp43eWord "aaaf"]) &&
  decide (burnsideF48s_sp43eU.length = 32) && decide (burnsideF48s_sp43eV.length = 32) &&
  decide (burnsideF48s_sp43eW.length = 32) &&
  burnsideF48s_eClosed P1L burnsideF48s_sp43eLS [0, 1, 2, 4] &&
  burnsideF48s_eClosed P2L burnsideF48s_sp43eLS [0, 1, 3, 4] &&
  burnsideF48s_eClosedW (burnsideF48s_sp43eKW.map burnsideF48s_sp43eEvL)
    ([burnsideF48s_sp43eWord "f", burnsideF48s_sp43eWord "aaa"].map burnsideF48s_sp43eEvL)

@[expose] def burnsideF48s_sp43eCheckCand (_ : Unit := ()) : Bool :=
  burnsideF48s_eCandOK (burnsideF48s_sp43eP1W.map burnsideF48s_sp43eEvL)
    (burnsideF48s_sp43eP2W.map burnsideF48s_sp43eEvL) (burnsideF48s_sp43eKW.map burnsideF48s_sp43eEvL)
    (burnsideF48s_sp43eTW.map burnsideF48s_sp43eEvL) (burnsideF48s_sp43eU.map burnsideF48s_sp43eEvL)
    (burnsideF48s_sp43eV.map burnsideF48s_sp43eEvL) (burnsideF48s_sp43eW.map burnsideF48s_sp43eEvL)

end CFSG.ASVolI
