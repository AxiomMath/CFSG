module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1LPoints
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1Check
public import Certificates.Data.CFSGNative.Schreier.Check
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Matrix.Mul

public section

namespace CFSG.ComponentClassification.HarrisLit.P1.L43

open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.Certificates.Native CFSG.Monster.B.Co2.Native

@[expose] def tbl (a : Array ℕ) : Table := a.map UInt32.ofNat

@[expose] def tm (k : ℕ) : Table := tbl (tab80 k false)

@[expose] def ts (k : ℕ) : Table := tbl (tab80 k true)

@[expose] def codeA : ℕ := 12346818

@[expose] def codeB : ℕ := 15221030

@[expose] def codeD : ℕ := 14408201

@[expose] def codeI : ℕ := 14408200

@[expose] def chainS : Array (Array ℕ) := #[
    tab80 codeA false, tab80 codeB false, tab80 11520448 false, tab80 35178691 false,
    tab80 33560272 false, tab80 20826580 false, tab80 27183445 false, tab80 14467507 false,
    tab80 16002526 false, tab80 14408203 false, tab80 14447566 false]

@[expose] def chainW : Array (List ℤ) := #[
    [], [], [2, -1, 2], [1, -3, -1, -1], [-4, -4, 3], [-5, -5], [-5, -3, -4, -6, 3], [-7, 6, 7, -6],
    [-7, -8, 7, 6, 6], [-8, -6, -8, -9, 6], [7, -5, -3, 9, 3, 4]]

@[expose] def chainBase : List (Fin 80) := [0, 1, 2, 3, 4, 9]

@[expose] def baseArr : Array ℕ := (chainBase.map Fin.val).toArray

@[expose] def l43Levels : Array Level := rawLevels 80 chainS baseArr

@[expose] def pgTbls : Array Table := #[tm codeA, tm codeB]

@[expose] def pgInvTbls : Array Table := pgTbls.map (invT 80)

@[expose] def l43Sift (T : Table) : Bool := siftA 80 l43Levels baseArr 0 (natArr T)

@[expose] def uD : Table := tm codeD

@[expose] def uS : Table := ts codeI

@[expose] def uDS : Table := ts codeD

@[expose] def runuD : Run where
  u := uD
  sylowGens := [tm 11821474, tm 35176627, tm 14650228, tm 38855539]
  sylowOrder := 256
  rows := [
    { row :=
        { rep := tm 11821474, outer := false, classSize := 2106,
          centOrder := 2880, centGens := [tm 10394616, tm 17819842],
          oddPrimes := [3, 5], odd := [
            { rep := tm 31670277, prime := 3, classSize := 40,
              wit := .conj (tm 3354199) 2 },
            { rep := tm 5198163, prime := 3, classSize := 40,
              wit := .conj (tm 22454271) 2 },
            { rep := tm 22610070, prime := 5, classSize := 144,
              wit := .conj (tm 9981372) 2 }] },
      kind := .a6 (tm 22222087) (tm 30806896)
                [some (tm 14408200), some (tm 29414775), some (ts 25614936), some (ts 24033253)] },
    { row :=
        { rep := tm 14650228, outer := true, classSize := 1080,
          centOrder := 5616, centGens := [tm 15481057, tm 42492655],
          oddPrimes := [3, 13], odd := [
            { rep := tm 42492655, prime := 3, classSize := 624,
              wit := .conj (tm 6836235) 8 },
            { rep := tm 14198556, prime := 3, classSize := 104,
              wit := .conj (tm 36243934) 4 },
            { rep := tm 15481057, prime := 13, classSize := 432,
              wit := .conj (tm 21549090) 8 },
            { rep := tm 36248308, prime := 13, classSize := 432,
              wit := .conj (tm 13618771) 8 },
            { rep := tm 1311376, prime := 13, classSize := 432,
              wit := .conj (tm 36243474) 4 },
            { rep := tm 27791802, prime := 13, classSize := 432,
              wit := .conj (tm 14956027) 8 }] },
      kind := .noFive },
    { row :=
        { rep := tm 38855539, outer := false, classSize := 5265,
          centOrder := 1152, centGens := [tm 34288414, tm 37099471],
          oddPrimes := [3], odd := [
            { rep := tm 31947706, prime := 3, classSize := 32,
              wit := .conj (tm 16598296) 4 },
            { rep := tm 20798695, prime := 3, classSize := 32,
              wit := .conj (tm 21275478) 2 },
            { rep := tm 15484285, prime := 3, classSize := 16,
              wit := .conj (tm 29827459) 4 }] },
      kind := .small [tm 18085123, tm 27169507] 288 }]

@[expose] def runuS : Run where
  u := uS
  sylowGens := [tm 40942156, ts 6629227, tm 28874841, tm 33541807, ts 38086032, tm 9694318]
  sylowOrder := 256
  rows := [
    { row :=
        { rep := tm 40942156, outer := false, classSize := 2106,
          centOrder := 2880, centGens := [tm 6388611, tm 11307727],
          oddPrimes := [3, 5], odd := [
            { rep := tm 36462699, prime := 3, classSize := 40,
              wit := .conj (tm 13556082) 2 },
            { rep := tm 10271347, prime := 3, classSize := 40,
              wit := .conj (tm 14101852) 2 },
            { rep := tm 38038059, prime := 5, classSize := 144,
              wit := .conj (tm 36899206) 4 }] },
      kind := .inner },
    { row :=
        { rep := ts 6629227, outer := true, classSize := 10530,
          centOrder := 576, centGens := [tm 16162266, tm 37212132],
          oddPrimes := [3], odd := [
            { rep := tm 37562298, prime := 3, classSize := 8,
              wit := .conj (tm 2252773) 2 },
            { rep := tm 38100277, prime := 3, classSize := 64,
              wit := .conj (tm 5756347) 2 },
            { rep := tm 11702980, prime := 3, classSize := 8,
              wit := .conj (tm 36224290) 2 }] },
      kind := .noFive },
    { row :=
        { rep := tm 28874841, outer := false, classSize := 5265,
          centOrder := 1152, centGens := [tm 23277730, tm 40696764],
          oddPrimes := [3], odd := [
            { rep := tm 14561020, prime := 3, classSize := 32,
              wit := .conj (tm 14573727) 4 },
            { rep := tm 23703816, prime := 3, classSize := 32,
              wit := .conj (tm 2348940) 6 },
            { rep := tm 14408529, prime := 3, classSize := 16,
              wit := .conj (tm 26270242) 4 }] },
      kind := .inner },
    { row :=
        { rep := ts 12439050, outer := true, classSize := 117,
          centOrder := 51840, centGens := [tm 39850015, tm 22163176],
          oddPrimes := [3, 5], odd := [
            { rep := tm 4225828, prime := 3, classSize := 80,
              wit := .conj (tm 3287460) 4 },
            { rep := tm 42529789, prime := 3, classSize := 240,
              wit := .conj (tm 14306122) 2 },
            { rep := tm 1658275, prime := 3, classSize := 480,
              wit := .conj (tm 35560123) 6 },
            { rep := tm 33477270, prime := 5, classSize := 5184,
              wit := .conj (tm 2443399) 4 }] },
      kind := .five [tm 17897863, tm 17928943] 960 },
    { row :=
        { rep := ts 12940497, outer := true, classSize := 117,
          centOrder := 51840, centGens := [tm 15086220, tm 39271333],
          oddPrimes := [3, 5], odd := [
            { rep := tm 20882835, prime := 3, classSize := 240,
              wit := .conj (tm 1931770) 6 },
            { rep := tm 32458551, prime := 3, classSize := 480,
              wit := .conj (tm 11426955) 2 },
            { rep := tm 35633302, prime := 3, classSize := 80,
              wit := .conj (tm 16403250) 6 },
            { rep := tm 15086220, prime := 5, classSize := 5184,
              wit := .conj (tm 13356646) 4 }] },
      kind := .five [tm 2221498, tm 41267271] 960 }]

@[expose] def runuDS : Run where
  u := uDS
  sylowGens := [tm 28777033, tm 12703935, tm 8563353, ts 40509289, ts 7174611]
  sylowOrder := 256
  rows := [
    { row :=
        { rep := tm 28777033, outer := false, classSize := 5265,
          centOrder := 1152, centGens := [tm 8629557, tm 8883729],
          oddPrimes := [3], odd := [
            { rep := tm 30762343, prime := 3, classSize := 32,
              wit := .conj (tm 3593743) 2 },
            { rep := tm 32164225, prime := 3, classSize := 32,
              wit := .conj (tm 11751996) 2 },
            { rep := tm 17596846, prime := 3, classSize := 16,
              wit := .conj (tm 14600656) 6 }] },
      kind := .inner },
    { row :=
        { rep := tm 12703935, outer := false, classSize := 2106,
          centOrder := 2880, centGens := [tm 19240684, tm 32466360],
          oddPrimes := [3, 5], odd := [
            { rep := tm 28071514, prime := 3, classSize := 40,
              wit := .conj (tm 13370493) 2 },
            { rep := tm 30749242, prime := 3, classSize := 40,
              wit := .conj (tm 41376432) 2 },
            { rep := tm 20101108, prime := 5, classSize := 144,
              wit := .conj (tm 1034677) 4 }] },
      kind := .inner },
    { row :=
        { rep := ts 7174611, outer := true, classSize := 8424,
          centOrder := 720, centGens := [tm 1288381, tm 660594],
          oddPrimes := [3, 5], odd := [
            { rep := tm 1185946, prime := 3, classSize := 80,
              wit := .conj (tm 12335485) 4 },
            { rep := tm 21064147, prime := 5, classSize := 72,
              wit := .conj (tm 41805427) 2 },
            { rep := tm 41918103, prime := 5, classSize := 72,
              wit := .conj (tm 21245760) 4 }] },
      kind := .a6 (tm 28947042) (tm 5634355)
                [some (tm 14408200), some (tm 21158344), some (ts 7406221), some (ts 14204479)] }]

@[expose] def l43Runs : List Run := [runuD, runuS, runuDS]

@[expose] def codeAi : ℕ := 18401750

@[expose] def codeBi : ℕ := 39521228

@[expose] def l43CentTriv : List (Table × Table) := [
    (tm 9826243, tm 35314987), (tm 33793471, tm 41973097), (tm 20972452, tm 14614908),
    (tm 32324161, tm 24457290), (tm 11216031, tm 41649538), (tm 23123787, tm 4798872),
    (tm 23150490, tm 21527179), (tm 34361272, tm 29030571), (tm 41717652, tm 28246422),
    (tm 12343810, tm 38446264), (tm 21983929, tm 14723763), (tm 1436545, tm 9266776),
    (tm 31805812, tm 38953449), (tm 26535165, tm 1297972), (tm 5376487, tm 32934118),
    (tm 6907762, tm 6738696), (tm 14458989, tm 20440936), (tm 19339432, tm 26267445),
    (tm 7200426, tm 12165681), (tm 21285505, tm 18049744), (tm 4052640, tm 14620420),
    (tm 27143668, tm 10323757), (tm 12102262, tm 1354672), (tm 29743566, tm 2988064),
    (tm 36243922, tm 36910771), (tm 3106432, tm 38953449), (tm 3783613, tm 14620420),
    (tm 19501857, tm 24927255), (tm 26647537, tm 42889576), (tm 30026830, tm 39659442),
    (tm 26693415, tm 14861437), (tm 15061527, tm 28941078), (tm 26605606, tm 13417879),
    (tm 1131030, tm 27559009), (tm 24853567, tm 28689910), (tm 30337897, tm 10323757),
    (tm 29837701, tm 16792380), (tm 21912349, tm 14831557), (tm 35432803, tm 28914937),
    (tm 28226985, tm 28849621), (tm 8269777, tm 22483981), (tm 38897182, tm 14771971),
    (tm 24120685, tm 22664707), (tm 1269835, tm 35223198), (tm 29503312, tm 27246457),
    (tm 29920233, tm 3565552), (tm 16507326, tm 1060602), (tm 26144382, tm 37169115),
    (tm 32315758, tm 21601333), (tm 24960079, tm 8310871), (tm 29307061, tm 14445735),
    (tm 16246270, tm 6422515), (tm 3200272, tm 29653830), (tm 36652360, tm 704812),
    (tm 23611392, tm 2894077), (tm 30836185, tm 2942086), (tm 12810661, tm 35043081),
    (tm 17246728, tm 19915444), (tm 35202961, tm 12571120), (tm 1402774, tm 30474673),
    (tm 35110458, tm 29110584), (tm 5644311, tm 13388436), (tm 29715208, tm 35090170),
    (tm 22124959, tm 20420161), (tm 22541307, tm 28883010), (tm 38223184, tm 35007412),
    (tm 34279074, tm 30397617), (tm 40101349, tm 32956213), (tm 2698887, tm 11152852),
    (tm 960708, tm 3108421), (tm 37501029, tm 2762857), (tm 28479835, tm 40799014),
    (tm 40811682, tm 10751224), (tm 8748349, tm 39260629), (tm 29387158, tm 13807813),
    (tm 13985176, tm 1294096), (tm 1184629, tm 2718537), (tm 5742637, tm 41474206),
    (tm 4605118, tm 28816801), (tm 14666883, tm 14633844)]

end CFSG.ComponentClassification.HarrisLit.P1.L43
