module

public import CFSG.Sporadic.Schreier.PairJ3Cert
public import CFSG.Sporadic.Schreier.PairF2Sep
public import Certificates.Data.CFSGNative.J3.Data
public meta import CFSG.Sporadic.Schreier.PairJ3Cert
public meta import CFSG.Sporadic.Schreier.PairF2Sep
public meta import Certificates.Data.CFSGNative.J3.Data
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain

public section

namespace CFSG.Sporadic.Schreier.PairJ3

open CFSG.Sporadic.Schreier.PairF2 CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Co2.Native

@[expose] def rowsA1 : Array ℕ := CFSG.Sporadic.J3.Native.j3Data.rowsA

@[expose] def rowsA2 : Array ℕ := CFSG.Sporadic.J3.Native.j3Data.rowsB

@[expose] def pullOKRows (AT A U U' : Array ℕ) : Bool :=
  canonRows 80 (mulRows 80 AT (mulRows 80 U' A)) == U

@[expose] def formsCheckWith (bytes : ByteArray) (S : Array (Array ℕ)) (A1 A2 : Array ℕ) : Bool :=
  let a0 := S[0]!
  let a1 := S[1]!
  let A1T := transposeRows 80 A1
  let A2T := transposeRows 80 A2
  let tri : Array (Array ℕ) :=
    Array.ofFn (n := 6156) fun r => triRowsZ 80 (hexAt bytes (810 * r.val) 810)
  parLt 6156 4 fun r =>
    packRowsZ 80 tri[r]! == hexAt bytes (810 * r) 810 &&
      pullOKRows A1T A1 tri[r]! tri[a0[r]!]! && pullOKRows A2T A2 tri[r]! tri[a1[r]!]!

@[expose] def BRows : Array ℕ := polarRowsZ 80 j3InvWord

@[expose] def BInv : Array ℕ := invRowsF2 80 BRows

@[expose] def TRows : Array (Array ℕ) :=
  Array.ofFn fun r : Fin 4 => mulRows 80 BInv (polarRowsZ 80 (j3FormWord r.val))

@[expose] def sepTerms : List (List ℕ) := [[0, 1], [1, 1, 0], [2, 0, 0], []]

@[expose] def sepVec : ℕ := 266761068769396266742287

@[expose] def sepIdx : ℕ := 0

@[expose] def sepP : Array ℕ :=
  #[0, 67902288224237979670649, 319854663001744065390965,
    554726305130949879061757, 327924924511730953265493, 218238024846078658947982,
    392157076500114366349790, 39246954371148469774981, 363184849010103421431218,
    284844213454524205745240, 585203798751814882058055, 76151538059673421376614,
    596399295652930393027889, 334793852701710211783742, 519222941334412271685253,
    57333536601262290857938, 523695631758913976288826, 148284966147893668041476,
    417162745781230708670156, 194967700193912116569087, 166038559332142683373200,
    71335224694791479350415, 24339919477354702287024, 486805714481857287938475,
    109665931669005966692599, 256247675500751637582442, 86091671244232662865841,
    252143317341816550453044, 570782929777283084412620, 245490894623588947370176,
    321225616431418084998869, 555490884604571416313456, 329260105173845222094963,
    33006747341454174549590, 280556050166300895585519, 94451566440890548974183,
    35202085066950166174555, 119725102886742086106077, 297511848948560126544687,
    422676831108298377330706, 45132090730873826364957, 6716986788549316146936,
    464996309448786559974575, 204397500209060166639324, 565096761235850094816574,
    146778189125352940923042, 340211964456435854236539, 507969413632512284431943,
    301431099977668854582299, 460044655526369045265801, 438133765983494771294414,
    30714453204840828938257, 383402036977468725548942, 221797738897021028407429,
    89989387895270726732138, 126969526609509418452777, 179777850926772549708901,
    538314723772057992306013, 390098249074721903164693, 190508303096628533259106,
    294361759862467004480136, 330711824961950740466014, 203724316754966428204061,
    12650627590232803090645, 281794802838448015322648, 482373509203220616522675,
    248323538640394176762305, 486984056234502916324360, 6267758625588979015282,
    43788359236292103760201, 525163798276928660808409, 453151466490822196947269,
    341544331720922898636472, 546132837660419782200098, 56353340333995841369059,
    322305230281193746746738, 483279377453623243438820, 462763010952411764386341,
    130111159292261402651997, 274913690877777761227905]

@[expose] def sepTree : List (ℕ × ℕ) :=
  [(0, 0), (0, 1), (0, 2), (0, 3), (1, 1), (1, 2), (1, 3), (2, 2), (2, 3), (3, 0), (3, 1),
    (3, 3), (4, 0), (4, 1), (4, 2), (5, 0), (5, 2), (5, 3), (6, 1), (6, 3), (7, 0), (7, 1),
    (7, 2), (8, 0), (8, 1), (8, 3), (9, 0), (9, 1), (9, 2), (10, 1), (10, 2), (10, 3), (11, 0),
    (11, 2), (11, 3), (12, 0), (12, 1), (12, 2), (13, 1), (13, 2), (13, 3), (14, 0), (14, 2),
    (14, 3), (15, 0), (15, 1), (15, 3), (16, 1), (16, 2), (16, 3), (17, 0), (17, 1), (17, 3),
    (18, 0), (18, 1), (18, 2), (19, 0), (19, 2), (19, 3), (20, 0), (20, 1), (20, 2), (21, 1),
    (21, 2), (21, 3), (22, 0), (22, 2), (22, 3), (23, 0), (23, 1), (23, 3), (24, 1), (24, 2),
    (24, 3), (25, 0), (25, 2), (25, 3), (26, 0), (26, 1)]

@[expose] def sepCheckWith (T : Array (Array ℕ)) : Bool :=
  let S := spinVecs 80 T sepVec sepTree
  sepF2OK 80 T sepTerms sepVec sepIdx sepP (invRowsF2 80 S) sepTree S

@[expose] def sortedWords (bytes : ByteArray) : List ℕ :=
  ((List.range 6156).map fun r => hexAt bytes (810 * r) 810).mergeSort

end CFSG.Sporadic.Schreier.PairJ3
