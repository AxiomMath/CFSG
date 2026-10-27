module

public import Certificates.Data.Kernel.Misc.A7Nat

public section

namespace CFSG.KD.A7Cnt

open CFSG.KC.LQT.P CFSG.KC.Ord CFSG.KD.A7Nat

@[expose] noncomputable def oneC : Nat := 6614517792

@[expose] noncomputable def imgM (s m : Nat) : Nat :=
  Nat.land (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft (nat_lit 1)
      (Bool.rec (motive := fun _ => Nat) (nat_lit 31) (img s i) (bitJ m i)))) (nat_lit 7))
    (nat_lit 127)

@[expose] noncomputable def presB (s : Nat) (P : List Nat) : Bool :=
  allL P fun m => letB (imgM s m) fun x => memL x P

@[expose] noncomputable def f1L : List Nat := [11, 22, 44, 88, 49, 98, 69]

@[expose] noncomputable def f2L : List Nat := [35, 70, 13, 26, 52, 104, 81]

@[expose] noncomputable def letN (y : Nat) (k : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (k (nat_lit 0)) (fun m _ => k (Nat.succ m)) y

@[expose] noncomputable def sqK (s : Nat) : Nat := mul 7 s s

@[expose] noncomputable def p5 (s : Nat) : Nat :=
  letN (sqK s) fun t => letN (sqK t) fun u => mul 7 u s

@[expose] noncomputable def p7 (s : Nat) : Nat :=
  letN (sqK s) fun t => letN (sqK t) fun u => letN (mul 7 t s) fun v => mul 7 u v

@[expose] noncomputable def p35 (s : Nat) : Nat :=
  letN (sqK s) fun t => letN (sqK t) fun t4 => letN (sqK t4) fun t8 => letN (sqK t8) fun t16 =>
    letN (sqK t16) fun t32 => letN (mul 7 t s) fun v => mul 7 t32 v

@[expose] noncomputable def pent (h : Nat) : Bool :=
  andB (Nat.beq (p5 h) oneC) (notB (Nat.beq h oneC))

@[expose] noncomputable def cycC : Nat := 206703681
@[expose] noncomputable def dblC : Nat := 5470621760

@[expose] noncomputable def hL : List Nat :=
  [6614517792, 5470621760, 3424814208, 206703681, 6578771041, 4298311841, 1080201314, 170956930,
    5406461122, 2181239939, 1279328419, 6514839555, 3289389220, 2152826052, 107025444, 4397760709,
    3261204485, 1208064069, 5506139142, 4362243110, 2316435558]

@[expose] noncomputable def hLK : Bool :=
  allL hL fun h => anyN 7 fun i => anyN 3 fun j => Nat.beq h (mul 7 (pow 7 cycC i) (pow 7 dblC j))

@[expose] noncomputable def c1F (s : Nat) : Bool :=
  impB (even 7 s) (orB (presB s f1L) (orB (presB s f2L) (anyL hL fun h => letB (mul 7 s h) pent)))

@[expose] noncomputable def c1K : Bool := allP 7 c1F

@[expose] noncomputable def stK (P : List Nat) : Nat := cntP 7 fun s => andB (presB s P) (even 7 s)

@[expose] noncomputable def rL : List Nat :=
  [6614517792, 4501637152, 5509318688, 6548490272, 3395422240, 6579980320, 3426912288, 4466083872,
    5473765408, 6612454432, 6513921056, 2319649824, 6613438496, 6547379232, 3393263648]

@[expose] noncomputable def repK : Bool :=
  andB (allL rL (even 7)) (andB (nodupL rL)
    (allL rL fun a => allL rL fun b => impB (notB (Nat.beq a b))
      (notB (presB (mul 7 (inv 7 a) b) f1L))))

@[expose] noncomputable def cj (r g : Nat) : Nat := mul 7 (mul 7 (inv 7 r) g) r

@[expose] noncomputable def wL : List Nat :=
  [2287048736, 2186379398, 6513857537, 3390050374, 1278216356, 4469131265, 2319489120]

@[expose] noncomputable def witB (rj ri : Nat) : Bool :=
  anyL wL fun w => andB (even 7 w) (andB (presB w f1L) (andB (presB (cj rj w) f1L)
    (notB (presB (cj ri w) f1L))))

@[expose] noncomputable def fxK : Bool :=
  andB (allL wL (permK 7)) (allL rL fun rj => impB (notB (Nat.beq rj oneC))
    (Nat.ble (cntL (fun ri => notB (witB rj ri)) rL) (nat_lit 3)))

@[expose] noncomputable def x3C : Nat := 6614515777
@[expose] noncomputable def x3iC : Nat := 6614516738

@[expose] noncomputable def normK : Nat :=
  cntP 7 fun s => andB (even 7 s) (letB (mul 7 s x3C) fun a =>
    orB (Nat.beq a (mul 7 x3C s)) (Nat.beq a (mul 7 x3iC s)))

@[expose] noncomputable def k1 : Nat :=
  cntP 7 fun s => andB (orB (andB (Nat.beq (img s 5) 5) (Nat.beq (img s 6) 6))
    (andB (Nat.beq (img s 5) 6) (Nat.beq (img s 6) 5))) (even 7 s)

@[expose] noncomputable def k2 : Nat :=
  cntP 7 fun s => andB (allN 7 fun i => iffB (Nat.blt (img s i) 4) (Nat.blt i 4)) (even 7 s)

@[expose] noncomputable def k3 : Nat := cntP 7 fun s => andB (Nat.beq (img s 4) 4) (even 7 s)

@[expose] noncomputable def k4 : Nat :=
  cntP 7 fun s => andB (Nat.beq (img s 4) 4) (andB (Nat.beq (p5 s) oneC) (even 7 s))

@[expose] noncomputable def k5 : Nat := cntP 7 fun s => andB (even 7 s) (Nat.beq (p35 s) oneC)

@[expose] noncomputable def k6 : Nat := cntP 7 fun s => andB (even 7 s) (Nat.beq (p7 s) oneC)

@[expose] noncomputable def x2C : Nat := 6614486017

@[expose] noncomputable def centK : Nat := cntP 7 fun s => andB (comm 7 x2C s) (even 7 s)

@[expose] noncomputable def t2L : List Nat :=
  [74946833627445594144, 74946799541413906464, 74945674739977488416, 148733808788413418528,
    222519623999980375072, 185627261750355233824, 111840321740503879712, 222519589915083313184,
    185627227664416968736, 111840287654439654432, 222518465114655560736, 148733740616410928160,
    111839162851963017248, 185624978062553782304, 148732615814975494176, 151039650663755777088,
    224825465875322733632, 187933103625697592384, 227130147800288986176, 225978352195522954304,
    189085989944856609856, 149886730258660493408, 223672545470227449952, 186780183220602308704,
    227130113715427381344, 225978318110628811872, 189085955858922248288, 112993243210749937792,
    223672511385329371264, 186780149134663026816, 227128988915031149696, 224825397705530512512,
    187933035453823948928, 112993209124653205664, 223671386584869111968, 149886662086624479392,
    225976068509804858528, 224824272905102790816, 151039548405785401504, 112992084321136380096,
    186777899531727145152, 149885537284148857024, 189082581456662891712, 187930785851960824000,
    151038423604349998272, 151111707123922339841, 224897522335489296385, 188005160085864155137,
    227202204260455548929, 226050408655689517057, 189158046405023172609, 227273100770215529473,
    227238197873101344769, 226086402268302775297, 189194040016596211713, 151075679426415001634,
    224861494637981958178, 187969132388356816930, 227166176562948210722, 226014380958182178850,
    189122018707515834402, 227273066685355032674, 227238163788239831170, 226086368183408754850,
    189194005930662002882, 149922759021319686179, 223708574232886642723, 186816211983261501475,
    227166142478086574115, 226014346873288004643, 189121984621581441059, 227271941884959786051,
    227202136090732398723, 226050340485901322403, 189157978233154570435, 113029271973408114724,
    223708540147987548196, 186816177897321203748, 227165017677689326628, 224861426468188689444,
    187969064216482125860, 227235914187448353860, 227201011290336168036, 224897420080802007204,
    188005057828055255236, 113029237887278876709, 223707415347494783013, 149922690849250150437,
    226012097272430529573, 224860301667728461861, 151075577168411072549, 226082993782189556805,
    226048090885077370981, 224896295280374286469, 151111570779984201925, 113028113082721863718,
    186813928293312628774, 149921566045734340646, 189118610218248375334, 187966814613546307622,
    151074452365935481894, 189189506728007402566, 189154603830895216742, 188002808226192132230,
    151110445978548799654]

@[expose] noncomputable def lo35 (e : Nat) : Nat := Nat.land e (nat_lit 34359738367)

@[expose] noncomputable def invF (x : Nat) : Bool :=
  impB (andB (even 7 x) (andB (notB (Nat.beq x oneC)) (Nat.beq (mul 7 x x) oneC)))
    (anyL t2L fun e => andB (Nat.beq (lo35 e) x)
      (letB (Nat.shiftRight e (nat_lit 35)) fun g => andB (permK 7 g) (Nat.beq (conj 7 g x2C) x)))

@[expose] noncomputable def invK : Bool := allP 7 invF

end CFSG.KD.A7Cnt

end
