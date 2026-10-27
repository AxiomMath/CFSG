module

public import CFSG.Certificates.Kernel.Orders.Mat
public import CFSG.Certificates.Kernel.Enum.Defs
public import Certificates.Data.Kernel.SporSch.LyMat

public section

namespace CFSG.KD.LocLn

open CFSG.KC.Enum CFSG.KC.Ord

structure Kit where
  n : Nat
  S : Nat
  D : Nat
  E2 : Nat
  L : Nat
  H : Nat
  CM : Nat
  RM : Nat
  ONEh : Nat
  LV : Nat
  HV : Nat
  MA : Nat
  M2 : Nat
  ONE : Nat
  MONE : Nat

@[expose] def k4 : Kit where
  n := 4
  S := 32
  D := 128
  E2 := 256
  L := 1334440654591915542993625911497130241
  H := 170808403787765189503184116671632670848
  CM := 20203181445841325826244859658495
  RM := 4294967295
  ONEh := 1329227995786124798723422788966678529
  LV := 16843009
  HV := 2155905152
  MA := 340282366920938463463374607431768211455
  M2 := 2658455991572249597446845577933357058
  ONE := 452312848583677764512654835845145039400233870286445900876090644636213706753
  MONE := 904625697167355529025309671690290078800467740572891801752181289272427413506

@[expose] def k5 : Kit where
  n := 5
  S := 40
  D := 200
  E2 := 400
  L := 6301717820623491276635145460161421970675305857971736609025
  H := 806619881039806883409298618900662012246439149820382285955200
  CM := 372682917519719197280865094166326642823449301483775
  RM := 1099511627775
  ONEh := 6277101735386703064580987953910036114334892711894061154305
  LV := 4311810305
  HV := 551911719040
  MA := 1606938044258990275541962092341162602522202993782792835301375
  M2 := 12554203470773406129161975907820072228669785423788122308610
  ONE := 10086913586277022514259309110631448801697808181052230732116306589415334515098768947772922494707403146339279873175977985
  MONE := 20173827172554045028518618221262897603395616362104461464232613178830669030197537895545844989414806292678559746351955970

@[expose] noncomputable def kitOK (K : Kit) : Bool :=
  andB (constsOK (nat_lit 3) (nat_lit 8) K.S K.n (nat_lit 5) K.L K.H K.CM K.RM K.ONEh K.LV K.HV)
  (andB (Nat.ble (nat_lit 1) K.n)
  (andB (Nat.beq K.D (Nat.mul K.n K.S))
  (andB (Nat.beq K.E2 (Nat.add K.D K.D))
  (andB (Nat.beq K.MA (Nat.sub (Nat.shiftLeft (nat_lit 1) K.D) (nat_lit 1)))
  (andB (Nat.beq K.M2 (Nat.add K.ONEh K.ONEh))
  (andB (Nat.beq K.ONE (Nat.lor K.ONEh (Nat.shiftLeft K.ONEh K.D)))
    (Nat.beq K.MONE (Nat.lor K.M2 (Nat.shiftLeft K.M2 K.D)))))))))

@[expose] noncomputable def hA (K : Kit) (P : Nat) : Nat := Nat.land P K.MA

@[expose] noncomputable def hB (K : Kit) (P : Nat) : Nat := Nat.land (Nat.shiftRight P K.D) K.MA

@[expose] noncomputable def eps (K : Kit) (P : Nat) : Nat := Nat.shiftRight P K.E2

@[expose] noncomputable def mk (K : Kit) (a b e : Nat) : Nat :=
  Nat.lor (Nat.lor a (Nat.shiftLeft b K.D)) (Nat.shiftLeft e K.E2)

@[expose] noncomputable def mulH (K : Kit) (X Y : Nat) : Nat :=
  mulR (nat_lit 3) (nat_lit 8) K.S K.n (nat_lit 5) K.L K.H K.CM K.RM X Y

@[expose] noncomputable def mulN (K : Kit) (P Q : Nat) : Nat :=
  strictN (hA K P) fun a => strictN (hB K P) fun b => strictN (hA K Q) fun a' =>
  strictN (hB K Q) fun b' => strictN (Nat.land (Nat.add (eps K P) (eps K Q)) (nat_lit 1)) fun e =>
  Bool.rec (motive := fun _ => Nat) (mk K (mulH K a a') (mulH K b b') e)
    (mk K (mulH K a b') (mulH K b a') e) (Nat.beq (eps K P) (nat_lit 1))

@[expose] noncomputable def trH (K : Kit) (X : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun k acc => strictN acc fun a =>
    Nat.lor a (Nat.shiftLeft (Nat.land (Nat.shiftRight X (Nat.mul (nat_lit 8) k)) (nat_lit 255))
      (Nat.mul (nat_lit 8) (Nat.add (Nat.mul K.n (Nat.mod k K.n)) (Nat.div k K.n)))))
    (Nat.mul K.n K.n)

@[expose] noncomputable def invN (K : Kit) (P : Nat) : Nat :=
  strictN (trH K (hA K P)) fun a => strictN (trH K (hB K P)) fun b =>
  Bool.rec (motive := fun _ => Nat) (mk K b a (eps K P)) (mk K a b (eps K P))
    (Nat.beq (eps K P) (nat_lit 1))

@[expose] noncomputable def fnzN (K : Kit) (P : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun j acc => strictN acc fun a =>
    strictN (Nat.land (Nat.shiftRight P (Nat.mul (nat_lit 8)
      (Nat.sub (Nat.sub (Nat.mul K.n K.n) (nat_lit 1)) j))) (nat_lit 255)) fun v =>
      nIf(Nat.beq v (nat_lit 0), a, v)) (Nat.mul K.n K.n)

@[expose] noncomputable def normN (K : Kit) (P : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) P (mulN K K.MONE P) (Nat.beq (fnzN K P) (nat_lit 2))

@[expose] noncomputable def actN (K : Kit) (G P : Nat) : Nat := strictN (mulN K G P) (normN K)

@[expose] noncomputable def eqN (K : Kit) (P Q : Nat) : Bool :=
  bAnd(Nat.beq (eps K P) (eps K Q), strictB (hA K P) fun a => strictB (hA K Q) fun b =>
    bIf(Nat.beq a b, true, Nat.beq a (mulH K b K.M2)))

@[expose] noncomputable def b3N (K : Kit) (X : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun j acc => strictN acc fun a =>
    Nat.add (Nat.mul a (nat_lit 3)) (Nat.land (Nat.shiftRight X (Nat.mul (nat_lit 8)
      (Nat.sub (Nat.sub (Nat.mul K.n K.n) (nat_lit 1)) j))) (nat_lit 255))) (Nat.mul K.n K.n)

@[expose] noncomputable def keyN (K : Kit) (P : Nat) : Nat :=
  strictN (hA K P) fun A => strictN (b3N K A) fun a => strictN (b3N K (mulH K A K.M2)) fun b =>
    Nat.add (Nat.mul (nat_lit 2) (Bool.rec (motive := fun _ => Nat) b a (Nat.ble a b)))
      (Nat.mod (eps K P) (nat_lit 2))

@[expose] noncomputable def canonN (K : Kit) (P : Nat) : Bool :=
  andB (validM (nat_lit 3) K.D K.L K.H (hA K P))
    (andB (validM (nat_lit 3) K.D K.L K.H (hB K P)) (Nat.blt (eps K P) (nat_lit 2)))

@[expose] noncomputable def validN (K : Kit) (P : Nat) : Bool :=
  bAnd(canonN K P, Nat.beq (mulN K P (invN K P)) K.ONE)

@[expose] noncomputable def powN (K : Kit) (P m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) K.ONE (fun _ acc => strictN acc fun a => mulN K a P) m

@[expose] noncomputable def conjN (K : Kit) (S X : Nat) : Nat :=
  strictN (mulN K S X) fun Y => mulN K Y (invN K S)

@[expose] noncomputable def mAN (K : Kit) (P Q : Nat) : Nat :=
  mulH K (hA K P) (Bool.rec (motive := fun _ => Nat) (hA K Q) (hB K Q) (Nat.beq (eps K P) (nat_lit 1)))

@[expose] noncomputable def commN (K : Kit) (X Y : Nat) : Bool :=
  strictB (mAN K X Y) fun u => strictB (mAN K Y X) fun v =>
    bIf(Nat.beq u v, true, Nat.beq u (mulH K v K.M2))

@[expose] noncomputable def flagN (K : Kit) (P : Nat) : Nat :=
  Nat.add
    (nIf(bAnd(eqN K (powN K P (nat_lit 8)) K.ONE, notB (eqN K (powN K P (nat_lit 4)) K.ONE)),
      (nat_lit 1), (nat_lit 0)))
    (nIf(bAnd(eqN K (powN K P (nat_lit 2)) K.ONE, notB (eqN K P K.ONE)), (nat_lit 2), (nat_lit 0)))

@[expose] noncomputable def selN (W0 W1 W2 i : Nat) : Nat :=
  nIf(Nat.beq i (nat_lit 0), W0, nIf(Nat.beq i (nat_lit 1), W1, W2))

@[expose] noncomputable def evalN (K : Kit) (W0 W1 W2 : Nat) (w : List (Nat × Bool)) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun l _ ih acc => strictN (mulN K acc (Prod.rec (motive := fun _ => Nat)
      (fun i b => Bool.rec (motive := fun _ => Nat) (selN W0 W1 W2 i)
        (invN K (selN W0 W1 W2 i)) b) l)) ih) w K.ONE

@[expose] noncomputable def wordN (w : List (Nat × Bool)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun l _ ih => bAnd(Nat.blt (Prod.fst l) (nat_lit 3), ih))
    w

@[expose] noncomputable def repN (K : Kit) (X T G1 G2 : Nat) (wa wb : List (Nat × Bool))
    (ma mb j : Nat) : Bool :=
  bAnd(validN K X, bAnd(validN K T, bAnd(validN K G1, bAnd(validN K G2,
  bAnd(Nat.beq (eps K G1) (nat_lit 0), bAnd(Nat.beq (eps K G2) (nat_lit 0),
  bAnd(eqN K (mulN K G1 T) (mulN K T G1), bAnd(eqN K (mulN K G2 T) (mulN K T G2),
  bAnd(wordN wa, bAnd(wordN wb,
  bAnd(Nat.beq (Nat.mod ma (nat_lit 2)) (nat_lit 1), bAnd(Nat.beq (Nat.mod mb (nat_lit 2)) (nat_lit 1),
  strictB (conjN K G1 X) fun C1 => strictB (conjN K G2 X) fun C2 =>
  strictB (evalN K X C1 C2 wa) fun A => strictB (evalN K X C1 C2 wb) fun B =>
  strictB (mulN K A B) fun AB =>
  bAnd(eqN K (powN K A ma) K.ONE, bAnd(eqN K (powN K B mb) K.ONE,
  bAnd(eqN K (powN K AB (Nat.mul (nat_lit 2) j)) K.ONE,
    notB (eqN K (powN K AB j) K.ONE))))))))))))))))

@[expose] noncomputable def pkL (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun d _ acc => Nat.add d (Nat.shiftLeft acc (nat_lit 8))) l

@[expose] noncomputable def lenL (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ k => Nat.succ k) l

@[expose] noncomputable def smallL (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun d _ ih => bAnd(Nat.blt d (nat_lit 3), ih)) l

@[expose] noncomputable def codeN (K : Kit) (x : Array Nat) (P : Nat) : Bool :=
  bAnd(Nat.beq (lenL x.toList) (Nat.succ (Nat.add (Nat.mul K.n K.n) (Nat.mul K.n K.n))),
    bAnd(smallL x.toList, Nat.beq (pkL x.toList) P))

@[expose] noncomputable def posN (m : Nat) (PA LA : Nat → Nat) (j : Nat) : Nat :=
  Nat.add (Nat.mul m (PA j)) (LA j)

@[expose] noncomputable def ptN (K : Kit) (m N : Nat) (G T : Nat → Nat) (E : Nat → Nat → Nat)
    (PA LA SO SOI : Nat → Nat) (i : Nat) : Bool :=
  strictB (T i) fun P =>
  bAnd(validN K P, bAnd(CFSG.KS.SporSch.LyM.sortB (fun j => keyN K (T j)) SO SOI N i,
    bAnd(allBlk (nat_lit 0) (fun k => strictB (E i k) fun e =>
      bAnd(Nat.blt e N, bAnd(Nat.beq (actN K (G k) P) (T e),
        bIf(Nat.beq e (nat_lit 0), true,
          Nat.ble (posN m PA LA e) (Nat.add (Nat.mul m i) k))))) m,
    bIf(Nat.beq i (nat_lit 0),
      bAnd(Nat.beq P K.ONE, bAnd(Nat.beq (PA (nat_lit 0)) (nat_lit 0),
        Nat.beq (LA (nat_lit 0)) (nat_lit 0))),
      bAnd(Nat.blt (PA i) i, bAnd(Nat.blt (LA i) m, bAnd(Nat.beq (E (PA i) (LA i)) i,
        bIf(Nat.beq (Nat.succ i) N, true,
          Nat.blt (posN m PA LA i) (posN m PA LA (Nat.succ i))))))))))

@[expose] noncomputable def blkN (K : Kit) (m N : Nat) (G T : Nat → Nat) (E : Nat → Nat → Nat)
    (PA LA SO SOI : Nat → Nat) (b len : Nat) : Bool :=
  allBlk b (fun i => strictB i fun i => ptN K m N G T E PA LA SO SOI i) len

@[expose] noncomputable def flagBlk (K : Kit) (T F : Nat → Nat) (b len : Nat) : Bool :=
  allBlk b (fun i => strictB i fun i => Nat.beq (flagN K (T i)) (F i)) len

@[expose] noncomputable def covN (K : Kit) (N NR : Nat) (T RX RT : Nat → Nat) (c X Y : Nat) :
    Bool :=
  bAnd(Nat.blt (nat_lit 0) c, strictB (Nat.sub c (nat_lit 1)) fun c =>
    strictB (Nat.div c N) fun ri => strictB (Nat.mod c N) fun si =>
    bAnd(Nat.blt ri NR, strictB (T si) fun S =>
      bAnd(eqN K (conjN K S (RX ri)) X, eqN K (conjN K S (RT ri)) Y)))

@[expose] noncomputable def pairN (K : Kit) (N NR : Nat) (T O8 O2 CV RX RT : Nat → Nat)
    (nb a : Nat) : Bool :=
  strictB (T (O8 a)) fun X => allBlk (nat_lit 0) (fun b => strictB (T (O2 b)) fun Y =>
    bIf(commN K X Y, covN K N NR T RX RT (CV (Nat.add (Nat.mul nb a) b)) X Y, true)) nb

@[expose] noncomputable def pairBlk (K : Kit) (N NR : Nat) (T O8 O2 CV RX RT : Nat → Nat)
    (nb a len : Nat) : Bool :=
  allBlk a (fun a => strictB a fun a => pairN K N NR T O8 O2 CV RX RT nb a) len

end CFSG.KD.LocLn

end
