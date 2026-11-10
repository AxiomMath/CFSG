
module

public import Certificates.Data.ParrottExtraspecial


@[expose] public section

namespace Certificates

open CFSG.RankThree.GF2n.Parrott

def fixedMasks (M : Matrix (Fin 8) (Fin 8) (ZMod 2)) (ms : List Nat) : List Nat :=
  (List.range 512).filter (fun p => phiMask M ms p == p)

def isInv (p : Nat) : Bool := mulMask p p == 0

def invMaskCount (M : Matrix (Fin 8) (Fin 8) (ZMod 2)) (ms : List Nat) : Nat :=
  ((fixedMasks M ms).filter fun p => isInv p).length

def fixedNoncomm (M : Matrix (Fin 8) (Fin 8) (ZMod 2)) (ms : List Nat) : Bool :=
  let F := fixedMasks M ms
  F.any fun p => F.any fun q => mulMask p q != mulMask q p

def fixedCentral (M : Matrix (Fin 8) (Fin 8) (ZMod 2)) (ms : List Nat) : Bool :=
  (fixedMasks M ms).all fun p => p % 256 == 0

def fixedCentreCard (M : Matrix (Fin 8) (Fin 8) (ZMod 2)) (ms : List Nat) : Nat :=
  let F := fixedMasks M ms
  (F.filter fun z => F.all fun q => mulMask z q == mulMask q z).length

def fixedOrderFour (M : Matrix (Fin 8) (Fin 8) (ZMod 2)) (ms : List Nat) : Bool :=
  (fixedMasks M ms).all fun p =>
    mulMask p (mulMask p (mulMask p p)) == 0

def cocycleCheck (M : Matrix (Fin 8) (Fin 8) (ZMod 2)) (ms : List Nat) : Bool :=
  (List.range 256).all fun p => (List.range 256).all fun q =>
    (cMask ms (p ^^^ q) ^^^ cMask ms p ^^^ cMask ms q ==
      bhMask (bitRow M p) (bitRow M q) ^^^ bhMask p q)

def cubeCheck (M : Matrix (Fin 8) (Fin 8) (ZMod 2)) (ms : List Nat) : Bool :=
  (List.range 512).all fun p => phiMask M ms (phiMask M ms (phiMask M ms p)) == p

structure LiftFacts (M Minv : Matrix (Fin 8) (Fin 8) (ZMod 2)) (ms : List Nat)
    (fixedCard invCard : ℕ) (noncommValue : Bool) : Prop where
  mul_inv : M * Minv = 1
  inv_mul : Minv * M = 1
  M_cube : M * M * M = 1
  cocycle : cocycleCheck M ms = true
  one : phiMask M ms 0 = 0
  cube : cubeCheck M ms = true
  fix_card : ((List.range 512).filter (fun p => phiMask M ms p == p)).length = fixedCard
  noncomm : fixedNoncomm M ms = noncommValue
  involutions : ((List.range 512).filter
    (fun p => phiMask M ms p == p ∧ mulMask p p == 0)).length = invCard

structure ExtraspecialFacts : Prop where
  s1 : LiftFacts Ms1H Ms1HInv cMs1 8 2 true
  s2 : LiftFacts Ms2H Ms2HInv cMs2 8 2 true
  s1s2 : LiftFacts Ms1s2H Ms1s2HInv cMs1s2 2 2 false
  s1s2inv : LiftFacts Ms1s2invH Ms1s2invHInv cMs1s2inv 32 20 true
  s1_fixed_noncomm : fixedNoncomm Ms1H cMs1 = true
  s2_fixed_noncomm : fixedNoncomm Ms2H cMs2 = true
  s1s2_fixed_central : fixedCentral Ms1s2H cMs1s2 = true
  s1s2_fixed_commute : fixedNoncomm Ms1s2H cMs1s2 = false
  s1s2inv_fixed_noncomm : fixedNoncomm Ms1s2invH cMs1s2inv = true
  s1s2inv_fixed_involutions : invMaskCount Ms1s2invH cMs1s2inv = 20
  s1s2inv_fixed_centre : fixedCentreCard Ms1s2invH cMs1s2inv = 2
  s1_fixed_order_le_four : fixedOrderFour Ms1H cMs1 = true
  s2_fixed_order_le_four : fixedOrderFour Ms2H cMs2 = true
  s1s2inv_fixed_order_le_four : fixedOrderFour Ms1s2invH cMs1s2inv = true

end Certificates

