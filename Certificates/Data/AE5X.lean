module

public import Certificates.Data.AE5Sq

public section

namespace Certificates.AE5X

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr Certificates.AE117 Certificates.AE5Sq

abbrev Lab : Type := Finset (Fin 5) × Bool

@[expose] def labs : List Lab := alphas.flatMap fun α => [(α, true), (α, false)]

@[expose] def memL (p : Lab) : List (Wr 5) := memAtL p.1 p.2

@[expose] def zW (p : Lab) : Wr 5 := (memL p).getD 1 1

@[expose] def twin (p q : Lab) : Bool :=
  (memL p).all fun m => (memL q).all fun m' => eqPi (m * m') (m' * m)

@[expose] def prodL (p q : Lab) : List (Wr 5) :=
  (memL p).flatMap fun m => (memL q).map fun m' => m * m'

@[expose] def inv18With (Pl : List (Wr 5)) (z : Wr 5) (x : Wr 5) : Bool :=
  Pl.any (fun y => eqPi x y) && !inPi x && inPi (x * x) && !eqPi x z

@[expose] def L18 (p q : Lab) : List (Wr 5) :=
  let Pl := prodL p q
  Pl.filter (inv18With Pl (zW p))

@[expose] def inV (x : Wr 5) : Bool := decide (x.perm = 1)

@[expose] def isAE (w : Wr 5) : Bool := decide (∑ i, w.vec i = 0) && decide (Equiv.Perm.sign w.perm = 1)

@[expose] def normG (p q : Lab) (w : Wr 5) : Bool :=
  let Pl := prodL p q
  ((memL p) ++ (memL q)).all fun g => Pl.any fun y => eqPi (w * g * w⁻¹) y

@[expose] def nrm (p q : Lab) : Finset (Wr 5) :=
  Finset.univ.filter fun w => (isAE w && eqPi (w * zW p * w⁻¹) (zW p) && normG p q w) = true

@[expose] def excOK (c : Wr 5) : Bool :=
  labs.all fun l => (memL l).all fun m => !ord4Pi m || !eqPi (c * m * c⁻¹) m

@[expose] def swapOK (p q : Lab) (w : Wr 5) : Bool :=
  isAE w &&
  (memL p).all (fun m => (memL q).any fun m' => eqPi (w * zW p * w⁻¹ * m * (w * zW p * w⁻¹)⁻¹) m') &&
  (memL q).all (fun m' => (memL p).any fun m => eqPi (w * zW p * w⁻¹ * m' * (w * zW p * w⁻¹)⁻¹) m) &&
  !eqPi (w * zW p * w⁻¹) (zW p) &&
  labs.any (fun l => (memL l).any fun m =>
    ord4Pi m && eqPi (w * zW p * w⁻¹ * zW p * m) (m * (w * zW p * w⁻¹ * zW p))) &&
  finAll Finset.univ (fun c => !eqPi (c * zW p * c⁻¹) (w * zW p * w⁻¹ * zW p))

@[expose] def chkCent (_ : Unit := ()) : Bool :=
  finAll Finset.univ fun c : Wr 5 =>
    !(eqPi (c * a0 ()) (a0 () * c) && eqPi (c * b0 ()) (b0 () * c)) || inPi c

@[expose] def chkOdd (_ : Unit := ()) : Bool :=
  labs.all fun l => finAll Finset.univ fun c : Wr 5 =>
    !((memL l).all fun m => eqPi (c * m) (m * c)) || !inPi (c ^ 15) || inPi c

@[expose] def chkInv (_ : Unit := ()) : Bool :=
  labs.all fun l => (memL l).all fun m => !(!inPi m && inPi (m * m)) || eqPi m (zW l)

@[expose] def chkZV (_ : Unit := ()) : Bool := labs.all fun l => inV (zW l)

@[expose] def chkA1 (p q : Lab) : Bool :=
  let L := L18 p q
  L.any (fun x => inV x) && L.any (fun x => !inV x)

@[expose] def chkA2 (p q : Lab) : Bool :=
  let L := L18 p q
  let N := nrm p q
  [true, false].all fun v => L.any fun x₀ => inV x₀ == v &&
    L.all fun x' => (inV x' != v) || decide (∃ w ∈ N, eqPi (w * x₀ * w⁻¹) x' = true)

@[expose] def chkA3 (p q : Lab) : Bool := decide (∃ w ∈ (Finset.univ : Finset (Wr 5)), swapOK p q w = true)

@[expose] def chkA5 (p q : Lab) : Bool :=
  let L := L18 p q
  finAll Finset.univ fun c : Wr 5 =>
    !(eqPi (c * c * a0 ()) (a0 () * (c * c)) && eqPi (c * c * b0 ()) (b0 () * (c * c))) ||
      !normG p q c || !excOK c ||
      (L.any (fun x => inV x && !eqPi (c * x * c⁻¹) x) && L.any (fun x => !inV x && !eqPi (c * x * c⁻¹) x))

@[expose] def chkTwin (p q : Lab) : Bool := chkA1 p q && chkA2 p q && chkA3 p q && chkA5 p q

@[expose] def checkX (_ : Unit := ()) : Bool :=
  chkCent () && chkOdd () && chkInv () && chkZV () &&
    labs.all fun p => labs.all fun q => !twin p q || chkTwin p q

end Certificates.AE5X
