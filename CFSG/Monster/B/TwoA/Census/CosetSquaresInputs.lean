module

public import CFSG.Monster.B.TwoA.Census.CosetReps
public import CFSG.Monster.B.TwoA.Census.CosetCert
public import CFSG.Monster.B.TwoA.Census.LatticeInv
public import CFSG.Monster.B.Rep4371.SpinAct
public import CFSG.Monster.B.Rep4371.GlueDefs
public meta import CFSG.Monster.B.Rep4371.GlueDefs
public meta import CFSG.Monster.B.TwoA.Census.CosetCertData
public meta import CFSG.Monster.B.TwoA.Census.MonoCert
public import CFSG.Monster.Visible.AlgebraAction
public import CFSG.Monster.Visible.SignCompat

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Census

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.VisQuot
  CFSG.Monster.Visible CFSG.Monster.ScalarKernel CFSG.Monster.SpinLattice CFSG.Monster.Spin
  CFSG.Monster.Griess CFSG.Monster.B.Rep4371 Matrix

@[expose] def cosetA (i : ℕ) : ℕ := Model.coeffN (monoSign.getD i 0)

@[expose] def cosetArr (i : ℕ) : Array ℕ := seedA (monoSeed.getD i 0)

@[expose] def genPauli (k : ℕ) : Model.Pauli :=
  if k < 12 then (false, 2 ^ k, 0) else (false, 0, 2 ^ (k - 12))

@[expose] def ofTriple (t : PTriple) : Model.Pauli := (t.1 % 2 == 1, t.2.1, t.2.2)

@[expose] def genCheck (conjY : ℕ → Model.Pauli → Model.Pauli)
    (conjP : Array ℕ → Model.Pauli → Model.Pauli) : Bool :=
  cosetData.all fun c => (List.range 24).all fun k =>
    conjP (cosetArr c.index) (conjY (cosetA c.index) (genPauli k)) ==
      ofTriple (c.genImages.getD k (0, 0, 0))

@[expose] def eSigma (eY : ℕ → Bool → ℕ → Bool × Bool × ℕ)
    (eP : Array ℕ → Bool → ℕ → Bool × Bool × ℕ) (i : ℕ) (η : Bool) (c : ℕ) :
    Bool × Bool × ℕ :=
  let r := eY (cosetA i) η c
  let r' := eP (cosetArr i) r.2.1 r.2.2
  (r.1 ^^ r'.1, r'.2.1, r'.2.2)

@[expose] def eSigmaSq (eY : ℕ → Bool → ℕ → Bool × Bool × ℕ)
    (eP : Array ℕ → Bool → ℕ → Bool × Bool × ℕ) (i : ℕ) (η : Bool) (c : ℕ) :
    Bool × Bool × ℕ :=
  let r := eSigma eY eP i η c
  let r' := eSigma eY eP i r.2.1 r.2.2
  (r.1 ^^ r'.1, r'.2.1, r'.2.2)

@[expose] def sqRowCheck (eY : ℕ → Bool → ℕ → Bool × Bool × ℕ)
    (eP : Array ℕ → Bool → ℕ → Bool × Bool × ℕ) (eQ : Model.Pauli → Bool → ℕ → Bool × Bool × ℕ)
    (i : ℕ) (u : Model.Pauli) : Bool :=
  (List.range 4096).all fun c => [false, true].all fun η => eSigmaSq eY eP i η c == eQ u η c

@[expose] def sqPauli (i : ℕ) : Model.Pauli := if i = 2 then (true, 63, 0) else (false, 0, 0)

end CFSG.Monster.B.TwoA.Census
