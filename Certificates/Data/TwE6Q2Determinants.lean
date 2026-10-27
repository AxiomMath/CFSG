module

public import Certificates.Data.E6DiagRegular
public import CFSG.RankThree.E6.RootLatticeTools

public section

namespace Certificates.TwE6Q2Determinants

open CFSG.Blueprint.Chevalley CFSG.RankThree.E6 CFSG.HardMathSupport.Timmesfeld.Steinberg
open CFSG.LieType.SeitzGeneration.ExcWideThree.E6DiagRegular

@[expose] def charMatrix (t : List ℕ) : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ :=
  Matrix.of fun i k => e6Certificate.root (t.getD (e6Rho k) 0) i - if i = k then 2 else 0

@[expose] def tupleOrder (t : List ℕ) : ℕ :=
  (detLaplace Tag.E6.rank (charMatrix t)).natAbs

@[expose] def tupleCheck (t : List ℕ) : Bool :=
  let d := tupleOrder t
  decide ((13 ∣ d → d = 39) ∧ (19 ∣ d → d = 57))

@[expose] def determinantCheck (_ : Unit := ()) : Bool :=
  let S : StabCert3 := ⟨[], [], e6WKeys ()⟩
  S.check e6Certificate && (S.elems .E6).all tupleCheck

end Certificates.TwE6Q2Determinants

end
