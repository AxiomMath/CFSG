module

import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Index
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeProofDefs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofL364Hyper
public import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofSeitzCover

public section

namespace CFSG.RankThree.PartTwo.Sec19.SeitzScopeProof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo TauCeti CFSG.AGLEmbeddingD2
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Res6Seitz
open CFSG.LieType.SeitzGeneration
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

theorem scope_A (q : PrimePower) {r : ℕ} (hr : 2 ≤ r) (hr3 : r ≤ 3) :
    IsLThreePiIndex (.A r q) ∨ IsTrialityIndex (.A r q) ∨ IsSeitz441Index (.A r q) := by
  rcases (by omega : r = 2 ∨ r = 3) with rfl | rfl
  · exact Or.inl ⟨q, Or.inl rfl⟩
  · exact Or.inr (Or.inr (Or.inl ⟨q, Or.inl rfl⟩))

theorem scope_twistedA (q : PrimePower) {r : ℕ} (hr : 2 ≤ r) (hr3 : r ≤ 3) :
    IsLThreePiIndex (.twistedA r q) ∨ IsTrialityIndex (.twistedA r q) ∨
      IsSeitz441Index (.twistedA r q) := by
  rcases (by omega : r = 2 ∨ r = 3) with rfl | rfl
  · exact Or.inl ⟨q, Or.inr rfl⟩
  · exact Or.inr (Or.inr (Or.inl ⟨q, Or.inr (Or.inl rfl)⟩))

theorem scope_B2 (q : PrimePower) :
    IsLThreePiIndex (.B 2 q) ∨ IsTrialityIndex (.B 2 q) ∨ IsSeitz441Index (.B 2 q) :=
  Or.inr (Or.inr (Or.inl ⟨q, Or.inr (Or.inr rfl)⟩))

theorem scope_G2 (q : PrimePower) :
    IsLThreePiIndex (.G2 q) ∨ IsTrialityIndex (.G2 q) ∨ IsSeitz441Index (.G2 q) :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨q, rfl⟩)))

theorem scope_trialityD4 (q : PrimePower) :
    IsLThreePiIndex (.trialityD4 q) ∨ IsTrialityIndex (.trialityD4 q) ∨
      IsSeitz441Index (.trialityD4 q) :=
  Or.inr (Or.inl ⟨q, rfl⟩)

theorem scope_reeF4 (m : ℕ) :
    IsLThreePiIndex (.reeF4 m) ∨ IsTrialityIndex (.reeF4 m) ∨ IsSeitz441Index (.reeF4 m) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨m, rfl⟩)))

end CFSG.RankThree.PartTwo.Sec19.SeitzScopeProof

