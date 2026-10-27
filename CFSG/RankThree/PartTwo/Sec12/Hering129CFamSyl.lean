module

import CFSG.RankThree.PartTwo.Sec4.Ronan148LT2SU4
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartOne.S12.ModelTransport
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projImage projSL projSU projSp)
open CFSG.Open (StatedSL StatedSp)
open CFSG.RankThree.PartTwo.Sec4.Ronan148L

namespace Hering129C

theorem sylow_comm_projSp_two {K : Type} [Field K] [Finite K] (hK : ¬ 3 ∣ Nat.card K) :
    ∀ P : Sylow 3 (projSp 2 K), ∀ a b : projSp 2 K, a ∈ (P : Subgroup (projSp 2 K)) →
      b ∈ (P : Subgroup (projSp 2 K)) → a * b = b * a := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [← CFSG.RankThree.PartOne.projImage_statedSp_eq_projSp 2 K]
  rcases (by omega : Nat.card K % 3 = 1 ∨ Nat.card K % 3 = 2) with h | h
  · exact comm_sylow_projImage fun P hP => comm_of_isPGroup_Sp4_mod_one h P hP
  · refine comm_sylow_projImage fun P hP a ha b hb => ?_
    set f : ↥(StatedSp 2 K) →* GL (Fin 4) K :=
      (glSumEquiv K).toMonoidHom.comp (StatedSp 2 K).subtype with hf
    have hfi : Function.Injective f := (glSumEquiv K).injective.comp Subtype.val_injective
    have h' := comm_of_isPGroup_GL4 h (P.map f) (hP.map _) _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul] at h'
    exact hfi h'

theorem sylow_comm_projSL_four {K : Type} [Field K] [Finite K] (hK : Nat.card K % 3 = 2) :
    ∀ P : Sylow 3 (projSL 4 K), ∀ a b : projSL 4 K, a ∈ (P : Subgroup (projSL 4 K)) →
      b ∈ (P : Subgroup (projSL 4 K)) → a * b = b * a := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [← CFSG.RankThree.PartOne.projImage_statedSL_eq_projSL 4 K]
  refine comm_sylow_projImage fun P hP a ha b hb => ?_
  have h := comm_of_isPGroup_GL4 hK (P.map (StatedSL 4 K).subtype) (hP.map _) _
    ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  exact Subtype.ext h

theorem sylow_comm_projSU_four (p : ℕ) [Fact p.Prime] (hp : p % 3 = 1) :
    ∀ P : Sylow 3 (projSU 4 p 1), ∀ a b : projSU 4 p 1, a ∈ (P : Subgroup (projSU 4 p 1)) →
      b ∈ (P : Subgroup (projSU 4 p 1)) → a * b = b * a := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [← CFSG.RankThree.PartOne.projImage_statedSU_eq_projSU 4 p 1]
  exact comm_sylow_projImage fun P hP => comm_of_isPGroup_SU4_mod_one hp P hP

end Hering129C

end CFSG.RankThree.PartTwo.Sec12
