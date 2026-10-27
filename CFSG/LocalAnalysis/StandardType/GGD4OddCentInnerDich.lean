module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentInnerLeafDefs
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentInnerOne

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType.Triality

namespace D4Inner

local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

theorem ggD4InnerTwoDichInput_of_leaves
    (hD1 : ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ), Nat.card K = 2 ^ n → Odd n →
      3 ≤ n → ∀ (s : Om8 K), s ^ 3 = 1 → D4Rank.omFixDim s = 2 → ∀ (J : Subgroup (Om8 K)),
      IsComponentOf J (ggAutFixedSubgroup (MulAut.conj s)) →
      ∀ (A : Subgroup (MulAut (Om8 K))), (∀ a ∈ A, ∀ j ∈ J, a j ∈ J) →
        GGMarkingAll (K := ↥J) fun lab _ _ I _ θ =>
          (GGLabelA2 lab ∧ lab.tag = .twA) → GGAutsInduceOn A J θ I → InnDiagOn A s J)
    (hD23 : ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ), Nat.card K = 2 ^ n →
      Odd n → 3 ≤ n → ∀ (A : Subgroup (MulAut (Om8 K))) (s : Om8 K) (J : Subgroup (Om8 K)),
      GGKLocal A (MulAut.conj s) J → Nat.card A = 3 ^ 3 → D4Rank.omFixDim s = 2 →
      InnDiagOn A s J → GGAutsFixedInCenter A J ∨ ToralOn A s J)
    (hD6 : ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ), Nat.card K = 2 ^ n →
      Odd n → 3 ≤ n → ∀ (A : Subgroup (MulAut (Om8 K))) (s : Om8 K) (J : Subgroup (Om8 K)),
      GGKLocal A (MulAut.conj s) J → Nat.card A = 3 ^ 3 → D4Rank.omFixDim s = 2 →
      (∀ a ∈ A, a ∈ Inn (Om8 K) ⊔ (AutOm.fieldAutP 4).range → a ∈ Inn (Om8 K)) →
      (∃ a ∈ A, a ∉ Inn (Om8 K) ⊔ (AutOm.fieldAutP 4).range) → ToralOn A s J → False) :
    GGD4InnerTwoDichInput := by
  intro K _ _ _ n hK hn A s J hloc hA hd hdat hout
  have hs3 : s ^ 3 = 1 := NbrGraphD4.conj_injective (by
    rw [map_pow, hloc.1.1.2 _ hloc.1.2.1, map_one])
  rcases (show n = 1 ∨ 3 ≤ n by obtain ⟨m, rfl⟩ := hn; omega) with rfl | hn3
  · exact absurd hloc.1.2.2.2.1
      (ggD4InnerOneInput_holds K (by rw [hK, pow_one]) s hs3 (Or.inl hd) J)
  · refine ggMarkingAll_mono (fun lab R _ I F θ h hlab => ?_)
      (hD1 K n hK hn hn3 s hs3 hd J hloc.1.2.2.2.1 A hloc.1.2.2.2.2)
    by_cases hind : GGAutsInduceOn A J θ I
    · rcases hD23 K n hK hn hn3 A s J hloc hA hd (h hlab hind) with hfix | htor
      · exact Or.inl hfix
      · exact (hD6 K n hK hn hn3 A s J hloc hA hd hdat hout htor).elim
    · exact Or.inr hind

end D4Inner

end CFSG.StandardType

end
