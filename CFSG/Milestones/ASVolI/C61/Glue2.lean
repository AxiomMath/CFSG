module

public import CFSG.Milestones.ASVolI.C5

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {H Λ K₁ : Subgroup G}

theorem burnsideC56_glue_exists_x {S X : Subgroup G} (h2 : S.relIndex X = 2) :
    ∃ x ∈ X, x ∉ S := by
  by_contra hcon
  push Not at hcon
  have : S.relIndex X = 1 := Subgroup.relIndex_eq_one.mpr hcon
  omega

theorem burnsideC56_glue_c1 (hC : C61Concl Λ H (Λ ⊓ H) K₁) :
    (Λ ⊓ H).relIndex (Λ ⊓ Subgroup.normalizer ((Λ ⊓ H : Subgroup G) : Set G)) = 2 ∧
      thompsonJ (Λ ⊓ H) = baum (Λ ⊓ H) ∧
      ∀ x ∈ Λ ⊓ Subgroup.normalizer ((Λ ⊓ H : Subgroup G) : Set G), x ∉ Λ ⊓ H →
        (baum (Λ ⊓ H) : Set G) = (pCoreOf 2 H : Set G) * (ChC.rconj x (pCoreOf 2 H) : Set G) := by
  obtain ⟨⟨h2, h1⟩, -⟩ := hC
  obtain ⟨x₀, hx₀, hx₀S⟩ := burnsideC56_glue_exists_x h2
  refine ⟨h2, (h1 x₀ hx₀ hx₀S).1, fun x hx hxS => ?_⟩
  have hb := (h1 x hx hxS).2
  have hle : conjR (pCoreOf 2 H) x ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := by
    have h3 : conjR (pCoreOf 2 H) x ≤ baum (Λ ⊓ H) := by rw [hb]; exact le_sup_right
    exact h3.trans (inf_le_left.trans (inf_le_right.trans
      (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H)))
  rw [hb, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hle]
  rfl

theorem burnsideC56_glue_L_eq (hjoin : conjJoin (Λ ⊓ H) K₁ = oTwoUpper H)
    (hj : conjJoin (Λ ⊓ H) K₁ = K₁) : oTwoUpper H = K₁ := hjoin.symm.trans hj

theorem burnsideC56_glue_blockD (hjoin : conjJoin (Λ ⊓ H) K₁ = oTwoUpper H) :
    blockD (Λ ⊓ H) K₁ = (Λ ⊓ H) ⊓ Subgroup.centralizer (oTwoUpper H : Set G) := by
  unfold blockD
  rw [hjoin]

theorem burnsideC56_glue_c5 (hjoin : conjJoin (Λ ⊓ H) K₁ = oTwoUpper H)
    (hC : C61Concl Λ H (Λ ⊓ H) K₁) :
    (pCoreOf 2 H : Set G) =
      (((Λ ⊓ H) ⊓ Subgroup.centralizer (oTwoUpper H : Set G) : Subgroup G) : Set G) *
        (pCoreOf 2 (oTwoUpper H) : Set G) := by
  obtain ⟨-, -, -, h5, -⟩ := hC
  rw [h5, burnsideC56_glue_blockD hjoin, hjoin]
  have hle : (Λ ⊓ H) ⊓ Subgroup.centralizer (oTwoUpper H : Set G) ≤
      Subgroup.normalizer (pCoreOf 2 (oTwoUpper H) : Set G) :=
    (inf_le_left.trans inf_le_right).trans ((le_normalizer_oTwoUpper H).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) (oTwoUpper H)))
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle]

end CFSG.ASVolI
