module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
import CFSG.GroupTheory.SylowComap

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6S846

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise

theorem exists_isSylowOf_le_normalizer_of_rhoL {G : Type} [Group G] [Finite G]
    {J B : Subgroup G} (hBN : B ≤ Subgroup.normalizer (J : Set G)) (ω : Sylow 2 (UC22.Bar2 J))
    (hω : ∀ b : ↥B, rhoL J (Subgroup.inclusion hBN b) • ω = ω) :
    ∃ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 S J ∧
      B ≤ Subgroup.normalizer (S : Set G) := by
  classical
  let π : ↥J →* UC22.Bar2 J := QuotientGroup.mk' (CFSG.pCore 2 ↥J)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : IsPGroup 2 π.ker := by
    rw [show π.ker = CFSG.pCore 2 ↥J from QuotientGroup.ker_mk' _]
    exact CFSG.pCore_isPGroup
  let U : Sylow 2 ↥J := CFSG.sylowComapOfKerIsPGroup π hπ hker ω
  have hU : (U : Subgroup ↥J) = (ω : Subgroup (UC22.Bar2 J)).comap π :=
    CFSG.coe_sylowComapOfKerIsPGroup π hπ hker ω
  refine ⟨(U : Subgroup ↥J).map J.subtype, ⟨U, rfl⟩, ?_⟩
  have hfix : ∀ (b : ↥B) (y : UC22.Bar2 J),
      rhoL J (Subgroup.inclusion hBN b) • y ∈ (ω : Subgroup (UC22.Bar2 J)) ↔ y ∈ ω := by
    intro b y
    have hb : (rhoL J (Subgroup.inclusion hBN b)) • (ω : Subgroup (UC22.Bar2 J)) =
        (ω : Subgroup (UC22.Bar2 J)) := by
      simpa [Sylow.pointwise_smul_def] using
        congrArg (fun S : Sylow 2 (UC22.Bar2 J) => (S : Subgroup (UC22.Bar2 J))) (hω b)
    rw [← hb, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp only [MulAut.smul_def, MulAut.inv_apply_self]
    rfl
  have hmem : ∀ (b : ↥B) (j : ↥J), j ∈ (U : Subgroup ↥J) ↔
      Subgroup.normalizerMonoidHom J (Subgroup.inclusion hBN b) j ∈ (U : Subgroup ↥J) := by
    intro b j
    rw [hU, Subgroup.mem_comap, Subgroup.mem_comap]
    have hcoe : π (Subgroup.normalizerMonoidHom J (Subgroup.inclusion hBN b) j) =
        rhoL J (Subgroup.inclusion hBN b) (π j) := by
      show QuotientGroup.mk (Subgroup.normalizerMonoidHom J (Subgroup.inclusion hBN b) j) =
        rhoL J (Subgroup.inclusion hBN b) (QuotientGroup.mk j)
      rw [rhoL_mk]
    rw [hcoe]
    exact (hfix b (π j)).symm
  have hconj : ∀ b ∈ B, ∀ s ∈ (U : Subgroup ↥J).map J.subtype,
      b * s * b⁻¹ ∈ (U : Subgroup ↥J).map J.subtype := by
    rintro b hb _ ⟨j, hj, rfl⟩
    refine ⟨Subgroup.normalizerMonoidHom J (Subgroup.inclusion hBN ⟨b, hb⟩) j,
      (hmem ⟨b, hb⟩ j).1 hj, ?_⟩
    show ((Subgroup.normalizerMonoidHom J (Subgroup.inclusion hBN ⟨b, hb⟩) j : ↥J) : G) =
      b * (j : G) * b⁻¹
    rw [rhoL_mk_coe]
    simp
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact hconj b hb x hx
  · intro hx
    have h := hconj b⁻¹ (B.inv_mem hb) (b * x * b⁻¹) hx
    simpa [mul_assoc] using h

end CFSG.LocalAnalysis.UniquenessCase.UC6S846
