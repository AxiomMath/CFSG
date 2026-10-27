module

public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)

theorem normalizer_le_map_normalizer_of_sylow {Γ : Type} [Group Γ] [Finite Γ] {p : ℕ}
    [Fact p.Prime] (N : Subgroup Γ) [N.Normal] {P₁ : Subgroup Γ} {Pb : Subgroup (Γ ⧸ N)}
    (hPb : P₁.map (QuotientGroup.mk' N) = Pb)
    (hP₁ : IsSylowOf p P₁ (Pb.comap (QuotientGroup.mk' N))) :
    normalizer (Pb : Set (Γ ⧸ N)) ≤ (normalizer (P₁ : Set Γ)).map (QuotientGroup.mk' N) := by
  intro xb hxb
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N xb
  set H₁ : Subgroup Γ := Pb.comap (QuotientGroup.mk' N) with hH₁def
  have hxH₁ : x ∈ normalizer (H₁ : Set Γ) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [hH₁def]
    change QuotientGroup.mk' N y ∈ Pb ↔ QuotientGroup.mk' N (x * y * x⁻¹) ∈ Pb
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hxb) (QuotientGroup.mk' N y)
  have hxH₁map : H₁.map (MulAut.conj x : Γ →* Γ) = H₁ :=
    (Subgroup.mem_normalizer_iff_map_conj_eq (H := H₁)).mp hxH₁
  have hsyl' : IsSylowOf p (P₁.map (MulAut.conj x : Γ →* Γ)) H₁ := by
    refine (CFSG.ABGLocalTools.isSylowOf_iff (p := p)).mpr
      ⟨?_, hP₁.isPGroup.map (MulAut.conj x : Γ →* Γ), ?_⟩
    · rw [← hxH₁map]
      exact Subgroup.map_mono hP₁.le
    · rw [← hxH₁map,
        Subgroup.relIndex_map_map_of_injective P₁ H₁ (MulAut.conj x).injective]
      exact ((CFSG.ABGLocalTools.isSylowOf_iff (p := p)).mp hP₁).2.2
  obtain ⟨k, hk, hconj⟩ := hP₁.exists_mem_conj hsyl'
  have hn : k⁻¹ * x ∈ normalizer (P₁ : Set Γ) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 : x * y * x⁻¹ ∈ P₁.map (MulAut.conj x : Γ →* Γ) ↔ y ∈ P₁ := by
      change (MulAut.conj x : Γ →* Γ) y ∈ P₁.map (MulAut.conj x : Γ →* Γ) ↔ y ∈ P₁
      rw [Subgroup.mem_map_iff_mem (MulAut.conj x).injective]
    rw [← h1, hconj,
      show k⁻¹ * (x * y * x⁻¹) * k = (k⁻¹ * x) * y * (k⁻¹ * x)⁻¹ by group]
  have hkPb : QuotientGroup.mk' N k ∈ Pb := by
    have hk' := hk
    rw [hH₁def] at hk'
    exact hk'
  have hk_mem : QuotientGroup.mk' N k ∈
      (normalizer (P₁ : Set Γ)).map (QuotientGroup.mk' N) := by
    rw [← hPb] at hkPb
    obtain ⟨q, hq, hqk⟩ := Subgroup.mem_map.mp hkPb
    rw [← hqk]
    exact Subgroup.mem_map_of_mem _ (Subgroup.le_normalizer hq)
  have hn_mem : QuotientGroup.mk' N (k⁻¹ * x) ∈
      (normalizer (P₁ : Set Γ)).map (QuotientGroup.mk' N) :=
    Subgroup.mem_map_of_mem _ hn
  have hdecomp : QuotientGroup.mk' N x =
      QuotientGroup.mk' N k * QuotientGroup.mk' N (k⁻¹ * x) := by
    rw [← map_mul, show k * (k⁻¹ * x) = x by group]
  rw [hdecomp]
  exact ((normalizer (P₁ : Set Γ)).map (QuotientGroup.mk' N)).mul_mem hk_mem hn_mem

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
