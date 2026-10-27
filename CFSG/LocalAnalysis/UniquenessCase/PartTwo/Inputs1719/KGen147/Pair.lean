module

public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGen

open Subgroup CFSG.Open

variable {G G' : Type*} [Group G] [Group G']

@[expose] def IsKGenPair (B R : Subgroup G) : Prop :=
  Nat.card B = 3 ∧ IsElemAbelian 7 R ∧ Nat.card R = 49 ∧ B ≤ normalizer (R : Set G) ∧
    R ⊓ centralizer (B : Set G) = ⊥

@[expose] def KGenSpans (B R : Subgroup G) : Prop :=
  ∀ H : Subgroup G, normalizer (B : Set G) ≤ H →
    (∀ Y : Subgroup G, R ≤ Y → IsPGroup 7 Y → normalizer (Y : Set G) ≤ H) → H = ⊤

theorem IsKGenPair.map {B R : Subgroup G} (h : IsKGenPair B R) (e : G ≃* G') :
    IsKGenPair (B.map e.toMonoidHom) (R.map e.toMonoidHom) := by
  obtain ⟨hB, hR, hR49, hBR, hRB⟩ := h
  refine ⟨?_, hR.map e.toMonoidHom, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective e.injective, hB]
  · rw [Subgroup.card_map_of_injective e.injective, hR49]
  · rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hBR
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxR, hxC⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hxR
    have hrC : r ∈ centralizer (B : Set G) := by
      rw [Subgroup.mem_centralizer_iff] at hxC ⊢
      intro b hb
      apply e.injective
      simpa using hxC (e b) ⟨b, hb, rfl⟩
    have hr1 : r ∈ R ⊓ centralizer (B : Set G) := ⟨hr, hrC⟩
    rw [hRB, Subgroup.mem_bot] at hr1
    simp [hr1]

theorem KGenSpans.of_map {B R : Subgroup G} (e : G ≃* G')
    (h : KGenSpans (B.map e.toMonoidHom) (R.map e.toMonoidHom)) : KGenSpans B R := by
  intro H hBH hYH
  have hmap : H.map e.toMonoidHom = ⊤ := by
    refine h _ ?_ ?_
    · rw [← Subgroup.map_equiv_normalizer_eq]
      exact Subgroup.map_mono hBH
    · intro Y' hRY' hY'
      have hY : IsPGroup 7 (Y'.comap e.toMonoidHom) := hY'.comap_of_injective _ e.injective
      have hRY : R ≤ Y'.comap e.toMonoidHom := Subgroup.map_le_iff_le_comap.mp hRY'
      have hYY : (Y'.comap e.toMonoidHom).map e.toMonoidHom = Y' :=
        Subgroup.map_comap_eq_self_of_surjective e.surjective Y'
      rw [← hYY, ← Subgroup.map_equiv_normalizer_eq]
      exact Subgroup.map_mono (hYH _ hRY hY)
  rw [eq_top_iff]
  intro x _
  have hx : e x ∈ H.map e.toMonoidHom := hmap ▸ Subgroup.mem_top (e x)
  obtain ⟨y, hy, hyx⟩ := hx
  have hyx' : y = x := e.injective (by simpa using hyx)
  exact hyx' ▸ hy

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGen
