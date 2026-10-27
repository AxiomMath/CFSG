module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102KTypesDefs
public import CFSG.RankThree.PartTwo.Sec21.KS21U4Transport
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102KTypesMap

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KTypes

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartTwo.Sec21.U4Lines (mapL mapL_le mapL_mono mapLEquiv card_mapL
  mapL_inj)

variable {G G' : Type} [Group G] [Group G'] [Finite G] [Finite G'] {L : Subgroup G}
  {L' : Subgroup G'}

omit [Finite G'] in
private theorem relIndex_mapL (E : L ≃* L') {S : Subgroup G} (hS : S ≤ L) :
    (mapL E S).relIndex L' = S.relIndex L := by
  have h1 := Subgroup.relIndex_mul_card (H := mapL E S) (K := L')
  rw [inf_eq_left.mpr (mapL_le E S), card_mapL E hS,
    ← Nat.card_congr E.toEquiv] at h1
  have h2 := Subgroup.relIndex_mul_card (H := S) (K := L)
  rw [inf_eq_left.mpr hS] at h2
  exact Nat.mul_right_cancel (Nat.card_pos (α := S)) (h1.trans h2.symm)

private theorem exists_notationA_of_mapL (E : L ≃* L') {S : Subgroup G} {p n : ℕ}
    (h : ∃ A' : Subgroup G', F08.NotationA8103 L' (mapL E S) p n A') :
    ∃ A : Subgroup G, F08.NotationA8103 L S p n A := by
  obtain ⟨A', hA'⟩ := h
  have hA'L' : A' ≤ L' := hA'.2.1.trans (mapL_le E S)
  have hA : mapL E.symm A' ≤ L := mapL_le E.symm A'
  have hmap : mapL E (mapL E.symm A') = A' := mapL_mapL_symm E hA'L'
  exact ⟨mapL E.symm A', (notationA8103_mapL_iff E hA).mp (by rwa [hmap])⟩

private theorem exists_notationB_of_mapL (E : L ≃* L') {S : Subgroup G} {n : ℕ}
    (h : ∃ B' : Subgroup G', F08.NotationB8103 L' (mapL E S) n B') :
    ∃ B : Subgroup G, F08.NotationB8103 L S n B := by
  obtain ⟨B', hB'⟩ := h
  have hB'L' : B' ≤ L' := hB'.2.1.trans (mapL_le E S)
  have hB : mapL E.symm B' ≤ L := mapL_le E.symm B'
  have hmap : mapL E (mapL E.symm B') = B' := mapL_mapL_symm E hB'L'
  exact ⟨mapL E.symm B', (notationB8103_mapL_iff E hB).mp (by rwa [hmap])⟩

private theorem notation8103_of_mapL (E : L ≃* L') {S Y : Subgroup G} (hS : S ≤ L)
    (hY : Y ≤ S) {p n : ℕ}
    (h : F08.NotationA8103 L' (mapL E S) p n (mapL E Y) ∨
      F08.NotationB8103 L' (mapL E S) n (mapL E Y)) :
    F08.NotationA8103 L S p n Y ∨ F08.NotationB8103 L S n Y := by
  have hYL : Y ≤ L := hY.trans hS
  rcases h with h | h
  · exact Or.inl ((notationA8103_mapL_iff E hYL).mp h)
  · exact Or.inr ((notationB8103_mapL_iff E hYL).mp h)

private theorem dvd_card_bar2_of_mapL (E : L ≃* L') {A : Subgroup G} (hA : A ≤ L) {p : ℕ}
    (h : p ∣ Nat.card (Bar2 (F08.DerInf8 (L' ⊓ centralizer (mapL E A : Set G'))))) :
    p ∣ Nat.card (Bar2 (F08.DerInf8 (L ⊓ centralizer (A : Set G)))) := by
  obtain ⟨e⟩ := nonempty_bar2_derInf8_mapL E hA
  rwa [← Nat.card_congr e.toEquiv] at h

omit [Finite G] [Finite G'] in
private theorem conj_of_mapL (E : L ≃* L') {S B₁ B₂ : Subgroup G} {n : ℕ} (hS : S ≤ L)
    (hB₁ : F08.NotationB8103 L S n B₁) (hB₂ : F08.NotationB8103 L S n B₂)
    (h : ∃ x' ∈ L', mapL E B₂ = (mapL E B₁).map (MulAut.conj x').toMonoidHom) :
    ∃ x ∈ L, B₂ = B₁.map (MulAut.conj x).toMonoidHom := by
  obtain ⟨x', hx'L', hx'⟩ := h
  have hB₁L : B₁ ≤ L := hB₁.2.1.trans hS
  have hB₂L : B₂ ≤ L := hB₂.2.1.trans hS
  let x : L := E.symm ⟨x', hx'L'⟩
  have hxL : (x : G) ∈ L := x.2
  have hxE : ((E x : L') : G') = x' := by simp [x]
  have hmap : mapL E (B₁.map (MulAut.conj (x : G)).toMonoidHom) = mapL E B₂ := by
    rw [mapL_map_conj E hB₁L x, hxE, ← hx']
  have hB₁mapL : B₁.map (MulAut.conj (x : G)).toMonoidHom ≤ L := by
    rintro _ ⟨b, hb, rfl⟩
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using
      mul_mem (mul_mem hxL (hB₁L hb)) (inv_mem hxL)
  exact ⟨(x : G), hxL, (mapL_inj E hB₁mapL hB₂L hmap).symm⟩

theorem KTypesAt.of_mapL (E : L ≃* L') {p n : ℕ} (h : KTypesAt G' L' p n) :
    KTypesAt G L p n := by
  intro S hSL hS3 hSidx
  have hS'L' : mapL E S ≤ L' := mapL_le E S
  have hS'3 : IsPGroup 3 (mapL E S) := hS3.of_equiv (mapLEquiv E hSL)
  have hidx : (mapL E S).relIndex L' = S.relIndex L := relIndex_mapL E hSL
  obtain ⟨hA, hB, hc, hd, he⟩ := h (mapL E S) hS'L' hS'3 (by rwa [hidx])
  refine ⟨exists_notationA_of_mapL E hA, exists_notationB_of_mapL E hB, ?_, ?_, ?_⟩
  · intro Y hYS hY3
    have hYcard : Nat.card (mapL E Y) = 3 := by
      rw [card_mapL E (hYS.trans hSL), hY3]
    exact notation8103_of_mapL E hSL hYS (hc (mapL E Y) (mapL_mono E hYS) hYcard)
  · intro A hA'
    have hAL : A ≤ L := hA'.2.1.trans hSL
    have hA'map : F08.NotationA8103 L' (mapL E S) p n (mapL E A) :=
      (notationA8103_mapL_iff E hAL).mpr hA'
    exact dvd_card_bar2_of_mapL E hAL (hd (mapL E A) hA'map)
  · intro B₁ B₂ hB₁ hB₂
    have hB₁L : B₁ ≤ L := hB₁.2.1.trans hSL
    have hB₂L : B₂ ≤ L := hB₂.2.1.trans hSL
    have hB₁' : F08.NotationB8103 L' (mapL E S) n (mapL E B₁) :=
      (notationB8103_mapL_iff E hB₁L).mpr hB₁
    have hB₂' : F08.NotationB8103 L' (mapL E S) n (mapL E B₂) :=
      (notationB8103_mapL_iff E hB₂L).mpr hB₂
    exact conj_of_mapL E hSL hB₁ hB₂ (he (mapL E B₁) (mapL E B₂) hB₁' hB₂')

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KTypes
