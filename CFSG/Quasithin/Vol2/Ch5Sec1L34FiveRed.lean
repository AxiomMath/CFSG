module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveDefs
public import CFSG.Quasithin.H13.NQCatT513PSL2

public section

namespace CFSG.Quasithin.H13.FiveNorm

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.NQCat.T513
open scoped Pointwise

section Red

variable {Y : Type} [Group Y] [Finite Y] {L T D : Subgroup Y}
variable {P : Type} [Group P] (e : ↥L ⧸ Subgroup.center ↥L ≃* P)

theorem isSylowTwoOf_pImg (hT : IsSylowTwoOf T ⊤) (hTN : T ≤ Subgroup.normalizer (L : Set Y)) :
    IsSylowTwoOf (pImg L e (T ⊓ L)) ⊤ := by
  have h1 : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal (A4.isSylowTwoOf_mono hT le_sup_right le_top) le_sup_left
      (sup_le Subgroup.le_normalizer hTN)
  exact isSylowTwoOf_top_map_of_surjective (CFSG.Quasithin.isSylowTwoOf_top_subgroupOf h1) _
    (toP_surjective L e)

theorem eq_one_or_card_iPart (hcen : Subgroup.center P = ⊥) (hinn : FiveInner P)
    (hD : Nat.card D = 5) (hDN : D ≤ Subgroup.normalizer (L : Set Y)) :
    (∀ (d : Y) (hd : d ∈ D), autOf L e ⟨d, hDN hd⟩ = 1) ∨
      ((∀ α ∈ aImg L e D, ∃ x, α = MulAut.conj x) ∧ Nat.card (iPart L e D) = 5) := by
  have h1 : Nat.card (aImg L e D) ∣ 5 := by
    rw [← hD]
    exact card_aImg_dvd L e hDN
  have hinn' : ∀ α ∈ aImg L e D, ∃ x, α = MulAut.conj x := fun α hα =>
    hinn α (orderOf_dvd_iff_pow_eq_one.mp ((Subgroup.orderOf_dvd_natCard _ hα).trans h1))
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp h1 with h | h
  · left
    intro d hd
    have hmem := autOf_mem_aImg L e (hDN hd) hd
    rwa [Subgroup.eq_bot_of_card_eq _ h, Subgroup.mem_bot] at hmem
  · refine Or.inr ⟨hinn', ?_⟩
    have hle : aImg L e D ≤ (MulAut.conj : P →* MulAut P).range := fun α hα => by
      obtain ⟨x, hx⟩ := hinn' α hα
      exact ⟨x, hx.symm⟩
    rw [← h, ← Subgroup.map_comap_eq_self hle,
      Subgroup.card_map_of_injective (conj_injective_of_center hcen)]
    rfl

theorem le_normalizer_of_iPart_le {B : Subgroup Y} (hBL : B ≤ L) (hB : ⁅B, B⁆ = B)
    (hDN : D ≤ Subgroup.normalizer (L : Set Y))
    (hinn : ∀ α ∈ aImg L e D, ∃ x, α = MulAut.conj x)
    (hle : iPart L e D ≤ Subgroup.normalizer (pImg L e B : Set P)) :
    D ≤ Subgroup.normalizer (B : Set Y) := by
  refine le_normalizer_of_pImg L e hBL hB hDN fun d hd y hy => ?_
  obtain ⟨x, hx⟩ := hinn _ (autOf_mem_aImg L e (hDN hd) hd)
  have hxD : x ∈ iPart L e D := by
    show MulAut.conj x ∈ aImg L e D
    rw [← hx]
    exact autOf_mem_aImg L e _ hd
  rw [hx, MulAut.conj_apply]
  exact (Subgroup.mem_normalizer_iff.mp (hle hxD) y).mp hy

include e in
theorem le_normalizer_of_fiveRigid (hP : FiveRigid P) (hT : IsSylowTwoOf T ⊤)
    (hTN : T ≤ Subgroup.normalizer (L : Set Y)) (hD : Nat.card D = 5)
    (hDN : D ≤ Subgroup.normalizer (L : Set Y))
    (hDT : (D : Set Y) * (T : Set Y) = (T : Set Y) * (D : Set Y)) {B : Subgroup Y} (hBL : B ≤ L)
    (hB : ⁅B, B⁆ = B) : D ≤ Subgroup.normalizer (B : Set Y) := by
  obtain ⟨hcen, hinn, hno⟩ := hP
  have : Finite P := Finite.of_surjective (toP L e) (toP_surjective L e)
  rcases eq_one_or_card_iPart e hcen hinn hD hDN with h1 | ⟨hinn', h5⟩
  · exact le_normalizer_of_pImg L e hBL hB hDN fun d hd y hy => by
      rw [h1 d hd, MulAut.one_apply]
      exact hy
  · exfalso
    have hsyl := isSylowTwoOf_pImg e hT hTN
    have hmax : ∀ X : Subgroup P, IsPGroup 2 X → pImg L e (T ⊓ L) ≤ X →
        X = pImg L e (T ⊓ L) := fun X hX hle =>
      le_antisymm ((A4.isSylowTwoOf_iff_maximal.mp hsyl).2.2 X le_top hX hle) hle
    have hperm := inner_perm L e hTN hDN hDT hT.2.1 hinn' (conj_injective_of_center hcen) hmax
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hsyl.2.1
    have hcop : Nat.Coprime (Nat.card (iPart L e D)) (Nat.card (pImg L e (T ⊓ L))) := by
      rw [h5, hk]
      exact Nat.Coprime.pow_right _ (by norm_num)
    have hcard := card_sup_of_perm hperm hcop
    rw [h5] at hcard
    exact hno _ _ hsyl le_sup_right hcard

omit [Finite Y] in
theorem toP_commute_iPart (hcen : Subgroup.center P = ⊥) {b : Y} (hbL : b ∈ L)
    (hbD : ∀ d ∈ D, d * b = b * d) {x : P} (hx : x ∈ iPart L e D) :
    x * toP L e ⟨b, hbL⟩ = toP L e ⟨b, hbL⟩ * x := by
  obtain ⟨d, hdN, hdD, hd⟩ := (mem_aImg L e).1 (show MulAut.conj x ∈ aImg L e D from hx)
  apply conj_injective_of_center hcen
  rw [map_mul, map_mul, ← autOf_of_mem L e hbL, ← hd, ← map_mul (autOf L e),
    ← map_mul (autOf L e)]
  congr 1
  exact Subtype.ext (hbD d hdD)

omit [Finite Y] in
theorem toP_mem_normalizer_pImg {X : Subgroup Y} (hXL : X ≤ L) {b : Y} (hbL : b ∈ L)
    (hbX : b ∈ Subgroup.normalizer (X : Set Y)) :
    toP L e ⟨b, hbL⟩ ∈ Subgroup.normalizer (pImg L e X : Set P) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    obtain ⟨x, hxL, hxX, rfl⟩ := (mem_pImg L e).1 hy
    have h1 : b * x * b⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hbX x).mp hxX
    refine (mem_pImg L e).2 ⟨b * x * b⁻¹, hXL h1, h1, ?_⟩
    rw [← map_inv (toP L e), ← map_mul (toP L e), ← map_mul (toP L e)]
    rfl
  · intro hy
    obtain ⟨x, hxL, hxX, hx⟩ := (mem_pImg L e).1 hy
    have h1 : b⁻¹ * x * b ∈ X := by
      apply (Subgroup.mem_normalizer_iff.mp hbX _).mpr
      rw [show b * (b⁻¹ * x * b) * b⁻¹ = x by group]
      exact hxX
    refine (mem_pImg L e).2 ⟨b⁻¹ * x * b, hXL h1, h1, ?_⟩
    have h2 : y = (toP L e ⟨b, hbL⟩)⁻¹ * toP L e ⟨x, hxL⟩ * toP L e ⟨b, hbL⟩ := by
      rw [hx]
      group
    rw [h2, ← map_inv (toP L e), ← map_mul (toP L e), ← map_mul (toP L e)]
    rfl

end Red

end CFSG.Quasithin.H13.FiveNorm
