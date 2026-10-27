module

public import CFSG.Quasithin.EmptyFaithful.S1422Setting

public section

open scoped MatrixGroups

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7

private theorem s1422_nat_aux' (q : ℕ) (hq : 2 ≤ q) :
    (q ^ 2 - 1) * (q ^ 2 - q) / (q - 1) = q * (q ^ 2 - 1) := by
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : q ≤ q ^ 2 := by nlinarith
  have h3 : (q ^ 2 - 1) * (q ^ 2 - q) = q * (q ^ 2 - 1) * (q - 1) := by
    zify [h1, h2, (by omega : 1 ≤ q)]
    ring
  exact Nat.div_eq_of_eq_mul_left (by omega) h3

theorem card_sl_two_of_fintype (F : Type) [Field F] [Fintype F] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = Fintype.card F * (Fintype.card F ^ 2 - 1) := by
  classical
  have hq : 2 ≤ Fintype.card F := Fintype.one_lt_card
  rw [Matrix.card_SL_field 2]
  simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  exact s1422_nat_aux' _ hq

theorem isLin2Type_card_quot {G : Type*} [Group G] {L : Subgroup G} {n : ℕ}
    (h : IsLin2Type L n) : Nat.card (OTwoQuot L) = 2 ^ n * (4 ^ n - 1) := by
  obtain ⟨F, _, hFin, hF, α, hα, hker, -⟩ := h
  have hker' : α.ker = CFSG.Open.pCore 2 ↥L := hker.trans (CFSG.pCore_eq_open _ _)
  have h1 : Nat.card (↥L ⧸ α.ker) = Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hα).toEquiv
  rw [hker'] at h1
  have h2 : Nat.card (OTwoQuot L) = Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := h1
  rw [h2, card_sl_two_of_fintype F, hF]
  have : (4 : ℕ) ^ n = (2 ^ n) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [this]

theorem isLin2Type_eq_one_of_card_six {G : Type*} [Group G] {L : Subgroup G} {n : ℕ}
    (hn : 1 ≤ n) (h : IsLin2Type L n) (hL : Nat.card (OTwoQuot L) = 6) : n = 1 := by
  by_contra hne
  have := two_pow_mul_four_pow_sub_one_ge n (by omega)
  have := isLin2Type_card_quot h
  omega

theorem isL2Quot_card_le_false {f : ℕ} (hf : 2 ≤ f) {X : Type*} [Group X] (h : IsL2Quot f X)
    (hX : Nat.card X ≤ 20) : False := by
  have := two_pow_mul_four_pow_sub_one_ge f hf
  have := h.card (by omega)
  omega

namespace Setting1422

variable {G : Type} [Group G] [Finite G] {T M Y H : Subgroup G}

theorem card_quot_H_le (hSz : Nat.card ↥(Sz 0) = 20) (S : Setting1422 T M Y H) :
    Nat.card (OTwoQuot H) ≤ 20 := by
  obtain ⟨k, r, hk, hr, hr2, hcard⟩ := S.exists_card_H hSz
  obtain h | h | h := S.small
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card]
    norm_num
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, hSz]
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
    decide

end Setting1422

theorem no_iso_of_trivial_center {G : Type*} [Group G] {K : Subgroup G} {X : Type*} [Group X]
    (hK : ∀ x ∈ K, (∀ y ∈ K, x * y = y * x) → x = 1) (e : ↥K ≃* X) (c : X) (hc1 : c ≠ 1)
    (hc : ∀ y : X, c * y = y * c) : False := by
  apply hc1
  have h1 : (e.symm c : G) = 1 := by
    apply hK _ (e.symm c).2
    intro y hy
    have := hc (e ⟨y, hy⟩)
    have h2 := congrArg e.symm this
    simp only [map_mul, MulEquiv.symm_apply_apply] at h2
    exact congrArg Subtype.val h2
  have h3 : e.symm c = 1 := Subtype.ext h1
  have := congrArg e h3
  simpa using this

end CFSG.Quasithin
