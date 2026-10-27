module

public import CFSG.RankThree.PartTwo.KFacts.K412Conjugacy

public section

namespace CFSG.RankThree.PartTwo.KFacts.K412

open Equiv Subgroup CFSG.RankThree.PartTwo.KFacts.KP2

abbrev swSix (a b : Fin 6) : Perm (Fin 6) := swap a b

@[expose] def fOne : Perm (Fin 6) := swSix 0 1 * swSix 1 2

@[expose] def fTwo : Perm (Fin 6) := swSix 3 4 * swSix 4 5

@[expose] def sixF (i j : Fin 3) : Perm (Fin 6) := fOne ^ (i : ℕ) * fTwo ^ (j : ℕ)

theorem sixF_mul : ∀ i j k l : Fin 3, ∃ m n : Fin 3, sixF i j * sixF k l = sixF m n := by
  decide +kernel

theorem sixF_inv : ∀ i j : Fin 3, ∃ m n : Fin 3, (sixF i j)⁻¹ = sixF m n := by
  decide +kernel

@[expose] def eSix : Subgroup (Perm (Fin 6)) where
  carrier := {x | ∃ i j, x = sixF i j}
  mul_mem' := by
    rintro _ _ ⟨i, j, rfl⟩ ⟨k, l, rfl⟩
    exact sixF_mul i j k l
  one_mem' := ⟨0, 0, by decide +kernel⟩
  inv_mem' := by
    rintro _ ⟨i, j, rfl⟩
    exact sixF_inv i j

theorem sixF_comm : ∀ i j k l : Fin 3, sixF i j * sixF k l = sixF k l * sixF i j := by
  decide +kernel

theorem sixF_pow_three : ∀ i j : Fin 3, sixF i j ^ 3 = 1 := by
  decide +kernel

theorem sixF_injective : ∀ p q : Fin 3 × Fin 3, sixF p.1 p.2 = sixF q.1 q.2 → p = q := by
  decide +kernel

theorem sixF_sign : ∀ i j : Fin 3, Perm.sign (sixF i j) = 1 := by
  decide +kernel

theorem sixF_zero : sixF 0 0 = 1 := by
  decide +kernel

theorem card_eSix : Nat.card eSix = 9 := by
  have : (eSix : Set (Perm (Fin 6))) = Set.range (fun p : Fin 3 × Fin 3 => sixF p.1 p.2) := by
    ext x
    exact ⟨fun ⟨i, j, h⟩ => ⟨(i, j), h.symm⟩, fun ⟨p, h⟩ => ⟨p.1, p.2, h.symm⟩⟩
  rw [← SetLike.coe_sort_coe, this,
    Nat.card_range_of_injective (fun p q h => sixF_injective p q h)]
  simp

theorem eSix_le_alternatingGroup : eSix ≤ alternatingGroup (Fin 6) := by
  rintro _ ⟨i, j, rfl⟩
  exact sixF_sign i j

instance : CFSG.IsElementaryAbelian 3 eSix where
  is_comm := ⟨fun ⟨x, hx⟩ ⟨y, hy⟩ => by
    obtain ⟨i, j, rfl⟩ := hx
    obtain ⟨k, l, rfl⟩ := hy
    exact Subtype.ext (sixF_comm i j k l)⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun ⟨x, hx⟩ => by
    obtain ⟨i, j, rfl⟩ := hx
    exact Subtype.ext (sixF_pow_three i j)

theorem card_filter_six : ∀ i j : Fin 3, (i, j) ≠ (0, 0) →
    (Finset.univ.filter (fun x : Perm (Fin 6) => x * sixF i j = sixF i j * x ∧
      ¬ (x ^ 6 = 1 ∧ (x ^ 2 = 1 → x = 1 ∨
        ((x * (fOne * x * fOne⁻¹)) ^ 3 = 1 ∧ x * (fOne * x * fOne⁻¹) ≠ 1) ∨
        ((x * (fTwo * x * fTwo⁻¹)) ^ 3 = 1 ∧ x * (fTwo * x * fTwo⁻¹) ≠ 1))))).card = 0 := by
  decide +kernel

theorem fOne_mem_eSix : fOne ∈ eSix := ⟨1, 0, by decide +kernel⟩

theorem fTwo_mem_eSix : fTwo ∈ eSix := ⟨0, 1, by decide +kernel⟩

theorem eq_bot_of_le_normalizer {Q : Subgroup (Perm (Fin 6))} (h3 : ¬ 3 ∣ Nat.card Q)
    (hE : eSix ≤ normalizer (Q : Set (Perm (Fin 6)))) : Q = ⊥ := by
  refine eq_bot_iff.2 (le_of_forall_commute (A := eSix) (W := ⊥) (by rw [card_eSix]) h3 hE ?_)
  rintro _ ⟨i, j, rfl⟩ ha x hxQ hxa
  have hij : (i, j) ≠ (0, 0) := by
    rintro h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact ha sixF_zero
  have hnot : ¬ ¬ (x ^ 6 = 1 ∧ (x ^ 2 = 1 → x = 1 ∨
        ((x * (fOne * x * fOne⁻¹)) ^ 3 = 1 ∧ x * (fOne * x * fOne⁻¹) ≠ 1) ∨
        ((x * (fTwo * x * fTwo⁻¹)) ^ 3 = 1 ∧ x * (fTwo * x * fTwo⁻¹) ≠ 1))) := fun h =>
    Finset.filter_eq_empty_iff.1 (Finset.card_eq_zero.1 (card_filter_six i j hij))
      (Finset.mem_univ x) ⟨hxa, h⟩
  obtain ⟨h6, h2⟩ := not_not.1 hnot
  have hx2 : x ^ 2 = 1 := by
    by_contra hne
    exact h3 ((three_dvd_orderOf_of_pow (m := 2) h6 hne).trans
      (Subgroup.orderOf_dvd_natCard Q hxQ))
  have hconj : ∀ b ∈ eSix, b * x * b⁻¹ ∈ Q := fun b hb => (mem_normalizer_iff.1 (hE hb) x).1 hxQ
  rw [mem_bot]
  rcases h2 hx2 with h | ⟨hy3, hy1⟩ | ⟨hy3, hy1⟩
  · exact h
  · exfalso
    have hy := mul_mem hxQ (hconj fOne fOne_mem_eSix)
    have : orderOf (x * (fOne * x * fOne⁻¹)) = 3 := orderOf_eq_prime hy3 hy1
    exact h3 (this ▸ Subgroup.orderOf_dvd_natCard Q hy)
  · exfalso
    have hy := mul_mem hxQ (hconj fTwo fTwo_mem_eSix)
    have : orderOf (x * (fTwo * x * fTwo⁻¹)) = 3 := orderOf_eq_prime hy3 hy1
    exact h3 (this ▸ Subgroup.orderOf_dvd_natCard Q hy)

theorem card_perm_six : Nat.card (Perm (Fin 6)) = 720 := by
  rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem not_three_dvd_index_six {E : Subgroup (Perm (Fin 6))} (h9 : Nat.card E = 9) :
    ¬ 3 ∣ E.index := by
  have h := E.card_mul_index
  rw [h9, card_perm_six] at h
  omega

theorem exists_conj_eq_eSix {E : Subgroup (Perm (Fin 6))} (h9 : Nat.card E = 9) :
    ∃ g : Perm (Fin 6), E.map (MulAut.conj g).toMonoidHom = eSix := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE : IsPGroup 3 E := IsPGroup.of_card (n := 2) (by rw [h9]; norm_num)
  have hE0 : IsPGroup 3 eSix := IsPGroup.of_card (n := 2) (by rw [card_eSix]; norm_num)
  obtain ⟨g, hg⟩ := exists_conj_le_sylow hE (hE0.toSylow (not_three_dvd_index_six card_eSix))
  refine ⟨g, Subgroup.eq_of_le_of_card_ge hg ?_⟩
  rw [card_map_conj, h9, card_eSix]

end CFSG.RankThree.PartTwo.KFacts.K412
