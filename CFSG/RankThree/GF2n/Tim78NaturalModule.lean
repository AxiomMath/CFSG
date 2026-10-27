module

public import CFSG.RankThree.GF2n.Basic
import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.RankThree.GF2n
open scoped Matrix

theorem card_SL_two_galoisField {n : ℕ} (hn : n ≠ 0) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  let := Fintype.ofFinite (GaloisField 2 n)
  have hK : Fintype.card (GaloisField 2 n) = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 n hn]
  have h1 : 1 < 2 ^ n := Nat.one_lt_two_pow hn
  rw [Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one, hK,
    show (2 ^ n) ^ 2 - 2 ^ n = 2 ^ n * (2 ^ n - 1) by rw [Nat.mul_sub_one, sq], ← mul_assoc,
    Nat.mul_div_cancel _ (by omega), mul_comm]

variable {G : Type*} [Group G]

theorem exists_compl_of_isElemAbelian [Finite G] {E U : Subgroup G}
    (hE : Assembly.IsElemAbelian 2 E) (hUE : U ≤ E) :
    ∃ C : Subgroup G, C ≤ E ∧ C ⊓ U = ⊥ ∧ C ⊔ U = E := by
  classical
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have : Finite (Subgroup G) :=
    Finite.of_injective (SetLike.coe : Subgroup G → Set G) SetLike.coe_injective
  let _ : Fintype (Subgroup G) := Fintype.ofFinite _
  obtain ⟨C, hC, hmax⟩ := Finset.exists_max_image
    (Finset.univ.filter fun C : Subgroup G => C ≤ E ∧ C ⊓ U = ⊥)
    (fun C : Subgroup G => Nat.card C) ⟨⊥, by simp⟩
  obtain ⟨hCE, hCU⟩ := (Finset.mem_filter.mp hC).2
  refine ⟨C, hCE, hCU, ?_⟩
  by_contra hne
  obtain ⟨e, heE, heCU⟩ : ∃ e ∈ E, e ∉ C ⊔ U := by
    by_contra h
    push Not at h
    exact hne (le_antisymm (sup_le hCE hUE) h)
  have he2 : e ^ 2 = 1 := hE.2 e heE
  have hZE : Subgroup.zpowers e ≤ E := Subgroup.zpowers_le.mpr heE
  have hN : Subgroup.zpowers e ≤ Subgroup.normalizer (C : Set G) :=
    le_normalizer_of_comm fun a ha b hb => hcomm a (hZE ha) b (hCE hb)
  have hC'E : C ⊔ Subgroup.zpowers e ≤ E := sup_le hCE hZE
  have hC'U : (C ⊔ Subgroup.zpowers e) ⊓ U = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    obtain ⟨c, hc, b, hb, rfl⟩ := exists_mul_of_mem_sup hN hx1
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hsq : e ^ (2 : ℤ) = 1 := by rw [zpow_two, ← sq, he2]
    rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
    · rw [zpow_mul, hsq, one_zpow, mul_one] at hx2 ⊢
      have : c ∈ C ⊓ U := ⟨hc, hx2⟩
      rw [hCU] at this
      exact this
    · exfalso
      rw [zpow_add_one, zpow_mul, hsq, one_zpow, one_mul] at hx2
      apply heCU
      have : e = c⁻¹ * (c * e) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_left hc))
        (Subgroup.mem_sup_right hx2)
  have hcard : Nat.card (C ⊔ Subgroup.zpowers e : Subgroup G) ≤ Nat.card C :=
    hmax _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hC'E, hC'U⟩)
  have hEq : C = C ⊔ Subgroup.zpowers e := Subgroup.eq_of_le_of_card_ge le_sup_left hcard
  apply heCU
  have hmem : e ∈ C ⊔ Subgroup.zpowers e := Subgroup.mem_sup_right (Subgroup.mem_zpowers e)
  rw [← hEq] at hmem
  exact Subgroup.mem_sup_left hmem

end CFSG.RankThree.GF2n.Tim78
