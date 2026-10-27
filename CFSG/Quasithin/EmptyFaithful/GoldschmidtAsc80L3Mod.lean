module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80L3Levi

public section

namespace CFSG.Quasithin.E2P.Asc80

open Matrix CFSG.Quasithin.A38c15
open scoped MatrixGroups

variable {p : ℕ} [Fact p.Prime]

abbrev PSL3 (p : ℕ) [Fact p.Prime] : Type := Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod p)

@[expose] def piL (p : ℕ) [Fact p.Prime] : SL(3, ZMod p) →* PSL3 p :=
  QuotientGroup.mk' (Subgroup.center SL(3, ZMod p))

theorem piL_surjective : Function.Surjective (piL p) := QuotientGroup.mk'_surjective _

theorem ker_piL : (piL p).ker = Subgroup.center SL(3, ZMod p) := QuotientGroup.ker_mk' _

theorem center_le_leviBlock : Subgroup.center SL(3, ZMod p) ≤ leviBlock p := by
  intro g hg
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hg
  rw [mem_leviBlock_iff, ← hr]
  simp [Matrix.scalar_apply]

theorem ker_piL_le_leviBlock : (piL p).ker ≤ leviBlock p := by
  rw [ker_piL]
  exact center_le_leviBlock

theorem card_leviBlock :
    Nat.card (leviBlock p) = (p ^ 2 - 1) * (p ^ 2 - p) := by
  have h1 : Nat.card (leviBlock p) = Nat.card (GL (Fin 2) (ZMod p)) :=
    (Nat.card_congr (Equiv.ofInjective (leviHom p) leviHom_injective)).symm
  rw [h1, Matrix.card_GL_field]
  simp [Fin.prod_univ_two, ZMod.card]

theorem index_leviBlock (hp2 : p ≠ 2) : (leviBlock p).index = p ^ 2 * (p ^ 2 + p + 1) := by
  have hp3 : 3 ≤ p := by
    have := (Fact.out : p.Prime).two_le
    omega
  have h := (leviBlock p).index_mul_card
  rw [card_leviBlock] at h
  have hSL := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (K := ZMod p) (n := 3)
    (by norm_num)
  rw [show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num), Nat.card_zmod] at hSL
  norm_num at hSL
  rw [Nat.card_eq_fintype_card, hSL] at h
  have hp1 : 1 ≤ p := by omega
  have hpp : p ≤ p ^ 2 := by nlinarith
  have hp1' : 1 ≤ p ^ 2 := by nlinarith
  have hp3' : 1 ≤ p ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hne : (p ^ 2 - 1) * (p ^ 2 - p) ≠ 0 := by
    apply Nat.mul_ne_zero
    · have : 1 < p ^ 2 := by nlinarith
      omega
    · have : p < p ^ 2 := by nlinarith
      omega
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hne)
  rw [h]
  zify [hp1, hp1', hp3', hpp]
  ring

@[expose] noncomputable def leviC (p : ℕ) [Fact p.Prime] : Subgroup (PSL3 p) :=
  (leviBlock p).map (piL p)

theorem index_leviC (hp2 : p ≠ 2) : (leviC p).index = p ^ 2 * (p ^ 2 + p + 1) := by
  rw [leviC, Subgroup.index_map_eq _ piL_surjective ker_piL_le_leviBlock, index_leviBlock hp2]

theorem odd_main_index (hp2 : p ≠ 2) : Odd (p ^ 2 * (p ^ 2 + p + 1)) := by
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  refine (hodd.pow).mul ?_
  have : p ^ 2 + p + 1 = p * (p + 1) + 1 := by ring
  rw [this]
  exact (Nat.even_mul_succ_self p).add_one

theorem odd_index_leviBlock (hp2 : p ≠ 2) : Odd (leviBlock p).index := by
  rw [index_leviBlock hp2]
  exact odd_main_index hp2

theorem odd_index_leviC (hp2 : p ≠ 2) : Odd (leviC p).index := by
  rw [index_leviC hp2]
  exact odd_main_index hp2

end CFSG.Quasithin.E2P.Asc80
