module

public import CFSG.RepresentationTheory.SL2NatSum.NatSumInput
public import CFSG.Quasithin.Background.C41PfW
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.CGT.Timmesfeld75
open CFSG.SignalizerFunctorTheorem.Quadratic
open Subgroup

theorem isPSL_of_isL2Pair {n : ℕ} (hn : 2 ≤ n) {B : Type} [Group B] {P : Subgroup B}
    (hP : IsL2Pair B P (2 ^ n)) : CFSG.Quasithin.IsPSL 2 2 n B := by
  obtain ⟨F, _, _, _, e, hF, -⟩ := hP
  exact CFSG.Quasithin.C41Pf.isPSL_two_two_of_equiv_sl2 hn hF e

private theorem w16q_finrank_finset_sup {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W] (t : Finset (Submodule (ZMod 2) W))
    (h : ∀ U ∈ t, U ⊓ (t.erase U).sup id = ⊥) :
    Module.finrank (ZMod 2) ↥(t.sup id) = ∑ U ∈ t, Module.finrank (ZMod 2) ↥U := by
  classical
  revert h
  refine Finset.induction_on t ?_ ?_
  · intro _
    simp
  · intro U t' hU ih h
    rw [Finset.sup_insert, Finset.sum_insert hU]
    change Module.finrank (ZMod 2) ↥(U ⊔ t'.sup id)
      = Module.finrank (ZMod 2) ↥U + ∑ x ∈ t', Module.finrank (ZMod 2) ↥x
    have hUbot : U ⊓ t'.sup id = ⊥ := by
      have hU' := h U (Finset.mem_insert_self U t')
      rwa [Finset.erase_insert hU] at hU'
    have h' : ∀ V ∈ t', V ⊓ (t'.erase V).sup id = ⊥ := by
      intro V hV
      have hV' := h V (Finset.mem_insert_of_mem hV)
      have hne : U ≠ V := by rintro rfl; exact hU hV
      rw [Finset.erase_insert_of_ne hne, Finset.sup_insert] at hV'
      exact le_antisymm ((inf_le_inf_left V le_sup_right).trans hV'.le) bot_le
    have hfin := Submodule.finrank_sup_add_finrank_inf_eq U (t'.sup id)
    rw [hUbot, finrank_bot, add_zero] at hfin
    rw [hfin, ih h']

theorem exists_finrank_eq_of_pair {n : ℕ} (hn : 2 ≤ n) {B : Type} [Group B] [Finite B]
    {P : Subgroup B} (hP : IsL2Pair B P (2 ^ n)) {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] [Finite W] (ρ : B →* LGL 2 W)
    (hD : ∃ D : Subgroup B, Nat.card D = 3 ∧ ∀ w : W, (∀ d ∈ D, ρ d w = w) → w = 0) :
    ∃ s : ℕ, Module.finrank (ZMod 2) W = 2 * n * s := by
  classical
  have hB : CFSG.Quasithin.IsPSL 2 2 n B := isPSL_of_isL2Pair hn hP
  obtain ⟨s, _hInv, htop, hind, hnat⟩ :=
    CFSG.RepresentationTheory.SL2NatSum.natSumL2Input_holds n (by omega) B hB W ρ hD
  have hU : ∀ U ∈ s, Module.finrank (ZMod 2) ↥U = 2 * n := by
    intro U hU
    obtain ⟨K, _hKf, _hKfin, _φ, ψ, hKcard, _⟩ := hnat U hU
    have hcard : Nat.card ↥U = 2 ^ (2 * n) := by
      rw [Nat.card_congr ψ.toEquiv, Nat.card_fun, hKcard, Nat.card_fin]
      rw [← pow_mul, mul_comm]
    have hpow := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥U)
    rw [Nat.card_zmod] at hpow
    have h2 : 2 ^ Module.finrank (ZMod 2) ↥U = 2 ^ (2 * n) := by
      rw [← hpow, hcard]
    exact Nat.pow_right_injective (show 2 ≤ 2 by norm_num) h2
  have hsum := w16q_finrank_finset_sup s hind
  rw [htop, finrank_top] at hsum
  have hsum2 : (∑ U ∈ s, Module.finrank (ZMod 2) ↥U) = s.card * (2 * n) := by
    rw [Finset.sum_congr rfl hU, Finset.sum_const, Nat.nsmul_eq_mul]
  exact ⟨s.card, by rw [hsum, hsum2, mul_comm]⟩

end CFSG.LocalAnalysis.WeakClosure81

end
