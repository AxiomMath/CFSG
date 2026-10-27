module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80U3WrCen

public section

namespace CFSG.Quasithin.E2P.Asc80

open Matrix CFSG.Quasithin.B6 CFSG.QuasithinUnique CFSG.Quasithin.A312U3
  CFSG.LocalAnalysis.ComponentInitial

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F]

theorem exists_sq_eq_neg_one_of_card [Finite F] (hp4 : p % 4 = 3) (hF : Nat.card F = p ^ 2) :
    ∃ i : F, i ^ 2 = -1 ∧ (uniData hF).bar i * i = 1 := by
  have := Fintype.ofFinite F
  have hc : Fintype.card F = p ^ 2 := by rw [← Nat.card_eq_fintype_card, hF]
  have hsq : IsSquare (-1 : F) := by
    rw [FiniteField.isSquare_neg_one_iff, hc]
    obtain ⟨k, hk⟩ : ∃ k, p = 4 * k + 3 := ⟨p / 4, by omega⟩
    rw [hk]
    ring_nf
    omega
  obtain ⟨i, hi⟩ := hsq
  have hi2 : i ^ 2 = -1 := by rw [sq, ← hi]
  refine ⟨i, hi2, ?_⟩
  obtain ⟨m, hm⟩ : ∃ m, p + 1 = 4 * m := ⟨(p + 1) / 4, by omega⟩
  rw [UnitaryFieldData.bar_apply, pow_one, ← pow_succ, hm]
  calc i ^ (4 * m) = (i ^ 2) ^ (2 * m) := by rw [← pow_mul]; ring_nf
    _ = 1 := by rw [hi2, pow_mul, neg_one_sq, one_pow]

theorem exists_wreathed_normalizer_u [Finite F] (hp4 : p % 4 = 3) (hF : Nat.card F = p ^ 2) :
    ∃ U : Subgroup (PSU3F p F), IsSylowTwoOf U ⊤ ∧ U ≤ leviCU hF ∧ ⁅U, U⁆ ≠ ⊥ ∧
      (∀ a ∈ ⁅U, U⁆, ∀ b ∈ ⁅U, U⁆, a * b = b * a) ∧
      ¬ Subgroup.normalizer (Subgroup.centralizer
          ((⁅U, U⁆ : Subgroup (PSU3F p F)) : Set (PSU3F p F)) : Set (PSU3F p F)) ≤
        leviCU hF := by
  have hp2 : p ≠ 2 := fun h => by
    rw [h] at hp4
    omega
  obtain ⟨i, hi, hbar⟩ := exists_sq_eq_neg_one_of_card hp4 hF
  have hi0 : i ≠ 0 := fun h => by
    rw [h] at hi
    simp at hi
  have hu : Units.mk0 i hi0 ∈ muU hF := mem_muU_of_bar_mul_self hF hbar
  set u : ↥(muU hF) := ⟨Units.mk0 i hi0, hu⟩ with hudef
  have hi' : ((u : Fˣ) : F) ^ 2 = -1 := hi
  have hu4 : u ^ 4 = 1 := by
    apply Subtype.ext
    apply Units.ext
    show ((u : Fˣ) : F) ^ 4 = 1
    calc ((u : Fˣ) : F) ^ 4 = (((u : Fˣ) : F) ^ 2) ^ 2 := by ring
      _ = 1 := by rw [hi']; norm_num
  obtain ⟨U, hU, hUm, hEU, hUD⟩ := exists_wreathed_sylow_u hF hp4
  refine ⟨U, hU, hUm.trans (monoCU_le_leviCU hp2 hF), ?_, fun a ha b hb =>
    diagCU_comm (commutator_le_diagCU hUm ha) (commutator_le_diagCU hUm hb), ?_⟩
  · intro hbot
    have hmem := piU_xOU_mem_commutator hu4 hEU hUm hUD
    rw [hbot] at hmem
    obtain ⟨r, -, hr⟩ := exists_scalar_of_mem_ker hF
      (show xOU hF u ∈ (piU p F).ker from Subgroup.mem_bot.mp hmem)
    have e00 := congrFun (congrFun hr 0) 0
    have e11 := congrFun (congrFun hr 1) 1
    rw [matU_xOU] at e00 e11
    simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq, Matrix.cons_val_zero,
      Matrix.cons_val_one] at e00 e11
    rw [val_inv_eq_neg_u hi'] at e11
    have hui : ((u : Fˣ) : F) = i := rfl
    rw [hui] at e00 e11
    have h2i : (2 : F) * i = 0 := by linear_combination e00 - e11
    exact hi0 ((mul_eq_zero.mp h2i).resolve_left (two_ne_zero_u hp2 hF))
  · intro hN
    have hw : piU p F (flipU hF) ∈ Subgroup.normalizer (Subgroup.centralizer
        ((⁅U, U⁆ : Subgroup (PSU3F p F)) : Set (PSU3F p F)) : Set (PSU3F p F)) := by
      rw [centralizer_commutator_eq_diagCU hp2 hi' hu4 hEU hUm hUD]
      exact piU_flipU_mem_normalizer hF
    exact piU_flipU_not_mem_leviCU hp2 hF (hN hw)

end CFSG.Quasithin.E2P.Asc80
