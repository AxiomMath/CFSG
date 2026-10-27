module

public import CFSG.RankThree.PartOne.KLC.PRankTwo
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122APerfect
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Quasithin.Vol2.Ch10SecQ9G7
public import CFSG.Sporadic.Schreier.J4SSylowBase
public import Certificates.Data.CFSGNative.H13.J4Chain

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped commutatorElement

theorem isQuasisimple_of_open' {Q : Type*} [Group Q] (h : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q := by
  refine ⟨Group.isPerfect_def.mpr h.1, h.2, ?_⟩
  by_contra hcon
  have hcon' : ∀ a b : Q ⧸ Subgroup.center Q, a * b = b * a := fun a b => by
    by_contra hab
    exact hcon ⟨a, b, hab⟩
  have hcomm : commutator Q ≤ Subgroup.center Q := by
    refine Subgroup.commutator_le.mpr fun a _ b _ => ?_
    have h1 : QuotientGroup.mk' (Subgroup.center Q) ⁅a, b⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (hcon' _ _)
    exact (QuotientGroup.eq_one_iff _).mp h1
  have htop : Subgroup.center Q = ⊤ := top_le_iff.mp (h.1 ▸ hcomm)
  have := h.2
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (Q ⧸ Subgroup.center Q)
  apply hxy
  induction x using QuotientGroup.induction_on
  induction y using QuotientGroup.induction_on
  rw [QuotientGroup.eq]
  rw [htop]
  exact Subgroup.mem_top _

theorem center_SL_eq_bot (n : ℕ) :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Subgroup.mem_bot]
  by_cases hn : n = 0
  · subst hn
    exact Subsingleton.elim _ _
  have hr1 : r = 1 := by
    have h0 : r ≠ 0 := by
      intro h0
      rw [h0, zero_pow (by simpa using hn)] at hr
      exact zero_ne_one hr
    revert h0
    generalize r = r'
    revert r'
    decide
  apply Subtype.ext
  rw [← hrA, hr1, map_one, Matrix.SpecialLinearGroup.coe_one]

theorem indep_of_three {P : Type*} [Group P] {e₁ e₂ : P} (h₁ : e₁ ^ 3 = 1) (h₂ : e₂ ^ 3 = 1)
    (h : ∀ a b : Fin 3, e₁ ^ (a : ℕ) * e₂ ^ (b : ℕ) = 1 → a = 0 ∧ b = 0) :
    ∀ i j : ℤ, e₁ ^ i * e₂ ^ j = 1 → (3 : ℤ) ∣ i ∧ (3 : ℤ) ∣ j := by
  have key : ∀ e : P, e ^ 3 = 1 → ∀ k : ℤ, e ^ k = e ^ (k % 3).toNat := by
    intro e he k
    have h2 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
    have he' : e ^ (3 : ℤ) = 1 := by exact_mod_cast he
    conv_lhs => rw [← Int.emod_add_mul_ediv k 3]
    rw [zpow_add, zpow_mul, he', one_zpow, mul_one, ← zpow_natCast, Int.toNat_of_nonneg h2]
  intro i j hij
  rw [key e₁ h₁ i, key e₂ h₂ j] at hij
  have hi3 : (i % 3).toNat < 3 := by omega
  have hj3 : (j % 3).toNat < 3 := by omega
  obtain ⟨ha, hb⟩ := h ⟨_, hi3⟩ ⟨_, hj3⟩ hij
  have ha' : (i % 3).toNat = 0 := congrArg Fin.val ha
  have hb' : (j % 3).toNat = 0 := congrArg Fin.val hb
  constructor <;> omega

@[expose] def s4a : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) :=
  ⟨!![0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1], by decide⟩

@[expose] def s4b : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) :=
  ⟨!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 1], by decide⟩

@[expose] def s5a : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2) :=
  ⟨!![0, 1, 0, 0, 0; 1, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1], by
    decide +kernel⟩

@[expose] def s5b : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2) :=
  ⟨!![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 1, 1, 0; 0, 0, 0, 0, 1], by
    decide +kernel⟩

theorem s4a_pow : s4a ^ 3 = 1 := Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_pow]; decide)
theorem s4b_pow : s4b ^ 3 = 1 := Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_pow]; decide)
theorem s5a_pow : s5a ^ 3 = 1 :=
  Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_pow]; decide +kernel)
theorem s5b_pow : s5b ^ 3 = 1 :=
  Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_pow]; decide +kernel)

theorem s4_comm : Commute s4a s4b := Subtype.ext (by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]; decide)
theorem s5_comm : Commute s5a s5b := Subtype.ext (by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]; decide +kernel)

theorem s4_indep : ∀ a b : Fin 3, s4a ^ (a : ℕ) * s4b ^ (b : ℕ) = 1 → a = 0 ∧ b = 0 := by
  intro a b h
  have h' := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) =>
    (g : Matrix (Fin 4) (Fin 4) (ZMod 2))) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow,
    Matrix.SpecialLinearGroup.coe_one] at h'
  revert h'
  revert a b
  decide

theorem s5_indep : ∀ a b : Fin 3, s5a ^ (a : ℕ) * s5b ^ (b : ℕ) = 1 → a = 0 ∧ b = 0 := by
  intro a b h
  have h' := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2) =>
    (g : Matrix (Fin 5) (Fin 5) (ZMod 2))) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow,
    Matrix.SpecialLinearGroup.coe_one] at h'
  revert h'
  revert a b
  decide +kernel

theorem two_le_pRank_SL4 :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))) := by
  rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact CFSG.RankThree.PartOne.KLC.two_le_pRank_of_two_commuting Nat.prime_three s4_comm s4a_pow
    s4b_pow (indep_of_three s4a_pow s4b_pow s4_indep)

theorem two_le_pRank_SL5 :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))) := by
  rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact CFSG.RankThree.PartOne.KLC.two_le_pRank_of_two_commuting Nat.prime_three s5_comm s5a_pow
    s5b_pow (indep_of_three s5a_pow s5b_pow s5_indep)

theorem three_dvd_card_SL4 : 3 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h : orderOf s4a = 3 := orderOf_eq_prime s4a_pow (fun h => by
    have := (s4_indep 1 0 (by rw [h]; simp)).1
    exact absurd this (by decide))
  rw [← h]
  exact orderOf_dvd_natCard _

theorem three_dvd_card_SL5 : 3 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h : orderOf s5a = 3 := orderOf_eq_prime s5a_pow (fun h => by
    have := (s5_indep 1 0 (by rw [h]; simp)).1
    exact absurd this (by decide))
  rw [← h]
  exact orderOf_dvd_natCard _

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
