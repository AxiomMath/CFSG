module

public import CFSG.RankThree.PartOne.AUTSL.Interface
public import CFSG.LocalAnalysis.UniquenessCase.UC6AutEbar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.RankThree.PartTwo.KFacts.L34
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ABGLocalTools
open CFSG.Blueprint (LieModel)

namespace L34K

section Concrete

variable {k : Type} [Field k]

theorem absKC_eZero (hk : Nat.card k = 4) : AbsKC (projectiveSL 3 k) 3 (eZero k) := by
  classical
  have := LinearFieldFour.finite_of_card_eq_four hk
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  have hσ : ∀ a, frobeniusEquiv k 2 a = a ^ 2 := fun a => frobeniusEquiv_apply k 2 a
  intro α ⟨j, hj⟩ hfix
  obtain ⟨e, he, rfl | rfl⟩ := (forall_fixes_eZero_iff hk hσ α).mp hfix
  · exact ⟨e, he, rfl⟩
  · exfalso
    set β : MulAut (projectiveSL 3 k) := betaAut (frobeniusEquiv k 2) with hβdef
    have hb : β * MulAut.conj e * β⁻¹ = MulAut.conj e := by
      rw [CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv, betaAut_fixed hk hσ he]
    have hcomm : Commute (MulAut.conj e) β := by
      show _ * _ = _ * _
      calc MulAut.conj e * β = β * MulAut.conj e * β⁻¹ * β := by rw [hb]
        _ = β * MulAut.conj e := by group
    have hββ : β * β = 1 := betaAut_mul_self hk hσ
    have he3 := pow_three_of_mem_eZero hk he
    have hα3 : (MulAut.conj e * β) ^ 3 = β := by
      rw [hcomm.mul_pow, ← map_pow, he3, map_one, one_mul, pow_succ, pow_two, hββ, one_mul]
    have hα6 : (MulAut.conj e * β) ^ 6 = 1 := by
      rw [show 6 = 3 * 2 from rfl, pow_mul, hα3, pow_two, hββ]
    have hdvd : orderOf (MulAut.conj e * β) ∣ 3 := by
      have h6 : orderOf (MulAut.conj e * β) ∣ 6 := orderOf_dvd_of_pow_eq_one hα6
      rw [hj] at h6 ⊢
      rcases Nat.eq_zero_or_pos j with rfl | hjpos
      · simp
      · have : 3 ∣ 3 ^ j := dvd_pow_self 3 hjpos.ne'
        have hcop : Nat.Coprime (3 ^ j) 2 := Nat.Coprime.pow_left _ (by norm_num)
        exact hcop.dvd_of_dvd_mul_right (by simpa using h6)
    have h1 : (MulAut.conj e * β) ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd
    rw [hα3] at h1
    exact betaAut_ne_one hk h1

theorem absKInv_eZero (hk : Nat.card k = 4) : AbsKInv (projectiveSL 3 k) (eZero k) := by
  classical
  have := LinearFieldFour.finite_of_card_eq_four hk
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  have hσ : ∀ a, frobeniusEquiv k 2 a = a ^ 2 := fun a => frobeniusEquiv_apply k 2 a
  have h3 : ∀ {z : MulAut (projectiveSL 3 k)} {n : ℕ}, orderOf z = 2 ^ n → ¬ 3 ∣ orderOf z := by
    intro z n h h3
    rw [h] at h3
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  intro x y ⟨i, hi⟩ ⟨j, hj⟩ hx hy hx1 hy1
  rcases eq_one_or_eq_betaAut hk hσ hx (h3 hi) with rfl | rfl
  · exact absurd rfl hx1
  rcases eq_one_or_eq_betaAut hk hσ hy (h3 hj) with rfl | rfl
  · exact absurd rfl hy1
  rfl

theorem absKN_of_card (hk : Nat.card k = 4) {E : Subgroup (projectiveSL 3 k)} (hE : Nat.card E = 9)
    {P : Prop} (hP : P) : AbsKN (projectiveSL 3 k) 3 E P := by
  classical
  have hfin := LinearFieldFour.finite_of_card_eq_four hk
  have : Finite (MulAut (projectiveSL 3 k)) :=
    Nat.finite_of_card_ne_zero (by rw [card_mulAut hk]; norm_num)
  intro X hXn hX3
  have hcard : ¬ 3 ∣ Nat.card X := by
    intro h3
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := X) 3 h3
    have hx' : orderOf (x : MulAut (projectiveSL 3 k)) = 3 := by
      rw [Subgroup.orderOf_coe]; exact hx
    have := hX3 x x.2 ⟨1, by rw [hx', pow_one]⟩
    rw [this, orderOf_one] at hx'
    omega
  have hEX : ∀ e ∈ E, MulAut.conj e ∈ Subgroup.normalizer (X : Set (MulAut (projectiveSL 3 k))) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hXn e he x hx
    · intro hx
      have := hXn e⁻¹ (E.inv_mem he) _ hx
      simpa [map_inv, mul_assoc] using this
  exact ⟨fun x hx e he => forall_apply_eq_of_invariant hk hE hcard hEX hx he, Or.inr hP⟩

theorem isSylowOf_eZero (hk : Nat.card k = 4) : IsSylowOf 3 (eZero k) ⊤ := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact isSylowOf_of_card le_top (by rw [Subgroup.card_top]; exact card_eZero_eq hk)

end Concrete

end L34K

namespace Mz614

variable {G : Type} [Group G] [Finite G] (m : Mz614 G)

theorem kc633_of_l34 (h620 : m.C620) (hr3 : m.r = 3) (hL : LieModel m.Lbar .PSL 3 2 2) :
    m.KC633 := by
  obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hL
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  have := LinearFieldFour.finite_of_card_eq_four hK4
  haveI : Finite (projectiveSL 3 K) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [card_projectiveSL hK4]; norm_num
  refine m.kc633_of_model h620 φ (by rw [hr3]; exact factorization_card hK4)
    (E₀ := eZero K) (by rw [hr3]; exact L34K.isSylowOf_eZero hK4) ?_
  rw [hr3]
  exact L34K.absKC_eZero hK4

theorem kn633_of_l34 (h620 : m.C620) (hr3 : m.r = 3) (hL : LieModel m.Lbar .PSL 3 2 2) :
    m.KN633 := by
  obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hL
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  have := LinearFieldFour.finite_of_card_eq_four hK4
  haveI : Finite (projectiveSL 3 K) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [card_projectiveSL hK4]; norm_num
  refine m.kn633_of_model h620 φ (by rw [hr3]; exact factorization_card hK4)
    (E₀ := eZero K) (by rw [hr3]; exact L34K.isSylowOf_eZero hK4) ?_
  have key : AbsKN (projectiveSL 3 K) 3 (eZero K) (m.r = 3 ∧ LieModel m.Lbar .PSL 3 2 2) :=
    L34K.absKN_of_card hK4 (card_eZero hK4) ⟨hr3, hL⟩
  have hsw : ∀ n : ℕ, n = 3 →
      AbsKN (projectiveSL 3 K) 3 (eZero K) (m.r = 3 ∧ LieModel m.Lbar .PSL 3 2 2) →
      AbsKN (projectiveSL 3 K) n (eZero K) (m.r = 3 ∧ LieModel m.Lbar .PSL 3 2 2) :=
    fun n hn h => by subst hn; exact h
  exact hsw _ hr3 key

theorem kinv633_of_l34 (h620 : m.C620) (hr3 : m.r = 3) (hL : LieModel m.Lbar .PSL 3 2 2) :
    m.KInv633 := by
  obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hL
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  have := LinearFieldFour.finite_of_card_eq_four hK4
  haveI : Finite (projectiveSL 3 K) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [card_projectiveSL hK4]; norm_num
  exact m.kinv633_of_model h620 φ (by rw [hr3]; exact factorization_card hK4)
    (E₀ := eZero K) (by rw [hr3]; exact L34K.isSylowOf_eZero hK4) (L34K.absKInv_eZero hK4)

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6
