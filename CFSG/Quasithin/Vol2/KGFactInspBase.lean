module

public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LieType.Ree.SuzukiOrder

public section

namespace CFSG.Quasithin.H13.KGInsp43

open CFSG.Quasithin CFSG.ComponentClassification.OuterAutomorphisms
open scoped MatrixGroups

structure Cfg {X : Type} [Group X] (S R K : Subgroup X) (n : ℕ) : Prop where
  normal : S.Normal
  simple : IsSimpleGroup ↥S
  centralizer_eq_bot : Subgroup.centralizer (S : Set X) = ⊥
  two_le : 2 ≤ n
  ne_bot : R ≠ ⊥
  isPGroup : IsPGroup 2 ↥R
  le : K ≤ S
  perfect : ⁅K, K⁆ = K
  le_normalizer : K ≤ Subgroup.normalizer (R : Set X)
  normalizer_le : Subgroup.normalizer (R : Set X) ≤ Subgroup.normalizer (K : Set X)
  chi : ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ n ∧
    ∃ χ : ↥K →* SL(2, F), Function.Surjective χ ∧ IsPGroup 2 ↥χ.ker

namespace Cfg

variable {X : Type} [Group X] {S R K : Subgroup X} {n : ℕ}

@[expose] def omega3 (F : Type) [Field F] [CharP F 2] : SL(2, F) :=
  ⟨!![0, 1; 1, 1], by
    rw [Matrix.det_fin_two_of]
    simp [CharTwo.neg_eq]⟩

theorem orderOf_omega3 (F : Type) [Field F] [CharP F 2] : orderOf (omega3 F) = 3 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have h3 : omega3 F ^ 3 = 1 := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
    simp only [omega3, pow_succ, pow_zero, one_mul]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> linear_combination h2
  have h1 : omega3 F ≠ 1 := by
    intro h
    have := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
    simp [omega3] at this
  exact orderOf_eq_prime h3 h1

theorem three_dvd_card [Finite X] (h : Cfg S R K n) : 3 ∣ Nat.card K := by
  obtain ⟨F, _, _, hF, χ, hχ, -⟩ := h.chi
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow hF
  obtain ⟨k, hk⟩ := hχ (omega3 F)
  have h1 : 3 ∣ orderOf k := by
    rw [← orderOf_omega3 F, ← hk]
    exact orderOf_map_dvd χ k
  exact h1.trans (orderOf_dvd_natCard k)

theorem three_dvd_card_S [Finite X] (h : Cfg S R K n) : 3 ∣ Nat.card S :=
  h.three_dvd_card.trans (Subgroup.card_dvd_of_le h.le)

theorem le_normalizer_inf (h : Cfg S R K n) :
    K ≤ Subgroup.normalizer ((R ⊓ S : Subgroup X) : Set X) := by
  intro k hk
  have hkR := h.le_normalizer hk
  have hkS := h.le hk
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  constructor
  · rintro ⟨hxR, hxS⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp hkR x).mp hxR, h.normal.conj_mem x hxS k⟩
  · rintro ⟨hxR, hxS⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp hkR x).mpr hxR, ?_⟩
    have := h.normal.conj_mem _ hxS k⁻¹
    simpa [mul_assoc] using this

theorem false_of_isSz [Finite X] (h : Cfg S R K n) {f : ℕ}
    (hS : IsSz f ↥S) : False := by
  obtain ⟨-, a, -, F, _, _, rfl, hF, ⟨e⟩⟩ := hS
  have h3 := h.three_dvd_card_S
  rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hF] at h3
  have hq : 2 ^ (2 * a + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hq1 : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
  have hp := Nat.prime_three
  rcases (Nat.Prime.dvd_mul hp).mp h3 with h4 | h4
  · rcases (Nat.Prime.dvd_mul hp).mp h4 with h5 | h5
    · have := Nat.Prime.dvd_of_dvd_pow hp h5
      omega
    · omega
  · have h5 : (2 ^ (2 * a + 1)) ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hq]
    omega

end Cfg

end CFSG.Quasithin.H13.KGInsp43
