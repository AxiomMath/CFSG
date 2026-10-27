module

public import CFSG.RankThree.PartOne.MB3.Seven
import CFSG.RankThree.PartOne.S10.NonquasisimpleMovingScalarKernelHyperplane

public section

namespace CFSG.RankThree.PartOne.BRANCH

open Subgroup CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne.MB3
open scoped commutatorElement

theorem seven_lifting_full {G : Type} [Group G] [Finite G] {A L : Subgroup G} {q : ℕ}
    {D R : Subgroup G} (hTwo : TwoActionInputs) (h : SteinbergBM.SectionTenSetup G 7 A)
    (hd : SevenData A L q D R) (hRAD : R ⊔ A ≤ Subgroup.normalizer (D : Set G)) :
    IsElementaryAbelian q D ∧ Nat.card D = q ^ 7 ∧ ⁅D, R⁆ = D ∧
      D ⊓ Subgroup.centralizer (R : Set G) = ⊥ := by
  have hp : Nat.Prime 7 := by norm_num
  have hq := hd.q_prime
  have hq2 := hd.q_ne_two
  have hqp : q ≠ 7 := hd.q_ne_seven
  have hAe : IsElementaryAbelian 7 A := h.2.2.2.2.2.2.1
  have hAcard : Nat.card A = 7 ^ 3 := h.2.2.2.2.2.2.2.1
  have hBA : A ⊓ Subgroup.centralizer (R : Set G) ≤ A := inf_le_left
  have hrel : (A ⊓ Subgroup.centralizer (R : Set G)).relIndex A = 7 := by
    rw [hd.kernel]
    exact hd.relIndex
  have hDq : IsPGroup q D := fun x => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hd.D_exp x x.2)⟩
  obtain ⟨a, b₀, haA, haB, hb₀B, hb₀1, hA₀A, hA₀elem, hA₀card, hfac, hker⟩ :=
    exists_plane_of_index_prime_subgroup hp hAe hAcard hBA hrel
  set A₀ := zpowers a ⊔ zpowers b₀ with hA₀
  have hset : MinTwoActionSetting 7 q A₀ D R :=
    minTwoActionSetting_of_plane hp hq (by norm_num) hq2 hqp hA₀elem hA₀card hA₀A hfac hRAD
      hd.D_exp hd.D_class hd.R_two hd.R_inv hd.R_comm hd.R_ne_bot hd.R_act hd.R_min
  have hA₀R : A₀ ≤ Subgroup.normalizer (R : Set G) := hA₀A.trans hd.R_inv
  have hA₀D : A₀ ≤ Subgroup.normalizer (D : Set G) := hA₀A.trans (le_sup_right.trans hRAD)
  have hRD' : R ≤ Subgroup.normalizer (D : Set G) := le_sup_left.trans hRAD
  obtain ⟨hAlt, -, hlift⟩ := hTwo
  rcases hAlt G 7 q A₀ D R hset hd.fixed_rank with
    ⟨hRcase, ⟨r, hrR, hr1, hr3⟩, -⟩ | ⟨h5, -⟩ | ⟨h5, -⟩
  · obtain ⟨hRe, hRcard⟩ : IsElementaryAbelian 2 R ∧ Nat.card R = 8 := by
      rcases hRcase with ⟨h5, -⟩ | ⟨-, hRe, hRcard⟩
      · omega
      · exact ⟨hRe, hRcard⟩
    have hkerA₀ : Nat.card ↥(A₀ ⊓ Subgroup.centralizer (R : Set G)) = 7 := by
      rw [← hker, ← inf_assoc, inf_eq_left.mpr hA₀A]
    have hfrR : inSubgroup frattini R = ⊥ := by
      have : Fact (IsPGroup 2 ↥R) := ⟨hRe.isPGroup 2 ↥R⟩
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      rw [inSubgroup, frattini_eq_bot_of_isElementaryAbelian (p := 2), Subgroup.map_bot]
    have hodd : ¬ 2 ∣ Nat.card A₀ := by
      rw [hA₀card]
      decide
    have hmin₀ : ∀ U : Subgroup G, U < R → A₀ ≤ Subgroup.normalizer (U : Set G) →
        ⁅U, A₀⁆ = U → ⁅U, D⁆ = ⊥ := fun U hU hA₀U hUA₀ =>
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hset.R_min U hU hA₀U hUA₀)
    have hirrR : ∀ Y : Subgroup G, Y ≤ R → A₀ ≤ Subgroup.normalizer (Y : Set G) →
        Y = ⊥ ∨ Y = R := by
      intro Y hYR hA₀Y
      by_cases hYe : Y = R
      · exact Or.inr hYe
      refine Or.inl ?_
      have h' := le_inSubgroup_frattini_of_proper_invariant hd.R_two hd.R_ne_bot hodd hA₀R hA₀D
        hset.R_comm hd.R_act hmin₀ Y (lt_of_le_of_ne hYR hYe) hA₀Y
      rw [hfrR] at h'
      exact le_bot_iff.mp h'
    have hRA₀D : R ⊔ A₀ ≤ Subgroup.normalizer (D : Set G) := sup_le hRD' hA₀D
    obtain ⟨-, hDe, hDcard, hDR, hDC, -⟩ := hlift G 7 q 3 A₀ D R hp hq hq2 hqp
      (Or.inl ⟨rfl, rfl⟩) hA₀elem hA₀card hA₀R hRe (by rw [hRcard]; norm_num) hkerA₀ hirrR
      hRA₀D hDq hd.D_exp hd.D_class hd.R_act hd.fixed_rank
    exact ⟨hDe, hDcard, hDR, hDC⟩
  · omega
  · omega

theorem mod_eq_one_of_pow_seven_modEq {q : ℕ} (hq : q = 3 ∨ q = 5) (k : ℕ)
    (h : k ^ 7 ≡ 1 [MOD q]) : k % q = 1 := by
  rcases hq with rfl | rfl
  · have h' : (k % 3) ^ 7 % 3 = 1 := by
      unfold Nat.ModEq at h
      rw [Nat.pow_mod] at h
      exact h
    have hlt : k % 3 < 3 := Nat.mod_lt _ (by norm_num)
    interval_cases hm : k % 3 <;> simp_all
  · have h' : (k % 5) ^ 7 % 5 = 1 := by
      unfold Nat.ModEq at h
      rw [Nat.pow_mod] at h
      exact h
    have hlt : k % 5 < 5 := Nat.mod_lt _ (by norm_num)
    interval_cases hm : k % 5 <;> simp_all

theorem seven_commutator_E_D {G : Type} [Group G] [Finite G] {A L : Subgroup G} {q : ℕ}
    {D R : Subgroup G} (hd : SevenData A L q D R) (hAe : IsElementaryAbelian 7 A)
    (hDe : IsElementaryAbelian q D) (hq35 : q = 3 ∨ q = 5) :
    ⁅thetaQuotientCentralizer 7 A L, D⁆ = ⊥ := by
  have hq := hd.q_prime
  have : Fact q.Prime := ⟨hq⟩
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro e he
  rw [Subgroup.mem_centralizer_iff]
  intro d hdD
  have heA : e ∈ A := (inf_le_left : thetaQuotientCentralizer 7 A L ≤ A) he
  have he7 : e ^ 7 = 1 := elemPow_eq_one_of_isElementaryAbelian (p := 7) (A := A) e heA
  obtain ⟨k, hk⟩ := hd.scalar e he
  have hfr : inSubgroup frattini D = ⊥ := by
    have : Fact (IsPGroup q ↥D) := ⟨hDe.isPGroup q ↥D⟩
    rw [inSubgroup, frattini_eq_bot_of_isElementaryAbelian (p := q), Subgroup.map_bot]
  have hkd : ∀ x ∈ D, e * x * e⁻¹ = x ^ k := by
    intro x hx
    have h1 := hk x hx
    rw [hfr, Subgroup.mem_bot] at h1
    exact (inv_mul_eq_one.mp h1)
  have hit : ∀ n : ℕ, ∀ x ∈ D, e ^ n * x * (e ^ n)⁻¹ = x ^ (k ^ n) := by
    intro n
    induction n with
    | zero => intro x hx; simp
    | succ n ih =>
      intro x hx
      have h1 : e ^ (n + 1) * x * (e ^ (n + 1))⁻¹ = e * (e ^ n * x * (e ^ n)⁻¹) * e⁻¹ := by
        rw [pow_succ']
        group
      rw [h1, ih x hx, ← conj_pow, hkd x hx, ← pow_mul, ← pow_succ']
  have h7 := hit 7 d hdD
  rw [he7] at h7
  simp only [one_mul, inv_one, mul_one] at h7
  have hdk : e * d * e⁻¹ = d := by
    by_cases hd1 : d = 1
    · simp [hd1]
    · have hdq : d ^ q = 1 := elemPow_eq_one_of_isElementaryAbelian (p := q) (A := D) d hdD
      have hord : orderOf d = q := orderOf_eq_prime hdq hd1
      have hmod : k ^ 7 ≡ 1 [MOD q] := by
        have h8 : d ^ (k ^ 7) = d ^ 1 := by rw [pow_one]; exact h7.symm
        rwa [pow_eq_pow_iff_modEq, hord] at h8
      have hk1 : k % q = 1 := mod_eq_one_of_pow_seven_modEq hq35 k hmod
      have hdkd : d ^ k = d := by
        calc d ^ k = d ^ (q * (k / q) + k % q) := by rw [Nat.div_add_mod]
          _ = d := by rw [pow_add, pow_mul, hdq, one_pow, one_mul, hk1, pow_one]
      rw [hkd d hdD, hdkd]
  exact (mul_inv_eq_iff_eq_mul.mp hdk).symm

end CFSG.RankThree.PartOne.BRANCH
