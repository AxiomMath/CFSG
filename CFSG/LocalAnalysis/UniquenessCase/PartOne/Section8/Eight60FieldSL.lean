module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight60FieldAutOmega
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight60FieldMatrix
import CFSG.ClassicalInvolution.Asc77.AscSCH22
import CFSG.LieType.SemisimpleCentralizers.HeldCompTrivSL
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight60FieldSL2
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight60FieldSLBAux1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Matrix
open CFSG.Open (StatedProj StatedSL StatedSU StatedSp)
open CFSG.Open.StatedAPI (mem_statedSL_iff)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ClassicalInvolution.Asc77.SCH (isPerfect_statedSL_four)
open CFSG.LieType.SemisimpleCentralizers.Held (hct_isPerfect_statedSL)

private theorem fieldAut_pow_three_pow_eq_one {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) (φ : RingAut K)
    (hφpow : ∀ x : K, φ x = x ^ (p ^ (f / 3 ^ (f.factorization 3)))) :
    φ ^ (3 ^ (f.factorization 3)) = 1 := by
  let q₀ := p ^ (f / 3 ^ (f.factorization 3))
  have hpow : ∀ m : ℕ, ∀ x : K, (φ ^ m) x = x ^ (q₀ ^ m) := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih =>
        intro x
        rw [pow_succ']
        change φ ((φ ^ m) x) = x ^ (q₀ ^ (m + 1))
        rw [ih, hφpow, ← pow_mul, pow_succ]
  have hq0pow : q₀ ^ (3 ^ (f.factorization 3)) = p ^ f := by
    dsimp only [q₀]
    rw [← pow_mul, Nat.div_mul_cancel]
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three (by omega)).mpr le_rfl
  have hpowcard : ∀ x : K, x ^ Nat.card K = x := by
    intro x
    have hF : Fintype K := Fintype.ofFinite K
    simp [Nat.card_eq_fintype_card]
  apply RingEquiv.ext
  intro x
  rw [hpow, hq0pow, ← hK]
  exact hpowcard x

theorem exists_abelian_sylow_power_map_statedSL {n p f : ℕ} (hn : n = 4 ∨ n = 5)
    (hp : p.Prime) (hf : 1 ≤ f) (hq : p ^ f % 3 = 2) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = p ^ f) (φ : RingAut K)
    (hφ : ∀ x : K, φ x = x ^ (p ^ (f / 3 ^ (f.factorization 3)))) :
    ∃ (Q : Sylow 3 (StatedProj (StatedSL n K))) (s : ℕ),
      (∀ x ∈ (Q : Subgroup (StatedProj (StatedSL n K))),
        ∀ y ∈ (Q : Subgroup (StatedProj (StatedSL n K))), x * y = y * x) ∧
      s % 3 = 1 ∧
      ∀ τ : MulAut (StatedProj (StatedSL n K)), IsFieldMapQuot (StatedSL n K) φ τ →
        ∀ x ∈ (Q : Subgroup (StatedProj (StatedSL n K))), τ x = x ^ s := by
  have hp3 : p ≠ 3 := by
    rintro rfl
    have h3 : 3 ^ f % 3 = 0 := by
      have hf0 : f ≠ 0 := by omega
      obtain ⟨g, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hf0
      rw [pow_succ']
      exact Nat.mul_mod_right 3 (3 ^ g)
    omega
  obtain ⟨C, s, hCsyl, hCcyc, hs, hCmap⟩ :=
    exists_stable_cyclic_sylow_three_statedSL_two hp hp3 hf hK φ hφ
  rcases hn with rfl | rfl
  · exact exists_abelian_sylow_power_map_statedSL_four hq hK φ C s hCsyl hCcyc hs hCmap
  · exact exists_abelian_sylow_power_map_statedSL_five hq hK φ C s hCsyl hCcyc hs hCmap

theorem exists_test_element_statedSL {n : ℕ} (hn : n = 4 ∨ n = 5) {K : Type} [Field K]
    [Finite K] :
    ∃ a : K, (∀ σ : RingAut K, σ a = a → σ = 1) ∧
      ∃ A₀ : StatedSL n K, Matrix.trace (((A₀ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) =
        a + a⁻¹ + ((n - 2 : ℕ) : K) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  let a : K := (g : K)
  have ha : a ≠ 0 := Units.ne_zero g
  have hfix : ∀ σ : RingAut K, σ a = a → σ = 1 := by
    intro σ hσ
    let σu : Kˣ →* Kˣ := Units.map σ.toRingHom.toMonoidHom
    have hσu : σu g = g := by
      apply Units.ext
      exact hσ
    ext x
    by_cases hx : x = 0
    · subst hx; simp
    · let u : Kˣ := Units.mk0 x hx
      have hu : (u : K) = x := rfl
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg u)
      have hσuu : σu u = u := by
        rw [← hk, map_zpow, hσu]
      have h1 : σ x = (σu u : K) := by
        rw [← hu, ← hk]
        simp [σu]
      rw [h1, hσuu]
      exact hu
  rcases hn with rfl | rfl
  · refine ⟨a, hfix, ?_⟩
    refine ⟨⟨Matrix.GeneralLinearGroup.mkOfDetNeZero
      (Matrix.diagonal ![a, a⁻¹, 1, 1]) ?_, mem_statedSL_iff.mpr ?_⟩, ?_⟩
    · rw [Matrix.det_diagonal, Fin.prod_univ_four]; simp [ha]
    · simp [Matrix.det_diagonal, Fin.prod_univ_four, ha]
    · simp [Matrix.trace_diagonal, Fin.sum_univ_four]; ring
  · refine ⟨a, hfix, ?_⟩
    refine ⟨⟨Matrix.GeneralLinearGroup.mkOfDetNeZero
      (Matrix.diagonal ![a, a⁻¹, 1, 1, 1]) ?_, mem_statedSL_iff.mpr ?_⟩, ?_⟩
    · rw [Matrix.det_diagonal, Fin.prod_univ_five]; simp [ha]
    · simp [Matrix.det_diagonal, Fin.prod_univ_five, ha]
    · simp [Matrix.trace_diagonal, Fin.sum_univ_five]; ring

theorem three_pow_dvd_of_pow_mem_inner_statedSL {n p f : ℕ} (hn : n = 4 ∨ n = 5)
    (hp : p.Prime) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = p ^ f)
    (φ : RingAut K) (hφ : ∀ x : K, φ x = x ^ (p ^ (f / 3 ^ (f.factorization 3))))
    (τ : MulAut (StatedProj (StatedSL n K))) (hτ : IsFieldMapQuot (StatedSL n K) φ τ)
    (j : ℕ) (hj : τ ^ j ∈ inner (StatedProj (StatedSL n K))) :
    3 ^ (f.factorization 3) ∣ j := by
  obtain ⟨a, ha, A₀, hA₀⟩ := exists_test_element_statedSL hn (K := K)
  have hperf : Group.IsPerfect (StatedSL n K) := by
    rcases hn with rfl | rfl
    · exact isPerfect_statedSL_four K
    · exact hct_isPerfect_statedSL K (by norm_num) (Or.inl (by norm_num)) (Or.inl (by norm_num))
  let q₀ := p ^ (f / 3 ^ (f.factorization 3))
  have hpow : ∀ m : ℕ, ∀ x : K, (φ ^ m) x = x ^ (q₀ ^ m) := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih =>
        intro x
        rw [pow_succ']
        change φ ((φ ^ m) x) = x ^ (q₀ ^ (m + 1))
        rw [ih, hφ, ← pow_mul, pow_succ]
  have hφb : φ ^ (3 ^ (f.factorization 3)) = 1 :=
    fieldAut_pow_three_pow_eq_one hf hK φ hφ
  have h3odd : Odd (3 ^ (f.factorization 3)) := (show Odd (3 : ℕ) by decide).pow
  have hodd : Odd (orderOf φ) :=
    Odd.of_dvd_nat h3odd (orderOf_dvd_iff_pow_eq_one.mpr hφb)
  have hφj : φ ^ j = 1 :=
    pow_eq_one_of_pow_mem_inner (StatedSL n K) hperf φ hodd a ha (n - 2) A₀ hA₀ τ hτ j hj
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hpowcard : ∀ x : K, x ^ Nat.card K = x := by
    intro x
    have hF : Fintype K := Fintype.ofFinite K
    simp [Nat.card_eq_fintype_card]
  have hgu : g ^ (q₀ ^ j) = g := by
    have h1 : (g : K) ^ (q₀ ^ j) = (g : K) := by
      have := hpow j (g : K)
      rw [hφj] at this
      simpa using this.symm
    apply Units.ext
    simpa using h1
  have hdvdorder : orderOf g ∣ q₀ ^ j - 1 := by
    rw [orderOf_dvd_iff_pow_eq_one]
    have hq1 : 1 ≤ q₀ ^ j := one_le_pow₀ (one_le_pow₀ hp.one_le : 1 ≤ q₀)
    have h2 : g ^ (q₀ ^ j - 1) * g = 1 * g := by
      rw [← pow_succ, Nat.sub_add_cancel hq1, hgu, one_mul]
    exact mul_right_cancel h2
  have hq0pow : q₀ ^ (3 ^ (f.factorization 3)) = p ^ f := by
    dsimp only [q₀]
    rw [← pow_mul, Nat.div_mul_cancel]
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three (by omega)).mpr le_rfl
  have hordg : orderOf g = q₀ ^ (3 ^ (f.factorization 3)) - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hK, ← hq0pow]
  have hbig : q₀ ^ (3 ^ (f.factorization 3)) - 1 ∣ q₀ ^ j - 1 := by
    rw [← hordg]; exact hdvdorder
  have h3bdvd : 3 ^ (f.factorization 3) ∣ f :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three (by omega)).mpr le_rfl
  have hq0ge : 2 ≤ q₀ := by
    have hle : 3 ^ (f.factorization 3) ≤ f := Nat.le_of_dvd (by omega) h3bdvd
    have hk : f / 3 ^ (f.factorization 3) ≠ 0 := by
      have hpos : 0 < f / 3 ^ (f.factorization 3) :=
        Nat.div_pos hle (pow_pos (by norm_num) _)
      omega
    calc 2 ≤ p := hp.two_le
      _ ≤ p ^ (f / 3 ^ (f.factorization 3)) := le_self_pow hp.one_le hk
      _ = q₀ := rfl
  exact dvd_of_pow_sub_one_dvd_pow_sub_one hq0ge (pow_pos (by norm_num) _) hbig

theorem fieldSylowData_statedSL {n p f : ℕ} (hn : n = 4 ∨ n = 5) (hp : p.Prime) (hf : 1 ≤ f)
    (hq : p ^ f % 3 = 2) {K : Type} [Field K] [Finite K] (hK : Nat.card K = p ^ f) :
    FieldSylowData (StatedProj (StatedSL n K)) (f.factorization 3) := by
  obtain ⟨φ, hφpow⟩ := by
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : Fintype K := Fintype.ofFinite K
    haveI : CharP K p :=
      charP_of_card_eq_prime_pow (R := K) (by simpa [Nat.card_eq_fintype_card] using hK)
    exact exists_ringAut_pow_of_charP (K := K) (p := p) (f / 3 ^ (f.factorization 3))
  obtain ⟨Q, s, hQab, hs, hQmap⟩ :=
    exists_abelian_sylow_power_map_statedSL hn hp hf hq hK φ hφpow
  have hH : ∀ g ∈ StatedSL n K, Matrix.GeneralLinearGroup.map (φ : K →+* K) g ∈ StatedSL n K := by
    intro g hg
    rw [mem_statedSL_iff] at hg ⊢
    have hg' : Matrix.GeneralLinearGroup.det g = 1 := by
      apply Units.ext
      simpa [Matrix.GeneralLinearGroup.val_det_apply] using hg
    rw [← Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.map_det, hg']
    simp
  obtain ⟨τ, hτ⟩ := exists_isFieldMapQuot (StatedSL n K) φ hH
  have hφb : φ ^ (3 ^ (f.factorization 3)) = 1 :=
    fieldAut_pow_three_pow_eq_one hf hK φ hφpow
  refine ⟨Q, τ, s, hQab, hs, ?_, ?_, ?_⟩
  · intro x hx
    exact hQmap τ hτ x hx
  · have hτα : IsFieldMapQuot (StatedSL n K) (φ ^ (3 ^ (f.factorization 3)))
        (τ ^ (3 ^ (f.factorization 3))) := isFieldMapQuot_pow hτ _
    rw [hφb] at hτα
    exact eq_one_of_isFieldMapQuot_one hτα
  · intro j hj
    exact three_pow_dvd_of_pow_mem_inner_statedSL hn hp hf hK φ hφpow τ hτ j hj

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
