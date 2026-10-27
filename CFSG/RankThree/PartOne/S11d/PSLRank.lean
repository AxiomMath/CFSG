module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
import CFSG.LocalAnalysis.SectionRank.GroupRankTransport
public import CFSG.Foundations.Basic
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.RankThree.PartOne

open Subgroup

theorem pRank_eq_of_mulEquiv_of_one_lt {X Y : Type*} [Group X] [Finite X] [Group Y] [Finite Y]
    {p : ℕ} (_hp : 1 < p) (e : X ≃* Y) : CFSG.pRank p X = CFSG.pRank p Y :=
  CFSG.pRank_congr_of_mulEquiv e p

theorem two_le_pRank_of_two_elements {P : Type*} [Group P] [Finite P] {p : ℕ} (hp : p.Prime)
    {e₁ e₂ : P} (hc : Commute e₁ e₂) (h₁ : e₁ ^ p = 1) (h₂ : e₂ ^ p = 1)
    (hi : ∀ i j : ℤ, e₁ ^ i * e₂ ^ j = 1 → (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j) :
    2 ≤ CFSG.pRank p P := CFSG.two_le_pRank_of_commute_independent hp hc h₁ h₂ hi


@[expose] def torusTwoMat {n : ℕ} (hn : 3 ≤ n) {K : Type*} [Field K] (ab : Kˣ × Kˣ) :
    Matrix (Fin n) (Fin n) K :=
  Matrix.diagonal (fun i : Fin n =>
      (((if i = ⟨0, by omega⟩ then ab.1 else 1) *
        (if i = ⟨1, by omega⟩ then ab.2 * ab.1⁻¹ else 1) *
        (if i = ⟨2, by omega⟩ then ab.2⁻¹ else 1) : Kˣ) : K))

theorem torusTwoMat_det {n : ℕ} (hn : 3 ≤ n) {K : Type*} [Field K] (ab : Kˣ × Kˣ) :
    (torusTwoMat hn ab).det = 1 := by
  rw [torusTwoMat, Matrix.det_diagonal, ← Units.coe_prod, Finset.prod_mul_distrib,
    Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_eq', Finset.prod_ite_eq']
  simp

theorem torusTwoMat_mul {n : ℕ} (hn : 3 ≤ n) {K : Type*} [Field K] (ab ab' : Kˣ × Kˣ) :
    torusTwoMat hn (ab * ab') = torusTwoMat hn ab * torusTwoMat hn ab' := by
  rw [torusTwoMat, torusTwoMat, torusTwoMat, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  simp only [Prod.fst_mul, Prod.snd_mul]
  rw [← Units.val_mul]
  congr 1
  by_cases h0 : i = ⟨0, by omega⟩ <;> by_cases h1 : i = ⟨1, by omega⟩ <;>
    by_cases h2 : i = ⟨2, by omega⟩ <;> simp [h0, h1, h2, mul_comm, mul_left_comm, mul_assoc]

open Matrix in
@[expose] def torusTwo {n : ℕ} (hn : 3 ≤ n) {K : Type*} [Field K] (ab : Kˣ × Kˣ) :
    SpecialLinearGroup (Fin n) K :=
  ⟨torusTwoMat hn ab, torusTwoMat_det hn ab⟩

open Matrix in
theorem torusTwo_mul {n : ℕ} (hn : 3 ≤ n) {K : Type*} [Field K] (ab ab' : Kˣ × Kˣ) :
    torusTwo hn (ab * ab') = torusTwo hn ab * torusTwo hn ab' :=
  Subtype.ext (torusTwoMat_mul hn ab ab')

@[expose] noncomputable def torusTwoHom {n : ℕ} (hn : 3 ≤ n) (K : Type*) [Field K] :
    Kˣ × Kˣ →* Matrix.SpecialLinearGroup (Fin n) K :=
  MonoidHom.mk' (torusTwo hn) (torusTwo_mul hn)

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem torusTwo_scalar {n : ℕ} (hn : 3 ≤ n) {K : Type*} [Field K] {a b : Kˣ}
    (h : torusTwo hn (a, b) ∈ scalars n K) : a ^ 3 = 1 ∧ b = a ^ 2 := by
  obtain ⟨c, -, hmat⟩ := mem_scalars.mp h
  have hent : ∀ i : Fin n, (((if i = ⟨0, by omega⟩ then a else 1) *
        (if i = ⟨1, by omega⟩ then b * a⁻¹ else 1) *
        (if i = ⟨2, by omega⟩ then b⁻¹ else 1) : Kˣ) : K) = (c : K) := by
    intro i
    have := congrFun (congrFun hmat i) i
    simpa [torusTwo, torusTwoMat, Matrix.scalar_apply, Matrix.diagonal_apply_eq] using this
  have h0 := hent ⟨0, by omega⟩
  have h1 := hent ⟨1, by omega⟩
  have h2 := hent ⟨2, by omega⟩
  simp at h0 h1 h2
  have ha0 : (a : K) ≠ 0 := a.ne_zero
  have hb0 : (b : K) ≠ 0 := b.ne_zero
  have e1 : (a : K) = (b : K) * (a : K)⁻¹ := h0.trans h1.symm
  have e2 : (a : K) = (b : K)⁻¹ := h0.trans h2.symm
  have hbK : (b : K) = (a : K) ^ 2 := by
    field_simp at e1
    linear_combination -e1
  have h3K : (a : K) ^ 3 = 1 := by
    field_simp at e2
    rw [hbK] at e2
    linear_combination e2
  exact ⟨Units.ext (by simpa using h3K), Units.ext (by simpa using hbK)⟩

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem two_le_pRank_projectiveSL {n : ℕ} (hn : 3 ≤ n) {K : Type} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp3 : p ≠ 3) (hpK : p ∣ Nat.card Kˣ) :
    2 ≤ CFSG.pRank p (projectiveSL n K) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p hpK
  set Θ := torusTwoHom hn K with hΘ
  have hωp : ω ^ p = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  refine two_le_pRank_of_two_elements hp (e₁ := proj n K (Θ (ω, 1)))
    (e₂ := proj n K (Θ (1, ω))) ?_ ?_ ?_ ?_
  · exact ((Commute.all (ω, 1) (1, ω)).map Θ).map (proj n K)
  · rw [← map_pow, ← map_pow]
    have : ((ω, 1) : Kˣ × Kˣ) ^ p = 1 := by
      ext <;> simp [hωp]
    rw [this, map_one, map_one]
  · rw [← map_pow, ← map_pow]
    have : ((1, ω) : Kˣ × Kˣ) ^ p = 1 := by
      ext <;> simp [hωp]
    rw [this, map_one, map_one]
  · intro i j hij
    rw [← map_zpow, ← map_zpow, ← map_zpow, ← map_zpow, ← map_mul, ← map_mul,
      proj_eq_one_iff] at hij
    have hpair : ((ω, 1) : Kˣ × Kˣ) ^ i * ((1, ω) : Kˣ × Kˣ) ^ j = (ω ^ i, ω ^ j) := by
      ext <;> simp
    rw [hpair] at hij
    obtain ⟨h3, hb⟩ := torusTwo_scalar hn hij
    have hai : (ω ^ i) ^ p = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hωp, one_zpow]
    have hcop : Nat.gcd 3 p = 1 := by
      rw [Nat.gcd_comm]
      exact (Nat.coprime_primes hp Nat.prime_three).mpr hp3
    have h1 : ω ^ i = 1 := by
      have := pow_gcd_eq_one.mpr ⟨h3, hai⟩
      rwa [hcop, pow_one] at this
    have h2 : ω ^ j = 1 := by rw [hb, h1]; simp
    have h1' := orderOf_dvd_iff_zpow_eq_one.mpr h1
    have h2' := orderOf_dvd_iff_zpow_eq_one.mpr h2
    rw [hω] at h1' h2'
    exact ⟨h1', h2'⟩

end CFSG.RankThree.PartOne
