module

public import CFSG.RankThree.PartOne.CTP.SeitzMaxSLRoot
public import CFSG.LieType.Ree.SuzukiFrobeniusExponents

public section

namespace CFSG.RankThree.PartOne.SEITZ9

open CFSG.LieType.Ree CFSG.RankThree.PartOne.CTP

section Smul

variable {K : Type} [Field K] [Finite K] {k : Subfield K}

theorem eq_univ_of_smul_closed {p : ℕ} (hp : p.Prime) (hK : Nat.card K = Nat.card k ^ p)
    (M : Set K) (h1 : (1 : K) ∈ M) (hadd : ∀ x ∈ M, ∀ y ∈ M, x + y ∈ M)
    (hk : ∀ c ∈ k, ∀ x ∈ M, c * x ∈ M) {μ : K} (hμ : ∀ x ∈ M, μ * x ∈ M) (hμk : μ ∉ k) :
    M = Set.univ := by
  classical
  have : Fintype K := Fintype.ofFinite K
  set A : Set K := {c | ∀ x ∈ M, c * x ∈ M} with hA
  have h0 : (0 : K) ∈ M := by simpa using hk 0 k.zero_mem 1 h1
  have hApow : ∀ c ∈ A, ∀ n : ℕ, c ^ n ∈ A := by
    intro c hc n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih => intro x hx; rw [pow_succ, mul_assoc]; exact ih _ (hc x hx)
  have hAcl : ∀ c ∈ Subfield.closure ((k : Set K) ∪ {μ}), c ∈ A := by
    intro c hc
    induction hc using Subfield.closure_induction with
    | mem c hc =>
      rcases hc with hc | hc
      · exact hk c hc
      · rw [Set.mem_singleton_iff] at hc
        subst hc
        exact hμ
    | one => intro x hx; simpa using hx
    | add c d _ _ hc hd => intro x hx; rw [add_mul]; exact hadd _ (hc x hx) _ (hd x hx)
    | neg c _ hc =>
      intro x hx
      rw [neg_mul]
      simpa using hk (-1) (k.neg_mem k.one_mem) _ (hc x hx)
    | inv c _ hc =>
      by_cases hc0 : c = 0
      · subst hc0
        intro x hx
        simpa using h0
      · have h := FiniteField.pow_card_sub_one_eq_one c hc0
        have hpos : 2 ≤ Fintype.card K := Fintype.one_lt_card
        have hinv : c⁻¹ = c ^ (Fintype.card K - 2) := by
          refine inv_eq_of_mul_eq_one_right ?_
          rw [← pow_succ', show Fintype.card K - 2 + 1 = Fintype.card K - 1 by omega, h]
        rw [hinv]
        exact hApow c hc _
    | mul c d _ _ hc hd => intro x hx; rw [mul_assoc]; exact hc _ (hd x hx)
  have hkF : k ≤ Subfield.closure ((k : Set K) ∪ {μ}) := fun c hc =>
    Subfield.subset_closure (Or.inl hc)
  have hμF : μ ∈ Subfield.closure ((k : Set K) ∪ {μ}) := Subfield.subset_closure (Or.inr rfl)
  rcases subfield_eq_or_eq_top hkF hp hK with h | h
  · rw [h] at hμF
    exact absurd hμF hμk
  · refine Set.eq_univ_of_forall fun z => ?_
    have hz : z ∈ Subfield.closure ((k : Set K) ∪ {μ}) := by rw [h]; exact Subfield.mem_top z
    simpa using hAcl z hz 1 h1

end Smul

section Power

variable {a : ℕ} {K : Type} [Field K] [Finite K]

theorem pow_theta_succ_injective (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Function.Injective fun x : K => x ^ (2 ^ (a + 1) + 1) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hbij, -, -⟩ := suzuki_frobenius_exponents a K hK
  have hne : 2 ^ (a + 1) + 1 ≠ 0 := Nat.succ_ne_zero _
  intro x y hxy
  simp only at hxy
  by_cases hx : x = 0
  · subst hx
    rw [zero_pow hne] at hxy
    exact (pow_eq_zero_iff hne |>.1 hxy.symm).symm
  · by_cases hy : y = 0
    · subst hy
      rw [zero_pow hne] at hxy
      exact (pow_eq_zero_iff hne |>.1 hxy)
    · have h : (Units.mk0 x hx) ^ (2 ^ (a + 1) + 1 : ℤ) =
          (Units.mk0 y hy) ^ (2 ^ (a + 1) + 1 : ℤ) := by
        apply Units.ext
        have e : (2 ^ (a + 1) + 1 : ℤ) = ((2 ^ (a + 1) + 1 : ℕ) : ℤ) := by push_cast; rfl
        rw [e, zpow_natCast, zpow_natCast, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
        exact hxy
      exact congrArg Units.val (hbij.1 h)

variable {k : Subfield K}

theorem exists_pow_theta_succ_eq (hK : Nat.card K = 2 ^ (2 * a + 1)) {c : K} (hc : c ∈ k) :
    ∃ κ ∈ k, κ ^ (2 ^ (a + 1) + 1) = c := by
  classical
  have hinj : Function.Injective fun x : k => x ^ (2 ^ (a + 1) + 1) := by
    intro x y h
    apply Subtype.ext
    apply pow_theta_succ_injective hK
    have := congrArg (fun z : k => (z : K)) h
    simpa using this
  obtain ⟨x, hx⟩ := (Finite.injective_iff_surjective.1 hinj) ⟨c, hc⟩
  refine ⟨x, x.2, ?_⟩
  have := congrArg (fun z : k => (z : K)) hx
  simpa using this

theorem mem_of_pow_theta_succ_mem (hK : Nat.card K = 2 ^ (2 * a + 1)) {x : K}
    (hx : x ^ (2 ^ (a + 1) + 1) ∈ k) : x ∈ k := by
  obtain ⟨κ, hκ, hκx⟩ := exists_pow_theta_succ_eq (a := a) hK hx
  have := pow_theta_succ_injective hK hκx
  exact this ▸ hκ

end Power

end CFSG.RankThree.PartOne.SEITZ9
