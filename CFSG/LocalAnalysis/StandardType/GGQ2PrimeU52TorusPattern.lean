module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.GroupWithZero.Units.Fintype
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.GroupTheory.Perm.DomMulAct
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum.NatFactorial

public section

namespace CFSG.GGQ2Prime

private theorem prod_factorial_le_twelve {a b c : ℕ} (ha : a ≤ 3) (hb : b ≤ 3) (hc : c ≤ 3)
    (h : a + b + c = 5) : a.factorial * b.factorial * c.factorial ≤ 12 := by
  interval_cases a <;> interval_cases b <;> interval_cases c <;>
    first | omega | norm_num [Nat.factorial]

theorem exists_two_valued_of_stabilizer_card {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4) {d : Fin 5 → Kˣ} (hd3 : ∀ i, d i ^ 3 = 1) (hprod : ∏ i, d i = 1)
    (hne : d ≠ 1) (h : 24 ≤ Set.ncard {τ : Equiv.Perm (Fin 5) | d ∘ τ = d}) :
    ∃ I : Finset (Fin 5), I.card = 4 ∧ ∃ l ν : Kˣ, l ≠ ν ∧ ∀ i, d i = if i ∈ I then l else ν := by
  classical
  have : Fintype Kˣ := Fintype.ofFinite _
  have hcard3 : Fintype.card Kˣ = 3 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_units, hK]
  set n : Kˣ → ℕ := fun u => (Finset.univ.filter fun a => d a = u).card with hn
  have hncard : ∀ u, Set.ncard {a | d a = u} = n u := fun u => by
    rw [hn]
    simp only
    rw [← Set.ncard_coe_finset]
    congr 1
    ext a
    simp
  rw [DomMulAct.stabilizer_ncard d] at h
  simp only [hncard] at h
  have hsum : ∑ u, n u = 5 := by
    have := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin 5)))
      (t := Finset.univ) (f := d) (fun _ _ => Finset.mem_univ _)
    simpa [hn] using this.symm
  have hex : ∃ u, 4 ≤ n u := by
    by_contra hcon
    push Not at hcon
    obtain e := Fintype.equivFinOfCardEq hcard3
    rw [← Equiv.prod_comp e.symm, Fin.prod_univ_three] at h
    rw [← Equiv.sum_comp e.symm, Fin.sum_univ_three] at hsum
    have := prod_factorial_le_twelve (Nat.lt_succ_iff.1 (hcon (e.symm 0)))
      (Nat.lt_succ_iff.1 (hcon (e.symm 1))) (Nat.lt_succ_iff.1 (hcon (e.symm 2))) hsum
    omega
  obtain ⟨u, hu⟩ := hex
  set I : Finset (Fin 5) := Finset.univ.filter fun a => d a = u with hI
  have hIle : I.card ≤ 5 := by simpa using Finset.card_le_univ I
  have hI4 : I.card = 4 := by
    by_contra hne4
    have h5 : I.card = 5 := by have : 4 ≤ I.card := hu; omega
    have hIuniv : I = Finset.univ := Finset.eq_univ_of_card I (by simpa using h5)
    have hall : ∀ i, d i = u := fun i => by
      have : i ∈ I := by rw [hIuniv]; exact Finset.mem_univ i
      simpa [hI] using this
    have hu5 : u ^ 5 = 1 := by
      have := hprod
      simp only [hall, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
      exact this
    have hu3 : u ^ 3 = 1 := by rw [← hall 0]; exact hd3 0
    have : u = 1 := by simpa using pow_gcd_eq_one.2 ⟨hu5, hu3⟩
    exact hne (funext fun i => by rw [hall i, this]; rfl)
  have hcompl : Iᶜ.card = 1 := by rw [Finset.card_compl, hI4]; simp
  obtain ⟨j₀, hj₀⟩ := Finset.card_eq_one.1 hcompl
  have hj₀I : j₀ ∉ I := by
    have : j₀ ∈ Iᶜ := by rw [hj₀]; exact Finset.mem_singleton_self j₀
    simpa using this
  refine ⟨I, hI4, u, d j₀, ?_, fun i => ?_⟩
  · intro huν
    apply hj₀I
    simp [hI, huν]
  · by_cases hi : i ∈ I
    · rw [if_pos hi]; simpa [hI] using hi
    · rw [if_neg hi]
      have : i ∈ Iᶜ := by simpa using hi
      rw [hj₀, Finset.mem_singleton] at this
      rw [this]

end CFSG.GGQ2Prime
