module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.ZMod.Basic
import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
import CFSG.Mathlib.Algebra.Order.ProdOneSub
import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthIso
import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthList
import CFSG.LieType.Universal.SpinOmega.Reflections
import CFSG.ClassicalInvolution.Orders.OrthogonalIndex
import CFSG.LieType.Universal.SpinOmega.Range
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.StandardType.ZS

private theorem sum_Icc_two_mul (m : ℕ) :
    ∑ i ∈ Finset.Icc 1 m, 2 * i = m * (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1) (fun i => 2 * i), ih]
    ring

private theorem sum_inv_sq_le (q m : ℕ) (hq : 3 ≤ q) :
    ∑ j ∈ Finset.range m, (1 : ℝ) / (q : ℝ) ^ (2 * (j + 1)) ≤ 1 / 8 := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hq2 : (8 : ℝ) ≤ (q : ℝ) ^ 2 - 1 := by
    have h32 : (3 : ℝ) ≤ q := by exact_mod_cast hq
    nlinarith [sq_nonneg ((q : ℝ) - 3)]
  have hterm : ∀ j ∈ Finset.range m,
      8 * ((1 : ℝ) / (q : ℝ) ^ (2 * (j + 1))) ≤
        1 / (q : ℝ) ^ (2 * j) - 1 / (q : ℝ) ^ (2 * (j + 1)) := by
    intro j _
    have h2 : (0 : ℝ) < (q : ℝ) ^ (2 * (j + 1)) := pow_pos hqpos _
    have hsplit : (q : ℝ) ^ (2 * (j + 1)) = (q : ℝ) ^ (2 * j) * (q : ℝ) ^ 2 := by
      rw [show 2 * (j + 1) = 2 * j + 2 by ring, pow_add]
    have hdiff : 1 / (q : ℝ) ^ (2 * j) - 1 / (q : ℝ) ^ (2 * (j + 1)) =
        ((q : ℝ) ^ 2 - 1) / (q : ℝ) ^ (2 * (j + 1)) := by
      rw [hsplit]
      field_simp
    rw [hdiff, mul_one_div, div_le_div_iff_of_pos_right h2]
    exact hq2
  have hsum : 8 * (∑ j ∈ Finset.range m, (1 : ℝ) / (q : ℝ) ^ (2 * (j + 1))) ≤
      ∑ j ∈ Finset.range m,
        (1 / (q : ℝ) ^ (2 * j) - 1 / (q : ℝ) ^ (2 * (j + 1))) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  have htel : ∑ j ∈ Finset.range m,
      (1 / (q : ℝ) ^ (2 * j) - 1 / (q : ℝ) ^ (2 * (j + 1))) =
        1 - 1 / (q : ℝ) ^ (2 * m) := by
    rw [Finset.sum_range_sub']
    simp
  have hfin : 8 * (∑ j ∈ Finset.range m, (1 : ℝ) / (q : ℝ) ^ (2 * (j + 1))) ≤ 1 := by
    rw [htel] at hsum
    have hpos : (0 : ℝ) ≤ 1 / (q : ℝ) ^ (2 * m) := by positivity
    linarith
  linarith

private theorem sum_Icc_one_eq_sum_range (f : ℕ → ℝ) (m : ℕ) :
    ∑ i ∈ Finset.Icc 1 m, f i = ∑ j ∈ Finset.range m, f (j + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1) f, ih, Finset.sum_range_succ]

private theorem prod_two_mul_sub_one_ge (q m : ℕ) (hq : 3 ≤ q) :
    (7 / 8 : ℝ) * (q : ℝ) ^ (m * (m + 1)) ≤
      ∏ i ∈ Finset.Icc 1 m, ((q : ℝ) ^ (2 * i) - 1) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hq1R : (1 : ℝ) ≤ q := by
    have h32 : (3 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hfac : ∀ i ∈ Finset.Icc 1 m, ((q : ℝ) ^ (2 * i) - 1) =
      (q : ℝ) ^ (2 * i) * (1 - 1 / (q : ℝ) ^ (2 * i)) := by
    intro i _
    have hp : (0 : ℝ) < (q : ℝ) ^ (2 * i) := pow_pos hqpos _
    field_simp
  have hcongr : ∏ i ∈ Finset.Icc 1 m, ((q : ℝ) ^ (2 * i) - 1) =
      ∏ i ∈ Finset.Icc 1 m, ((q : ℝ) ^ (2 * i) * (1 - 1 / (q : ℝ) ^ (2 * i))) :=
    Finset.prod_congr rfl hfac
  rw [hcongr, Finset.prod_mul_distrib]
  have hprod : ∏ i ∈ Finset.Icc 1 m, (q : ℝ) ^ (2 * i) = (q : ℝ) ^ (m * (m + 1)) := by
    rw [Finset.prod_pow_eq_pow_sum, sum_Icc_two_mul]
  have hx0 : ∀ i ∈ Finset.Icc 1 m, 0 ≤ 1 / (q : ℝ) ^ (2 * i) := by
    intro i _; positivity
  have hx1 : ∀ i ∈ Finset.Icc 1 m, 1 / (q : ℝ) ^ (2 * i) ≤ 1 := by
    intro i _
    rw [div_le_one (by positivity)]
    exact one_le_pow₀ hq1R
  have hW := CFSG.one_sub_sum_le_prod_finset (Finset.Icc 1 m)
    (fun i => 1 / (q : ℝ) ^ (2 * i)) hx0 hx1
  have hsum : ∑ i ∈ Finset.Icc 1 m, 1 / (q : ℝ) ^ (2 * i) ≤ 1 / 8 := by
    rw [sum_Icc_one_eq_sum_range]
    exact sum_inv_sq_le q m hq
  have h7 : (7 / 8 : ℝ) ≤ ∏ i ∈ Finset.Icc 1 m, (1 - 1 / (q : ℝ) ^ (2 * i)) := by
    linarith
  rw [hprod, mul_comm (7 / 8)]
  exact mul_le_mul_of_nonneg_left h7 (le_of_lt (pow_pos hqpos _))


private theorem odd_formula_bound (p k : ℕ) (hp3 : 3 ≤ p) :
    (p : ℝ) ^ (k * (2 * k + 1)) ≤
      2 * (2 * (p : ℝ) ^ (k ^ 2) * ∏ i ∈ Finset.Icc 1 k, ((p : ℝ) ^ (2 * i) - 1)) := by
  have hP := prod_two_mul_sub_one_ge p k hp3
  have hX : (0 : ℝ) ≤ (p : ℝ) ^ (k ^ 2) := pow_nonneg (by positivity) _
  have hN : k * (2 * k + 1) = k ^ 2 + k * (k + 1) := by ring
  rw [hN, pow_add]
  have h1 : (p : ℝ) ^ (k ^ 2) * ((7 / 8) * (p : ℝ) ^ (k * (k + 1))) ≤
      (p : ℝ) ^ (k ^ 2) * ∏ i ∈ Finset.Icc 1 k, ((p : ℝ) ^ (2 * i) - 1) :=
    mul_le_mul_of_nonneg_left hP hX
  have hY : (0 : ℝ) ≤ (p : ℝ) ^ (k * (k + 1)) := by positivity
  nlinarith [h1, mul_nonneg hX hY]

private theorem even_plus_formula_bound (p m : ℕ) (hp3 : 3 ≤ p) (hm : 2 ≤ m) :
    (p : ℝ) ^ ((m + 1) * (2 * m + 1)) ≤
      2 * (2 * (p : ℝ) ^ (m * (m + 1)) * ((p : ℝ) ^ (m + 1) - 1) *
        ∏ i ∈ Finset.Icc 1 m, ((p : ℝ) ^ (2 * i) - 1)) := by
  have hp3R : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hqpos : (0 : ℝ) < p := by linarith
  have hP := prod_two_mul_sub_one_ge p m hp3
  have hqA : (0 : ℝ) ≤ (p : ℝ) ^ (m * (m + 1)) := pow_nonneg (by linarith) _
  have hpow27 : (27 : ℝ) ≤ (p : ℝ) ^ (m + 1) := by
    rw [show m + 1 = 3 + (m - 2) by omega, pow_add]
    have hp1 : (1 : ℝ) ≤ p := by linarith
    have h1 : (1 : ℝ) ≤ (p : ℝ) ^ (m - 2) := one_le_pow₀ hp1
    have h3 : (27 : ℝ) ≤ (p : ℝ) ^ 3 := by
      have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hp3R 3
      norm_num at h
      exact h
    calc (27 : ℝ) ≤ (p : ℝ) ^ 3 := h3
      _ = (p : ℝ) ^ 3 * 1 := by ring
      _ ≤ (p : ℝ) ^ 3 * (p : ℝ) ^ (m - 2) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
  have hF : (p : ℝ) ^ (m + 1) ≤ (7 / 2) * ((p : ℝ) ^ (m + 1) - 1) := by linarith
  have h2A : (p : ℝ) ^ (2 * (m * (m + 1))) = ((p : ℝ) ^ (m * (m + 1))) ^ 2 := by
    rw [sq, ← pow_add]
    congr 1
    ring
  calc (p : ℝ) ^ ((m + 1) * (2 * m + 1))
      = (p : ℝ) ^ (2 * (m * (m + 1)) + (m + 1)) := by congr 1; ring
    _ = (p : ℝ) ^ (2 * (m * (m + 1))) * (p : ℝ) ^ (m + 1) := by rw [pow_add]
    _ ≤ (p : ℝ) ^ (2 * (m * (m + 1))) * ((7 / 2) * ((p : ℝ) ^ (m + 1) - 1)) :=
        mul_le_mul_of_nonneg_left hF (pow_nonneg (by linarith) _)
    _ = (7 / 2) * (p : ℝ) ^ (2 * (m * (m + 1))) * ((p : ℝ) ^ (m + 1) - 1) := by ring
    _ = 4 * (p : ℝ) ^ (m * (m + 1)) * ((p : ℝ) ^ (m + 1) - 1) *
          ((7 / 8) * (p : ℝ) ^ (m * (m + 1))) := by rw [h2A]; ring
    _ ≤ 4 * (p : ℝ) ^ (m * (m + 1)) * ((p : ℝ) ^ (m + 1) - 1) *
          ∏ i ∈ Finset.Icc 1 m, ((p : ℝ) ^ (2 * i) - 1) := by
        refine mul_le_mul_of_nonneg_left hP ?_
        have h1 : (1 : ℝ) ≤ (p : ℝ) ^ (m + 1) := by linarith
        positivity
    _ = 2 * (2 * (p : ℝ) ^ (m * (m + 1)) * ((p : ℝ) ^ (m + 1) - 1) *
          ∏ i ∈ Finset.Icc 1 m, ((p : ℝ) ^ (2 * i) - 1)) := by ring

private theorem even_minus_formula_bound (p m : ℕ) (hp3 : 3 ≤ p) :
    (p : ℝ) ^ ((m + 1) * (2 * m + 1)) ≤
      2 * (2 * (p : ℝ) ^ (m * (m + 1)) * ((p : ℝ) ^ (m + 1) + 1) *
        ∏ i ∈ Finset.Icc 1 m, ((p : ℝ) ^ (2 * i) - 1)) := by
  have hp3R : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hqpos : (0 : ℝ) < p := by linarith
  have hP := prod_two_mul_sub_one_ge p m hp3
  set X : ℝ := (p : ℝ) ^ (m * (m + 1)) with hX
  set F : ℝ := (p : ℝ) ^ (m + 1) + 1 with hF
  set P : ℝ := ∏ i ∈ Finset.Icc 1 m, ((p : ℝ) ^ (2 * i) - 1) with hPdef
  have hX0 : (0 : ℝ) ≤ X := by rw [hX]; positivity
  have hF0 : (0 : ℝ) ≤ F := by rw [hF]; positivity
  have hXF : (p : ℝ) ^ (m + 1) ≤ F := by rw [hF]; linarith
  have h2A : (p : ℝ) ^ (2 * (m * (m + 1))) = X * X := by
    rw [hX, ← pow_add]; congr 1; ring
  have hgoal : (p : ℝ) ^ (2 * (m * (m + 1))) * (p : ℝ) ^ (m + 1) ≤ 4 * X * F * P := by
    have h1 : 4 * X * F * ((7 / 8) * X) ≤ 4 * X * F * P :=
      mul_le_mul_of_nonneg_left hP (by positivity)
    have h2 : X * X * (p : ℝ) ^ (m + 1) ≤ 4 * X * F * ((7 / 8) * X) := by
      have h3 : X * X * (p : ℝ) ^ (m + 1) ≤ X * X * F := by
        have := mul_le_mul_of_nonneg_left hXF (mul_nonneg hX0 hX0)
        linarith
      have h4 : X * X * F ≤ 4 * X * F * ((7 / 8) * X) := by
        have h5 : (0 : ℝ) ≤ X * X * F := by positivity
        nlinarith [h5]
      linarith
    have h6 : (p : ℝ) ^ (2 * (m * (m + 1))) * (p : ℝ) ^ (m + 1) = X * X * (p : ℝ) ^ (m + 1) := by
      rw [h2A]
    rw [h6]
    linarith
  calc (p : ℝ) ^ ((m + 1) * (2 * m + 1))
      = (p : ℝ) ^ (2 * (m * (m + 1)) + (m + 1)) := by congr 1; ring
    _ = (p : ℝ) ^ (2 * (m * (m + 1))) * (p : ℝ) ^ (m + 1) := by rw [pow_add]
    _ ≤ 4 * X * F * P := hgoal
    _ = 2 * (2 * (p : ℝ) ^ (m * (m + 1)) * ((p : ℝ) ^ (m + 1) + 1) *
          ∏ i ∈ Finset.Icc 1 m, ((p : ℝ) ^ (2 * i) - 1)) := by
        rw [hX, hF, hPdef]; ring


private theorem order_bound_even {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {n d : ℕ} (hn : Module.finrank K V = n)
    (hd : n = 2 * d) (hd3 : 3 ≤ d) {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hK3 : 3 ≤ Nat.card K) :
    ((Nat.card K : ℕ) : ℝ) ^ (n * (n - 1) / 2) ≤
      2 * (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) : ℝ) := by
  set m := d - 1 with hm
  have hm1 : m + 1 = d := by omega
  have hm2 : 2 ≤ m := by omega
  have hdim : Module.finrank K V = 2 * (m + 1) := by rw [hn, hd, hm1]
  have hexp : n * (n - 1) / 2 = (m + 1) * (2 * m + 1) := by
    have hd' : n = 2 * (m + 1) := by rw [hd, hm1]
    rw [hd']
    have h2 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
    rw [h2, show 2 * (m + 1) * (2 * m + 1) = 2 * ((m + 1) * (2 * m + 1)) by ring,
      Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  rw [hexp]
  by_cases hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q
  · have hf := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type (K := K) hQ
        (m := m) hdim (ε := 1) (Or.inl ⟨rfl, hplus⟩)
    have hreal : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) : ℝ) =
        2 * (Nat.card K : ℝ) ^ (m * (m + 1)) * ((Nat.card K : ℝ) ^ (m + 1) - 1) *
          ∏ i ∈ Finset.Icc 1 m, ((Nat.card K : ℝ) ^ (2 * i) - 1) := by
      rw [← Int.cast_natCast (R := ℝ), hf]
      push_cast
      simp only [pow_mul]
    rw [hreal]
    exact even_plus_formula_bound (Nat.card K) m hK3 hm2
  · have hf := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type (K := K) hQ
        (m := m) hdim (ε := -1) (Or.inr ⟨rfl, hplus⟩)
    have hreal : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) : ℝ) =
        2 * (Nat.card K : ℝ) ^ (m * (m + 1)) * ((Nat.card K : ℝ) ^ (m + 1) + 1) *
          ∏ i ∈ Finset.Icc 1 m, ((Nat.card K : ℝ) ^ (2 * i) - 1) := by
      rw [← Int.cast_natCast (R := ℝ), hf]
      push_cast
      simp only [pow_mul, sub_neg_eq_add]
    rw [hreal]
    exact even_minus_formula_bound (Nat.card K) m hK3

private theorem order_bound_odd {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {n d : ℕ} (hn : Module.finrank K V = n)
    (hd : n = 2 * d + 1) {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hK2 : ringChar K ≠ 2)
    (hK3 : 3 ≤ Nat.card K) :
    ((Nat.card K : ℕ) : ℝ) ^ (n * (n - 1) / 2) ≤
      2 * (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) : ℝ) := by
  have hdim : Module.finrank K V = 2 * d + 1 := by rw [hn, hd]
  have hexp : n * (n - 1) / 2 = d * (2 * d + 1) := by
    rw [hd]
    have h2 : 2 * d + 1 - 1 = 2 * d := by omega
    rw [h2, show (2 * d + 1) * (2 * d) = 2 * (d * (2 * d + 1)) by ring,
      Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  rw [hexp]
  have hf := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_odd (K := K) hK2 hQ hdim
  have hreal : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) : ℝ) =
      2 * (Nat.card K : ℝ) ^ (d ^ 2) *
        ∏ i ∈ Finset.Icc 1 d, ((Nat.card K : ℝ) ^ (2 * i) - 1) := by
    rw [← Int.cast_natCast (R := ℝ), hf]
    push_cast
    simp only [pow_mul]
  rw [hreal]
  exact odd_formula_bound (Nat.card K) d hK3

private theorem order_bound {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {n : ℕ}
    (hn : Module.finrank K V = n) (h5 : 5 ≤ n) {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hK2 : ringChar K ≠ 2)
    (hK3 : 3 ≤ Nat.card K) :
    (Nat.card K) ^ (n * (n - 1) / 2) ≤
      2 * Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  have hR : ((Nat.card K : ℕ) : ℝ) ^ (n * (n - 1) / 2) ≤
      2 * (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) : ℝ) := by
    obtain ⟨d, hd | hd⟩ := Nat.even_or_odd' n
    · exact order_bound_even hn hd (by omega) hQ hK3
    · exact order_bound_odd hn hd hQ hK2 hK3
  exact_mod_cast hR

open CFSG.ClassicalGroups.Orthogonal in
private theorem exists_two_orthogonal_hypPairs {K V : Type*} [Field K] [Finite K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (hodd : Odd (Nat.card K))
    {Q : QuadraticForm K V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (h5 : 5 ≤ Module.finrank K V) : ∃ P₁ P₂ : HypPair Q, P₁.Orth P₂ := by
  obtain ⟨e, he0, hQe⟩ :=
    CFSG.ClassicalInvolution.ModelFacts.exists_isotropic_of_finrank_ge_three hodd Q hQ (by omega)
  obtain ⟨P₁, -⟩ := exists_hypPair hQ hQe he0
  have hW : PolarNondegOn Q P₁.perp := HypPair.polarNondegOn_perp hQ P₁
  have hWnd : (QuadraticMap.polarBilin (Q.restrict P₁.perp)).Nondegenerate :=
    nondegenerate_polarBilin_restrict hW
  have hdim : 3 ≤ Module.finrank K P₁.perp := by
    have := CFSG.ClassicalInvolution.ModelFacts.finrank_hypPair_perp hQ P₁
    omega
  obtain ⟨w, hw0, hQw⟩ :=
    CFSG.ClassicalInvolution.ModelFacts.exists_isotropic_of_finrank_ge_three hodd
      (Q.restrict P₁.perp) hWnd hdim
  obtain ⟨P₂', -⟩ := exists_hypPair hWnd hQw hw0
  let P₂ : HypPair Q :=
    { e := (P₂'.e : V)
      f := (P₂'.f : V)
      Q_e := P₂'.Q_e
      Q_f := P₂'.Q_f
      polar_ef := by rw [← polar_restrict]; exact P₂'.polar_ef }
  refine ⟨P₁, P₂, ?_⟩
  exact ⟨(HypPair.mem_perp.mp P₂'.e.2).1, (HypPair.mem_perp.mp P₂'.f.2).1,
    (HypPair.mem_perp.mp P₂'.e.2).2, (HypPair.mem_perp.mp P₂'.f.2).2⟩

open scoped commutatorElement in
open CFSG.ClassicalGroups.Orthogonal in
private theorem reflect_mul_reflect_mem_commutator {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {P P' : HypPair Q} (h : P.Orth P') {a b : V} (hb : Q b ≠ 0) {t : K} (ht : t ≠ 0)
    (hab : Q a = t ^ 2 * Q b) :
    reflect Q a * reflect Q b ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  have hQa : Q a = Q (t • b) := by rw [hab, map_smul_eq_sq]
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [QuadraticMap.map_zero] at hab
    exact mul_ne_zero (pow_ne_zero 2 ht) hb hab.symm
  have htb0 : t • b ≠ 0 := smul_ne_zero ht fun h0 => hb (by rw [h0, QuadraticMap.map_zero])
  obtain ⟨g, hg, hga⟩ := exists_mem_elementaryGroup_apply_eq hQ h ha0 htb0 hQa
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := elementaryGroup_le_orthogonalGroup Q hg
  have hconj : reflect Q b = g * reflect Q a * g⁻¹ := by
    rw [reflect_conj hgO, hga, CFSG.LieType.Universal.Spin.reflect_smul_of_ne_zero ht]
  have heq : reflect Q a * reflect Q b = ⁅reflect Q a, g⁆ := by
    rw [hconj, commutatorElement_def, reflect_inv]
    group
  rw [heq]
  exact Subgroup.commutator_mem_commutator (reflect_mem_orthogonalGroup Q a) hgO

private abbrev orthCommutator {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q) :=
  ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆.subgroupOf
    (TauCeti.QuadraticMap.orthogonalGroup Q)

private instance orthCommutator_normal {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) : (orthCommutator Q).Normal := by
  have h := Subgroup.normal_subgroupOf_commutator_sup
    (H₁ := TauCeti.QuadraticMap.orthogonalGroup Q) (H₂ := TauCeti.QuadraticMap.orthogonalGroup Q)
  rwa [sup_idem] at h

private theorem mk'_mul_comm_of_commutator_mem {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    {x y : G} (h : x * y * x⁻¹ * y⁻¹ ∈ N) :
    QuotientGroup.mk' N x * QuotientGroup.mk' N y =
      QuotientGroup.mk' N y * QuotientGroup.mk' N x := by
  have h1 : QuotientGroup.mk' N (x * y * x⁻¹ * y⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr h
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  have h2 : QuotientGroup.mk' N x * QuotientGroup.mk' N y =
      (QuotientGroup.mk' N x * QuotientGroup.mk' N y * (QuotientGroup.mk' N x)⁻¹ *
        (QuotientGroup.mk' N y)⁻¹) * (QuotientGroup.mk' N y * QuotientGroup.mk' N x) := by group
  rw [h1, one_mul] at h2
  exact h2

private noncomputable abbrev cosetPlus {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (P : CFSG.ClassicalGroups.Orthogonal.HypPair Q) :
    TauCeti.QuadraticMap.orthogonalGroup Q ⧸ orthCommutator Q :=
  QuotientGroup.mk' (orthCommutator Q)
    (⟨CFSG.ClassicalGroups.Orthogonal.reflect Q (P.e + (1 : K) • P.f),
      CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup Q _⟩ :
      TauCeti.QuadraticMap.orthogonalGroup Q)

private noncomputable abbrev cosetMinus {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (P : CFSG.ClassicalGroups.Orthogonal.HypPair Q) (ν : K) :
    TauCeti.QuadraticMap.orthogonalGroup Q ⧸ orthCommutator Q :=
  QuotientGroup.mk' (orthCommutator Q)
    (⟨CFSG.ClassicalGroups.Orthogonal.reflect Q (P.e + ν • P.f),
      CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup Q _⟩ :
      TauCeti.QuadraticMap.orthogonalGroup Q)

open CFSG.ClassicalGroups.Orthogonal TauCeti.QuadraticMap in
private theorem mk'_reflect_eq_or {K V : Type*} [Field K] [Finite K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [NeZero (2 : K)] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {P₁ P₂ : HypPair Q} (h₁₂ : P₁.Orth P₂)
    {ν : K} (hν : ¬ IsSquare ν) (v : V) [Invertible (Q v)] :
    QuotientGroup.mk' (orthCommutator Q)
        (⟨reflect Q v, reflect_mem_orthogonalGroup Q v⟩ : orthogonalGroup Q) = cosetPlus Q P₁ ∨
    QuotientGroup.mk' (orthCommutator Q)
        (⟨reflect Q v, reflect_mem_orthogonalGroup Q v⟩ : orthogonalGroup Q) =
      cosetMinus Q P₁ ν := by
  have hv0 : Q v ≠ 0 := (isUnit_of_invertible (Q v)).ne_zero
  have hν0 : ν ≠ 0 := fun h => hν (by rw [h]; exact ⟨0, by simp⟩)
  have hv₁ : Q (P₁.e + (1 : K) • P₁.f) = 1 :=
    CFSG.ClassicalInvolution.map_hypPair_add_smul P₁ 1
  have hvν : Q (P₁.e + ν • P₁.f) = ν :=
    CFSG.ClassicalInvolution.map_hypPair_add_smul P₁ ν
  obtain ⟨t, ht, h | h⟩ := CFSG.ClassicalInvolution.exists_sq_or_sq_mul_of_ne_zero hν hv0
  · left
    have hmem : reflect Q v * reflect Q (P₁.e + (1 : K) • P₁.f) ∈
        ⁅orthogonalGroup Q, orthogonalGroup Q⁆ :=
      reflect_mul_reflect_mem_commutator hQ h₁₂ (by rw [hv₁]; exact one_ne_zero) ht
        (by rw [h, hv₁, mul_one])
    rw [show cosetPlus Q P₁ = QuotientGroup.mk' (orthCommutator Q)
        (⟨reflect Q (P₁.e + (1 : K) • P₁.f),
          reflect_mem_orthogonalGroup Q (P₁.e + (1 : K) • P₁.f)⟩ : orthogonalGroup Q) from rfl,
      QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf,
      show (⟨reflect Q v, reflect_mem_orthogonalGroup Q v⟩ : orthogonalGroup Q)⁻¹ =
          ⟨reflect Q v, reflect_mem_orthogonalGroup Q v⟩ from Subtype.ext (reflect_inv Q v)]
    simpa using hmem
  · right
    have hmem : reflect Q v * reflect Q (P₁.e + ν • P₁.f) ∈
        ⁅orthogonalGroup Q, orthogonalGroup Q⁆ :=
      reflect_mul_reflect_mem_commutator hQ h₁₂ (by rw [hvν]; exact hν0) ht
        (by rw [h, hvν])
    rw [show cosetMinus Q P₁ ν = QuotientGroup.mk' (orthCommutator Q)
        (⟨reflect Q (P₁.e + ν • P₁.f),
          reflect_mem_orthogonalGroup Q (P₁.e + ν • P₁.f)⟩ : orthogonalGroup Q) from rfl,
      QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf,
      show (⟨reflect Q v, reflect_mem_orthogonalGroup Q v⟩ : orthogonalGroup Q)⁻¹ =
          ⟨reflect Q v, reflect_mem_orthogonalGroup Q v⟩ from Subtype.ext (reflect_inv Q v)]
    simpa using hmem

open CFSG.ClassicalGroups.Orthogonal TauCeti.QuadraticMap in
private theorem closure_mk'_reflect_eq_top {K V : Type*} [Field K] [Finite K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [NeZero (2 : K)] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {P₁ P₂ : HypPair Q} (h₁₂ : P₁.Orth P₂)
    {ν : K} (hν : ¬ IsSquare ν) :
    Subgroup.closure ({cosetPlus Q P₁, cosetMinus Q P₁ ν} :
      Set (orthogonalGroup Q ⧸ orthCommutator Q)) = ⊤ := by
  let _ : Invertible (2 : K) := invertibleOfNonzero (NeZero.ne (2 : K))
  have hQ' : Q.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mp hQ
  let H : Subgroup (orthogonalGroup Q) :=
    (Subgroup.closure ({cosetPlus Q P₁, cosetMinus Q P₁ ν} :
      Set (orthogonalGroup Q ⧸ orthCommutator Q))).comap (QuotientGroup.mk' (orthCommutator Q))
  have hH : H = ⊤ :=
    subgroup_eq_top_of_reflection_mem Q hQ' H fun v _ => by
      rw [Subgroup.mem_comap]
      have hbridge : reflectionOrthogonal Q v =
          (⟨reflect Q v, reflect_mem_orthogonalGroup Q v⟩ : orthogonalGroup Q) :=
        Subtype.ext (CFSG.ClassicalInvolution.coe_reflectionOrthogonal_eq_reflect v)
      rw [hbridge]
      rcases mk'_reflect_eq_or hQ h₁₂ hν v with h | h <;> rw [h]
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
  refine le_antisymm le_top ?_
  intro x _
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  exact Subgroup.mem_comap.1 (hH ▸ Subgroup.mem_top g)

private theorem card_le_four_of_closure_pair {G : Type*} [Group G] (a b : G)
    (haa : a * a = 1) (hbb : b * b = 1) (hab : a * b = b * a)
    (hgen : Subgroup.closure ({a, b} : Set G) = ⊤) : Nat.card G ≤ 4 := by
  have hmem : ∀ x : G, x ∈ Subgroup.closure ({a, b} : Set G) := by
    intro x; rw [hgen]; exact Subgroup.mem_top x
  have hsurj : Function.Surjective (fun i : Fin 4 => ![1, a, b, a * b] i) := by
    intro x
    rcases CFSG.ClassicalInvolution.eq_one_or_eq_or_eq_mul_of_mem_closure_pair haa hbb hab
      (hmem x) with rfl | rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  simpa using Nat.card_le_card_of_surjective _ hsurj

open CFSG.ClassicalGroups.Orthogonal TauCeti.QuadraticMap in
private theorem relIndex_commutator_orthogonalGroup_le_four {K V : Type*} [Field K] [Finite K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [NeZero (2 : K)]
    {Q : QuadraticForm K V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {P₁ P₂ : HypPair Q}
    (h₁₂ : P₁.Orth P₂) :
    (⁅orthogonalGroup Q, orthogonalGroup Q⁆).relIndex (orthogonalGroup Q) ≤ 4 := by
  classical
  let _ : Invertible (2 : K) := invertibleOfNonzero (NeZero.ne (2 : K))
  have hring : ringChar K ≠ 2 := by
    intro h
    exact (NeZero.ne (2 : K)) ((ringChar.spec K 2).mpr (h ▸ dvd_rfl))
  obtain ⟨ν, hν⟩ := FiniteField.exists_nonsquare hring
  let a : orthogonalGroup Q ⧸ orthCommutator Q := cosetPlus Q P₁
  let b : orthogonalGroup Q ⧸ orthCommutator Q := cosetMinus Q P₁ ν
  have haa : a * a = 1 := by
    rw [show a = QuotientGroup.mk' (orthCommutator Q)
        (⟨reflect Q (P₁.e + (1 : K) • P₁.f),
          reflect_mem_orthogonalGroup Q (P₁.e + (1 : K) • P₁.f)⟩ : orthogonalGroup Q) from rfl,
      ← map_mul,
      show (⟨reflect Q (P₁.e + (1 : K) • P₁.f),
          reflect_mem_orthogonalGroup Q (P₁.e + (1 : K) • P₁.f)⟩ : orthogonalGroup Q) *
        ⟨reflect Q (P₁.e + (1 : K) • P₁.f),
          reflect_mem_orthogonalGroup Q (P₁.e + (1 : K) • P₁.f)⟩ = 1 from
        Subtype.ext (reflect_mul_self Q _),
      map_one]
  have hbb : b * b = 1 := by
    rw [show b = QuotientGroup.mk' (orthCommutator Q)
        (⟨reflect Q (P₁.e + ν • P₁.f),
          reflect_mem_orthogonalGroup Q (P₁.e + ν • P₁.f)⟩ : orthogonalGroup Q) from rfl,
      ← map_mul,
      show (⟨reflect Q (P₁.e + ν • P₁.f),
          reflect_mem_orthogonalGroup Q (P₁.e + ν • P₁.f)⟩ : orthogonalGroup Q) *
        ⟨reflect Q (P₁.e + ν • P₁.f),
          reflect_mem_orthogonalGroup Q (P₁.e + ν • P₁.f)⟩ = 1 from
        Subtype.ext (reflect_mul_self Q _),
      map_one]
  have hab : a * b = b * a := by
    refine mk'_mul_comm_of_commutator_mem (orthCommutator Q) (Subgroup.mem_subgroupOf.mpr ?_)
    exact Subgroup.commutator_mem_commutator (reflect_mem_orthogonalGroup Q _)
      (reflect_mem_orthogonalGroup Q _)
  have htop : Subgroup.closure ({a, b} : Set (orthogonalGroup Q ⧸ orthCommutator Q)) = ⊤ :=
    closure_mk'_reflect_eq_top hQ h₁₂ hν
  exact card_le_four_of_closure_pair a b haa hbb hab htop

theorem pow_le_card_of_commutator_isometry_mem {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V] {n : ℕ}
    (hn : Module.finrank (ZMod p) V = n) (h5 : 5 ≤ n) {Q : QuadraticForm (ZMod p) V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hA : ∀ g h : V ≃ₗ[ZMod p] V, (∀ v, Q (g v) = Q v) → (∀ v, Q (h v) = Q v) →
      g * h * g⁻¹ * h⁻¹ ∈ A) :
    p ^ (n * (n - 1) / 2) ≤ 8 * Nat.card A := by
  have hp3 : 3 ≤ p := by
    have := (Fact.out : p.Prime).two_le
    omega
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
  have hoddZ : Odd (Nat.card (ZMod p)) := by
    rw [Nat.card_eq_fintype_card, ZMod.card]; exact hodd
  have hK2 : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp
  have hK3 : 3 ≤ Nat.card (ZMod p) := by
    rw [Nat.card_eq_fintype_card, ZMod.card]; exact hp3
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp (by simpa using h)
    exact hp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hdvd)
  let _ : NeZero (2 : ZMod p) := ⟨htwo⟩
  let _ : Finite V := Module.finite_of_finite (ZMod p)
  let _ : Finite (V ≃ₗ[ZMod p] V) :=
    Finite.of_injective (fun g : V ≃ₗ[ZMod p] V => (g : V → V))
      (fun g h hgh => LinearEquiv.ext (congrFun hgh))
  let O := TauCeti.QuadraticMap.orthogonalGroup Q
  have hΩA : ⁅O, O⁆ ≤ A := by
    rw [Subgroup.commutator_le]
    intro g hg h hh
    exact hA g h (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg)
      (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hh)
  have hΩcard : Nat.card ↥⁅O, O⁆ ≤ Nat.card A :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hΩA) (Subgroup.inclusion_injective hΩA)
  obtain ⟨P₁, P₂, h₁₂⟩ := exists_two_orthogonal_hypPairs hoddZ hQ (by rw [hn]; omega)
  have hidx : (⁅O, O⁆).relIndex O ≤ 4 := relIndex_commutator_orthogonalGroup_le_four hQ h₁₂
  have hcard : Nat.card O ≤ 4 * Nat.card ↥⁅O, O⁆ := by
    have h := Subgroup.relIndex_mul_card (⁅O, O⁆) O
    rw [inf_of_le_left (Subgroup.commutator_le_self O)] at h
    calc Nat.card O = (⁅O, O⁆).relIndex O * Nat.card ↥⁅O, O⁆ := h.symm
      _ ≤ 4 * Nat.card ↥⁅O, O⁆ := Nat.mul_le_mul_right _ hidx
  have hordZ := order_bound (K := ZMod p) (V := V) hn h5 hQ hK2 hK3
  rw [Nat.card_eq_fintype_card, ZMod.card] at hordZ
  have hord : p ^ (n * (n - 1) / 2) ≤ 2 * Nat.card O := hordZ
  calc p ^ (n * (n - 1) / 2) ≤ 2 * Nat.card O := hord
    _ ≤ 2 * (4 * Nat.card ↥⁅O, O⁆) := Nat.mul_le_mul_left 2 hcard
    _ = 8 * Nat.card ↥⁅O, O⁆ := by ring
    _ ≤ 8 * Nat.card A := Nat.mul_le_mul_left 8 hΩcard

end CFSG.StandardType.ZS
