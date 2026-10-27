module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item228Census2Proof

open Module

variable {L : Type*} [Field L] [CharP L 2] {σ : L →+* L}
  {V : Type*} [AddCommGroup V] [Module L V]

omit [CharP L 2] in
theorem two_smul_eq_zero_charTwo [CharP L 2] (x : V) : (2 : L) • x = 0 := by
  rw [CharTwo.two_eq_zero, zero_smul]

omit [CharP L 2] in
theorem add_self_eq_zero_charTwo (F : Type*) [Field F] [CharP F 2] {W : Type*} [AddCommGroup W]
    [Module F W] (x : W) : x + x = 0 := by
  rw [← two_smul F x, CharTwo.two_eq_zero, zero_smul]

@[expose] def phi5End (c : Module.End L V) : Module.End L V := 1 + c + c ^ 2 + c ^ 3 + c ^ 4

omit [CharP L 2] in
theorem phi5End_mul_sub_one (c : Module.End L V) : phi5End c * (c - 1) = c ^ 5 - 1 := by
  unfold phi5End
  noncomm_ring

omit [CharP L 2] in
theorem sub_one_mul_phi5End (c : Module.End L V) : (c - 1) * phi5End c = c ^ 5 - 1 := by
  unfold phi5End
  noncomm_ring

theorem phi5End_apply_of_fixed {c : Module.End L V} {y : V} (hy : c y = y) : phi5End c y = y := by
  have h2 : (c ^ 2) y = y := by rw [pow_two, Module.End.mul_apply, hy, hy]
  have h3 : (c ^ 3) y = y := by rw [pow_succ, Module.End.mul_apply, hy, h2]
  have h4 : (c ^ 4) y = y := by rw [pow_succ, Module.End.mul_apply, hy, h3]
  simp only [phi5End, LinearMap.add_apply, Module.End.one_apply, hy, h2, h3, h4]
  rw [add_self_eq_zero_charTwo L, zero_add, add_self_eq_zero_charTwo L, zero_add]

theorem decomp_phi5End (c : Module.End L V) (y : V) :
    y = phi5End c y + (c - 1) ((c + c ^ 3) y) := by
  have key : phi5End c + (c - 1) * (c + c ^ 3) = 1 + 2 * (c ^ 2 + c ^ 4) := by
    unfold phi5End
    noncomm_ring
  have h2 : ((2 : Module.End L V) * (c ^ 2 + c ^ 4)) y = 0 := by
    rw [Module.End.mul_apply, show (2 : Module.End L V) = (2 : L) • 1 by
      rw [two_smul, one_add_one_eq_two], LinearMap.smul_apply, Module.End.one_apply,
      two_smul_eq_zero_charTwo]
  have := LinearMap.congr_fun key y
  rw [LinearMap.add_apply (phi5End c), Module.End.mul_apply,
    LinearMap.add_apply (1 : Module.End L V), h2, add_zero, Module.End.one_apply] at this
  exact this.symm

section Unitary

variable (h : V →ₛₗ[σ] V →ₗ[L] L) {c : Module.End L V}

omit [CharP L 2] in
theorem map_sub_one_le {E : Submodule L V} (hEc : ∀ x ∈ E, c x ∈ E) : E.map (c - 1) ≤ E := by
  rintro _ ⟨w, hw, rfl⟩
  rw [LinearMap.sub_apply, Module.End.one_apply]
  exact E.sub_mem (hEc w hw) hw

omit [CharP L 2] in
theorem map_sub_one_invariant {E : Submodule L V} (hEc : ∀ x ∈ E, c x ∈ E) :
    ∀ x ∈ E.map (c - 1), c x ∈ E.map (c - 1) := by
  rintro _ ⟨w, hw, rfl⟩
  refine ⟨c w, hEc w hw, ?_⟩
  simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]

omit [CharP L 2] in
theorem phi5End_apply_eq_zero_of_mem_map (hc5 : c ^ 5 = 1) {E : Submodule L V} {x : V}
    (hx : x ∈ E.map (c - 1)) : phi5End c x = 0 := by
  obtain ⟨w, -, rfl⟩ := hx
  rw [← Module.End.mul_apply, phi5End_mul_sub_one, hc5, sub_self, LinearMap.zero_apply]

theorem eq_zero_of_mem_map_of_fixed (hc5 : c ^ 5 = 1) {E : Submodule L V} {x : V}
    (hx : x ∈ E.map (c - 1)) (hfix : c x = x) : x = 0 := by
  rw [← phi5End_apply_of_fixed hfix]
  exact phi5End_apply_eq_zero_of_mem_map hc5 hx

omit [CharP L 2] in
theorem sesq_fixed_map_eq_zero (hc : ∀ x y, h (c x) (c y) = h x y) {E : Submodule L V}
    {z x : V} (hz : c z = z) (hx : x ∈ E.map (c - 1)) : h z x = 0 := by
  obtain ⟨w, -, rfl⟩ := hx
  rw [LinearMap.sub_apply, Module.End.one_apply, map_sub, ← hc z w, hz, sub_self]

theorem nondeg_map (hc : ∀ x y, h (c x) (c y) = h x y) (hc5 : c ^ 5 = 1) {E : Submodule L V}
    (hEc : ∀ x ∈ E, c x ∈ E) (hEnd : ∀ x ∈ E, (∀ y ∈ E, h y x = 0) → x = 0) {x : V}
    (hx : x ∈ E.map (c - 1)) (hxF : ∀ y ∈ E.map (c - 1), h y x = 0) : x = 0 := by
  refine hEnd x (map_sub_one_le hEc hx) fun y hy => ?_
  rw [decomp_phi5End c y, map_add, LinearMap.add_apply]
  have hfix : c (phi5End c y) = phi5End c y := by
    have := LinearMap.congr_fun (sub_one_mul_phi5End c) y
    rw [hc5, sub_self, LinearMap.zero_apply, Module.End.mul_apply, LinearMap.sub_apply,
      Module.End.one_apply] at this
    exact sub_eq_zero.mp this
  have hmem : (c + c ^ 3) y ∈ E := by
    rw [LinearMap.add_apply]
    refine E.add_mem (hEc y hy) ?_
    rw [pow_succ, Module.End.mul_apply, pow_two, Module.End.mul_apply]
    exact hEc _ (hEc _ (hEc y hy))
  rw [sesq_fixed_map_eq_zero h hc hfix hx, hxF _ ⟨_, hmem, rfl⟩, add_zero]

omit [CharP L 2] in
theorem pow_apply_of_eigen' {x : V} {μ : L} (hμ : c x = μ • x) (k : ℕ) : (c ^ k) x = μ ^ k • x := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hμ, smul_smul, pow_succ]

theorem not_eigen_of_mem_map (hc5 : c ^ 5 = 1) (h5 : ∀ μ : L, μ ^ 5 = 1 → μ = 1)
    {E : Submodule L V} {x : V} (hx : x ∈ E.map (c - 1)) (hx0 : x ≠ 0) (μ : L) :
    c x ≠ μ • x := by
  intro hμ
  have h1 : μ ^ 5 • x = x := by rw [← pow_apply_of_eigen' hμ, hc5, Module.End.one_apply]
  have hμ5 : μ ^ 5 = 1 := by
    have : (μ ^ 5 - 1) • x = 0 := by rw [sub_smul, h1, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right hx0)
  rw [h5 μ hμ5, one_smul] at hμ
  exact hx0 (eq_zero_of_mem_map_of_fixed hc5 hx hμ)

theorem linearIndependent_pair_of_mem_map (hc5 : c ^ 5 = 1) (h5 : ∀ μ : L, μ ^ 5 = 1 → μ = 1)
    {E : Submodule L V} {x : V} (hx : x ∈ E.map (c - 1)) (hx0 : x ≠ 0) :
    LinearIndependent L ![x, c x] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  by_cases ht : t = 0
  · subst ht
    rw [zero_smul, add_zero] at hst
    exact ⟨(smul_eq_zero.mp hst).resolve_right hx0, rfl⟩
  · exfalso
    apply not_eigen_of_mem_map hc5 h5 hx hx0 (-(s / t))
    have h1 : t • c x = -(s • x) := eq_neg_of_add_eq_zero_right hst
    calc c x = t⁻¹ • (t • c x) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
      _ = -(s / t) • x := by rw [h1, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]

omit [CharP L 2] in
theorem span_pair_invariant {x : V} (hx2 : c (c x) ∈ Submodule.span L (Set.range ![x, c x])) :
    ∀ y ∈ Submodule.span L (Set.range ![x, c x]),
      c y ∈ Submodule.span L (Set.range ![x, c x]) := by
  have hle : Submodule.span L (Set.range ![x, c x]) ≤
      (Submodule.span L (Set.range ![x, c x])).comap c := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact Submodule.subset_span ⟨1, rfl⟩
    · exact hx2
  exact fun y hy => hle hy

theorem phi5_ne_zero (h5 : ∀ μ : L, μ ^ 5 = 1 → μ = 1) (μ : L) :
    μ ^ 4 + μ ^ 3 + μ ^ 2 + μ + 1 ≠ 0 := by
  intro hμ
  have h2 : (2 : L) = 0 := CharTwo.two_eq_zero
  have hμ5 : μ ^ 5 = 1 := by linear_combination (μ - 1) * hμ
  rw [h5 μ hμ5] at hμ
  exact one_ne_zero (by linear_combination hμ - 2 * h2 : (1 : L) = 0)

theorem sq_mem_span_pair (hc5 : c ^ 5 = 1) (h5 : ∀ μ : L, μ ^ 5 = 1 → μ = 1)
    {E : Submodule L V} [FiniteDimensional L E] (hEc : ∀ x ∈ E, c x ∈ E)
    (hdim : finrank L E ≤ 3) {x : V} (hx : x ∈ E.map (c - 1)) :
    c (c x) ∈ Submodule.span L (Set.range ![x, c x]) := by
  by_contra hnot
  have hx0 : x ≠ 0 := by
    rintro rfl
    apply hnot
    rw [map_zero, map_zero]
    exact Submodule.zero_mem _
  have hFc := map_sub_one_invariant hEc
  have hli2 := linearIndependent_pair_of_mem_map hc5 h5 hx hx0
  have hli3 : LinearIndependent L (Fin.cons (c (c x)) ![x, c x] : Fin 3 → V) :=
    linearIndependent_finCons.mpr ⟨hli2, hnot⟩
  set S := Submodule.span L (Set.range (Fin.cons (c (c x)) ![x, c x] : Fin 3 → V)) with hSdef
  have hS : finrank L S = 3 := by rw [finrank_span_eq_card hli3, Fintype.card_fin]
  have hcx : c x ∈ E.map (c - 1) := hFc x hx
  have hccx : c (c x) ∈ E.map (c - 1) := hFc _ hcx
  have hSF : S ≤ E.map (c - 1) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hccx
    · exact hx
    · exact hcx
  have : FiniteDimensional L (E.map (c - 1)) :=
    Submodule.finiteDimensional_of_le (map_sub_one_le hEc)
  have hFE : finrank L (E.map (c - 1)) ≤ 3 :=
    (Submodule.finrank_mono (map_sub_one_le hEc)).trans hdim
  have hSeq : S = E.map (c - 1) := Submodule.eq_of_le_of_finrank_le hSF (by omega)
  have hc3 : c (c (c x)) ∈ S := hSeq ▸ hFc _ hccx
  obtain ⟨r, hr₀⟩ := (Submodule.mem_span_range_iff_exists_fun L).mp hc3
  have hr : r 0 • c (c x) + r 1 • x + r 2 • c x = c (c (c x)) := by
    rw [← hr₀]
    simp [Fin.sum_univ_succ, add_assoc]
  set γ := r 0
  set α := r 1
  set β := r 2
  have hc4 : c (c (c (c x))) = γ • c (c (c x)) + α • c x + β • c (c x) := by
    conv_lhs => rw [← hr]
    rw [map_add, map_add, map_smul, map_smul, map_smul]
  have hphi := phi5End_apply_eq_zero_of_mem_map hc5 hx
  have hphi' : x + c x + c (c x) + c (c (c x)) + c (c (c (c x))) = 0 := by
    have e2 : (c ^ 2) x = c (c x) := by rw [pow_two, Module.End.mul_apply]
    have e3 : (c ^ 3) x = c (c (c x)) := by
      rw [pow_succ, Module.End.mul_apply, pow_two, Module.End.mul_apply]
    have e4 : (c ^ 4) x = c (c (c (c x))) := by
      rw [pow_succ, Module.End.mul_apply, pow_succ, Module.End.mul_apply, pow_two,
        Module.End.mul_apply]
    simpa only [phi5End, LinearMap.add_apply, Module.End.one_apply, e2, e3, e4] using hphi
  have hsum : (1 + γ + γ ^ 2 + β) • c (c x) + (1 + α + γ * α) • x +
      (1 + β + γ * β + α) • c x = 0 := by
    rw [← hphi']
    linear_combination (norm := module) (1 + γ) • hr - hc4
  have hcoef := (Fintype.linearIndependent_iff.mp hli3)
    ![1 + γ + γ ^ 2 + β, 1 + α + γ * α, 1 + β + γ * β + α] (by
      simpa [Fin.sum_univ_succ, add_assoc] using hsum)
  have e3 : 1 + γ + γ ^ 2 + β = 0 := hcoef 0
  have e1 : 1 + α + γ * α = 0 := hcoef 1
  have e2 : 1 + β + γ * β + α = 0 := hcoef 2
  have h2 : (2 : L) = 0 := CharTwo.two_eq_zero
  apply phi5_ne_zero h5 (1 + γ)
  linear_combination (1 + γ) ^ 2 * e3 + (1 + γ) * e2 + e1 +
    ((1 + γ) ^ 3 - γ * (1 + γ) ^ 2 - β * (1 + γ) - α) * (1 + γ) * h2

theorem map_eq_span_pair [FiniteDimensional L V] (hc5 : c ^ 5 = 1)
    (h5 : ∀ μ : L, μ ^ 5 = 1 → μ = 1) {E : Submodule L V} (hEc : ∀ x ∈ E, c x ∈ E)
    (hdim : finrank L E ≤ 3) {v : V} (hv : v ∈ E.map (c - 1)) (hv0 : v ≠ 0) :
    E.map (c - 1) = Submodule.span L (Set.range ![v, c v]) := by
  have hFc := map_sub_one_invariant hEc
  have : FiniteDimensional L (E.map (c - 1)) :=
    Submodule.finiteDimensional_of_le (map_sub_one_le hEc)
  have hFE : finrank L (E.map (c - 1)) ≤ 3 :=
    (Submodule.finrank_mono (map_sub_one_le hEc)).trans hdim
  have hplane : ∀ x ∈ E.map (c - 1), x ≠ 0 →
      Submodule.span L (Set.range ![x, c x]) ≤ E.map (c - 1) ∧
      finrank L (Submodule.span L (Set.range ![x, c x])) = 2 ∧
      ∀ y ∈ Submodule.span L (Set.range ![x, c x]),
        c y ∈ Submodule.span L (Set.range ![x, c x]) := by
    intro x hx hx0
    refine ⟨?_, ?_, span_pair_invariant (sq_mem_span_pair hc5 h5 hEc hdim hx)⟩
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact hx
      · exact hFc x hx
    · rw [finrank_span_eq_card (linearIndependent_pair_of_mem_map hc5 h5 hx hx0)]
      simp
  obtain ⟨hPF, hP2, hPc⟩ := hplane v hv hv0
  by_contra hne
  have hlt : Submodule.span L (Set.range ![v, c v]) < E.map (c - 1) :=
    lt_of_le_of_ne hPF (Ne.symm hne)
  have hF3 : finrank L (E.map (c - 1)) = 3 := by
    have := Submodule.finrank_lt_finrank_of_lt hlt
    omega
  obtain ⟨w, hwF, hwP⟩ := IsConcreteLE.exists_of_lt hlt
  have hw0 : w ≠ 0 := fun h0 => hwP (h0 ▸ Submodule.zero_mem _)
  obtain ⟨hQF, hQ2, hQc⟩ := hplane w hwF hw0
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span L (Set.range ![v, c v]))
    (Submodule.span L (Set.range ![w, c w]))
  have hsupF : finrank L ↥(Submodule.span L (Set.range ![v, c v]) ⊔
      Submodule.span L (Set.range ![w, c w])) ≤ 3 :=
    (Submodule.finrank_mono (sup_le hPF hQF)).trans hF3.le
  have hinf_ne : Submodule.span L (Set.range ![v, c v]) ⊓
      Submodule.span L (Set.range ![w, c w]) ≠ ⊥ := by
    intro hb
    rw [hb, finrank_bot] at hsup
    omega
  obtain ⟨u, huPQ, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hinf_ne
  have huF : u ∈ E.map (c - 1) := hPF huPQ.1
  obtain ⟨-, hU2, -⟩ := hplane u huF hu0
  have hUPQ : Submodule.span L (Set.range ![u, c u]) ≤ Submodule.span L (Set.range ![v, c v]) ⊓
      Submodule.span L (Set.range ![w, c w]) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact huPQ
    · exact ⟨hPc u huPQ.1, hQc u huPQ.2⟩
  have hPQ2 : 2 ≤ finrank L ↥(Submodule.span L (Set.range ![v, c v]) ⊓
      Submodule.span L (Set.range ![w, c w])) := hU2 ▸ Submodule.finrank_mono hUPQ
  have hPeq : Submodule.span L (Set.range ![v, c v]) ⊓ Submodule.span L (Set.range ![w, c w]) =
      Submodule.span L (Set.range ![v, c v]) :=
    Submodule.eq_of_le_of_finrank_le inf_le_left (by omega)
  have hPQ : Submodule.span L (Set.range ![v, c v]) = Submodule.span L (Set.range ![w, c w]) :=
    Submodule.eq_of_le_of_finrank_le (hPeq ▸ inf_le_right) (by omega)
  exact hwP (by rw [hPQ]; exact Submodule.subset_span ⟨0, rfl⟩)

theorem false_of_plane_coeffs {q : ℕ} (hσ : ∀ x, σ x = x ^ q) (hq : q % 15 = 2 ∨ q % 15 = 8)
    {α β : L} (h1 : σ α + σ β * α = 0) (h2 : α ^ 3 * β = 1) (h3 : α ^ 4 + α ^ 2 * β + β ^ 2 = 0) :
    False := by
  have hc2 : (2 : L) = 0 := CharTwo.two_eq_zero
  have hα0 : α ≠ 0 := by
    rintro rfl
    simp at h2
  have h10 : α ^ 10 + α ^ 5 + 1 = 0 := by
    linear_combination α ^ 6 * h3 - (α ^ 5 + α ^ 3 * β + 1) * h2
  have h15 : α ^ 15 = 1 := by linear_combination (α ^ 5 - 1) * h10
  have h2' : σ α ^ 3 * σ β = 1 := by rw [← map_pow, ← map_mul, h2, map_one]
  have h4 : σ α ^ 4 = α := by
    linear_combination σ α ^ 3 * h1 - α * h2' - α * hc2
  rw [hσ, ← pow_mul] at h4
  have hα1 : α = 1 := by
    rcases hq with hq | hq
    · have hq' : q * 4 = 15 * (4 * (q / 15)) + 8 := by omega
      have h8 : α ^ 8 = α := by
        calc α ^ 8 = α ^ (q * 4) := by rw [hq', pow_add, pow_mul, h15, one_pow, one_mul]
          _ = α := h4
      have h7 : α ^ 7 = 1 := by
        have : α * (α ^ 7 - 1) = 0 := by linear_combination h8
        exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hα0)
      calc α = (α ^ 7) ^ 2 * α := by rw [h7, one_pow, one_mul]
        _ = α ^ 15 := by ring
        _ = 1 := h15
    · have h32 : α ^ 2 = α := by
        have hq' : q * 4 = 15 * (4 * (q / 15)) + 32 := by omega
        have : α ^ 32 = α := by
          calc α ^ 32 = α ^ (q * 4) := by rw [hq', pow_add, pow_mul, h15, one_pow, one_mul]
            _ = α := h4
        calc α ^ 2 = (α ^ 15) ^ 2 * α ^ 2 := by rw [h15, one_pow, one_mul]
          _ = α ^ 32 := by ring
          _ = α := this
      have : α * (α - 1) = 0 := by linear_combination h32
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hα0)
  rw [hα1] at h10
  exact one_ne_zero (by linear_combination h10 - hc2 : (1 : L) = 0)

theorem apply_eq_of_unitary_le_three [FiniteDimensional L V] {q : ℕ} (hσ : ∀ x, σ x = x ^ q)
    (hq : q % 15 = 2 ∨ q % 15 = 8) (hc : ∀ x y, h (c x) (c y) = h x y) (hc5 : c ^ 5 = 1)
    (h5 : ∀ μ : L, μ ^ 5 = 1 → μ = 1) {E : Submodule L V} (hEc : ∀ x ∈ E, c x ∈ E)
    (hEnd : ∀ x ∈ E, (∀ y ∈ E, h y x = 0) → x = 0) (hdim : finrank L E ≤ 3) {x : V}
    (hx : x ∈ E) : c x = x := by
  have hFc := map_sub_one_invariant hEc
  have hc5' : ∀ y, c (c (c (c (c y)))) = y := by
    intro y
    have := LinearMap.congr_fun hc5 y
    simpa [pow_succ, Module.End.mul_apply] using this
  have hF : E.map (c - 1) = ⊥ := by
    by_contra hne
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hFeq := map_eq_span_pair hc5 h5 hEc hdim hv hv0
    have hli := linearIndependent_pair_of_mem_map hc5 h5 hv hv0
    have hccv : c (c v) ∈ Submodule.span L (Set.range ![v, c v]) := hFeq ▸ hFc _ (hFc v hv)
    obtain ⟨r, hr₀⟩ := (Submodule.mem_span_range_iff_exists_fun L).mp hccv
    have hr : r 0 • v + r 1 • c v = c (c v) := by
      rw [← hr₀]
      simp [Fin.sum_univ_succ]
    set β := r 0
    set α := r 1
    have hr3 : c (c (c v)) = β • c v + α • c (c v) := by
      conv_lhs => rw [← hr]
      rw [map_add, map_smul, map_smul]
    have hr4 : c (c (c (c v))) = β • c (c v) + α • c (c (c v)) := by
      conv_lhs => rw [hr3]
      rw [map_add, map_smul, map_smul]
    have hr5 : c (c (c (c (c v)))) = β • c (c (c v)) + α • c (c (c (c v))) := by
      conv_lhs => rw [hr4]
      rw [map_add, map_smul, map_smul]
    have hsq : ∀ y ∈ E.map (c - 1), c (c y) = α • c y + β • y := by
      intro y hy
      rw [hFeq] at hy
      obtain ⟨s, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun L).mp hy
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, map_add, map_smul]
      linear_combination (norm := module) (-(s 0)) • hr + (s 1) • hr3
    have hadj : ∀ y ∈ E.map (c - 1), c (c (c y)) = σ α • c (c (c (c y))) + σ β • y := by
      intro y hy
      have hz : c (c (c y)) - (σ α • c (c (c (c y))) + σ β • y) ∈ E.map (c - 1) :=
        Submodule.sub_mem _ (hFc _ (hFc _ (hFc y hy)))
          (Submodule.add_mem _ (Submodule.smul_mem _ _ (hFc _ (hFc _ (hFc _ (hFc y hy)))))
            (Submodule.smul_mem _ _ hy))
      refine sub_eq_zero.mp (nondeg_map h hc hc5 hEc hEnd hz fun w hw => ?_)
      have e3 : h w (c (c (c y))) = h (c (c w)) y := by
        rw [← hc w, ← hc (c w), hc5' y]
      have e4 : h w (c (c (c (c y)))) = h (c w) y := by
        rw [← hc w, hc5' y]
      have e2 : h (c (c w)) y = σ α * h (c w) y + σ β * h w y := by
        rw [hsq w hw, map_add, LinearMap.add_apply, map_smulₛₗ, map_smulₛₗ, LinearMap.smul_apply,
          LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
      rw [map_sub, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, e3, e4, e2]
      ring
    have h1 := hadj v hv
    have h1' : v = σ α • c v + σ β • c (c v) := by
      have := congrArg (fun w => c (c w)) h1
      simpa only [map_add, map_smul, hc5'] using this
    have hcoef1 : (σ β * β - 1) • v + (σ α + σ β * α) • c v = 0 := by
      linear_combination (norm := module) -h1' + σ β • hr
    obtain ⟨-, hs2⟩ := LinearIndependent.pair_iff.mp hli _ _ hcoef1
    have hcoef2 : (α ^ 3 * β + 2 * α * β ^ 2 - 1) • v + (α ^ 4 + 3 * α ^ 2 * β + β ^ 2) • c v =
        0 := by
      linear_combination (norm := module) hc5' v - hr5 - α • hr4 - (β + α ^ 2) • hr3 +
        (α ^ 3 + 2 * α * β) • hr
    obtain ⟨ht1, ht2⟩ := LinearIndependent.pair_iff.mp hli _ _ hcoef2
    have hc2 : (2 : L) = 0 := CharTwo.two_eq_zero
    exact false_of_plane_coeffs hσ hq hs2 (by linear_combination ht1 - (α * β ^ 2) * hc2)
      (by linear_combination ht2 - (α ^ 2 * β) * hc2)
  have hmem : (c - 1) x ∈ E.map (c - 1) := ⟨x, hx, rfl⟩
  rw [hF, Submodule.mem_bot, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hmem
  exact hmem

omit [CharP L 2] in
theorem sigma_cube_root {q : ℕ} (hσ : ∀ x, σ x = x ^ q) (hq3 : q % 3 = 2) {μ : L}
    (hμ : μ ^ 3 = 1) : σ μ = μ ^ 2 := by
  rw [hσ, ← Nat.div_add_mod q 3, hq3, pow_add, pow_mul, hμ, one_pow, one_mul]

omit [CharP L 2] in
theorem sesq_eigen_eq_zero {q : ℕ} (hσ : ∀ x, σ x = x ^ q) (hq3 : q % 3 = 2)
    {a : Module.End L V} (ha : ∀ x y, h (a x) (a y) = h x y) {μ ν : L} (hμ : μ ^ 3 = 1)
    (hμν : μ ≠ ν) {x y : V} (hx : a x = μ • x) (hy : a y = ν • y) : h x y = 0 := by
  have h1 : h x y = μ ^ 2 * ν * h x y := by
    calc h x y = h (a x) (a y) := (ha x y).symm
      _ = h (μ • x) (ν • y) := by rw [hx, hy]
      _ = σ μ * (ν * h x y) := by
        simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring
      _ = μ ^ 2 * ν * h x y := by rw [sigma_cube_root hσ hq3 hμ]; ring
  by_contra hne
  apply hμν
  have h2 : μ ^ 2 * ν = 1 := by
    have : (μ ^ 2 * ν - 1) * h x y = 0 := by linear_combination -h1
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hne)
  linear_combination ν * hμ - μ * h2

omit [CharP L 2] in
theorem eigen_proj_apply {a : Module.End L V} (ha3 : ∀ y, a (a (a y)) = y) {μ : L}
    (hμ : μ ^ 3 = 1) (y : V) :
    a (y + μ ^ 2 • a y + μ • a (a y)) = μ • (y + μ ^ 2 • a y + μ • a (a y)) := by
  rw [map_add, map_add, map_smul, map_smul, ha3]
  linear_combination (norm := module) -(hμ • a y)

theorem eigen_proj_sum {a : Module.End L V} {ω : L} (hω : ω ^ 2 + ω + 1 = 0) (y : V) :
    (y + (1 : L) ^ 2 • a y + (1 : L) • a (a y)) + (y + ω ^ 2 • a y + ω • a (a y)) +
      (y + (ω ^ 2) ^ 2 • a y + ω ^ 2 • a (a y)) = y := by
  have hc2 : (2 : L) = 0 := CharTwo.two_eq_zero
  have h4 : 1 + ω ^ 2 + (ω ^ 2) ^ 2 = 0 := by linear_combination (ω ^ 2 - ω + 1) * hω
  linear_combination (norm := module) h4 • a y + hω • a (a y) + hc2 • y

theorem no_commuting_unitary_three_five [FiniteDimensional L V] (hV : finrank L V = 4) {q : ℕ}
    (hσ : ∀ x, σ x = x ^ q) (hq15 : q % 15 = 2 ∨ q % 15 = 8) (h5 : ∀ μ : L, μ ^ 5 = 1 → μ = 1)
    {ω : L} (hω : ω ^ 2 + ω + 1 = 0) (hnd : ∀ x, (∀ y, h y x = 0) → x = 0)
    {a : Module.End L V} (ha : ∀ x y, h (a x) (a y) = h x y) (hc : ∀ x y, h (c x) (c y) = h x y)
    (hac : a * c = c * a) (ha3 : a ^ 3 = 1) (hasc : ∀ μ : L, a ≠ μ • 1) (hc5 : c ^ 5 = 1)
    (hc1 : c ≠ 1) : False := by
  have hq3 : q % 3 = 2 := by omega
  have hc2 : (2 : L) = 0 := CharTwo.two_eq_zero
  have ha3' : ∀ y, a (a (a y)) = y := by
    intro y
    have := LinearMap.congr_fun ha3 y
    simpa [pow_succ, Module.End.mul_apply] using this
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hroots : ∀ μ : L, μ = 1 ∨ μ = ω ∨ μ = ω ^ 2 → μ ^ 3 = 1 := by
    rintro μ (rfl | rfl | rfl)
    · exact one_pow 3
    · exact hω3
    · rw [← pow_mul, show 2 * 3 = 3 * 2 by rfl, pow_mul, hω3, one_pow]
  have hω1 : ω ≠ 1 := by
    rintro rfl
    exact one_ne_zero (by linear_combination hω - hc2 : (1 : L) = 0)
  have hω21 : ω ^ 2 ≠ 1 := by
    intro h2
    exact hω1 (by linear_combination hω3 - ω * h2)
  have hωω2 : ω ≠ ω ^ 2 := by
    intro h2
    exact hω1 (by linear_combination (ω - 1) * hω + (ω - 1) * h2 - (ω - 1) * ω * hc2)
  set E : L → Submodule L V := fun μ => LinearMap.ker (a - μ • 1) with hE
  have hmemE : ∀ μ x, x ∈ E μ ↔ a x = μ • x := by
    intro μ x
    simp only [hE, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, sub_eq_zero]
  have hEc : ∀ μ, ∀ x ∈ E μ, c x ∈ E μ := by
    intro μ x hx
    rw [hmemE] at hx ⊢
    rw [← Module.End.mul_apply, hac, Module.End.mul_apply, hx, map_smul]
  have hEdim : ∀ μ, finrank L (E μ) ≤ 3 := by
    intro μ
    have hne : E μ ≠ ⊤ := by
      intro htop
      apply hasc μ
      ext x
      have hx : x ∈ E μ := htop ▸ Submodule.mem_top
      rw [hmemE] at hx
      rw [hx]
      rfl
    have := Submodule.finrank_lt hne
    omega
  have hP : ∀ μ, μ ^ 3 = 1 → ∀ y, y + μ ^ 2 • a y + μ • a (a y) ∈ E μ := fun μ hμ y =>
    (hmemE μ _).mpr (eigen_proj_apply ha3' hμ y)
  have hnondeg : ∀ μ, μ ^ 3 = 1 → ∀ x ∈ E μ, (∀ y ∈ E μ, h y x = 0) → x = 0 := by
    intro μ hμ x hx hxE
    have hterm : ∀ ν, ν ^ 3 = 1 → ∀ z ∈ E ν, h z x = 0 := by
      intro ν hν z hz
      by_cases hνμ : ν = μ
      · subst hνμ
        exact hxE z hz
      · exact sesq_eigen_eq_zero h hσ hq3 ha hν hνμ ((hmemE ν z).mp hz) ((hmemE μ x).mp hx)
    refine hnd x fun y => ?_
    rw [← eigen_proj_sum hω y, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply,
      hterm 1 (one_pow 3) _ (hP 1 (one_pow 3) y), hterm ω hω3 _ (hP ω hω3 y),
      hterm (ω ^ 2) (hroots _ (Or.inr (Or.inr rfl))) _ (hP _ (hroots _ (Or.inr (Or.inr rfl))) y),
      add_zero, add_zero]
  have hfix : ∀ μ, μ ^ 3 = 1 → ∀ x ∈ E μ, c x = x := fun μ hμ x hx =>
    apply_eq_of_unitary_le_three h hσ hq15 hc hc5 h5 (hEc μ) (hnondeg μ hμ) (hEdim μ) hx
  apply hc1
  ext y
  rw [Module.End.one_apply, ← eigen_proj_sum hω y, map_add, map_add,
    hfix 1 (one_pow 3) _ (hP 1 (one_pow 3) y), hfix ω hω3 _ (hP ω hω3 y),
    hfix (ω ^ 2) (hroots _ (Or.inr (Or.inr rfl))) _ (hP _ (hroots _ (Or.inr (Or.inr rfl))) y)]

end Unitary

end CFSG.RankThree.PartTwo.Sec21.Item228Census2Proof
