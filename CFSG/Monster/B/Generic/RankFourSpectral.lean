module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Data.Rat.Star
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Monster.B.Generic

open Polynomial Module Matrix

theorem natDegree_dvd_finrank_of_aeval_eq_zero {K M : Type*} [Field K] [AddCommGroup M]
    [Module K M] {f : K[X]} (hf : Irreducible f) (T : Module.End K M) (hT : aeval T f = 0) :
    f.natDegree ∣ Module.finrank K M := by
  have := Fact.mk hf
  let φ : AdjoinRoot f →ₐ[K] Module.End K M := Ideal.Quotient.liftₐ (Ideal.span {f}) (aeval T)
    fun a ha => by
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      rw [map_mul, hT, mul_zero]
  let _ : Module (AdjoinRoot f) M := Module.compHom M φ.toRingHom
  have : IsScalarTower K (AdjoinRoot f) M := ⟨fun c a m => by
    change φ (c • a) m = c • φ a m
    rw [map_smul]
    rfl⟩
  have h1 : Module.finrank K (AdjoinRoot f) = f.natDegree := by
    rw [(AdjoinRoot.powerBasis hf.ne_zero).finrank, AdjoinRoot.powerBasis_dim]
  rw [← Module.finrank_mul_finrank K (AdjoinRoot f) M, h1]
  exact dvd_mul_right _ _

theorem apply_mem_ker_aeval {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    (T : Module.End K M) (p : K[X]) {v : M} (hv : v ∈ LinearMap.ker (aeval T p)) :
    T v ∈ LinearMap.ker (aeval T p) := by
  rw [LinearMap.mem_ker] at hv ⊢
  have hc : aeval T p * T = T * aeval T p := by
    calc aeval T p * T = aeval T (p * X) := by rw [map_mul, aeval_X]
      _ = aeval T (X * p) := by rw [mul_comm]
      _ = T * aeval T p := by rw [map_mul, aeval_X]
  rw [← Module.End.mul_apply, hc, Module.End.mul_apply, hv, map_zero]

theorem coe_aeval_restrict_apply {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    (T : Module.End K M) {W : Submodule K M} (hW : ∀ v ∈ W, T v ∈ W) (p : K[X]) (w : W) :
    ((aeval (T.restrict hW) p w : W) : M) = aeval T p w := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply,
      Submodule.coe_add, hp, hq]
  | monomial n a =>
    rw [aeval_monomial, aeval_monomial, Module.End.mul_apply, Module.End.mul_apply,
      Module.algebraMap_end_apply, Module.algebraMap_end_apply, Module.End.pow_restrict,
      Submodule.coe_smul, LinearMap.restrict_apply]

theorem natDegree_dvd_finrank_ker_aeval {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    {f : K[X]} (hf : Irreducible f) (T : Module.End K M) :
    f.natDegree ∣ Module.finrank K (LinearMap.ker (aeval T f)) := by
  refine natDegree_dvd_finrank_of_aeval_eq_zero hf
    (T.restrict fun v hv => apply_mem_ker_aeval T f hv) (LinearMap.ext fun w => Subtype.ext ?_)
  rw [coe_aeval_restrict_apply, LinearMap.zero_apply, Submodule.coe_zero]
  exact w.2

variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]

omit [DecidableEq V] in
theorem adjMatrix_mulVec_comp (Γ : SimpleGraph V) [DecidableRel Γ.Adj] (Q : Matrix ι ι ℚ)
    (cell : V → ι)
    (hQ : ∀ y j, ((Finset.univ.filter fun z => Γ.Adj y z ∧ cell z = j).card : ℚ) = Q (cell y) j)
    (c : ι → ℚ) : Γ.adjMatrix ℚ *ᵥ (c ∘ cell) = (Q *ᵥ c) ∘ cell := by
  funext y
  rw [SimpleGraph.adjMatrix_mulVec_apply, Function.comp_apply, Matrix.mulVec, dotProduct,
    ← Finset.sum_fiberwise (Γ.neighborFinset y) cell (fun z => (c ∘ cell) z)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_congr rfl (fun z hz => by
      rw [Function.comp_apply, (Finset.mem_filter.1 hz).2]), Finset.sum_const, nsmul_eq_mul,
    ← hQ y j]
  congr 3
  ext z
  simp [SimpleGraph.mem_neighborFinset]

theorem pow_adjMatrix_mulVec_comp (Γ : SimpleGraph V) [DecidableRel Γ.Adj] (Q : Matrix ι ι ℚ)
    (cell : V → ι)
    (hQ : ∀ y j, ((Finset.univ.filter fun z => Γ.Adj y z ∧ cell z = j).card : ℚ) = Q (cell y) j)
    (n : ℕ) (c : ι → ℚ) : (Γ.adjMatrix ℚ ^ n) *ᵥ (c ∘ cell) = (Q ^ n *ᵥ c) ∘ cell := by
  induction n generalizing c with
  | zero => simp only [pow_zero, Matrix.one_mulVec]
  | succ n ih =>
    rw [pow_succ', pow_succ', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ih,
      adjMatrix_mulVec_comp Γ Q cell hQ]

theorem aeval_adjMatrix_mulVec_comp (Γ : SimpleGraph V) [DecidableRel Γ.Adj] (Q : Matrix ι ι ℚ)
    (cell : V → ι)
    (hQ : ∀ y j, ((Finset.univ.filter fun z => Γ.Adj y z ∧ cell z = j).card : ℚ) = Q (cell y) j)
    (p : ℚ[X]) (c : ι → ℚ) :
    aeval (Γ.adjMatrix ℚ) p *ᵥ (c ∘ cell) = (aeval Q p *ᵥ c) ∘ cell := by
  induction p using Polynomial.induction_on' generalizing c with
  | add p q hp hq => rw [map_add, map_add, Matrix.add_mulVec, Matrix.add_mulVec, hp, hq]; rfl
  | monomial n a =>
    rw [aeval_monomial, aeval_monomial, ← Algebra.smul_def, ← Algebra.smul_def,
      Matrix.smul_mulVec, Matrix.smul_mulVec, pow_adjMatrix_mulVec_comp Γ Q cell hQ]
    rfl

theorem aeval_adjMatrix_eq_zero (Γ : SimpleGraph V) [DecidableRel Γ.Adj] (Q : Matrix ι ι ℚ)
    (cell : V → V → ι) (i₀ : ι) (hcell : ∀ x y, cell x y = i₀ ↔ y = x)
    (hQ : ∀ x y j, ((Finset.univ.filter fun z => Γ.Adj y z ∧ cell x z = j).card : ℚ) =
      Q (cell x y) j)
    {p : ℚ[X]} (hp : aeval Q p = 0) : aeval (Γ.adjMatrix ℚ) p = 0 := by
  ext y x
  have h := aeval_adjMatrix_mulVec_comp Γ Q (cell x) (hQ x) p (Pi.single i₀ 1)
  rw [hp, Matrix.zero_mulVec] at h
  have hsingle : (Pi.single i₀ (1 : ℚ)) ∘ cell x = Pi.single x 1 := by
    funext z
    simp only [Function.comp_apply, Pi.single_apply, hcell x z]
  rw [hsingle, Matrix.mulVec_single_one] at h
  simpa using congrFun h y

omit [DecidableEq V] in
theorem eq_of_adjMatrix_mulVec_eq_smul {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
    (hconn : Γ.Connected) {k : ℕ} (hreg : Γ.IsRegularOfDegree k) {x : V → ℚ}
    (hx : Γ.adjMatrix ℚ *ᵥ x = (k : ℚ) • x) (y z : V) : x y = x z := by
  obtain ⟨y₀, -, hy₀⟩ := Finset.exists_max_image Finset.univ x ⟨y, Finset.mem_univ _⟩
  have hstep : ∀ a b, Γ.Adj a b → x a = x y₀ → x b = x y₀ := by
    intro a b hab ha
    have h1 := congrFun hx a
    rw [SimpleGraph.adjMatrix_mulVec_apply, Pi.smul_apply, smul_eq_mul, ha] at h1
    have h2 : ∑ w ∈ Γ.neighborFinset a, (x y₀ - x w) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree,
        hreg a, nsmul_eq_mul, h1, sub_self]
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg fun w _ =>
      sub_nonneg.2 (hy₀ w (Finset.mem_univ _))).1 h2 b ((Γ.mem_neighborFinset a b).2 hab)
    linarith
  have key : ∀ u v (w : Γ.Walk u v), x u = x y₀ → x v = x y₀ := by
    intro u v w
    induction w with
    | nil => exact id
    | cons h _ ih => exact fun hu => ih (hstep _ _ h hu)
  have hall : ∀ a, x a = x y₀ := fun a => key _ _ (hconn.preconnected y₀ a).some rfl
  rw [hall y, hall z]

theorem finrank_ker_aeval_X_sub_C_eq_one {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
    (hconn : Γ.Connected) {k : ℕ} (hreg : Γ.IsRegularOfDegree k) :
    finrank ℚ (LinearMap.ker (aeval (Matrix.toLin' (Γ.adjMatrix ℚ)) (X - C (k : ℚ)))) = 1 := by
  have hne : Nonempty V := hconn.nonempty
  have hmem : ∀ v : V → ℚ, v ∈ LinearMap.ker (aeval (Matrix.toLin' (Γ.adjMatrix ℚ))
      (X - C (k : ℚ))) ↔ Γ.adjMatrix ℚ *ᵥ v = (k : ℚ) • v := by
    intro v
    rw [LinearMap.mem_ker, map_sub, aeval_X, aeval_C, LinearMap.sub_apply,
      Module.algebraMap_end_apply, Matrix.toLin'_apply, sub_eq_zero]
  have heq : LinearMap.ker (aeval (Matrix.toLin' (Γ.adjMatrix ℚ)) (X - C (k : ℚ))) =
      ℚ ∙ (fun _ => (1 : ℚ)) := by
    ext v
    rw [hmem, Submodule.mem_span_singleton]
    constructor
    · intro hv
      obtain ⟨y₀⟩ := hne
      refine ⟨v y₀, funext fun y => ?_⟩
      rw [Pi.smul_apply, smul_eq_mul, mul_one]
      exact eq_of_adjMatrix_mulVec_eq_smul hconn hreg hv y₀ y
    · rintro ⟨a, rfl⟩
      funext y
      have := SimpleGraph.adjMatrix_mulVec_const_apply_of_regular (α := ℚ) (a := a) hreg (v := y)
      rw [Pi.smul_apply, smul_eq_mul]
      simpa [Function.const] using this
  rw [heq, finrank_span_singleton]
  intro h
  obtain ⟨y₀⟩ := hne
  exact one_ne_zero (congrFun h y₀)

theorem natDegree_dvd_card_sub_one_of_equitable (Γ : SimpleGraph V) [DecidableRel Γ.Adj]
    (hconn : Γ.Connected) {k : ℕ} (hreg : Γ.IsRegularOfDegree k)
    (cell : V → V → ι) (i₀ : ι) (hcell : ∀ x y, cell x y = i₀ ↔ y = x) (Q : Matrix ι ι ℕ)
    (hQ : ∀ x y j, (Finset.univ.filter fun z => Γ.Adj y z ∧ cell x z = j).card = Q (cell x y) j)
    {f : ℚ[X]} (hf : Irreducible f) (hfk : ¬ f.IsRoot (k : ℚ))
    (hQf : aeval (Q.map (Nat.cast : ℕ → ℚ)) ((X - C (k : ℚ)) * f) = 0) :
    f.natDegree ∣ Fintype.card V - 1 := by
  have hA := aeval_adjMatrix_eq_zero Γ (Q.map (Nat.cast : ℕ → ℚ)) cell i₀ hcell
    (fun x y j => by rw [hQ x y j]; rfl) hQf
  have hT : aeval (Matrix.toLin' (Γ.adjMatrix ℚ)) ((X - C (k : ℚ)) * f) = 0 := by
    have h := Polynomial.aeval_algHom_apply
      (Matrix.toLinAlgEquiv' (R := ℚ) (n := V)).toAlgHom (Γ.adjMatrix ℚ) ((X - C (k : ℚ)) * f)
    rw [hA, map_zero] at h
    exact h
  have hcop : IsCoprime (X - C (k : ℚ)) f :=
    (Polynomial.irreducible_X_sub_C (k : ℚ)).coprime_iff_not_dvd.2 fun h =>
      hfk (dvd_iff_isRoot.1 h)
  have hsup := Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime
    (Matrix.toLin' (Γ.adjMatrix ℚ)) hcop
  rw [hT, LinearMap.ker_zero] at hsup
  have hinf := (Polynomial.disjoint_ker_aeval_of_isCoprime (Matrix.toLin' (Γ.adjMatrix ℚ))
    hcop).eq_bot
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.ker (aeval (Matrix.toLin' (Γ.adjMatrix ℚ)) (X - C (k : ℚ))))
    (LinearMap.ker (aeval (Matrix.toLin' (Γ.adjMatrix ℚ)) f))
  rw [hsup, hinf, finrank_top, finrank_bot, add_zero, Module.finrank_fintype_fun_eq_card,
    finrank_ker_aeval_X_sub_C_eq_one hconn hreg] at hdim
  rw [hdim, Nat.add_sub_cancel_left]
  exact natDegree_dvd_finrank_ker_aeval hf _

theorem natDegree_dvd_card_sub_one_of_equitable_charpoly (Γ : SimpleGraph V)
    [DecidableRel Γ.Adj] (hconn : Γ.Connected) {k : ℕ} (hreg : Γ.IsRegularOfDegree k)
    (cell : V → V → ι) (i₀ : ι) (hcell : ∀ x y, cell x y = i₀ ↔ y = x) (Q : Matrix ι ι ℕ)
    (hQ : ∀ x y j, (Finset.univ.filter fun z => Γ.Adj y z ∧ cell x z = j).card = Q (cell x y) j)
    {f : ℚ[X]} (hf : Irreducible f) (hfk : ¬ f.IsRoot (k : ℚ))
    (hQf : (Q.map (Nat.cast : ℕ → ℚ)).charpoly = (X - C (k : ℚ)) * f) :
    f.natDegree ∣ Fintype.card V - 1 :=
  natDegree_dvd_card_sub_one_of_equitable Γ hconn hreg cell i₀ hcell Q hQ hf hfk
    (by rw [← hQf]; exact Matrix.aeval_self_charpoly _)

omit [DecidableEq V] in
theorem isRegularOfDegree_of_equitable (Γ : SimpleGraph V) [DecidableRel Γ.Adj]
    (cell : V → V → ι) (i₀ : ι) (hcell : ∀ x y, cell x y = i₀ ↔ y = x) (Q : Matrix ι ι ℕ)
    (hQ : ∀ x y j, (Finset.univ.filter fun z => Γ.Adj y z ∧ cell x z = j).card =
      Q (cell x y) j) :
    Γ.IsRegularOfDegree (∑ j, Q i₀ j) := by
  intro x
  rw [← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_eq_sum_card_fiberwise
    (f := cell x) (t := Finset.univ) fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← (hcell x x).2 rfl, ← hQ x x j]
  congr 1
  ext z
  simp [SimpleGraph.mem_neighborFinset]

omit [DecidableEq V] [Fintype ι] in
theorem card_cell_mul (Γ : SimpleGraph V) [DecidableRel Γ.Adj] (cell : V → ι)
    (Q : Matrix ι ι ℕ)
    (hQ : ∀ y j, (Finset.univ.filter fun z => Γ.Adj y z ∧ cell z = j).card = Q (cell y) j)
    (i j : ι) :
    (Finset.univ.filter fun y => cell y = i).card * Q i j =
      (Finset.univ.filter fun y => cell y = j).card * Q j i := by
  refine Finset.card_mul_eq_card_mul Γ.Adj (fun y hy => ?_) fun z hz => ?_
  · rw [Finset.mem_filter] at hy
    rw [← hy.2, ← hQ y j]
    congr 1
    ext z
    simp [Finset.mem_bipartiteAbove, and_comm]
  · rw [Finset.mem_filter] at hz
    rw [← hz.2, ← hQ z i]
    congr 1
    ext y
    simp [Finset.mem_bipartiteBelow, and_comm, Γ.adj_comm]

omit [DecidableEq V] in
theorem card_eq_sum_card_cell (cell : V → ι) :
    Fintype.card V = ∑ i, (Finset.univ.filter fun y => cell y = i).card :=
  Finset.card_eq_sum_card_fiberwise fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)

omit [DecidableEq V] [Fintype ι] in
theorem exists_equitable_of_vertexTransitive (Γ : SimpleGraph V) [DecidableRel Γ.Adj] (v : V)
    (htrans : ∀ x, ∃ σ : Γ ≃g Γ, σ v = x)
    (cell : V → ι) (i₀ : ι) (hcell : ∀ y, cell y = i₀ ↔ y = v) (Q : Matrix ι ι ℕ)
    (hQ : ∀ y j, (Finset.univ.filter fun z => Γ.Adj y z ∧ cell z = j).card = Q (cell y) j) :
    ∃ cell' : V → V → ι, (∀ x y, cell' x y = i₀ ↔ y = x) ∧
      ∀ x y j, (Finset.univ.filter fun z => Γ.Adj y z ∧ cell' x z = j).card =
        Q (cell' x y) j := by
  choose σ hσ using htrans
  refine ⟨fun x y => cell ((σ x).symm y), fun x y => ?_, fun x y j => ?_⟩
  · rw [hcell, RelIso.symm_apply_eq, hσ x]
  · rw [← hQ ((σ x).symm y) j]
    refine Finset.card_equiv (σ x).symm.toEquiv fun z => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← (σ x).symm.map_adj_iff]
    rfl

omit [DecidableEq V] [Fintype ι] in
theorem exists_cell_of_partition (Γ : SimpleGraph V) [DecidableRel Γ.Adj] (v : V)
    (O : ι → Set V) (hO : ∀ y, ∃! i, y ∈ O i) (i₀ : ι) (hO0 : O i₀ = {v})
    (Q : Matrix ι ι ℕ) (hQ : ∀ i j, ∀ y ∈ O i, {z | Γ.Adj y z ∧ z ∈ O j}.ncard = Q i j) :
    ∃ cell : V → ι, (∀ y, cell y = i₀ ↔ y = v) ∧ ∀ y i, (cell y = i ↔ y ∈ O i) ∧
      ∀ j, (Finset.univ.filter fun z => Γ.Adj y z ∧ cell z = j).card = Q (cell y) j := by
  classical
  choose cell hcell hcellu using hO
  have hmem : ∀ y i, cell y = i ↔ y ∈ O i :=
    fun y i => ⟨fun h => h ▸ hcell y, fun h => (hcellu y i h).symm⟩
  refine ⟨cell, fun y => by rw [hmem, hO0, Set.mem_singleton_iff], fun y i => ⟨hmem y i,
    fun j => ?_⟩⟩
  rw [← hQ (cell y) j y (hcell y), ← Set.ncard_coe_finset]
  congr 1
  ext z
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, hmem]

omit [Fintype V] [DecidableEq V] in
theorem exists_iso_of_mulAction {G : Type*} [Group G] [MulAction G V]
    [MulAction.IsPretransitive G V] (Γ : SimpleGraph V)
    (hΓ : ∀ (g : G) (y z : V), Γ.Adj (g • y) (g • z) ↔ Γ.Adj y z) (v x : V) :
    ∃ σ : Γ ≃g Γ, σ v = x := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G v x
  exact ⟨⟨MulAction.toPerm g, fun {a b} => hΓ g a b⟩, hg⟩

theorem natDegree_dvd_card_sub_one_of_vertexTransitive (Γ : SimpleGraph V) [DecidableRel Γ.Adj]
    (hconn : Γ.Connected) {k : ℕ} (hreg : Γ.IsRegularOfDegree k) (v : V)
    (htrans : ∀ x, ∃ σ : Γ ≃g Γ, σ v = x)
    (cell : V → ι) (i₀ : ι) (hcell : ∀ y, cell y = i₀ ↔ y = v) (Q : Matrix ι ι ℕ)
    (hQ : ∀ y j, (Finset.univ.filter fun z => Γ.Adj y z ∧ cell z = j).card = Q (cell y) j)
    {f : ℚ[X]} (hf : Irreducible f) (hfk : ¬ f.IsRoot (k : ℚ))
    (hQf : (Q.map (Nat.cast : ℕ → ℚ)).charpoly = (X - C (k : ℚ)) * f) :
    f.natDegree ∣ Fintype.card V - 1 := by
  obtain ⟨cell', hcell', hQ'⟩ :=
    exists_equitable_of_vertexTransitive Γ v htrans cell i₀ hcell Q hQ
  exact natDegree_dvd_card_sub_one_of_equitable_charpoly Γ hconn hreg cell' i₀ hcell' Q hQ' hf
    hfk hQf

theorem not_isRoot_of_irreducible_of_natDegree_eq_three {f : ℚ[X]} (hf : Irreducible f)
    (hf3 : f.natDegree = 3) (a : ℚ) : ¬ f.IsRoot a := fun h => by
  have := Polynomial.degree_eq_one_of_irreducible_of_root hf h
  rw [Polynomial.degree_eq_natDegree hf.ne_zero, hf3] at this
  exact absurd this (by decide)

theorem rank_four_spectral_obstruction {G : Type*} [Group G] [MulAction G V]
    [MulAction.IsPretransitive G V] (Γ : SimpleGraph V) [DecidableRel Γ.Adj]
    (hΓ : ∀ (g : G) (y z : V), Γ.Adj (g • y) (g • z) ↔ Γ.Adj y z)
    (hconn : Γ.Connected) {k : ℕ} (hreg : Γ.IsRegularOfDegree k) (v : V)
    (O : Fin 4 → Set V) (hO : ∀ y, ∃! i, y ∈ O i) (hO0 : O 0 = {v})
    (Q : Matrix (Fin 4) (Fin 4) ℕ)
    (hQ : ∀ i j, ∀ y ∈ O i, {z | Γ.Adj y z ∧ z ∈ O j}.ncard = Q i j)
    {f : ℚ[X]} (hf : Irreducible f) (hf3 : f.natDegree = 3)
    (hQf : (Q.map (Nat.cast : ℕ → ℚ)).charpoly = (X - C (k : ℚ)) * f) :
    3 ∣ Fintype.card V - 1 := by
  obtain ⟨cell, hcell, hcQ⟩ := exists_cell_of_partition Γ v O hO 0 hO0 Q hQ
  rw [← hf3]
  exact natDegree_dvd_card_sub_one_of_vertexTransitive Γ hconn hreg v
    (exists_iso_of_mulAction Γ hΓ v) cell 0 hcell Q (fun y j => (hcQ y 0).2 j) hf
    (not_isRoot_of_irreducible_of_natDegree_eq_three hf hf3 _) hQf

end CFSG.Monster.B.Generic
