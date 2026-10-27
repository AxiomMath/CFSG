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
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Topology.Sheaves.Init

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.SteinbergCB

open Module Equiv Equiv.Perm

@[expose] def sumForm (n : ℕ) : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun x := ∑ i, x i
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum]

@[expose] def evenWeight (n : ℕ) : Submodule (ZMod 2) (Fin n → ZMod 2) :=
  LinearMap.ker (sumForm n)

theorem mem_evenWeight {n : ℕ} {x : Fin n → ZMod 2} : x ∈ evenWeight n ↔ ∑ i, x i = 0 :=
  Iff.rfl

theorem finrank_evenWeight_five : finrank (ZMod 2) (evenWeight 5) = 4 := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (sumForm 5)
  have h2 : LinearMap.range (sumForm 5) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    refine ⟨Pi.single 0 c, ?_⟩
    change ∑ i, Pi.single (0 : Fin 5) c i = c
    rw [Finset.sum_pi_single']
    simp
  rw [h2, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h1
  change finrank (ZMod 2) (LinearMap.ker (sumForm 5)) = 4
  omega

theorem funLeft_inv_apply {n : ℕ} (g : Perm (Fin n)) (x : Fin n → ZMod 2) (i : Fin n) :
    LinearMap.funLeft (ZMod 2) (ZMod 2) ⇑g⁻¹ x i = x (g⁻¹ i) :=
  rfl

theorem funLeft_inv_mem_evenWeight {n : ℕ} (g : Perm (Fin n)) {x : Fin n → ZMod 2}
    (hx : x ∈ evenWeight n) : LinearMap.funLeft (ZMod 2) (ZMod 2) ⇑g⁻¹ x ∈ evenWeight n := by
  rw [mem_evenWeight] at hx ⊢
  simp only [funLeft_inv_apply]
  rw [Equiv.sum_comp g⁻¹ x, hx]

theorem single_add_single_mem_orbit :
    ∀ u : Fin 5 → ZMod 2, ∑ i, u i = 0 → u ≠ 0 → ∀ j : Fin 5, j ≠ 0 →
      (∃ g : alternatingGroup (Fin 5),
        Pi.single 0 1 + Pi.single j 1 = fun i => u ((g : Perm (Fin 5))⁻¹ i)) ∨
      ∃ g h : alternatingGroup (Fin 5), Pi.single 0 1 + Pi.single j 1 =
        (fun i => u ((g : Perm (Fin 5))⁻¹ i)) + fun i => u ((h : Perm (Fin 5))⁻¹ i) := by
  decide +kernel

theorem eq_one_of_fix_single_add_single :
    ∀ g : alternatingGroup (Fin 5), (∀ i j : Fin 5,
      (fun k => (Pi.single i 1 + Pi.single j 1 : Fin 5 → ZMod 2) ((g : Perm (Fin 5))⁻¹ k)) =
        Pi.single i 1 + Pi.single j 1) → g = 1 := by
  decide +kernel

theorem fixed_of_stabilizer :
    ∀ (i : Fin 5) (v : Fin 5 → ZMod 2), ∑ k, v k = 0 → (∀ g : alternatingGroup (Fin 5),
      (g : Perm (Fin 5)) i = i → (fun k => v ((g : Perm (Fin 5))⁻¹ k)) = v) →
        v = 0 ∨ v = fun k => if k = i then 0 else 1 := by
  decide +kernel

theorem perm_complement_vector :
    ∀ (g : alternatingGroup (Fin 5)) (i : Fin 5),
      (fun k => (fun l : Fin 5 => if l = i then (0 : ZMod 2) else 1) ((g : Perm (Fin 5))⁻¹ k)) =
        fun k => if k = (g : Perm (Fin 5)) i then 0 else 1 := by
  decide +kernel

theorem eq_sum_complement_vector :
    ∀ x : Fin 5 → ZMod 2, ∑ k, x k = 0 →
      x = ∑ j, x j • fun k : Fin 5 => if k = j then (0 : ZMod 2) else 1 := by
  decide +kernel

theorem exists_perm_zero_eq :
    ∀ i : Fin 5, ∃ g : alternatingGroup (Fin 5), (g : Perm (Fin 5)) 0 = i := by
  decide +kernel

theorem A7_deleted_A5_module_scalar_endomorphisms :
    (∀ g : alternatingGroup (Fin 5), ∀ x ∈ evenWeight 5,
      LinearMap.funLeft (ZMod 2) (ZMod 2) ⇑(g : Perm (Fin 5))⁻¹ x ∈ evenWeight 5) ∧
    (∀ g : alternatingGroup (Fin 5), (∀ x ∈ evenWeight 5,
      LinearMap.funLeft (ZMod 2) (ZMod 2) ⇑(g : Perm (Fin 5))⁻¹ x = x) → g = 1) ∧
    (∀ U : Submodule (ZMod 2) (Fin 5 → ZMod 2), U ≤ evenWeight 5 →
      (∀ g : alternatingGroup (Fin 5), ∀ x ∈ U,
        LinearMap.funLeft (ZMod 2) (ZMod 2) ⇑(g : Perm (Fin 5))⁻¹ x ∈ U) →
      U = ⊥ ∨ U = evenWeight 5) ∧
    finrank (ZMod 2) (evenWeight 5) = 4 ∧
    ∀ f : evenWeight 5 →ₗ[ZMod 2] evenWeight 5,
      (∀ (g : alternatingGroup (Fin 5)) (x y : evenWeight 5),
        (y : Fin 5 → ZMod 2) = LinearMap.funLeft (ZMod 2) (ZMod 2) ⇑(g : Perm (Fin 5))⁻¹ x →
          (f y : Fin 5 → ZMod 2) =
            LinearMap.funLeft (ZMod 2) (ZMod 2) ⇑(g : Perm (Fin 5))⁻¹ (f x)) →
      f = 0 ∨ f = LinearMap.id := by
  have hpair : ∀ i j : Fin 5, i ≠ j →
      (Pi.single i 1 + Pi.single j 1 : Fin 5 → ZMod 2) ∈ evenWeight 5 := by
    intro i j hij
    rw [mem_evenWeight]
    simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ,
      ite_true]
    decide
  have hspan : ∀ x ∈ evenWeight 5, x ∈ Submodule.span (ZMod 2)
      {v | ∃ j : Fin 5, j ≠ 0 ∧ v = Pi.single 0 1 + Pi.single j 1} := by
    intro x hx
    have hx' : x = ∑ j ∈ Finset.univ.erase (0 : Fin 5), x j • (Pi.single 0 1 + Pi.single j 1) := by
      rw [mem_evenWeight] at hx
      revert x
      decide +kernel
    rw [hx']
    refine Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact ⟨j, Finset.ne_of_mem_erase hj, rfl⟩
  refine ⟨fun g x hx => funLeft_inv_mem_evenWeight _ hx, fun g hg => ?_, fun U hUW hU => ?_,
    finrank_evenWeight_five, fun f hf => ?_⟩
  ·
    refine eq_one_of_fix_single_add_single g fun i j => ?_
    by_cases hij : i = j
    · subst hij
      have h2 : (Pi.single i 1 + Pi.single i 1 : Fin 5 → ZMod 2) = 0 := by
        rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
      rw [h2]
      rfl
    · exact hg _ (hpair i j hij)
  ·
    by_cases hU0 : U = ⊥
    · exact Or.inl hU0
    right
    obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
    refine le_antisymm hUW fun x hx => ?_
    have hgen : ∀ j : Fin 5, j ≠ 0 → (Pi.single 0 1 + Pi.single j 1 : Fin 5 → ZMod 2) ∈ U := by
      intro j hj
      rcases single_add_single_mem_orbit u (mem_evenWeight.1 (hUW huU)) hu0 j hj with
        ⟨g, hg⟩ | ⟨g, h, hgh⟩
      · rw [hg]
        exact hU g u huU
      · rw [hgh]
        exact U.add_mem (hU g u huU) (hU h u huU)
    refine (Submodule.span_le.2 ?_) (hspan x hx)
    rintro _ ⟨j, hj, rfl⟩
    exact hgen j hj
  ·
    set w : Fin 5 → (Fin 5 → ZMod 2) := fun i k => if k = i then 0 else 1 with hw
    have hwW : ∀ i, w i ∈ evenWeight 5 := by
      intro i
      rw [mem_evenWeight, hw]
      revert i
      decide +kernel
    have hfw : ∀ i, (f ⟨w i, hwW i⟩ : Fin 5 → ZMod 2) = 0 ∨
        (f ⟨w i, hwW i⟩ : Fin 5 → ZMod 2) = w i := by
      intro i
      refine fixed_of_stabilizer i _ (mem_evenWeight.1 (f ⟨w i, hwW i⟩).2) fun g hg => ?_
      have h1 := hf g ⟨w i, hwW i⟩ ⟨w i, hwW i⟩ (by
        funext k
        rw [funLeft_inv_apply]
        have := congrFun (perm_complement_vector g i) k
        rw [hg] at this
        exact this.symm)
      funext k
      exact (congrFun h1 k).symm
    have hcommon : ∀ i, (f ⟨w i, hwW i⟩ : Fin 5 → ZMod 2) =
        (f ⟨w 0, hwW 0⟩ : Fin 5 → ZMod 2) ∘ ⇑((Classical.choose (exists_perm_zero_eq i) :
          alternatingGroup (Fin 5)) : Perm (Fin 5))⁻¹ := by
      intro i
      set g := Classical.choose (exists_perm_zero_eq i) with hgdef
      have hg : (g : Perm (Fin 5)) 0 = i := Classical.choose_spec (exists_perm_zero_eq i)
      have h1 := hf g ⟨w 0, hwW 0⟩ ⟨w i, hwW i⟩ (by
        funext k
        rw [funLeft_inv_apply]
        have := congrFun (perm_complement_vector g 0) k
        rw [hg] at this
        exact this.symm)
      rw [h1]
      rfl
    have hgw : ∀ i, (w 0) ∘ ⇑((Classical.choose (exists_perm_zero_eq i) :
        alternatingGroup (Fin 5)) : Perm (Fin 5))⁻¹ = w i := by
      intro i
      have hg : ((Classical.choose (exists_perm_zero_eq i) : alternatingGroup (Fin 5)) :
          Perm (Fin 5)) 0 = i := Classical.choose_spec (exists_perm_zero_eq i)
      have := perm_complement_vector (Classical.choose (exists_perm_zero_eq i)) 0
      rw [hg] at this
      exact this
    have hscalar : ∀ x : evenWeight 5, (f x : Fin 5 → ZMod 2) =
        ∑ j, (x : Fin 5 → ZMod 2) j • (f ⟨w j, hwW j⟩ : Fin 5 → ZMod 2) := by
      intro x
      have hx := eq_sum_complement_vector x (mem_evenWeight.1 x.2)
      have hx' : x = ∑ j, (x : Fin 5 → ZMod 2) j • (⟨w j, hwW j⟩ : evenWeight 5) := by
        apply Subtype.ext
        rw [Submodule.coe_sum]
        simp only [Submodule.coe_smul]
        exact hx
      conv_lhs => rw [hx']
      rw [map_sum, Submodule.coe_sum]
      simp only [map_smul, Submodule.coe_smul]
    rcases hfw 0 with h0 | h1
    · left
      refine LinearMap.ext fun x => Subtype.ext ?_
      rw [hscalar x, LinearMap.zero_apply, Submodule.coe_zero]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [hcommon j, h0]
      simp
    · right
      refine LinearMap.ext fun x => Subtype.ext ?_
      rw [hscalar x, LinearMap.id_apply]
      have : ∀ j, (f ⟨w j, hwW j⟩ : Fin 5 → ZMod 2) = w j := fun j => by
        rw [hcommon j, h1, hgw j]
      simp only [this]
      exact (eq_sum_complement_vector x (mem_evenWeight.1 x.2)).symm

end CFSG.Quasithin.SteinbergCB
