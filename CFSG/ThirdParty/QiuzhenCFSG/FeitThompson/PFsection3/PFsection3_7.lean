module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection3.PFsection3_5
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection3.PFsection3_6

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 3, Hypothesis (3.6) and Proposition (3.7)

This file formalizes the first consequence of Hypothesis (3.6): the
coefficient matrix in the expansion of `ψ` satisfies the rectangle relation
`aᵢⱼ + aᵢ'ⱼ' = aᵢⱼ' + aᵢ'ⱼ`.

No result from BG is imported here.
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section3

universe v
universe u

/-! ## (3.7) -/

/--
Peterfalvi (3.7): under Hypothesis (3.6), the coefficient matrix has rank-one
additive shape on every rectangle.
-/
@[expose] public def proposition_3_7_statement
    {G : Type u} [Group G] [Finite G]
    (W1 W2 W : Subgroup G)
    (I J : Type*) [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (ψ β : Section1.ClassFunction G)
    (a : I → J → ℂ)
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (_h36 : hypothesis_3_6_statement W1 W2 W I J i0 j0 ω σ ψ β a h hω) :
    Prop :=
  (∀ i i' j j', a i j + a i' j' = a i j' + a i' j) ∧
    ∀ i j, a i j = a i j0 + a i0 j - a i0 j0


private theorem omega_left_kernel_value_pf37
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (i : I) {x : W} (hx : (x : G) ∈ W2) :
    ω i j0 x = 1 := by
  have hker := hω.left_kernel i ⟨x, hx⟩
  simpa [hω.degree_one i j0] using hker

private theorem omega_right_kernel_value_pf37
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (j : J) {x : W} (hx : (x : G) ∈ W1) :
    ω i0 j x = 1 := by
  have hker := hω.right_kernel j ⟨x, hx⟩
  simpa [hω.degree_one i0 j] using hker

@[expose] public def omegaRectangle
    {G : Type u} [Group G] (W : Subgroup G)
    {I J : Type*}
    (ω : I → J → Section1.ClassFunction W)
    (i i' : I) (j j' : J) :
    Section1.ClassFunction W :=
  ω i j + ω i' j' - ω i j' - ω i' j

public theorem omegaRectangle_CFOn_cyclicTISet
    {G : Type u} [Group G] [Finite G]
    (W1 W2 W : Subgroup G)
    (I J : Type*) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (i i' : I) (j j' : J) :
    Section2.CFOn W (cyclicTISet W1 W2 W) (omegaRectangle W ω i i' j j') := by
  constructor
  · intro x g
    simp [omegaRectangle, hω.is_class i j x g, hω.is_class i' j' x g,
      hω.is_class i j' x g, hω.is_class i' j x g]
  · intro x hx
    have hxW : (x : G) ∈ W := x.2
    have hx_union : (x : G) ∈ (W1 : Set G) ∪ (W2 : Set G) := by
      by_contra hnot
      exact hx ⟨hxW, hnot⟩
    rcases hx_union with hx1 | hx2
    · have hj : ω i0 j x = 1 := omega_right_kernel_value_pf37 hω j hx1
      have hj' : ω i0 j' x = 1 := omega_right_kernel_value_pf37 hω j' hx1
      calc
        omegaRectangle W ω i i' j j' x =
            ω i j x + ω i' j' x - ω i j' x - ω i' j x := by
              simp [omegaRectangle, sub_eq_add_neg, add_assoc]
        _ = ω i j0 x + ω i' j0 x - ω i j0 x - ω i' j0 x := by
              rw [hω.product i j x, hω.product i' j' x,
                hω.product i j' x, hω.product i' j x, hj, hj']
              ring
        _ = 0 := by ring
    · have hi : ω i j0 x = 1 := omega_left_kernel_value_pf37 hω i hx2
      have hi' : ω i' j0 x = 1 := omega_left_kernel_value_pf37 hω i' hx2
      calc
        omegaRectangle W ω i i' j j' x =
            ω i j x + ω i' j' x - ω i j' x - ω i' j x := by
              simp [omegaRectangle, sub_eq_add_neg, add_assoc]
        _ = ω i0 j x + ω i0 j' x - ω i0 j' x - ω i0 j x := by
              rw [hω.product i j x, hω.product i' j' x,
                hω.product i j' x, hω.product i' j x, hi, hi']
              ring
        _ = 0 := by ring

private theorem conjugateIn_symm_pf37 {G : Type u} [Group G] {a b : G}
    (h : Section2.conjugateIn a b) :
    Section2.conjugateIn b a := by
  rcases h with ⟨x, hx⟩
  refine ⟨x⁻¹, ?_⟩
  rw [← hx]
  simp [Section2.conjBy, mul_assoc]

public theorem inducedCF_eq_zero_of_not_mem_conjugateSet_of_CFOn
    {G : Type u} [Group G] [Finite G]
    (W : Subgroup G) [Finite W] {A : Set G}
    (α : Section1.ClassFunction W)
    (hα : Section2.CFOn W A α)
    {g : G} (hg : g ∉ Section2.conjugateSet A) :
    Section1.inducedCF W α g = 0 := by
  classical
  unfold Section1.inducedCF Section1.inducedClassFunction
  have hsum :
      ∑ x : G,
        (if hx : x * g * x⁻¹ ∈ W then α ⟨x * g * x⁻¹, hx⟩ else 0) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro x _hx
    by_cases hxW : x * g * x⁻¹ ∈ W
    · have hxA : (⟨x * g * x⁻¹, hxW⟩ : W) ∈
          {y : W | (y : G) ∈ A} → False := by
        intro hxA'
        apply hg
        refine ⟨x * g * x⁻¹, hxA', ?_⟩
        refine conjugateIn_symm_pf37 ?_
        exact ⟨x, rfl⟩
      have hnotA : ((⟨x * g * x⁻¹, hxW⟩ : W) : G) ∉ A := by
        intro hmem
        exact hxA hmem
      simp [hxW, hα.2 ⟨x * g * x⁻¹, hxW⟩ hnotA]
    · simp [hxW]
  rw [hsum]
  simp

private theorem vanishesOn_conjugateSet_of_class
    {G : Type u} [Group G]
    {A : Set G} {ψ : Section1.ClassFunction G}
    (hclass : Section1.IsClassFunction ψ)
    (hvanish : VanishesOn ψ A) :
    VanishesOn ψ (Section2.conjugateSet A) := by
  intro g hg
  rcases hg with ⟨a, ha, x, hx⟩
  rw [← hx]
  simpa [Section2.conjBy] using (hclass x a).trans (hvanish a ha)

private theorem scalarProduct_add_right_pf37
    {H : Type*} [Finite H] (φ ψ η : Section1.ClassFunction H) :
    Section1.scalarProduct H φ (ψ + η) =
      Section1.scalarProduct H φ ψ + Section1.scalarProduct H φ η := by
  simp [Section1.scalarProduct, mul_add, Finset.sum_add_distrib]

private theorem scalarProduct_sub_right_pf37
    {H : Type*} [Finite H] (φ ψ η : Section1.ClassFunction H) :
    Section1.scalarProduct H φ (ψ - η) =
      Section1.scalarProduct H φ ψ - Section1.scalarProduct H φ η := by
  calc
    Section1.scalarProduct H φ (ψ - η) =
        Section1.scalarProduct H φ (ψ + (-1 : ℂ) • η) := by
          congr 1
          ext x
          simp [sub_eq_add_neg]
    _ = Section1.scalarProduct H φ ψ +
          Section1.scalarProduct H φ ((-1 : ℂ) • η) := by
          rw [scalarProduct_add_right_pf37]
    _ = Section1.scalarProduct H φ ψ - Section1.scalarProduct H φ η := by
          rw [Section1.scalarProduct_smul_right]
          simp [sub_eq_add_neg]

private theorem scalarProduct_eq_zero_of_left_vanishes_right_supported
    {G : Type u} [Group G] [Finite G]
    {A : Set G}
    (ψ φ : Section1.ClassFunction G)
    (hψ : VanishesOn ψ A)
    (hφ : ∀ g : G, g ∉ A → φ g = 0) :
    Section1.scalarProduct G ψ φ = 0 := by
  have hsum : ∑ g : G, ψ g * star (φ g) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro g _hg
    by_cases hgA : g ∈ A
    · rw [hψ g hgA]
      simp
    · simp [hφ g hgA]
  rw [Section1.scalarProduct, hsum]
  simp

private theorem sigma_rectangle_inner_eq_coeff_rectangle
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {a : I → J → ℂ}
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hσ : IsCFLinearIsometry σ)
    (i i' : I) (j j' : J) :
    Section1.scalarProduct G
        (∑ p : I × J, a p.1 p.2 • σ (ω p.1 p.2))
        (σ (omegaRectangle W ω i i' j j')) =
      a i j + a i' j' - a i j' - a i' j := by
  classical
  have hrectClass :
      Section1.IsClassFunction (omegaRectangle W ω i i' j j') := by
    intro x g
    simp [omegaRectangle, hω.is_class i j x g, hω.is_class i' j' x g,
      hω.is_class i j' x g, hω.is_class i' j x g]
  have hsumfun :
      (∑ p : I × J, a p.1 p.2 • σ (ω p.1 p.2)) =
        (fun g : G => ∑ p : I × J, (a p.1 p.2 • σ (ω p.1 p.2)) g) := by
    ext g
    simp
  rw [hsumfun]
  rw [Section1.scalarProduct_fintype_sum_left]
  simp_rw [Section1.scalarProduct_smul_left]
  calc
    ∑ p : I × J,
        a p.1 p.2 *
          Section1.scalarProduct G (σ (ω p.1 p.2))
            (σ (omegaRectangle W ω i i' j j')) =
        ∑ p : I × J,
          a p.1 p.2 *
            Section1.scalarProduct W (ω p.1 p.2)
              (omegaRectangle W ω i i' j j') := by
          refine Finset.sum_congr rfl ?_
          intro p _hp
          rw [hσ (ω p.1 p.2) (omegaRectangle W ω i i' j j')
            (hω.is_class p.1 p.2) hrectClass]
    _ = ∑ p : I × J,
          a p.1 p.2 *
            ((if p = (i, j) then (1 : ℂ) else 0) +
              (if p = (i', j') then (1 : ℂ) else 0) -
              (if p = (i, j') then (1 : ℂ) else 0) -
              (if p = (i', j) then (1 : ℂ) else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro p _hp
          have hsp : ∀ q : I × J,
              Section1.scalarProduct W (ω p.1 p.2) (ω q.1 q.2) =
                if p = q then 1 else 0 := by
            intro q
            exact isOrthonormalDoubleFamily_apply hω.orthonormal p q
          rw [omegaRectangle, scalarProduct_sub_right_pf37,
            scalarProduct_sub_right_pf37, scalarProduct_add_right_pf37,
            hsp (i, j), hsp (i', j'), hsp (i, j'), hsp (i', j)]
    _ = a i j + a i' j' - a i j' - a i' j := by
          simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_add, mul_sub]

private theorem scalarProduct_psi_sigma_rectangle_eq_coeff_rectangle
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {ψ β : Section1.ClassFunction G}
    {a : I → J → ℂ}
    {h : hypothesis_3_1_statement W1 W2 W}
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h36 : hypothesis_3_6_statement W1 W2 W I J i0 j0 ω σ ψ β a h hω)
    (i i' : I) (j j' : J) :
    Section1.scalarProduct G ψ (σ (omegaRectangle W ω i i' j j')) =
      a i j + a i' j' - a i j' - a i' j := by
  have h32 := h36.1
  have hβorth := h36.2.1
  have hψ := h36.2.2.1
  have hσ := h32.1
  have hCFOn :
      Section2.CFOn W (cyclicTISet W1 W2 W) (omegaRectangle W ω i i' j j') :=
    omegaRectangle_CFOn_cyclicTISet W1 W2 W I J i0 j0 ω hω i i' j j'
  rw [hψ]
  rw [Section1.scalarProduct_add_left]
  rw [hβorth (omegaRectangle W ω i i' j j') hCFOn.1]
  simp [sigma_rectangle_inner_eq_coeff_rectangle (W1 := W1) (W2 := W2) (W := W)
    (i0 := i0) (j0 := j0) hω hσ i i' j j']


public theorem scalarProduct_vanishes_rectangle_eq_zero_of_agrees
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {T : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {ψ : Section1.ClassFunction G}
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hagrees :
      ∀ α : Section1.ClassFunction W,
        Section2.CFOn W (cyclicTISet W1 W2 W) α →
          T α = Section1.inducedCF W α)
    (hclass : Section1.IsClassFunction ψ)
    (hvanish : VanishesOn ψ (cyclicTISet W1 W2 W))
    (i i' : I) (j j' : J) :
    Section1.scalarProduct G ψ (T (omegaRectangle W ω i i' j j')) = 0 := by
  classical
  let rect : Section1.ClassFunction W := omegaRectangle W ω i i' j j'
  have hCFOn :
      Section2.CFOn W (cyclicTISet W1 W2 W) rect :=
    omegaRectangle_CFOn_cyclicTISet W1 W2 W I J i0 j0 ω hω i i' j j'
  change Section1.scalarProduct G ψ (T rect) = 0
  rw [hagrees rect hCFOn]
  exact scalarProduct_eq_zero_of_left_vanishes_right_supported ψ
    (Section1.inducedCF W rect)
    (vanishesOn_conjugateSet_of_class hclass hvanish)
    (fun g hg =>
      inducedCF_eq_zero_of_not_mem_conjugateSet_of_CFOn W rect hCFOn hg)

private theorem scalarProduct_psi_sigma_rectangle_eq_zero
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {ψ β : Section1.ClassFunction G}
    {a : I → J → ℂ}
    {h : hypothesis_3_1_statement W1 W2 W}
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h36 : hypothesis_3_6_statement W1 W2 W I J i0 j0 ω σ ψ β a h hω)
    (i i' : I) (j j' : J) :
    Section1.scalarProduct G ψ (σ (omegaRectangle W ω i i' j j')) = 0 := by
  have h32 := h36.1
  have hclass := h36.2.2.2.2.1
  have hvanish := h36.2.2.2.2.2
  have hagrees := h32.2.2.1
  have hCFOn :
      Section2.CFOn W (cyclicTISet W1 W2 W) (omegaRectangle W ω i i' j j') :=
    omegaRectangle_CFOn_cyclicTISet W1 W2 W I J i0 j0 ω hω i i' j j'
  rw [hagrees (omegaRectangle W ω i i' j j') hCFOn]
  exact scalarProduct_eq_zero_of_left_vanishes_right_supported ψ
    (Section1.inducedCF W (omegaRectangle W ω i i' j j'))
    (vanishesOn_conjugateSet_of_class hclass hvanish)
    (fun g hg =>
      inducedCF_eq_zero_of_not_mem_conjugateSet_of_CFOn W
        (omegaRectangle W ω i i' j j') hCFOn hg)

public theorem proposition_3_7_rectangle
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {ψ β : Section1.ClassFunction G}
    {a : I → J → ℂ}
    {h : hypothesis_3_1_statement W1 W2 W}
    {hω : notation_3_3_statement W1 W2 W I J i0 j0 ω}
    (h36 : hypothesis_3_6_statement W1 W2 W I J i0 j0 ω σ ψ β a h hω)
    (i i' : I) (j j' : J) :
    a i j + a i' j' = a i j' + a i' j := by
  have hzero := scalarProduct_psi_sigma_rectangle_eq_zero
    (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J)
    (i0 := i0) (j0 := j0) (ω := ω) (σ := σ) (ψ := ψ) (β := β)
    (a := a) hω h36 i i' j j'
  have hcoeff := scalarProduct_psi_sigma_rectangle_eq_coeff_rectangle
    (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J)
    (i0 := i0) (j0 := j0) (ω := ω) (σ := σ) (ψ := ψ) (β := β)
    (a := a) hω h36 i i' j j'
  have hrect : a i j + a i' j' - a i j' - a i' j = 0 := by
    simpa [hcoeff] using hzero
  linear_combination hrect

public theorem proposition_3_7_particular
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {ψ β : Section1.ClassFunction G}
    {a : I → J → ℂ}
    {h : hypothesis_3_1_statement W1 W2 W}
    {hω : notation_3_3_statement W1 W2 W I J i0 j0 ω}
    (h36 : hypothesis_3_6_statement W1 W2 W I J i0 j0 ω σ ψ β a h hω)
    (i : I) (j : J) :
    a i j = a i j0 + a i0 j - a i0 j0 := by
  have hrect := proposition_3_7_rectangle
    (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J)
    (i0 := i0) (j0 := j0) (ω := ω) (σ := σ) (ψ := ψ) (β := β)
    (a := a) h36 i i0 j j0
  linear_combination hrect

public theorem proposition_3_7
    {G : Type u} [Group G] [Finite G]
    (W1 W2 W : Subgroup G)
    (I J : Type*) [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (ψ β : Section1.ClassFunction G)
    (a : I → J → ℂ)
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h36 : hypothesis_3_6_statement W1 W2 W I J i0 j0 ω σ ψ β a h hω) :
    proposition_3_7_statement W1 W2 W I J i0 j0 ω σ ψ β a h hω h36 := by
  constructor
  · intro i i' j j'
    exact proposition_3_7_rectangle
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J)
      (i0 := i0) (j0 := j0) (ω := ω) (σ := σ) (ψ := ψ) (β := β)
      (a := a) h36 i i' j j'
  · intro i j
    exact proposition_3_7_particular
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J)
      (i0 := i0) (j0 := j0) (ω := ω) (σ := σ) (ψ := ψ) (β := β)
      (a := a) h36 i j

end CFSG.Section3
