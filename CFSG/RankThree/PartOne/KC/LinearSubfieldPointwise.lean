module

public import CFSG.RankThree.PartOne.KC.LinearSubfieldInclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityLinear
public import CFSG.RankThree.SteinbergR3ELinearRegularUnipotent

public section

namespace CFSG.RankThree.PartOne

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.UnbalancedCatalog

namespace KCLinearSubfield

variable {n : ℕ} {K : Type*} [Field K]

theorem fieldAut_injective [Finite K] (hn : 3 ≤ n) : Function.Injective (fieldAut n K) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro σ hσ
  rw [MonoidHom.mem_ker] at hσ
  exact Subgroup.mem_bot.mpr
    (eq_one_of_conjAut_mul_fieldAut_eq_one hn 1 σ (by rw [map_one, one_mul, hσ])).1

theorem orderOf_fieldAut [Finite K] (hn : 3 ≤ n) (σ : K ≃+* K) :
    orderOf (fieldAut n K σ) = orderOf σ :=
  orderOf_injective (fieldAut n K) (fieldAut_injective hn) σ

theorem apply_eq_self_iff_commute_conj [Finite K] (hn : 3 ≤ n) (α : MulAut (projectiveSL n K))
    (y : projectiveSL n K) : α y = y ↔ α * MulAut.conj y = MulAut.conj y * α := by
  have hinj := CFSG.RankThree.RegularUnipotent.conj_injective_projectiveSL (k := K) hn
  have h : α * MulAut.conj y * α⁻¹ = MulAut.conj (α y) :=
    (CFSG.RankThree.RegularUnipotent.conj_apply_mulAut α y).symm
  constructor
  · intro hy
    rw [hy] at h
    exact mul_inv_eq_iff_eq_mul.mp h
  · intro hc
    apply hinj
    rw [← h, hc, mul_inv_cancel_right]

theorem isSimpleGroup_projectiveSL (hn : 3 ≤ n) : IsSimpleGroup (projectiveSL n K) := by
  have := (CFSG.LinearGroups.linear_projective_simple (K := K) (n := n) (by omega)
    (Or.inl hn)).2.1
  exact (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K).symm.isSimpleGroup

theorem not_commutative_projectiveSL (hn : 3 ≤ n) :
    ¬ ∀ x y : projectiveSL n K, x * y = y * x := by
  intro h
  have := isSimpleGroup_projectiveSL (n := n) (K := K) hn
  have hc : Subgroup.center (projectiveSL n K) = ⊤ :=
    eq_top_iff.mpr fun x _ => Subgroup.mem_center_iff.mpr fun y => h y x
  rw [CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot hn] at hc
  exact bot_ne_top hc

end KCLinearSubfield

open KCLinearSubfield

variable {n : ℕ} {K : Type*} [Field K]

theorem simple_nonabelian_range_linearSubfieldInclusion (hn : 3 ≤ n) (k : Subfield K) :
    IsSimpleGroup (linearSubfieldInclusion n k).range ∧
      ¬ ∀ x y : (linearSubfieldInclusion n k).range, x * y = y * x := by
  have hinj := linearSubfieldInclusion_injective (by omega : 0 < n) k
  let e : (linearSubfieldInclusion n k).range ≃* projectiveSL n k :=
    (MonoidHom.ofInjective hinj).symm
  have := isSimpleGroup_projectiveSL (n := n) (K := k) hn
  refine ⟨e.isSimpleGroup, fun h => not_commutative_projectiveSL (n := n) (K := k) hn
    fun u v => ?_⟩
  apply e.symm.injective
  rw [map_mul, map_mul]
  exact h _ _

theorem fixingSubgroup_range_linearSubfieldInclusion [Finite K] {k : Subfield K}
    {σ : K ≃+* K} (hk : ∀ x, x ∈ k ↔ σ x = x) (hn : 3 ≤ n) :
    fixingSubgroup (MulAut (projectiveSL n K))
        ((linearSubfieldInclusion n k).range : Set (projectiveSL n K)) =
      zpowers (fieldAut n K σ) := by
  have hkf : k = CFSG.ComponentClassification.CatalogueBHigherLinearField.fixedField K σ :=
    Subfield.ext fun x => (hk x).trans
      (CFSG.ComponentClassification.CatalogueBHigherLinearField.mem_fixedField K σ x).symm
  subst hkf
  have hCN := (linear_quadratic_field_full_centralizer_rigidity (n := n) σ hn).2.2.2.2.2.2
  rw [← hCN]
  ext α
  rw [mem_fixingSubgroup_iff, mem_centralizer_iff]
  have hconjB : ∀ B : SpecialLinearGroup (Fin n)
      (CFSG.ComponentClassification.CatalogueBHigherLinearField.fixedField K σ),
      subfieldConj n σ B = MulAut.conj (linearSubfieldInclusion n _ (proj n _ B)) := fun B =>
    conjAut_toGL _
  constructor
  · rintro hfix _ ⟨B, rfl⟩
    have hy : α (linearSubfieldInclusion n _ (proj n _ B)) =
        linearSubfieldInclusion n _ (proj n _ B) := hfix _ ⟨proj n _ B, rfl⟩
    rw [hconjB]
    exact ((apply_eq_self_iff_commute_conj hn α _).mp hy).symm
  · intro hcomm y hy
    obtain ⟨z, rfl⟩ := hy
    obtain ⟨B, rfl⟩ := proj_surjective n _ z
    have := hcomm (subfieldConj n σ B) ⟨B, rfl⟩
    rw [hconjB] at this
    exact (apply_eq_self_iff_commute_conj hn α _).mpr this.symm

end CFSG.RankThree.PartOne
