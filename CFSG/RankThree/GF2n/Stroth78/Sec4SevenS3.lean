module

public import CFSG.RankThree.GF2n.Stroth78.Sec2Six

import CFSG.RankThree.GF2n.Stroth78.Sec3Six
import CFSG.RankThree.GF2n.Stroth78.Sec4SevenS6Quot
public import CFSG.GroupTheory.ThreeTranspositions.FischerResidual
public import CFSG.RankThree.GF2n.Stroth78.Sec3Comp
public import CFSG.RankThree.GF2n.Stroth78.Sec3Lbar
public import CFSG.RankThree.GF2n.Stroth78.Sec3Setup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.RankThree.GF2n.Stroth78.Sec4SevenS3

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions CFSG.GroupTheory.ThreeTranspositions
open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification Equiv Equiv.Perm

variable {X : Type} [Group X] {E : Set X}

theorem nonabelianCommutator_threeResidualQuot (hP : Pair X E)
    (h2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥)
    (h3 : ∀ N : Subgroup X, N.Normal → IsPGroup 3 N → N ≤ Subgroup.center X) {d : X}
    (hd : d ∈ E) : NonabelianCommutator ↥(threeResidualQuot d) := by
  obtain ⟨N, -, -, hNsol, -, hcomm⟩ :=
    Sec4SevenS6.exists_minimalNormal_commutator_eq hP h2 h3 hd
  by_contra hna
  apply hNsol
  have h1 : (commutator ↥(threeResidualQuot d)).map (threeResidualQuot d).subtype = N :=
    (Subgroup.map_subtype_commutator _).trans hcomm
  let e : ↥(commutator ↥(threeResidualQuot d)) ≃* ↥N :=
    (Subgroup.equivMapOfInjective _ (threeResidualQuot d).subtype
      (threeResidualQuot d).subtype_injective).trans (MulEquiv.subgroupCongr h1)
  have hx : ∀ a b : ↥(commutator ↥(threeResidualQuot d)), a * b = b * a := by
    by_contra hc
    push Not at hc
    exact hna hc
  refine Group.isSolvable_of_comm fun x y => ?_
  have h2' := congrArg e (hx (e.symm x) (e.symm y))
  simpa using h2'

theorem commutator_perm_three_comm :
    ∀ a b : ↥(commutator (Perm (Fin 3))), a * b = b * a := by
  have hle : ∀ x ∈ commutator (Perm (Fin 3)), Perm.sign x = 1 := fun x hx =>
    MonoidHom.mem_ker.mp (Abelianization.commutator_subset_ker Perm.sign hx)
  have hdec : ∀ x y : Perm (Fin 3), Perm.sign x = 1 → Perm.sign y = 1 → x * y = y * x := by
    decide +kernel
  intro a b
  exact Subtype.ext (hdec _ _ (hle _ a.2) (hle _ b.2))

end CFSG.RankThree.GF2n.Stroth78.Sec4SevenS3

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions CFSG.GroupTheory.ThreeTranspositions

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem stroth78_47_s3 (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {α : Hbar z} (hα : α ∈ Tset S a)
    (φ : ↥(threeResidualQuot
      (⟨α, subset_Xsub S a (Tset_subset_Eset S a hα)⟩ : ↥(Xsub S a))) ≃*
        Equiv.Perm (Fin 3)) : False := by
  have hd : (⟨α, subset_Xsub S a (Tset_subset_Eset S a hα)⟩ : ↥(Xsub S a)) ∈
      (Subtype.val ⁻¹' Eset S a : Set ↥(Xsub S a)) := Tset_subset_Eset S a hα
  obtain ⟨a₁, b₁, hab⟩ := Sec4SevenS3.nonabelianCommutator_threeResidualQuot
    (pair_Xsub S h h217 h3) (twoCore_Xsub S) (threeCore_Xsub S h h217) hd
  refine hab ((MulEquiv.commutatorCongr φ).injective ?_)
  rw [map_mul, map_mul]
  exact Sec4SevenS3.commutator_perm_three_comm _ _

end CFSG.RankThree.GF2n.Stroth78
