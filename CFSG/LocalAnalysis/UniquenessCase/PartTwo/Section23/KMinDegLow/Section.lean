module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148VSection
public import Mathlib.GroupTheory.OrderOfElement
import CFSG.SignalizerFunctorTheorem.Inheritance.Sections
import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.MinDegLow

open CFSG.RankThree.PartTwo.Sec4.Ronan148V
open CFSG.SignalizerFunctorTheorem (IsSectionOf)

variable {S S' G G' A B : Type*} [Group S] [Group S'] [Group G] [Group G'] [Group A] [Group B]

theorem isSec_self : IsSec G G :=
  isSec_of_surjective (MonoidHom.id G) Function.surjective_id

theorem isSec_trans (h : IsSec S G') (h' : IsSec G' G) : IsSec S G :=
  IsSectionOf.trans (X := S) (Y := G') (Z := G) h h'

theorem isSec_of_mulEquiv_left (e : S ≃* S') (h : IsSec S G) : IsSec S' G :=
  IsSectionOf.trans (X := S') (Y := S) (Z := G) (IsSectionOf.of_mulEquiv e) h

theorem not_isSolvable_of_isSimpleGroup [IsSimpleGroup S] (hS : ∃ a b : S, a * b ≠ b * a) :
    ¬ IsSolvable S := fun h => by
  obtain ⟨a, b, hab⟩ := hS
  exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr h a b)

theorem exists_orderOf_eq_of_isSec [Finite G] (h : IsSec S G) (s : S) :
    ∃ g : G, orderOf g = orderOf s := by
  obtain ⟨H, φ, hφ⟩ := h
  obtain ⟨x, rfl⟩ := hφ s
  have hx : orderOf x ≠ 0 := (orderOf_pos x).ne'
  refine ⟨((x ^ (orderOf x / orderOf (φ x)) : H) : G), ?_⟩
  rw [Subgroup.orderOf_coe, orderOf_pow_orderOf_div hx (orderOf_map_dvd φ x)]

theorem isSec_prod [IsSimpleGroup S] (h : IsSec S (A × B)) :
    IsSec S A ∨ IsSec S B := by
  rcases IsSectionOf.of_hom (X := S) (Y := A × B) (Z := A) h (MonoidHom.fst A B) with
    hker | hA
  · right
    have hinj : Function.Injective
        ((MonoidHom.snd A B).comp (MonoidHom.fst A B).ker.subtype) := by
      intro x y hxy
      apply Subtype.ext
      exact Prod.ext (x.2.trans y.2.symm) hxy
    exact IsSectionOf.of_injective hker ((MonoidHom.snd A B).comp
      (MonoidHom.fst A B).ker.subtype) hinj
  · exact Or.inl hA

theorem isSec_quotient_center_of_sup {X : Type*} [Group X] [Finite X] [IsSimpleGroup S]
    (hS : ∃ a b : S, a * b ≠ b * a) {K₁ K₂ : Subgroup X} (hsup : K₁ ⊔ K₂ = ⊤)
    (hcomm : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) (h : IsSec S X) :
    ∃ K' ∈ ({K₁, K₂} : Set (Subgroup X)), IsSec S (↥K' ⧸ Subgroup.center ↥K') := by
  classical
  have hcomm' : ∀ (a : ↥K₁) (b : ↥K₂), Commute (K₁.subtype a) (K₂.subtype b) :=
    fun a b => (commute_iff_eq _ _).mpr (hcomm a a.2 b b.2)
  let μ : ↥K₁ × ↥K₂ →* X := MonoidHom.noncommCoprod K₁.subtype K₂.subtype hcomm'
  have hμ : Function.Surjective μ := by
    have hrange : (MonoidHom.noncommCoprod K₁.subtype K₂.subtype hcomm').range = ⊤ := by
      rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype, hsup]
    rwa [MonoidHom.range_eq_top] at hrange
  have hprod : IsSec S (↥K₁ × ↥K₂) := IsSec.of_surjective hμ h
  have hnsol : ¬ IsSolvable S := not_isSolvable_of_isSimpleGroup hS
  have hcenter : ∀ K : Subgroup X, IsSolvable ↥(Subgroup.center ↥K) := fun K =>
    isSolvable_of_comm fun a b =>
      Subtype.ext (Subgroup.mem_center_iff.mp a.2 b.1).symm
  rcases isSec_prod hprod with h1 | h2
  · exact ⟨K₁, by simp, IsSec.quotient_of_isSolvable hnsol (hcenter K₁) h1⟩
  · exact ⟨K₂, by simp, IsSec.quotient_of_isSolvable hnsol (hcenter K₂) h2⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.MinDegLow
