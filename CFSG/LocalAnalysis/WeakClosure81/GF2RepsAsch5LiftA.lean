module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5LiftCore
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5LiftSub

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin.A1b Subgroup
open CFSG.Blueprint (LieModel)

theorem conjSub_eq_or_commute_of_isSubnormal {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hs : IsSimpleGroup ↥L) (hnab : ∃ a b : ↥L, a * b ≠ b * a) (hsub : L.IsSubnormal) (g : G) :
    conjSub g L = L ∨ ∀ x ∈ L, ∀ y ∈ conjSub g L, x * y = y * x := by
  haveI := hs
  have hcomp : CFSG.IsComponent L :=
    ⟨(CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).1, hsub⟩
  rcases CFSG.LocalCores.distinct_components_commute hcomp
    (CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hcomp) with h1 | h2
  · exact Or.inl h1.symm
  · right
    intro x hx y hy
    have hc : x ∈ Subgroup.centralizer (conjSub g L : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp h2 hx
    exact ((Subgroup.mem_centralizer_iff.mp hc) y hy).symm

theorem exists_proper_overgroups_of_almostSimple_overgroups
    {G : Type} [Group G] [Finite G] {T L : Subgroup G}
    (hOver : AlmostSimpleOvergroupPair ↥L)
    (hT : IsPGroup 2 T) (hLT : L ⊔ T = ⊤)
    (hsub : L.IsSubnormal) (hs : IsSimpleGroup ↥L)
    (hnab : ∃ a b : ↥L, a * b ≠ b * a) :
    ∃ D₁ D₂ : Subgroup G,
      T ≤ D₁ ∧ T ≤ D₂ ∧ D₁ < ⊤ ∧ D₂ < ⊤ ∧ D₁ ⊔ D₂ = ⊤ := by
  obtain ⟨M₁, M₂, h₁, h₂, hne₁, hne₂, hlt₁, hlt₂, hsup, hn⟩ := exists_subgroups_of_almostSimple_overgroups hOver hT
  exact exists_proper_overgroups hLT hs hnab (conjSub_eq_or_commute_of_isSubnormal hs hnab hsub)
    h₁ h₂ hne₁ hne₂ hlt₁ hlt₂ hsup (fun t ht htL => (hn t ht htL).1)
    (fun t ht htL => (hn t ht htL).2)

end CFSG.LocalAnalysis.WeakClosure81
