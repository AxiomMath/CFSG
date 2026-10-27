module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

namespace CFSG
end CFSG
open CFSG

/-!
# Normalizers of normal subgroups of maximal subgroups
-/

namespace CFSG.GorensteinWalter

universe u

/-- In a finite simple group, the ambient normalizer of a nontrivial subgroup
normal in a maximal subgroup is that maximal subgroup. -/
public theorem normalizer_eq_of_nontrivial_normal_in_coatom
    {G : Type u} [Group G]
    (hsimple : IsSimpleGroup G)
    {A K : Subgroup G} (hA : IsCoatom A)
    (hKA : K ≤ A) (hKne : K ≠ ⊥)
    (hKnormal : (K.subgroupOf A).Normal) :
    Subgroup.normalizer (K : Set G) = A := by
  have hAleN : A ≤ Subgroup.normalizer (K : Set G) := by
    let : (K.subgroupOf A).Normal := hKnormal
    exact Subgroup.le_normalizer_of_normal_subgroupOf hKA
  have hNne : Subgroup.normalizer (K : Set G) ≠ ⊤ := by
    intro hNtop
    have hKnormalG : K.Normal := (Subgroup.normalizer_eq_top_iff).mp hNtop
    rcases (haveI := hKnormalG; hsimple.eq_bot_or_eq_top_of_normal K) with hKbot | hKtop
    · exact hKne hKbot
    · have hAtop : A = ⊤ := by
        apply top_unique
        intro x hx
        exact hKA (hKtop ▸ hx)
      exact hA.1 hAtop
  apply le_antisymm
  · by_cases hEq : A = Subgroup.normalizer (K : Set G)
    · simp [hEq]
    · have hlt : A < Subgroup.normalizer (K : Set G) :=
        lt_of_le_of_ne hAleN hEq
      exact False.elim (hNne (hA.2 _ hlt))
  · exact hAleN

end CFSG.GorensteinWalter
