module

public import CFSG.RankThree.PartOne.N1322.Pure
public import CFSG.RankThree.PartOne.KF.F1322OmegaBig
public import CFSG.RankThree.PartOne.KF.F1322OmegaFive
public import CFSG.RankThree.PartOne.KF.F1322OmegaSeven

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartOne.KF1322

open Matrix CFSG.RankThree.SubgroupLists

theorem kf1322OmegaList_holds : N1322.KF1322OmegaList := by
  intro p _ hp5 X D hDrefl hX hDconj hodd H hHX hHnorm hirr M hMt hdet hH
  subst hH
  have hDX : ∀ t ∈ D, t ∈ X := fun t ht => hX ▸ Subgroup.subset_closure ht
  have hnorm : ∀ t ∈ D, ∀ x ∈ omegaGL M, t * x * t⁻¹ ∈ omegaGL M := fun t ht x hx =>
    hHnorm t (hDX t ht) x hx
  have hDconjH : ∀ x ∈ omegaGL M, ∀ g ∈ D, x * g * x⁻¹ ∈ D := fun x hx g hg =>
    hDconj x (hHX hx) g hg
  by_cases hp : p = 5
  · subst hp
    left
    exact five_case hMt hdet hirr hDrefl hDconjH hodd hnorm
  by_cases hp7 : p = 7
  · subst hp7
    right
    exact nonempty_omegaGL_equiv_GL_three_two hMt hdet
  · left
    intro s hs t ht
    exfalso
    have hprime : p.Prime := Fact.out
    have hp11 : 11 ≤ p := by
      by_contra hlt
      have h6 : p = 6 ∨ p = 8 ∨ p = 9 ∨ p = 10 := by omega
      rcases h6 with h | h | h | h <;> rw [h] at hprime <;> norm_num at hprime
    exact big_false hp11 hMt hdet hirr hDconjH hodd ht (hDrefl t ht) (hnorm t ht)

end CFSG.RankThree.PartOne.KF1322
