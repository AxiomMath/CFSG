module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.StandardType.GGResLeaf
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem three_dvd_card_of_hasLabel_D4 {X : Type} [Group X] [Finite X]
    {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (htag : lab.tag = .D) (hrank : lab.rank = 4)
    (hHas : CFSG.StandardType.GGHasLabel lab (X ⧸ Subgroup.center X)) :
    3 ∣ Nat.card X := by
  obtain ⟨tag, rank, n⟩ := lab
  subst htag
  subst hrank
  have hn : 1 ≤ n := hΛ.1
  have hSC : CFSG.Open.StatedClassicalModel (X ⧸ Subgroup.center X)
      .POmegaPlus 4 2 n := by
    unfold CFSG.StandardType.GGHasLabel at hHas
    dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hHas
    unfold LargeEvenRecipeOmegaPlus at hHas
    obtain ⟨K, hK, hKfin, hKcard, ⟨e⟩⟩ := hHas
    exact ⟨⟨Nat.prime_two, hn, le_rfl⟩, K, hK, hKfin, hKcard, ⟨e⟩⟩
  have hD4 : CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.IsD4Type X :=
    ⟨2, n, by norm_num, hSC⟩
  exact CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.d4r_three_dvd hD4

theorem J_le_K_of_label_D4 (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    {labJ : LargeEvenLabel} (hJΛ : LargeEvenInLambda2 labJ)
    (hJtag : labJ.tag = .D) (hJrank : labJ.rank = 4)
    (hJHas : CFSG.StandardType.GGHasLabel labJ (J ⧸ Subgroup.center J)) :
    J ≤ K := by
  have hpJ : 3 ∣ Nat.card J :=
    three_dvd_card_of_hasLabel_D4 hJΛ hJtag hJrank hJHas
  exact le_of_ggNbr hLB hH.1.1 hH.1.2.2 hpJ hH.2.2.2.2.1

end CFSG.StandardType

end
