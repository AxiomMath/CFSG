module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ComponentShapes
public import CFSG.GroupTheory.PRankLeOneOfSylowLe
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.OmegaPlusTorus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Ctx23L

variable {D : Data G} {Ch : Choice2011 G}

theorem isCyclic_fitting_commutator_of_cyclic (D : Data G)
    (hcyc : IsCyclic ↥(CFSG.fittingSubgroup (Bar2 D.M))) :
    IsCyclic ↥(CFSG.fittingSubgroup ↥(commutator (Bar2 D.M))) := by
  let Fbar : Subgroup (Bar2 D.M) := CFSG.fittingSubgroup (Bar2 D.M)
  haveI : IsCyclic ↥Fbar := hcyc
  have hC₁ : (CFSG.fittingSubgroup ↥(commutator (Bar2 D.M))).map
      (commutator (Bar2 D.M)).subtype = commutator (Bar2 D.M) ⊓ Fbar :=
    CFSG.LocalCores.fitting_normal_intersection (commutator (Bar2 D.M))
  have hcycNF : IsCyclic ↥(commutator (Bar2 D.M) ⊓ Fbar) :=
    Subgroup.isCyclic_of_le inf_le_right
  refine (MulEquiv.isCyclic (Subgroup.equivMapOfInjective
    (CFSG.fittingSubgroup ↥(commutator (Bar2 D.M)))
    (commutator (Bar2 D.M)).subtype (commutator (Bar2 D.M)).subtype_injective)).mpr ?_
  rw [hC₁]
  exact hcycNF

theorem commutator_hinf_oTwoF_le_pCoreOf (c : Ctx23L D Ch) (h1930 : H1930 D)
    (hcyc : IsCyclic ↥(CFSG.fittingSubgroup (Bar2 D.M))) :
    ⁅Hinf D.M, oTwoFOf D.M⁆ ≤ CFSG.Open.pCoreOf 2 D.M :=
  (uc22p21c_commutator_bar_eq_bot_iff D.M).2
    (uc22p21c_commutator_perfectResidual_fitting_eq_bot
      (isCyclic_fitting_commutator_of_cyclic D hcyc))

theorem calC_normal_and_shape_excluded (c : Ctx23L D Ch) (h1930 : H1930 D) (h8 : S23_8 D Ch) :
    ∀ L ∈ calC D.M, (L.subgroupOf D.M).Normal ∧
      ¬ ∃ n : ℕ, Odd n ∧ (IsSp4 (Bar2 L) n ∨ IsSU3 (Bar2 L) n) :=
  hyp2120_two_of_s23_8 j1NotSp4SU3 D Ch h8 h1930 c

theorem pRank_barPreimage_centE_le_one (c : Ctx23L D Ch) (h1930 : H1930 D)
    (h2123 : S21_23 D Ch) (hcycN : IsCyclic ↥(CFSG.fittingSubgroup ↥(commutator (Bar2 D.M))))
    {p : ℕ} (hp : p ∈ D.sig) :
    CFSG.Open.pRank p (barPreimage D.M (centE D.M)) ≤ 1 := by
  haveI : Fact p.Prime := ⟨(D.sig_prime p hp).1⟩
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf p (barPreimage D.M (centE D.M))
  exact CFSG.pRank_le_one_of_isSylowOf_le (D.sig_prime p hp).1 hP.le hP le_rfl
    (CFSG.SectionRank.pRank_le_one_of_isCyclic (D.sig_prime p hp).1
      (h2123 h1930 c.toCtx21 p hp P hP hcycN).2.2.2.2)

theorem not_invertedIn_zpowers_of_torus (c : Ctx23L D Ch) (h1930 : H1930 D)
    (h2123 : S21_23 D Ch) (hcyc : IsCyclic ↥(CFSG.fittingSubgroup (Bar2 D.M)))
    {r : ℕ} {a b t : G} (_hT : OmegaPlusTorus c r a b t) {p : ℕ} (hp : p ∈ D.sig)
    (hrank : 1 < CFSG.Open.pRank p (barPreimage D.M (centE D.M))) :
    ¬ InvertedIn D.M (Subgroup.zpowers a) :=
  absurd hrank
    (not_lt.mpr (pRank_barPreimage_centE_le_one c h1930 h2123
      (isCyclic_fitting_commutator_of_cyclic D hcyc) hp))

end Ctx23L

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
