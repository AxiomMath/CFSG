module

public import CFSG.RankThree.GF2n.Stroth80.Sec9Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec91b
public import CFSG.Open.StatedDefs
public import CFSG.RankThree.GF2n.Stroth80.ClassicalQuasisimple
public import CFSG.RankThree.GF2n.Stroth80.Sec41iii
public import CFSG.RankThree.GF2n.Stroth80.Sec311Stmt
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.GroupTheory.Subgroup.Simple
public import CFSG.ClassicalGroups.Orthogonal.RootGroupSwap
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourSplitQuotient
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOAut
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOEightSwap
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOKlein
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOPlusLevi
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.G11Stmts
public import CFSG.RankThree.GF2n.Stroth80.FrobClause
public import CFSG.RankThree.GF2n.Stroth80.Sec12Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec310Nt
public import CFSG.RankThree.GF2n.Stroth80.Sec310Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec4Rt
public import CFSG.RankThree.GF2n.Stroth80.Sec4Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec6Stmt
public import CFSG.RankThree.GF2n.SupIndepDecomp
public import CFSG.RankThree.GF2n.Tim79CentC
public import CFSG.RankThree.GF2n.Tim79CentL
public import CFSG.RankThree.GF2n.Tim79Mod
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearBridge
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

theorem sec9_isEmpty_equiv_statedSL {K K' : Type} [Field K] [Finite K] [CharP K 2]
    (h4 : 4 ≤ Nat.card K) [Field K'] [Finite K'] (hKK' : Nat.card K' = Nat.card K) {m : ℕ}
    (hm : 2 ≤ m) :
    IsEmpty (↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus 2 K)) ≃*
      ↥(CFSG.Open.StatedSL m K')) := by
  refine ⟨fun ε => ?_⟩
  obtain ⟨e⟩ := statedOmega_plus_four_nonempty_equiv K h4
  have f : ↥(CFSG.Open.StatedSL m K') ≃*
      (↥(CFSG.Open.StatedSL 2 K) × ↥(CFSG.Open.StatedSL 2 K)) := ε.symm.trans e
  have hZP : Subgroup.center
      (↥(CFSG.Open.StatedSL 2 K) × ↥(CFSG.Open.StatedSL 2 K)) = ⊥ := by
    rw [Subgroup.center_prod, center_statedSL_two_eq_bot, Subgroup.bot_prod_bot]
  have hZX : Subgroup.center ↥(CFSG.Open.StatedSL m K') = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_center_iff] at hx
    rw [Subgroup.mem_bot]
    have hfx : f x ∈ Subgroup.center
        (↥(CFSG.Open.StatedSL 2 K) × ↥(CFSG.Open.StatedSL 2 K)) := by
      rw [Subgroup.mem_center_iff]
      intro p
      have h : f (f.symm p * x) = f (x * f.symm p) := by rw [hx (f.symm p)]
      simpa only [map_mul, MulEquiv.apply_symm_apply] using h
    rw [hZP, Subgroup.mem_bot] at hfx
    exact f.injective (hfx.trans (map_one f).symm)
  have hq : CFSG.IsQuasisimple ↥(CFSG.Open.StatedSL m K') :=
    statedSL_quasisimple_of_card m K' hm (by rw [hKK']; exact h4)
  have hXs : IsSimpleGroup ↥(CFSG.Open.StatedSL m K') := by
    obtain ⟨-, hs, -⟩ := hq
    have e' : (↥(CFSG.Open.StatedSL m K') ⧸ Subgroup.center ↥(CFSG.Open.StatedSL m K')) ≃*
        ↥(CFSG.Open.StatedSL m K') :=
      (QuotientGroup.quotientMulEquivOfEq hZX).trans QuotientGroup.quotientBot
    exact (MulEquiv.isSimpleGroup_congr e').mp hs
  have hPs : IsSimpleGroup (↥(CFSG.Open.StatedSL 2 K) × ↥(CFSG.Open.StatedSL 2 K)) :=
    f.symm.isSimpleGroup
  have hsimple2 : IsSimpleGroup ↥(CFSG.Open.StatedSL 2 K) :=
    isSimpleGroup_statedSL_two (statedSL_quasisimple_of_card 2 K le_rfl h4)
  obtain ⟨a, ha⟩ := exists_ne (1 : ↥(CFSG.Open.StatedSL 2 K))
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (MonoidHom.snd ↥(CFSG.Open.StatedSL 2 K) ↥(CFSG.Open.StatedSL 2 K)).ker with hbot | htop
  · have hinj := (MonoidHom.ker_eq_bot_iff _).mp hbot
    have h2 : ((a, 1) : ↥(CFSG.Open.StatedSL 2 K) × ↥(CFSG.Open.StatedSL 2 K)) = (1, 1) :=
      hinj (by rfl)
    exact ha (congrArg Prod.fst h2)
  · have hmem : ((1 : ↥(CFSG.Open.StatedSL 2 K)), a) ∈
        (MonoidHom.snd ↥(CFSG.Open.StatedSL 2 K) ↥(CFSG.Open.StatedSL 2 K)).ker := by
      rw [htop]
      exact Subgroup.mem_top _
    rw [MonoidHom.mem_ker] at hmem
    exact ha (by simpa using hmem)

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec9_not_SLNat {hc : Ctx M Q Z B} {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) :
    ¬ SLNat hc t := by
  rintro ⟨K', fK', finK', hK', m, hm, φ', hφ'r, hφ'k, -⟩
  obtain ⟨K, fK, finK, hK, φ, hφr, hφk, -⟩ := hs.plus4
  obtain ⟨jj, kk, hZ2, -⟩ := hc.hyp.cp
  haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hK.trans hZ2)
  have h4 : 4 ≤ Nat.card K := by rw [hK]; exact hc.hyp.q4
  have hKK' : Nat.card K' = Nat.card K := hK'.trans hK.symm
  refine (sec9_isEmpty_equiv_statedSL h4 hKK' hm).false ?_
  exact (MulEquiv.subgroupCongr hφr.symm).trans
    ((QuotientGroup.quotientKerEquivRange φ).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq (hφk.trans hφ'k.symm)).trans
        ((QuotientGroup.quotientKerEquivRange φ').trans (MulEquiv.subgroupCongr hφ'r))))

theorem sec9NComm_of_311b (h34 : Stroth34Statement) (h311 : Stroth311bCommStatement) :
    Sec9NCommStatement := by
  intro G _ _ M Q Z B hc n t hs
  have hs5 := hs.toSec5
  obtain ⟨T, hT⟩ := exists_centLB hc t
  have hNT := h311 G M Q Z B hc n hs5.width hs5.n_gt hs5.noA2 hs5.gen t hs5.mem hs5.notQ
    (sec9_Rt_ne_LB h34 hs) (sec9_not_SLNat hs) T hT
  exact fun x hx => ((hT x).mp (hNT hx)).1

end CFSG.RankThree.GF2n.Stroth80
