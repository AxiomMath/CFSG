module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P2251r
import CFSG.LocalAnalysis.UniquenessCase.UC22S2251Factors
import CFSG.LocalAnalysis.UniquenessCase.UC22S2251Cyclic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Bar13
import CFSG.LocalAnalysis.UniquenessCase.UC7R71Three
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
import CFSG.LocalAnalysis.AGLEmbedding.LemmaBGroup
import CFSG.GroupTheory.AllPSubgroupsIsCyclicOfPRankLeOne
import CFSG.GroupTheory.CharacteristicNormalizer
import CFSG.RankThree.PartOne.S11c.Simple168
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22a
import CFSG.LocalAnalysis.UniquenessCase.UC22S2251Normalizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LocalAnalysis.RankThreeUC (Setup Standing AGL81TheoremC)

variable {G : Type} [Group G] [Finite G]

set_option linter.unusedVariables false in
theorem s22_5_1RStarSn_dataOfSetup (hS : Standing G) (hUC : CFSG.Open.rankThreeUC G)
    (hC : AGL81TheoremC G) (S : Setup G) (hMS : S.InMSigma) :
    S22_5_1RStarSn (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True) := by
  classical
  intro _h1930 _c m Nb hNb i hk _he hbad hS3 _hσ hrk _hcyc p hp C hCne hCS hch hCM
  let D := PartTwo.Three.dataOfSetup hS S
  have : Fact p.Prime := ⟨(D.sig_prime p hp).1⟩
  have hpP := (D.sig_prime p hp).1
  have hp2 := (D.sig_prime p hp).2
  have hbad' : IsL2Ev ↥(Nb i) 2 ∨ IsL3 ↥(Nb i) 1 ∨ IsS5 ↥(Nb i) := by
    rcases hNb.2 i with ⟨n, hn⟩ | hn | hn
    · by_cases hn2 : n = 2
      · exact Or.inl (hn2 ▸ hn)
      · exact (hbad ⟨n, hn, hn2⟩).elim
    · exact Or.inr (Or.inl hn)
    · exact Or.inr (Or.inr hn)
  have hns : ¬ Group.IsSolvable D.M := by
    intro hs
    have hsN : Group.IsSolvable ↥(mbarImage D.M D.U (proofN D)) := by
      have := hs
      exact Group.isSolvable_of_surjective
        (f := (QuotientGroup.mk' (kerAct D.M D.U).normalCore).subgroupMap
          ((proofN D).subgroupOf D.M)) (MonoidHom.subgroupMap_surjective _ _)
    have hle : ⁅Nb i, Nb i⁆ ≤ mbarImage D.M D.U (proofN D) :=
      (Subgroup.commutator_le_self _).trans (hNb.1.1.symm ▸ le_iSup Nb i)
    have hsB : Group.IsSolvable ↥⁅Nb i, Nb i⁆ :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
        (Subgroup.inclusion_injective hle)
    exact uc22p22a_qs_not_solvable (P2251b.badShape_commutator (hNb.2 i) hbad).layerShape.isQuasisimple hsB
  have hσstd := UC6S846.sigmaStd_dataOfSetup hS S
  have hsp := UC6S846.sp_of_mem_sig hσstd hns hp
  have hp5 : 5 ≤ p := by
    have hp3 : p ≠ 3 := by
      intro h
      subst p
      exact hk (by unfold Data.k CFSG.LocalAnalysis.RankThreeUC.kParam; rw [if_pos hsp])
    have hpp := hpP.two_le
    have hp4 : p ≠ 4 := by intro h; subst p; norm_num at hpP
    omega
  have hM3 : CFSG.pRank 3 D.M ≤ 3 := by
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact PartTwo.Three.pRank_le_three_dataOfSetup hS S Nat.prime_three (by norm_num) le_rfl
  have hm4 : m ≤ 4 := S2251.s3_factor_count_le D hNb i hS3 hM3
  have hV := P22x.uc22p22xf_hV D
  set Hb : Subgroup (MBar D.M D.U) := mbarImage D.M D.U (Subgroup.normalizer (C : Set G) ⊓ D.M)
  set Db : Subgroup (MBar D.M D.U) :=
    Subgroup.centralizer (mbarImage D.M D.U (proofN D) : Set (MBar D.M D.U))
  have hNn : (mbarImage D.M D.U (proofN D)).Normal :=
    uc22br4_mbarImage_normal _ _ _ (uc22p22e_jOf_le_self D.M) (uc22p22t_M_le_normalizer_jOf D)
  have hDn : Db.Normal := Subgroup.normal_centralizer
  have hSC := CFSG.GroupTheory.normalizer_le_normalizer_of_characteristic hCS hch
  have hDH : Db ≤ Hb :=
    (S2251.centralizer_proofN_le_mbarImage_normalizer D).trans
      (P22x.mbarImage_mono _ _ (fun x hx => ⟨hSC hx.2, hx.1⟩))
  have hidx : ∀ P : Subgroup (MBar D.M D.U), IsPGroup p P → Db.relIndex P ≤ p :=
    fun P hP => S2251.centralizer_relIndex_le_prime hNb.1 (hNb.2) i hbad' hS3 hpP hp5
      (by omega) hP (by rw [Subgroup.normalizer_eq_top_iff.2 hNn]; exact le_top)
  have hHrank : CFSG.Open.pRank p (Subgroup.normalizer (C : Set G) ⊓ D.M) ≤ 1 := by
    by_contra h
    have hlocal : CFSG.Open.IsTwoLocal (Subgroup.normalizer (C : Set G)) :=
      ⟨C, hCne, D.sylowM.isPGroup.to_le (hCS.trans inf_le_left), rfl⟩
    have hrank : 2 ≤ CFSG.Open.pRank p (Subgroup.normalizer (C : Set G) ⊓ D.M) := by omega
    exact hCM (hp.2.choose_spec.u2 _ hlocal (by simpa only [D,
      PartTwo.Three.dataOfSetup] using hrank))
  have hHbcyc : ∀ P : Subgroup (MBar D.M D.U), P ≤ Hb → IsPGroup p P → IsCyclic P := by
    intro P hPH hP
    have hQcyc : ∀ Q : Subgroup D.M,
        Q ≤ (Subgroup.normalizer (C : Set G) ⊓ D.M).subgroupOf D.M → IsPGroup p Q → IsCyclic Q := by
      intro Q hQ hQp
      have hle : Q.map D.M.subtype ≤ Subgroup.normalizer (C : Set G) ⊓ D.M := by
        rintro _ ⟨x, hx, rfl⟩
        exact hQ hx
      have hc := CFSG.all_pSubgroups_isCyclic_of_pRank_le_one hpP hp2 hHrank _ hle (hQp.map _)
      exact isCyclic_of_injective (Q.equivMapOfInjective D.M.subtype D.M.subtype_injective).toMonoidHom
        (Q.equivMapOfInjective D.M.subtype D.M.subtype_injective).injective
    exact CFSG.AGLEmbedding.isCyclic_of_le_map
      (QuotientGroup.mk' (kerAct D.M D.U).normalCore) hQcyc hPH hP
  have hPDb := S2251.pSubgroups_le_of_cyclic hpP hDH
    (by rw [← CFSG.SectionRank.pRank_eq_open_pRank_top, hrk p hp]) hidx hHbcyc
  have hYDb : mbarImage D.M D.U (Opp p (Subgroup.normalizer (C : Set G) ⊓ D.M)) ≤ Db := by
    have hYpre : Opp p (Subgroup.normalizer (C : Set G) ⊓ D.M) ≤
        (Db.comap (QuotientGroup.mk' (kerAct D.M D.U).normalCore)).map D.M.subtype := by
      apply (Subgroup.closure_le _).2
      rintro y ⟨hyH, n, hn⟩
      have hyp : IsPGroup p (Subgroup.zpowers y) :=
        IsPGroup.of_card (n := n) (by rw [Nat.card_zpowers, hn])
      have hpb : IsPGroup p (mbarImage D.M D.U (Subgroup.zpowers y)) :=
        hyp.comap_subtype.map _
      have hleH : mbarImage D.M D.U (Subgroup.zpowers y) ≤ Hb :=
        P22x.mbarImage_mono _ _ (Subgroup.zpowers_le.2 hyH)
      exact ⟨⟨y, hyH.2⟩, hPDb _ hleH hpb ⟨⟨y, hyH.2⟩, Subgroup.mem_zpowers y, rfl⟩, rfl⟩
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hYpre hx
    have hyx' : y = x := Subtype.ext hyx
    have hy' : (QuotientGroup.mk' (kerAct D.M D.U).normalCore) y ∈ Db := hy
    simpa only [hyx'] using hy'
  have hNY : Subgroup.normalizer (C : Set G) ⊓ D.M ≤
      Subgroup.normalizer (Opp p (Subgroup.normalizer (C : Set G) ⊓ D.M) : Set G) := fun x hx =>
    CFSG.RankThree.PartOne.mem_normalizer_of_forall_conj_mem
      (PartTwo.s13_Bar13_opp_conjInv p (M := Subgroup.normalizer (C : Set G) ⊓ D.M)
        (fun g hg x hx => (Subgroup.normalizer (C : Set G) ⊓ D.M).mul_mem
          ((Subgroup.normalizer (C : Set G) ⊓ D.M).mul_mem hg hx)
          ((Subgroup.normalizer (C : Set G) ⊓ D.M).inv_mem hg)) x hx)
  exact S2251.isSubnormal_mbarImage_of_centralizes D hNY hSC hYDb

end CFSG.LocalAnalysis.UniquenessCase.UC22
