module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Bridge13
public import CFSG.Blueprint.LieModelAPI
public import CFSG.GroupTheory.PerfectActionCritical
public import CFSG.GroupTheory.PRankQuotientLift
public import CFSG.GroupTheory.SLTwoInvertsElemAbelian
public import CFSG.RankThree.PartOne.S10.PlaneCoreBounds
public import CFSG.RankThree.PartTwo.Sec4.Item49CharTwo
public import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem isSolvable_outer_barImage_center (D : Data G) {p : ℕ} (hp : Hyp1754 D p)
    (hcyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) :
    ∀ L ∈ calC D.M,
      Group.IsSolvable (Outer (↥(barImage D.M L) ⧸ Subgroup.center ↥(barImage D.M L))) := by
  intro L hL
  have hcomp : CFSG.IsComponent (barImage D.M L) := s13_barImage_isComponent hL
  obtain ⟨e⟩ := s13_bar_equiv hL
  rcases (hp.2 L hL).2 with hthin | ⟨n, hU⟩ | hL3
  · have hrank : CFSG.pRank 3 (↥(barImage D.M L) ⧸ Subgroup.center ↥(barImage D.M L)) ≤ 1 :=
      CFSG.RankThree.OddKernel.pRank_le_one_of_surjective Nat.prime_three (by norm_num)
        ((QuotientGroup.mk' _).comp e.toMonoidHom)
        ((QuotientGroup.mk'_surjective _).comp e.surjective)
        (s13_pRank_bar_le_one hthin Nat.prime_three (by norm_num))
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact Group.isSolvable_of_comm
      (CFSG.RankThree.PartTwo.Sec4.Item49CharTwo.outer_mul_comm (hcyc _
        (((s13_isKGroup_bar_M D).subgroup (barImage D.M L)).quotient _) hcomp.1.2.1
        hcomp.1.2.2
        fun P => s13_Bridge13_isCyclic_of_pRank_le_one Nat.prime_three (by norm_num)
          P.isPGroup' ((CFSG.SectionRank.pRank_sylow P).2 ▸ hrank)))
  · exact (UnitaryHigher.unitary_rank_one_classical_model_schreier (LieModel.statedClassicalModel
      (LieModel.quotient_center_of_mulEquiv e (uc22p22d_isSU3_of_isU3 hL.2.2 hU).2)
      (by decide))).2
  · haveI : IsSimpleGroup (Bar2 L) :=
      CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL3
    exact (UnitaryHigher.linear_higher_classical_model_schreier le_rfl
      (LieModel.statedClassicalModel (LieModel.quotient_center_of_mulEquiv e
        (LieModel.quotient_center
          (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (s13_nonabelian_bar hL)).2 hL3))
        (by decide))).2

theorem perfectResidual_le_centralizer_pCore (D : Data G) {V₀ V : Subgroup G}
    (hV : Hyp125 D V₀ V) (h22 : R17_2_2At D V₀ V hV) (h23 : R17_2_3At D V₀ V hV)
    {q : ℕ} (hq : q.Prime) :
    CFSG.perfectResidual (Bar2 D.M) ≤
      Subgroup.centralizer (CFSG.pCore q (Bar2 D.M) : Set (Bar2 D.M)) := by
  classical
  set Q := Bar2 D.M with hQ
  let P : Subgroup Q := CFSG.perfectResidual Q
  have hP : ⁅P, P⁆ = P := Subgroup.isPerfect_iff.mp
    (CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_isPerfect (G := Q))
  by_cases hq2 : q = 2
  · subst q
    rw [s13_pCore_bar_eq_bot D.M]
    exact Subgroup.le_centralizer_iff.mpr (by simp)
  by_cases hQq : CFSG.pCore q Q = ⊥
  · rw [hQq]
    exact Subgroup.le_centralizer_iff.mpr (by simp)
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Nontrivial ↥(CFSG.pCore q Q) := (Subgroup.nontrivial_iff_ne_bot _).2 hQq
  let Qq : Subgroup Q := CFSG.pCore q Q
  haveI : Qq.Normal := CFSG.pCore_normal
  have hQqp : IsPGroup q ↥Qq := CFSG.pCore_isPGroup
  obtain ⟨Cq, hCqchar, -, hCqcomm, hCqexp, hCqfix⟩ :=
    CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup (p := q) hq2 hQqp
  let CqQ : Subgroup Q := Cq.map Qq.subtype
  have hCqQnormal : CqQ.Normal := by
    haveI : Cq.Characteristic := hCqchar
    exact ConjAct.normal_of_characteristic_of_normal
  haveI : CqQ.Normal := hCqQnormal
  let eC : ↥Cq ≃* ↥CqQ := Cq.equivMapOfInjective Qq.subtype Qq.subtype_injective
  have hCqQp : IsPGroup q ↥CqQ := hQqp.to_subgroup Cq |>.map Qq.subtype
  have hPC : P ≤ Subgroup.centralizer (CqQ : Set Q) := by
    by_cases hcycCq : IsCyclic ↥Cq
    · exact CFSG.LocalAnalysis.CyclicNormalConj.le_centralizer_of_perfect
        (isCyclic_of_surjective eC.toMonoidHom eC.surjective) hP
    let N2 : Subgroup ↥D.M := CFSG.pCore 2 ↥D.M
    haveI : N2.Normal := CFSG.pCore_normal
    obtain ⟨k2, hk2⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup : IsPGroup 2 ↥N2)
    let π : ↥D.M →* Q := QuotientGroup.mk' N2
    have hcop : q.Coprime (Nat.card N2) := by
      rw [hk2]
      exact ((Nat.coprime_primes hq Nat.prime_two).2 hq2).pow_right k2
    have hq_not_dvd_N2 : ¬ q ∣ Nat.card N2 := (Nat.Prime.coprime_iff_not_dvd hq).mp hcop
    obtain ⟨DsubM, hDsubMp, ⟨eDsub⟩, hDsup⟩ :=
      CFSG.GroupTheory.exists_isPGroup_of_coprime_kernel N2 hq hcop (K := CqQ) hCqQp
    have hDmap : DsubM.map π = CqQ := by
      have h := congrArg (Subgroup.map π) hDsup
      rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq,
        Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)] at h
    let Dg : Subgroup G := DsubM.map D.M.subtype
    have hDleM : Dg ≤ D.M := Subgroup.map_subtype_le _
    have hDp : IsPGroup q ↥Dg := hDsubMp.map D.M.subtype
    let eDC : ↥Dg ≃* ↥Cq :=
      ((DsubM.equivMapOfInjective D.M.subtype D.M.subtype_injective).symm.trans eDsub).trans
        eC.symm
    have hDnc : ¬ IsCyclic ↥Dg := fun hcyc =>
      hcycCq (isCyclic_of_surjective eDC.toMonoidHom eDC.surjective)
    have hDexp : ∀ x ∈ Dg, x ^ q = 1 := CFSG.AGLEmbedding.pow_eq_one_of_mulEquiv eDC hCqexp
    have hCtop : ⁅⁅(⊤ : Subgroup ↥Cq), (⊤ : Subgroup ↥Cq)⁆, (⊤ : Subgroup ↥Cq)⁆ = ⊥ :=
      Subgroup.commutator_top_right_eq_bot_iff_le_center.mpr
        (CFSG.RankThree.PartOne.PlaneCore.commutator_le_center_of_critical hCqcomm)
    have hDtop : ⁅⁅(⊤ : Subgroup ↥Dg), (⊤ : Subgroup ↥Dg)⁆, (⊤ : Subgroup ↥Dg)⁆ = ⊥ := by
      have hmap : (⁅⁅(⊤ : Subgroup ↥Dg), (⊤ : Subgroup ↥Dg)⁆, (⊤ : Subgroup ↥Dg)⁆).map
          eDC.toMonoidHom = ⊥ := by
        rw [Subgroup.map_commutator, Subgroup.map_commutator, Subgroup.map_top,
          MonoidHom.range_eq_top.mpr eDC.surjective, hCtop]
      exact (Subgroup.map_eq_bot_iff_of_injective _ (f := eDC.toMonoidHom) eDC.injective).mp hmap
    have hDclass : ⁅⁅Dg, Dg⁆, Dg⁆ = ⊥ := by
      have h := congrArg (Subgroup.map Dg.subtype) hDtop
      rwa [Subgroup.map_commutator, Subgroup.map_commutator, Subgroup.map_top,
        Subgroup.range_subtype, Subgroup.map_bot] at h
    have hsubmap : ((CqQ.comap π).map D.M.subtype).subgroupOf D.M = CqQ.comap π :=
      Subgroup.comap_map_eq_self_of_injective D.M.subtype_injective _
    have hDnormal : ((Dg ⊔ CFSG.Open.pCoreOf 2 D.M).subgroupOf D.M).Normal := by
      rw [show Dg ⊔ CFSG.Open.pCoreOf 2 D.M = (DsubM ⊔ N2).map D.M.subtype by
          rw [Subgroup.map_sup]; rfl, hDsup, hsubmap]
      exact Subgroup.Normal.comap hCqQnormal π
    have hDcard : Nat.card Dg = q ^ 2 :=
      (h22 q Dg hq hq2 hDleM hDp hDnc hDexp hDclass hDnormal).1
    have hCqQcard : Nat.card CqQ = q ^ 2 := by
      rw [← Nat.card_congr eC.toEquiv, ← Nat.card_congr eDC.toEquiv]
      exact hDcard
    have hDsubMleH : DsubM ≤ CqQ.comap π := hDsup ▸ le_sup_left
    have hirr := (h23 q Dg hq hq2 hDleM hDp hDnc hDexp hDclass hDnormal).1
    rw [IrrOn] at hirr
    push Not at hirr
    obtain ⟨W, hWle, hWN, hWnebot, hWneD⟩ := hirr
    have hWleM : W ≤ D.M := hWle.trans hDleM
    have hWcard : Nat.card W = q :=
      CFSG.GroupTheory.card_eq_prime_of_le_of_card_eq_sq hWle hDcard hWnebot hWneD
    let Wstar : Subgroup Q := (W.subgroupOf D.M).map π
    have hWstar_le : Wstar ≤ CqQ := by
      rintro x ⟨m, hm, rfl⟩
      obtain ⟨d, hd, hdm⟩ := Subgroup.mem_map.mp (hWle hm)
      have hdm' : d = m := Subtype.ext hdm
      rw [← hdm']
      exact Subgroup.mem_comap.mp (hDsubMleH hd)
    have hNtop : (Subgroup.normalizer (DsubM : Set ↥D.M)).map π = ⊤ := by
      rw [CFSG.GroupTheory.normal_coprime_quotient_normalizer q N2 hq_not_dvd_N2 DsubM hDsubMp,
        hDmap]
      exact Subgroup.normalizer_eq_top_iff.mpr hCqQnormal
    have hQleW : (⊤ : Subgroup Q) ≤ Subgroup.normalizer (Wstar : Set Q) := by
      rw [← hNtop]
      rintro _ ⟨n, hn, rfl⟩
      have hnWg : ((n : ↥D.M) : G) ∈ Subgroup.normalizer (W : Set G) := by
        have hnG : ((n : ↥D.M) : G) ∈ Subgroup.normalizer (Dg : Set G) := by
          have hmapn := Subgroup.le_normalizer_map (H := DsubM) D.M.subtype
            (Subgroup.mem_map_of_mem D.M.subtype hn)
          simpa [Dg] using hmapn
        exact hWN ⟨n.2, hnG⟩
      have hnW : n ∈ Subgroup.normalizer ((W.subgroupOf D.M : Subgroup ↥D.M) : Set ↥D.M) := by
        have h1 : n ∈ (Subgroup.normalizer (W : Set G)).subgroupOf D.M :=
          Subgroup.mem_subgroupOf.mpr hnWg
        simpa [Subgroup.subgroupOf_normalizer_eq hWleM] using h1
      have hmapn := Subgroup.le_normalizer_map (H := W.subgroupOf D.M) π
        (Subgroup.mem_map_of_mem π hnW)
      simpa [Wstar] using hmapn
    haveI hWstar_normal : Wstar.Normal :=
      Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hQleW)
    have hWstarcard : Nat.card Wstar = q :=
      (CFSG.RankThree.PartOne.StrongP.card_map_quotient_of_coprime (E := W.subgroupOf D.M)
        ((hDp.to_le hWle).comap_of_injective D.M.subtype D.M.subtype_injective)
        hq_not_dvd_N2).trans
        ((Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWleM).toEquiv).trans hWcard)
    exact CFSG.GroupTheory.le_centralizer_of_isPerfect_of_card_eq_sq hP hCqQcard hWstar_le
      hWstarcard
  have hPD : P.map (MulAut.conjNormal (H := Qq)) ≤ fixingSubgroup (MulAut Qq) (Cq : Set Qq) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_fixingSubgroup_iff]
    intro c hc
    apply Subtype.ext
    change (((MulAut.conjNormal (H := Qq) x) c : Qq) : Q) = (c : Q)
    rw [MulAut.conjNormal_apply,
      ← Subgroup.mem_centralizer_iff.mp (hPC hx) (c : Q) (Subgroup.mem_map_of_mem Qq.subtype hc),
      mul_inv_cancel_right]
  exact ((Subgroup.map_eq_bot_iff _).mp
    (CFSG.GroupTheory.map_eq_bot_of_isPerfect_of_le_fixingSubgroup
      (H := Q) (Q := Qq) (q := q) _ Cq hCqfix hP hPD)).trans
    (CFSG.AGLEmbedding.ker_conjNormal_eq_centralizer Qq).le

theorem perfectResidual_le_centralizer_fitting (D : Data G) {V₀ V : Subgroup G}
    (hV : Hyp125 D V₀ V) (h22 : R17_2_2At D V₀ V hV) (h23 : R17_2_3At D V₀ V hV) :
    CFSG.perfectResidual (Bar2 D.M) ≤
      Subgroup.centralizer (CFSG.fittingSubgroup (Bar2 D.M) : Set (Bar2 D.M)) :=
  CFSG.subgroup_le_centralizer_fitting_of_le_centralizer_pCores fun q =>
    perfectResidual_le_centralizer_pCore D hV h22 h23 (Nat.prime_of_mem_primeFactors q.1.2)

theorem layer_seventeen_fiftyfour (D : Data G) {p : ℕ} (hp : Hyp1754 D p)
    {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    (h22 : R17_2_2At D V₀ V hV) (h23 : R17_2_3At D V₀ V hV)
    (hcyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) :
    CFSG.perfectResidual (Bar2 D.M) = CFSG.layer (Bar2 D.M) := by
  refine le_antisymm
    (CFSG.LocalAnalysis.ComponentInitial.unique_perfect_component_normalizer_enters_layer
      CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_isPerfect
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        (perfectResidual_le_centralizer_fitting D hV h22 h23)) (fun K hK => ?_) (fun K hK => ?_))
    (uc22p21c_le_perfectResidual _ CFSG.LocalCores.layer_perfect)
  · obtain ⟨L, hL, rfl⟩ := s13_exists_calC_of_component D.M hK
    exact le_top.trans (Subgroup.normalizer_eq_top_iff.mpr
      (s13_barImage_normal (hp.2 L hL).1)).ge
  · obtain ⟨L, hL, rfl⟩ := s13_exists_calC_of_component D.M hK
    exact isSolvable_outer_barImage_center D hp hcyc L hL

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
