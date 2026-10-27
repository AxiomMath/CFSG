module

public import CFSG.LocalAnalysis.StandardType.GGTPNPCompDefs
public import CFSG.LocalAnalysis.StandardType.GGTPNDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyDichotomyBasic
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFlatIVPComp
public import CFSG.LocalAnalysis.StandardType.GGTPNTrOnlyAmbB
public import CFSG.LocalAnalysis.StandardType.GGTPNTrOnlyTrans
public import CFSG.LocalAnalysis.StandardType.GGTableBTransport
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentJLevel
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrSourceChange

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.ComponentClassification

theorem tpo_ggTPNOnlyAmb_le_of_pComp (hQ : GGPCompCentQuasisimple fun _ => True)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hc : GGConfig p B Bs x L D J) (hpJ : p ∣ Nat.card J) (hL : GGInnerDiagOn Bs L) {y : G}
    (hD : D = Subgroup.closure {x, y}) {S : Subgroup G}
    (hS : LargeEvenPComponent p (Subgroup.centralizer (D : Set G)) S) (hSL : S ≤ L) : S = J := by
  have hp : p.Prime := hc.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hc.1.2.2.2.2.2.1.2.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hSstar : LargeEvenSStar p B x L := hc.1.2.2.2.2.2.2.1
  have hDJ : LargeEvenStdSubPre p B x L D J := hc.2.2.1
  have hx1 : x ≠ 1 := hSstar.2.2.1
  have hxL : L ≤ Subgroup.centralizer ({x} : Set G) := hSstar.2.2.2.1.1
  have hxp : x ^ p = 1 := hSstar.1.1.2 x hSstar.2.1
  have hcardD : Nat.card D = p ^ 2 := hDJ.2.2.1
  have hxD : x ∈ D := hDJ.2.2.2.1
  have hJeq : J = LargeEvenLayer (L ⊓ Subgroup.centralizer (D : Set G)) := hDJ.2.2.2.2.1
  have hJcomp : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) := hDJ.2.2.2.2.2.1
  have hCD : Subgroup.centralizer (D : Set G) =
      Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G) := by
    rw [hD, Subgroup.centralizer_closure]
    ext g
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  have hyNotZp : y ∉ Subgroup.zpowers x := by
    intro hy
    have hDle : D ≤ Subgroup.zpowers x := by
      rw [hD]
      rw [Subgroup.closure_le]
      intro z hz
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hzx | hzy
      · rw [hzx]; exact Subgroup.mem_zpowers x
      · rw [hzy]; exact hy
    have hxcard : Nat.card (Subgroup.zpowers x) = p := by
      rw [Nat.card_zpowers, orderOf_eq_prime hxp hx1]
    have hle : p ^ 2 ≤ p := by
      rw [← hcardD]
      exact (Subgroup.card_le_of_le hDle).trans_eq hxcard
    have hle' : p * p ≤ p := by rwa [Nat.pow_two] at hle
    have hmul : p * p ≤ p * 1 := by simpa using hle'
    have hp1 : p ≤ 1 := Nat.le_of_mul_le_mul_left hmul hp.pos
    have h2p : 2 ≤ p := hp.two_le
    omega
  have hyD : y ∈ D := hD ▸ Subgroup.subset_closure (Set.mem_insert_of_mem x rfl)
  have hyB : y ∈ B := hDJ.1 hyD
  have hyBs : y ∈ Bs := hc.2.1.1 hyB
  have hNB : Bs ≤ Subgroup.normalizer (L : Set G) := ggInnerDiagOn_le_normalizer hL
  have hyN : y ∈ Subgroup.normalizer (L : Set G) := hNB hyBs
  let E : Subgroup (MulAut ↥L) := ggAutsOf L Bs hNB
  let ybar : MulAut ↥L := L.normalizerMonoidHom ⟨y, hyN⟩
  have hybarE : ybar ∈ E :=
    (mem_ggAutsOf hNB).2 ⟨y, hyBs, rfl⟩
  have hCBL : B ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x :=
    inf_centralizer_eq_zpowers_of_sstar hp hSstar
  have hybar_ne : ybar ≠ 1 := by
    intro h1
    have hyC : y ∈ Subgroup.centralizer (L : Set G) :=
      (normalizerMonoidHom_eq_one_iff hyN).1 h1
    have hmem : y ∈ B ⊓ Subgroup.centralizer (L : Set G) := ⟨hyB, hyC⟩
    rw [hCBL] at hmem
    exact hyNotZp hmem
  have hy1 : y ≠ 1 := fun h => hyNotZp (h.symm ▸ Subgroup.one_mem (Subgroup.zpowers x))
  have horder_y : orderOf y = p :=
    orderOf_eq_prime (hSstar.1.1.2 y hyB) hy1
  have hord : orderOf ybar = p := by
    have hdvd : orderOf ybar ∣ p := by
      have h1 : orderOf (L.normalizerMonoidHom ⟨y, hyN⟩) ∣
          orderOf (⟨y, hyN⟩ : ↥(Subgroup.normalizer (L : Set G))) := orderOf_map_dvd _ _
      rw [Subgroup.orderOf_mk, horder_y] at h1
      exact h1
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hybar_ne
    · exact h1
  have hmark' : LargeEvenMarking ↥L fun _ _ _ I _ θ => GGInducedInn E θ I :=
    largeEvenMarking_mono (fun _ _ _ I _ θ h => ggInducedInn_of_clause3 h.1 θ h.2) hL
  obtain ⟨lab, hlab, hhas, R, _instR, I, F, θ, _hP⟩ := largeEvenMarking_exists_hasLabel hL
  have hSpcCD : CFSG.IsPComponent p
      (S.subgroupOf (Subgroup.centralizer (D : Set G))) :=
    (ggLargeEvenPComponent_iff p (Subgroup.centralizer (D : Set G)) S).1 hS |>.2
  set H : Subgroup G := L ⊓ Subgroup.centralizer (D : Set G) with hHdef
  have hHleL : H ≤ L := inf_le_left
  have hHleCD : H ≤ Subgroup.centralizer (D : Set G) := inf_le_right
  have hSleH : S ≤ H := fun s hs => ⟨hSL hs, hS.1 hs⟩
  have hSpcH : CFSG.IsPComponent p (S.subgroupOf H) :=
    ggPComponent_subgroupOf_of_le p hSleH hHleCD hSpcCD
  have hHeq : L ⊓ Subgroup.centralizer (D : Set G) =
      L ⊓ Subgroup.centralizer ({y} : Set G) := by
    rw [hCD, ← inf_assoc, inf_eq_left.mpr hxL]
  have hfix : ggAutFixedSubgroup ybar = H.subgroupOf L := by
    have h1 := ggAutFixedSubgroup_normalizerMonoidHom hyN
    rw [h1]
    exact congrArg (fun K : Subgroup G => K.subgroupOf L) hHeq.symm
  have hSpcInside : CFSG.IsPComponent p
      ((S.subgroupOf L).subgroupOf (H.subgroupOf L)) :=
    (CFSG.ComponentClassification.UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff'
      (X := L) (Y := H) (L := S) hHleL p hp).2 hSpcH
  have hScompFixed : LargeEvenPComponent p (ggAutFixedSubgroup ybar) (S.subgroupOf L) := by
    refine (ggLargeEvenPComponent_iff p (ggAutFixedSubgroup ybar) (S.subgroupOf L)).2
      ⟨?_, ?_⟩
    · rw [hfix]
      intro z hz
      exact hSleH hz
    · rw [hfix]
      exact hSpcInside
  have hquasi : CFSG.IsQuasisimple ↥(S.subgroupOf L) :=
    hQ p hp hp2 ↥L E ybar lab hlab trivial hhas hybarE hord hmark' (S.subgroupOf L) hScompFixed
  have hquasiS : CFSG.IsQuasisimple ↥S :=
    CFSG.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hSL).symm hquasi
  have hSdata := (ggPComponent_iff_data p hSleH).1 hSpcH
  have hSsubH : IsSubnormal S H := hSdata.1
  have hScompH : IsComponentOf S H :=
    ⟨hSleH, hSsubH, ⟨Group.isPerfect_def.mp hquasiS.1, hquasiS.2.1⟩⟩
  have hSleJ : S ≤ J := by
    have hle : S ≤ LargeEvenLayer H := le_sSup hScompH
    rwa [← hJeq] at hle
  have hJnotO : ¬ J ≤ CFSG.Open.lBalancePrimeCore p H :=
    not_le_lBalancePrimeCore_of_dvd hpJ
  have hSpH : CFSG.Open.lBalanceIsPComponent p H S :=
    (CFSG.ComponentClassification.CatalogueBAlternating.pComponent_subgroupOf_iff_lBalance
      p H S hSleH).1 hSpcH
  rcases lBalanceIsPComponent_eq_or_commute hJcomp hJnotO hSpH with hEq | hComm
  · exact hEq
  · exfalso
    have hSS : ⁅S, S⁆ = ⊥ := by
      have h1 : ⁅S, S⁆ ≤ ⁅S, J⁆ := Subgroup.commutator_mono le_rfl hSleJ
      rw [hComm] at h1
      exact le_bot_iff.mp h1
    have hqAsm : CFSG.Assembly.IsQuasisimple ↥S :=
      ⟨Group.isPerfect_def.mp hquasiS.1, hquasiS.2.1⟩
    have hSperf : ⁅S, S⁆ = S := commutator_self_eq_of_isQuasisimple hqAsm
    have hSbot : S = ⊥ := by rw [← hSperf, hSS]
    haveI hsub : Subsingleton (↥S ⧸ Subgroup.center ↥S) := by
      rw [hSbot]
      infer_instance
    haveI hnt : Nontrivial (↥S ⧸ Subgroup.center ↥S) := hquasiS.2.1.toNontrivial
    exact (not_subsingleton_iff_nontrivial (α := ↥S ⧸ Subgroup.center ↥S)).mpr hnt hsub

theorem ggTPNTrOnly_of_pComp
    (hP : GGStdSubPrimeInput) (hQ : GGPCompCentQuasisimple fun _ => True) :
    GGTPNTrOnly := by
  intro G _ _ p B Bs x L D J y K hc hL _hK hn _hJK hx
  have hpJ : p ∣ Nat.card J := hP G p B x L D J hc.1 hc.2.2
  refine ggTPNOnlyComp_of_amb hc.1.2.2.2.2.2.1.1 hn hx fun S hS => ?_
  by_cases hSL : S ≤ L
  · exact tpo_ggTPNOnlyAmb_le_of_pComp hQ hc hpJ hL hn.2.1 hS hSL
  · exact (ggTPNOnlyAmb_not_le hc hpJ
      (ggLBalanceInput_of_catalogueSchreier
        CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds) hn.2.1 hS hSL).elim

end CFSG.StandardType

end
