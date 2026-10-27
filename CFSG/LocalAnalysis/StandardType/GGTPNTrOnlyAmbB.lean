module

public import CFSG.LocalAnalysis.StandardType.GGTPNDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyDichotomy
public import CFSG.LocalAnalysis.StandardType.GGNbrBalanceSchreier
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFlatIVPComp
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneRestCX
public import CFSG.LocalAnalysis.StandardType.GGSixJNotA6CycX
public import CFSG.RankThree.PartOne.TCB.SchreierFinal
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.Monster.AxisCount.HSIdentBaby
public import CFSG.Monster.AxisCount.HSIdentRec0
public import CFSG.Monster.AxisCount.HSIdentRec1
public import CFSG.Monster.AxisCount.HSIdentRec2
public import CFSG.Monster.AxisCount.HSIdentRec3
public import CFSG.Monster.AxisCount.HSIdentRec4
public import CFSG.Monster.AxisCount.HSIdentRec5
public import CFSG.Monster.AxisCount.HSIdentRec6
public import CFSG.Monster.AxisCount.HSIdentRec7
public import CFSG.Monster.AxisCount.HSIdentSmall
public import CFSG.RankThree.Native.PrimeLines
public import CFSG.RankThree.PartOne.SPOR.OuterSimple
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.Sporadic.Bridge.Catalogue
public import CFSG.Sporadic.FischerOddCore.Basic
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.Sporadic.SuzOddCore.GraphData
public import CFSG.Sporadic.SuzOddCore.SmallActionData
public import CFSG.YGroups.DCE.B433Check
public import Certificates.Certificate10027
public import Certificates.Certificate10107
public import Certificates.Certificate10108
public import Certificates.Certificate10110
public import Certificates.Certificate10111
public import Certificates.Certificate16018
public import Certificates.Certificate16041
public import Certificates.Certificate2098
public import Certificates.Certificate2103
public import Certificates.Certificate2108
public import Certificates.Certificate2109
public import Certificates.Certificate2173
public import Certificates.Certificate2178
public import Certificates.Certificate2274
public import Certificates.Certificate2323
public import Certificates.Certificate6006
public import Certificates.Certificate9124
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.ComponentClassification Subgroup

private lemma tpob_mem_centralizer_L {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {x : G} {L D J S : Subgroup G} (hpJ : p ∣ Nat.card J)
    (hSH : S ≤ Subgroup.centralizer (D : Set G))
    (hSpH : CFSG.Open.lBalanceIsPComponent p (Subgroup.centralizer (D : Set G)) S)
    (hJcompH : IsComponentOf J (Subgroup.centralizer (D : Set G))) (hJL : J ≤ L)
    (hLcompY : IsComponentOf L (Subgroup.centralizer ({x} : Set G))) (hxD : x ∈ D)
    (hcommSL : ⁅S, L⁆ ≤ CFSG.Open.lBalancePrimeCore p (Subgroup.centralizer ({x} : Set G)))
    {s : G} (hsS : s ∈ S) : s ∈ Subgroup.centralizer (L : Set G) := by
  have hp : p.Prime := Fact.out
  have hsY : s ∈ Subgroup.centralizer ({x} : Set G) := by
    have hsD : s ∈ Subgroup.centralizer (D : Set G) := hSH hsS
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_centralizer_iff.mp hsD) x hxD).symm
  have hJnotO : ¬ J ≤ CFSG.Open.lBalancePrimeCore p (Subgroup.centralizer (D : Set G)) :=
    not_le_lBalancePrimeCore_of_dvd hpJ
  have hJfix : J.map (MulAut.conj s).toMonoidHom = J := by
    rcases lBalanceIsPComponent_eq_or_commute hJcompH hJnotO hSpH with hEq | hComm
    · rw [hEq] at hsS
      exact map_conj_eq_of_mem hsS
    · have hSJ : S ≤ Subgroup.centralizer (J : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hComm
      exact map_conj_eq_of_mem_normalizer
        (Subgroup.centralizer_le_normalizer (J : Set G) (hSJ hsS))
  have hJLmap : J ≤ L.map (MulAut.conj s).toMonoidHom := hJfix ▸ Subgroup.map_mono hJL
  have hYmap : (Subgroup.centralizer ({x} : Set G)).map (MulAut.conj s).toMonoidHom =
      Subgroup.centralizer ({x} : Set G) := map_conj_eq_of_mem hsY
  have hLcompMap : IsComponentOf (L.map (MulAut.conj s).toMonoidHom)
      (Subgroup.centralizer ({x} : Set G)) := by
    have h := isComponentOf_map_mulEquiv' (MulAut.conj s) hLcompY
    rwa [hYmap] at h
  have hpL : p ∣ Nat.card L := hpJ.trans (Subgroup.card_dvd_of_le hJL)
  have hcardLmap : Nat.card (L.map (MulAut.conj s).toMonoidHom) = Nat.card L :=
    Subgroup.card_map_of_injective (MulAut.conj s).injective
  have hLpY : CFSG.Open.lBalanceIsPComponent p (Subgroup.centralizer ({x} : Set G)) L :=
    lBalanceIsPComponent_of_isComponentOf hLcompY (not_le_lBalancePrimeCore_of_dvd hpL)
  have hLpMap : CFSG.Open.lBalanceIsPComponent p (Subgroup.centralizer ({x} : Set G))
      (L.map (MulAut.conj s).toMonoidHom) :=
    lBalanceIsPComponent_of_isComponentOf hLcompMap
      (not_le_lBalancePrimeCore_of_dvd (Y := Subgroup.centralizer ({x} : Set G))
        (by rwa [hcardLmap]))
  have hLmap_eq : L.map (MulAut.conj s).toMonoidHom = L :=
    GGDichotomy.eq_of_le_of_pComponent hLpY hLpMap hJL hJLmap
      (commutator_self_eq_of_isQuasisimple hJcompH.2.2) hpJ
  have hsN : s ∈ Subgroup.normalizer (L : Set G) := mem_normalizer_iff_map_conj.mpr hLmap_eq
  have hOcop : Nat.Coprime p
      (Nat.card (CFSG.Open.lBalancePrimeCore p (Subgroup.centralizer ({x} : Set G)))) :=
    CFSG.ComponentClassification.LBalance.primeCore_coprime p (Subgroup.centralizer ({x} : Set G))
  have hON : Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer
      (CFSG.Open.lBalancePrimeCore p (Subgroup.centralizer ({x} : Set G)) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (CFSG.ComponentClassification.LBalance.primeCore_le p
        (Subgroup.centralizer ({x} : Set G)))).mp
      (CFSG.ComponentClassification.LBalance.primeCore_normal p
        (Subgroup.centralizer ({x} : Set G)))
  have hLN : L ≤ Subgroup.normalizer
      (CFSG.Open.lBalancePrimeCore p (Subgroup.centralizer ({x} : Set G)) : Set G) :=
    hLcompY.1.trans hON
  have hcommLs : ⁅L, Subgroup.zpowers s⁆ ≤
      CFSG.Open.lBalancePrimeCore p (Subgroup.centralizer ({x} : Set G)) :=
    (Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hsS)).trans
      (by rw [Subgroup.commutator_comm]; exact hcommSL)
  exact mem_centralizer_of_commutator_le_coprime hp hLcompY.2.2 hpL hOcop hLN hsN hcommLs

private lemma tpob_exists_order_p {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {x : G} {L S : Subgroup G} (hSperf : commutator ↥S = ⊤)
    (hSHx : S ≤ Subgroup.centralizer ({x} : Set G))
    (hScentL : S ≤ Subgroup.centralizer (L : Set G))
    (hcyclicL : ∀ T : Subgroup G, T ≤ Subgroup.centralizer (L : Set G) → IsPGroup p T →
      IsCyclic T)
    (hpS : p ∣ Nat.card S) (hx1 : x ≠ 1) (hxp : x ^ p = 1) :
    ∃ s ∈ S, s ^ p = 1 ∧ s ∉ Subgroup.zpowers x := by
  by_cases hxS : x ∈ S
  · exfalso
    have hcyc : ∀ P : Sylow p ↥S, IsCyclic ↥(P : Subgroup ↥S) := by
      intro P
      have hPle : (P : Subgroup ↥S).map S.subtype ≤ Subgroup.centralizer (L : Set G) :=
        (Subgroup.map_subtype_le (P : Subgroup ↥S)).trans hScentL
      haveI : IsCyclic ↥((P : Subgroup ↥S).map S.subtype) :=
        hcyclicL _ hPle (P.isPGroup'.map S.subtype)
      exact isCyclic_of_surjective
        ((P : Subgroup ↥S).equivMapOfInjective S.subtype S.subtype_injective).symm.toMonoidHom
        ((P : Subgroup ↥S).equivMapOfInjective S.subtype S.subtype_injective).symm.surjective
    have hxord : orderOf (⟨x, hxS⟩ : ↥S) = p := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime hxp hx1
    have hxc : (⟨x, hxS⟩ : ↥S) ∈ Subgroup.center ↥S := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hSHx g.2))
    exact ggFalse_of_perfect_of_center hSperf hxord hxc hcyc
  · obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := ↥S) p hpS
    refine ⟨(s : G), s.2, ?_, ?_⟩
    · have hs_pow : (s : ↥S) ^ p = 1 := by rw [← hs]; exact pow_orderOf_eq_one s
      simpa [Subgroup.coe_pow] using congrArg (fun z : ↥S => (z : G)) hs_pow
    · intro hmem
      apply hxS
      have hs1 : (s : G) ≠ 1 := by
        intro h1
        have hs_eq : s = 1 := Subtype.ext h1
        rw [hs_eq, orderOf_one] at hs
        exact (Fact.out : p.Prime).one_lt.ne hs
      exact (Subgroup.zpowers_le.mpr s.2)
        (mem_zpowers_of_mem_zpowers_of_ne_one (Fact.out : p.Prime) hxp hmem hs1)

private lemma tpob_prime_dvd_card {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {S H : Subgroup G} (hSH : S ≤ H) (hSpc : CFSG.IsPComponent p (S.subgroupOf H)) :
    p ∣ Nat.card S := by
  have hdata := (ggPComponent_iff_data p hSH).1 hSpc
  have hq : CFSG.IsQuasisimple (↥S ⧸ CFSG.pPrimeCore p ↥S) := hdata.2.2
  have hQnt : Nontrivial (↥S ⧸ CFSG.pPrimeCore p ↥S) := by
    haveI : IsSimpleGroup
        ((↥S ⧸ CFSG.pPrimeCore p ↥S) ⧸ Subgroup.center (↥S ⧸ CFSG.pPrimeCore p ↥S)) :=
      hq.2.1
    exact (QuotientGroup.mk'_surjective
      (Subgroup.center (↥S ⧸ CFSG.pPrimeCore p ↥S))).nontrivial
  by_contra hnd
  have htop : CFSG.pPrimeCore p ↥S = ⊤ := by
    refine top_le_iff.mp (le_sSup ⟨inferInstance, ?_⟩)
    rw [Subgroup.card_top]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hnd
  rw [htop] at hQnt
  have hsub : Subsingleton (↥S ⧸ (⊤ : Subgroup ↥S)) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (⊤ : Subgroup ↥S) a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (⊤ : Subgroup ↥S) b
    exact QuotientGroup.eq.mpr (Subgroup.mem_top _)
  obtain ⟨a, b, hab⟩ := hQnt
  exact hab (hsub.allEq a b)

theorem ggTPNOnlyAmb_not_le
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hc : GGConfig p B Bs x L D J) (hpJ : p ∣ Nat.card J)
    (hLB : GGLBalanceInput) {y : G}
    (hD : D = Subgroup.closure {x, y}) {S : Subgroup G}
    (hS : LargeEvenPComponent p (Subgroup.centralizer (D : Set G)) S) (hSL : ¬ S ≤ L) : False := by
  classical
  obtain ⟨hI, hBs, hDJ⟩ := hc
  haveI : IsSimpleGroup G := hI.1
  haveI : Fact p.Prime := ⟨hI.2.2.2.2.2.1.1⟩
  have hp : p.Prime := Fact.out
  have hSstar : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
  have hst : LargeEvenStandardType p B x L := hI.2.2.2.2.2.2.2
  have hLbal : GGLBalanceInput := hLB
  have hxD : x ∈ D := hDJ.1.2.2.2.1
  have hyD : y ∈ D := hD ▸ Subgroup.subset_closure (Set.mem_insert_of_mem x rfl)
  have hDB : D ≤ B := hDJ.1.1
  have hyB : y ∈ B := hDB hyD
  have hx1 : x ≠ 1 := hSstar.2.2.1
  have hBcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hSstar.1.1.1.is_comm.comm (⟨a, ha⟩ : ↥B) ⟨b, hb⟩)
  have hBexp : ∀ b ∈ B, b ^ p = 1 := hSstar.1.1.2
  have hxp : x ^ p = 1 := hBexp x hSstar.2.1
  obtain ⟨hJL, hLcompPc, -⟩ := eq_of_le_of_stdSub hI hDJ hpJ
  have hLcompY : IsComponentOf L (Subgroup.centralizer ({x} : Set G)) := hSstar.2.2.2.1
  have hYK : CFSG.Open.lBalanceIsKGroup ↥(Subgroup.centralizer ({x} : Set G)) :=
    lBalanceIsKGroup_of_kProper hI.2.2.1
      (centralizer_singleton_ne_top_of_isSimpleGroup hI.2.1 hx1)
  have hXbal : CFSG.Open.lBalanceIsPComponent p (Subgroup.centralizer ({x} : Set G)) L :=
    (largeEvenPComponent_iff_lBalance p _ L).1 hLcompPc |>.2
  have hSpH : CFSG.Open.lBalanceIsPComponent p (Subgroup.centralizer (D : Set G)) S :=
    (largeEvenPComponent_iff_lBalance p _ S).1 hS |>.2
  have hdich := GGDichotomy.dichotomy_core hLbal hp hBcomm hBexp hDB hxD hYK
    (le_normalizer_of_largeEvenStandardType hst) hXbal hSpH
  have hcommSL : ⁅S, L⁆ ≤
      CFSG.Open.lBalancePrimeCore p (Subgroup.centralizer ({x} : Set G)) :=
    hdich.resolve_left hSL
  have hCD : Subgroup.centralizer (D : Set G) =
      Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G) := by
    rw [hD, Subgroup.centralizer_closure]
    ext g
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  have hJcompH : IsComponentOf J (Subgroup.centralizer (D : Set G)) := by
    have h := isComponentOf_inf_centralizer_of_stdSub hSstar hDJ.1 hD
    rw [hCD, inf_comm]
    exact h
  have hScentL : S ≤ Subgroup.centralizer (L : Set G) := fun s hsS =>
    tpob_mem_centralizer_L hpJ hS.1 hSpH hJcompH hJL hLcompY hxD hcommSL hsS
  have hSpc : CFSG.IsPComponent p (S.subgroupOf (Subgroup.centralizer (D : Set G))) :=
    (CFSG.ComponentClassification.CatalogueBAlternating.pComponent_subgroupOf_iff_lBalance p
      (Subgroup.centralizer (D : Set G)) S hS.1).mpr hSpH
  have hSperf : commutator ↥S = ⊤ := by
    have hcommS : ⁅S, S⁆ = S := ggPComponent_commutator_eq p hS.1 hSpc
    exact Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr hcommS)
  have hpS : p ∣ Nat.card S := tpob_prime_dvd_card hS.1 hSpc
  have hSHx : S ≤ Subgroup.centralizer ({x} : Set G) := fun s hsS =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_centralizer_iff.mp (hS.1 hsS)) x hxD).symm
  obtain ⟨s, hsS, hsp, hsnotin⟩ :=
    tpob_exists_order_p hSperf hSHx hScentL hSstar.2.2.2.2 hpS hx1 hxp
  have hxcentL : x ∈ Subgroup.centralizer (L : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun l hl =>
      Subgroup.mem_centralizer_singleton_iff.mp (hLcompY.1 hl)
  have hscentL : s ∈ Subgroup.centralizer (L : Set G) := hScentL hsS
  have hxs : x * s = s * x := (Subgroup.mem_centralizer_iff.mp (hS.1 hsS)) x hxD
  let K : Subgroup G := Subgroup.zpowers x ⊔ Subgroup.zpowers s
  have hEx : CFSG.Open.IsElemAbelian p (Subgroup.zpowers x) :=
    CFSG.Open.isElemAbelian_zpowers hxp
  have hEs : CFSG.Open.IsElemAbelian p (Subgroup.zpowers s) :=
    CFSG.Open.isElemAbelian_zpowers hsp
  have hcommxs : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ Subgroup.zpowers s, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact ((show Commute x s from hxs).zpow_left i).zpow_right j |>.eq
  have hKexp : CFSG.Open.IsElemAbelian p K :=
    CFSG.Open.IsElemAbelian.sup_of_commute hEx hEs hcommxs
  have hKle : K ≤ Subgroup.centralizer (L : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr hxcentL) (Subgroup.zpowers_le.mpr hscentL)
  have hKcyc : IsCyclic ↥K := hSstar.2.2.2.2 K hKle hKexp.isPGroup
  have hxK : x ∈ K := Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  have hsK : s ∈ K := Subgroup.mem_sup_right (Subgroup.mem_zpowers s)
  have hKle_x : K ≤ Subgroup.zpowers x :=
    le_zpowers_of_isCyclic_of_pow_eq_one hp hKcyc (fun c hc => hKexp.2 c hc) hxK hx1
  exact hsnotin (hKle_x hsK)

end CFSG.StandardType

end
