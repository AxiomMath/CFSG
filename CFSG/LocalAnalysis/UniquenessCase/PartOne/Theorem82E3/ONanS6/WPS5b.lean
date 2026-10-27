module

public import CFSG.GroupTheory.CoprimeCentralizerCover
public import CFSG.GroupTheory.PRankCommutingSup
public import CFSG.GroupTheory.PRankLeOfSylowLe
public import CFSG.GroupTheory.PRankMapOfKerPrimeNotDvd
public import CFSG.GroupTheory.PRankQuotientLift
public import CFSG.LocalAnalysis.GLTheoremB.AutL34Bound
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalRank2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanK9bCat
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanKFacts
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPFF2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPL
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS2a
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS5c
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPZ
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WS6
public import CFSG.Sporadic.NativeFinite
public import CFSG.Sporadic.ON
public import CFSG.LocalAnalysis.GL83PartI.I_7_13
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Extremal
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL613Defs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S628Common
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.StrongMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointLemma32
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open GroupTheory.CoprimeActionSupport.CentralizerOnQuotientMembership (mem_centralizerOnQuotient)
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor IsAlt)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}
variable (c : Ctx82E3 D) {P A : Subgroup G} {a : G}

theorem mem_center_lbar_of_mem_centralizerOnQuotient_wPS5b
    {x : G} (hxL : x ∈ c.L)
    (hxC : x ∈ CFSG.LocalAnalysis.RankThreeUC.centralizerOnQuotient D.M
      (CFSG.Open.pCoreOf 2 c.L) c.L) :
    (QuotientGroup.mk (⟨x, hxL⟩ : ↥c.L) : c.Lbar) ∈
      Subgroup.center c.Lbar := by
  classical
  obtain ⟨-, -, -, hxcomm⟩ :=
    mem_centralizerOnQuotient.mp
      hxC
  rw [Subgroup.mem_center_iff]
  intro y
  induction y using QuotientGroup.induction_on with
  | H l =>
    obtain ⟨o, hoO2, hoL, hxl_eq⟩ :
        ∃ o ∈ CFSG.Open.pCoreOf 2 c.L, o ∈ c.L ∧
          x * l.1 = o * (l.1 * x) := by
      refine ⟨x * l.1 * x⁻¹ * l.1⁻¹, hxcomm l.1 l.2, ?_, ?_⟩
      · exact c.L.mul_mem (c.L.mul_mem (c.L.mul_mem hxL l.2) (c.L.inv_mem hxL))
          (c.L.inv_mem l.2)
      · group
    obtain ⟨o', ho', ho'val⟩ := Subgroup.mem_map.mp hoO2
    have ho'_eq : (⟨o, hoL⟩ : ↥c.L) = o' := Subtype.ext ho'val.symm
    have hmo : (QuotientGroup.mk (⟨o, hoL⟩ : ↥c.L) : c.Lbar) = 1 := by
      rw [ho'_eq]
      exact (QuotientGroup.eq_one_iff o').mpr ho'
    have hxl : (⟨x, hxL⟩ : ↥c.L) * l = (⟨o, hoL⟩ : ↥c.L) * (l * ⟨x, hxL⟩) := by
      apply Subtype.ext
      simpa using hxl_eq
    have hright : (QuotientGroup.mk (⟨x, hxL⟩ : ↥c.L) : c.Lbar) *
        (QuotientGroup.mk l : c.Lbar) = (QuotientGroup.mk (l * ⟨x, hxL⟩) : c.Lbar) := by
      rw [← QuotientGroup.mk_mul, hxl, QuotientGroup.mk_mul, hmo]
      exact one_mul _
    calc QuotientGroup.mk l * QuotientGroup.mk (⟨x, hxL⟩ : ↥c.L)
        = QuotientGroup.mk (l * ⟨x, hxL⟩) := by rw [QuotientGroup.mk_mul]
      _ = QuotientGroup.mk (⟨x, hxL⟩ : ↥c.L) * QuotientGroup.mk l := hright.symm

theorem SevenRankCentralizerLeOne_proved'
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) :
    CFSG.Open.pRank 7 (CFSG.LocalAnalysis.RankThreeUC.centralizerOnQuotient D.M
      (CFSG.Open.pCoreOf 2 c.L) c.L) ≤ 1 := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  obtain ⟨-, hZcard, hSpor⟩ := hON
  let O2G : Subgroup G := CFSG.Open.pCoreOf 2 c.L
  let C : Subgroup G := CFSG.LocalAnalysis.RankThreeUC.centralizerOnQuotient D.M O2G c.L
  obtain ⟨R, hRsyl⟩ := CFSG.ABGLocalTools.exists_isSylowOf 7 C
  have hRleC : R ≤ C := hRsyl.le
  have hRnormL : R ≤ Subgroup.normalizer (c.L : Set G) :=
    fun r hr => (mem_centralizerOnQuotient.mp
      (hRleC hr)).2.1
  have hRnormO2 : R ≤ Subgroup.normalizer (O2G : Set G) :=
    fun r hr => (mem_centralizerOnQuotient.mp
      (hRleC hr)).2.2.1
  have hO2leL : O2G ≤ c.L := CFSG.openPCoreOf_le 2 c.L
  have hO2not : ¬ 7 ∣ Nat.card O2G := by
    have hO2p : IsPGroup 2 O2G := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 c.L
    exact CFSG.GroupTheory.not_dvd_card_of_isPGroup hO2p Nat.prime_seven (by norm_num)
  have hcomm : ⁅c.L, R⁆ ≤ O2G := by
    rw [Subgroup.commutator_le]
    intro l hl r hr
    have hxcomm := (mem_centralizerOnQuotient.mp
      (hRleC hr)).2.2.2 l hl
    have h : ⁅l, r⁆ = (r * l * r⁻¹ * l⁻¹)⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [h]
    exact O2G.inv_mem hxcomm
  set J : Subgroup G := c.L ⊓ Subgroup.centralizer (R : Set G) with hJdef
  have hcover : J ⊔ O2G = c.L :=
    CFSG.GroupTheory.inf_centralizer_sup_eq_of_commutator_le (p := 7)
      (X := c.L) (N := O2G) (R := R) hO2leL hRnormL hRnormO2 hRsyl.isPGroup
      hO2not hcomm
  have hJleL : J ≤ c.L := hJdef.le.trans inf_le_left
  let incl : ↥J →* ↥c.L := Subgroup.inclusion hJleL
  let πJ : ↥J →* c.Lbar := (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)).comp incl
  have hsurj : Function.Surjective πJ := by
    intro y
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.Open.pCore 2 ↥c.L) y
    have hl : (l : G) ∈ J ⊔ O2G := by rw [hcover]; exact l.2
    have hJnormO2 : J ≤ Subgroup.normalizer (O2G : Set G) :=
      hJleL.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 c.L)
    have hcoe : ((J ⊔ O2G : Subgroup G) : Set G) = (J : Set G) * (O2G : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right J O2G hJnormO2
    have hmem : (l : G) ∈ (J : Set G) * (O2G : Set G) := by
      rw [← hcoe]
      exact hl
    obtain ⟨j, hjJ, o, hoO2, hjo⟩ := Set.mem_mul.mp hmem
    obtain ⟨o', ho', ho'val⟩ := Subgroup.mem_map.mp hoO2
    refine ⟨⟨j, hjJ⟩, ?_⟩
    change QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) (incl ⟨j, hjJ⟩) =
      QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) l
    have hincl : incl ⟨j, hjJ⟩ = (⟨j, hJleL hjJ⟩ : ↥c.L) := rfl
    rw [hincl]
    rw [QuotientGroup.mk'_eq_mk']
    refine ⟨o', ho', ?_⟩
    apply Subtype.ext
    change j * (o' : G) = (l : G)
    calc j * (o' : G) = j * o := congrArg (fun t : G => j * t) ho'val
      _ = (l : G) := hjo
  have hker_eq : MonoidHom.ker πJ = (CFSG.Open.pCore 2 ↥c.L).comap incl := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_comap]
    change (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)) (incl x) = 1 ↔
      incl x ∈ CFSG.Open.pCore 2 ↥c.L
    exact QuotientGroup.eq_one_iff (incl x)
  have hker_dvd : Nat.card ↥(MonoidHom.ker πJ) ∣ Nat.card (CFSG.Open.pCore 2 ↥c.L) := by
    rw [hker_eq]
    exact Subgroup.card_comap_dvd_of_injective _ incl (Subgroup.inclusion_injective hJleL)
  have hO2Lnot : ¬ 7 ∣ Nat.card (CFSG.Open.pCore 2 ↥c.L) := by
    have hO2Lp : IsPGroup 2 (CFSG.Open.pCore 2 ↥c.L) :=
      CFSG.pCore_isPGroup (p := 2) (G := ↥c.L)
    exact CFSG.GroupTheory.not_dvd_card_of_isPGroup hO2Lp Nat.prime_seven (by norm_num)
  have hker_not : ¬ 7 ∣ Nat.card ↥(MonoidHom.ker πJ) :=
    fun h => hO2Lnot (h.trans hker_dvd)
  have hLbar_rank : 2 ≤ CFSG.Open.pRank 7 (⊤ : Subgroup c.Lbar) := by
    obtain ⟨eON⟩ := hSpor
    haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier TauCeti.SporadicName.ONan) :=
      CFSG.Sporadic.finite_carrier_of_ne_M TauCeti.SporadicName.ONan (by decide)
    obtain ⟨x, y, -, hx, hy, hne, hzx, hzy, hQ, -, -, -⟩ :=
      CFSG.RankThree.PartOne.MultRes.ON_sylow7_cubic_witness
    have hONrank : 2 ≤ CFSG.Open.pRank 7
        (⊤ : Subgroup (CFSG.Blueprint.NativeSporadic.Carrier TauCeti.SporadicName.ONan)) := by
      change 2 ≤ CFSG.Open.pRank 7 (⊤ : Subgroup CFSG.Blueprint.NativeSporadic.ON)
      exact CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal.two_le_pRank_of_heisenberg
        (p := 7) Nat.prime_seven hx hy hne hzx hzy hQ
    have hquot : CFSG.Open.pRank 7 (⊤ : Subgroup (c.Lbar ⧸ Subgroup.center c.Lbar)) =
        CFSG.Open.pRank 7
          (⊤ : Subgroup (CFSG.Blueprint.NativeSporadic.Carrier TauCeti.SporadicName.ONan)) :=
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 7) (by norm_num) eON
    have h2 : 2 ≤ CFSG.Open.pRank 7 (⊤ : Subgroup (c.Lbar ⧸ Subgroup.center c.Lbar)) := by
      rw [hquot]
      exact hONrank
    exact CFSG.GroupTheory.two_le_pRank_of_quotient (N := Subgroup.center c.Lbar)
      (p := 7) Nat.prime_seven (by norm_num) h2
  have hJrank2 : 2 ≤ CFSG.Open.pRank 7 J := by
    have hmap := CFSG.pRank_map_eq_of_not_dvd_card_ker πJ hsurj (p := 7)
      Nat.prime_seven hker_not ⊤
    rw [Subgroup.map_top_of_surjective πJ hsurj] at hmap
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup J, ← hmap]
    exact hLbar_rank
  obtain ⟨E, hEJ, hEea, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank (p := 7) (by norm_num : 1 < 7) J
  have hdvd : 7 ^ 2 ∣ Nat.card E := by
    rw [hEcard]
    exact pow_dvd_pow 7 hJrank2
  obtain ⟨S, hScard, -, hSE⟩ :=
    Sylow.exists_subgroup_card_pow_prime_le_le (p := 7) (n := 2)
      (H := (⊥ : Subgroup G)) (L := E) Nat.prime_seven (by simp) hdvd bot_le
  have hSea : CFSG.Open.IsElemAbelian 7 S := hEea.mono hSE
  have hSJ : S ≤ J := hSE.trans hEJ
  have hSL : S ≤ c.L := hSJ.trans hJleL
  have hScent : S ≤ Subgroup.centralizer (R : Set G) :=
    hSJ.trans (hJdef.le.trans inf_le_right)
  have hSR_le_O2 : S ⊓ R ≤ O2G := by
    intro x hx
    have hxS : x ∈ S := hx.1
    have hxR : x ∈ R := hx.2
    have hxL : x ∈ c.L := hSL hxS
    have hxC : x ∈ C := hRleC hxR
    have hxcenter := mem_center_lbar_of_mem_centralizerOnQuotient_wPS5b c hxL hxC
    have hx7L : (⟨x, hxL⟩ : ↥c.L) ^ 7 = 1 :=
      Subtype.ext (by simpa using hSea.2 x hxS)
    set z : c.Lbar := QuotientGroup.mk (⟨x, hxL⟩ : ↥c.L) with hz
    have hx7bar : z ^ 7 = 1 := by
      rw [hz]
      rw [← QuotientGroup.mk_pow, hx7L]
      rfl
    have hdvd7 : orderOf z ∣ 7 := orderOf_dvd_of_pow_eq_one hx7bar
    have hdvd3 : orderOf z ∣ Nat.card (Subgroup.center c.Lbar) :=
      Subgroup.orderOf_dvd_natCard (Subgroup.center c.Lbar) (by simpa [hz] using hxcenter)
    have hdvd3' : orderOf z ∣ 3 := by simpa [hZcard] using hdvd3
    have hone : orderOf z = 1 := by
      have h : orderOf z ∣ Nat.gcd 7 3 := Nat.dvd_gcd hdvd7 hdvd3'
      simpa using h
    have himg1 : z = 1 := orderOf_eq_one_iff.mp hone
    have hxO2L : (⟨x, hxL⟩ : ↥c.L) ∈ CFSG.Open.pCore 2 ↥c.L := by
      rw [← QuotientGroup.eq_one_iff]
      simpa [hz] using himg1
    exact Subgroup.mem_map.mpr ⟨⟨x, hxL⟩, hxO2L, rfl⟩
  have hSRnotdvd : ¬ 7 ∣ Nat.card ↥(S ⊓ R) := by
    have hdvd : Nat.card ↥(S ⊓ R) ∣ Nat.card O2G := Subgroup.card_dvd_of_le hSR_le_O2
    exact fun h => hO2not (h.trans hdvd)
  have hadd : CFSG.Open.pRank 7 (S ⊔ R) =
      CFSG.Open.pRank 7 S + CFSG.Open.pRank 7 R :=
    CFSG.GroupTheory.pRank_sup_eq_add_of_commute_of_not_dvd (p := 7) Nat.prime_seven
      (A := S) (B := R) hScent hSRnotdvd
  have hSleM : S ≤ D.M := hSL.trans c.hyp81.1
  have hRleM : R ≤ D.M :=
    hRleC.trans (CFSG.LocalAnalysis.RankThreeUC.centralizerOnQuotient_le D.M O2G c.L)
  have hrankM : CFSG.Open.pRank 7 (S ⊔ R) ≤ 3 :=
    (CFSG.SectionRank.pRank_mono (p := 7) (by norm_num) (sup_le hSleM hRleM)).trans
      (c.pRank_le_three (p := 7) Nat.prime_seven (by norm_num))
  have hrankS : 2 ≤ CFSG.Open.pRank 7 S :=
    CFSG.SectionRank.le_pRank (p := 7) (by norm_num) (le_refl S) hSea (by rw [hScard])
  have hRle1 : CFSG.Open.pRank 7 R ≤ 1 := by
    have hsum : CFSG.Open.pRank 7 S + CFSG.Open.pRank 7 R ≤ 3 := by
      rw [← hadd]
      exact hrankM
    omega
  have hCrank : CFSG.Open.pRank 7 C ≤ CFSG.Open.pRank 7 R :=
    CFSG.pRank_le_of_isSylowOf_le (p := 7) Nat.prime_seven hRsyl.le hRsyl le_rfl
  change CFSG.Open.pRank 7 C ≤ 1
  exact hCrank.trans hRle1

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor IsAlt)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
open CFSG.Blueprint (LieModel)
open scoped commutatorElement
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}
variable (c : Ctx82E3 D) {P A : Subgroup G} {a : G}

theorem pRank_seven_centralizer_le_one'''
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    (haL : a ∈ P ⊓ c.L) (haZ : a ∉ zSub P c.L) :
    CFSG.Open.pRank 7 (Subgroup.centralizer ({a} : Set G)) = 1 := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  let H : Subgroup G := Subgroup.centralizer ({a} : Set G)
  obtain ⟨y, hyM, hyCent, hy7⟩ := F10SevenElement_proved' c hON h7 hP
  have hya : a * y = y * a :=
    (Subgroup.mem_centralizer_iff.mp hyCent) a haL
  have hyH : y ∈ H :=
    Subgroup.mem_centralizer_singleton_iff.mpr hya.symm
  let E : Subgroup ↥H := Subgroup.zpowers (⟨y, hyH⟩ : ↥H)
  have hyH7 : orderOf (⟨y, hyH⟩ : ↥H) = 7 :=
    (Subgroup.orderOf_coe (⟨y, hyH⟩ : ↥H)).symm.trans hy7
  have hE7 : IsPGroup 7 E := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hyH7]
    norm_num
  obtain ⟨S₀, hES₀⟩ := hE7.exists_le_sylow
  let S : Subgroup G := (S₀ : Subgroup ↥H).map H.subtype
  have hS7 : IsPGroup 7 S := (S₀.isPGroup').map H.subtype
  have hyS : y ∈ S := by
    refine ⟨⟨y, hyH⟩, ?_, rfl⟩
    exact hES₀ (Subgroup.mem_zpowers (⟨y, hyH⟩ : ↥H))
  have hSne : S ≠ ⊥ := by
    intro hbot
    have hy1 : y = 1 := by
      have hybot : y ∈ (⊥ : Subgroup G) := hbot ▸ hyS
      simpa using hybot
    rw [hy1] at hy7
    simp at hy7
  haveI : Nontrivial ↥S := (Subgroup.nontrivial_iff_ne_bot S).mpr hSne
  have hcenterNontriv : Nontrivial (Subgroup.center ↥S) :=
    IsPGroup.center_nontrivial hS7
  let Z : Subgroup G := (Subgroup.center ↥S).map S.subtype
  have hZne : Z ≠ ⊥ := by
    intro hbot
    have hcenterbot : Subgroup.center ↥S = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective (H := Subgroup.center ↥S)
        (f := S.subtype) S.subtype_injective).mp hbot
    exact (Subgroup.nontrivial_iff_ne_bot (Subgroup.center ↥S)).mp
      hcenterNontriv hcenterbot
  have hZ7 : IsPGroup 7 Z := hS7.to_le (Subgroup.map_subtype_le _)
  have hZcent : Z ≤ Subgroup.centralizer ({y} : Set G) := by
    rintro z ⟨w, hw, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcommS : w * (⟨y, hyS⟩ : ↥S) = (⟨y, hyS⟩ : ↥S) * w :=
      (Subgroup.mem_center_iff.mp hw (⟨y, hyS⟩ : ↥S)).symm
    simpa using congrArg (fun t : ↥S => (t : G)) hcommS
  have hZM : Z ≤ D.M :=
    hZcent.trans (centralizer_le_M_of_orderOf_seven c h7 hyM hy7)
  have hNZM : Subgroup.normalizer (Z : Set G) ≤ D.M :=
    normalizer_le_M_of_seven c h7 hZM hZ7 hZne
  have hSleN : S ≤ Subgroup.normalizer (Z : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro s hs z hz
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
    have hconj : (⟨s, hs⟩ : ↥S) * w * (⟨s, hs⟩ : ↥S)⁻¹ ∈
        Subgroup.center ↥S :=
      (inferInstance : (Subgroup.center ↥S).Normal).conj_mem w hw ⟨s, hs⟩
    exact Subgroup.mem_map.mpr
      ⟨⟨s, hs⟩ * w * (⟨s, hs⟩ : ↥S)⁻¹, hconj, by simp [Subgroup.coe_mul]⟩
  have hSM : S ≤ D.M := hSleN.trans hNZM
  have haM : a ∈ D.M := hP.le haL.1
  have ha1 : a ≠ 1 := by
    intro h1
    exact haZ (h1 ▸ Subgroup.one_mem (zSub P c.L))
  have ha3 : orderOf a = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine orderOf_eq_prime ?_ ha1
    simpa using c.pow_three_eq_one_of_mem_inf_L_of_onan hON hP a haL
  have hρane : (CFSG.GroupTheory.conjModPCore 2 c.L D.M c.le_normalizer_L)
      ⟨a, haM⟩ ≠ 1 := by
    intro h1
    have hker : a ∈ (CFSG.GroupTheory.conjModPCore 2 c.L D.M
        c.le_normalizer_L).ker.map D.M.subtype :=
      Subgroup.mem_map.mpr ⟨⟨a, haM⟩, MonoidHom.mem_ker.mpr h1, rfl⟩
    have hcomm := (CFSG.GroupTheory.mem_map_ker_conjModPCore_iff 2 c.L D.M
      c.le_normalizer_L).mp hker
    have hPL3 : IsPGroup 3 ↥(P ⊓ c.L : Subgroup G) :=
      IsPGroup.to_le (K := P) hP.isPGroup
        (show (P ⊓ c.L : Subgroup G) ≤ P from inf_le_left)
    have hQ2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 c.L) :=
      CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 c.L
    have hdisj : Disjoint (P ⊓ c.L) (CFSG.Open.pCoreOf 2 c.L) :=
      IsPGroup.disjoint_of_ne 3 2 (by norm_num) (P ⊓ c.L)
        (CFSG.Open.pCoreOf 2 c.L) hPL3 hQ2
    have hcentral : a ∈
        Subgroup.centralizer ((P ⊓ c.L : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hmemPL : a * x * a⁻¹ * x⁻¹ ∈ P ⊓ c.L := by
        refine ⟨?_, ?_⟩
        · exact P.mul_mem (P.mul_mem (P.mul_mem haL.1 hx.1)
            (P.inv_mem haL.1)) (P.inv_mem hx.1)
        · exact c.L.mul_mem (c.L.mul_mem (c.L.mul_mem haL.2 hx.2)
            (c.L.inv_mem haL.2)) (c.L.inv_mem hx.2)
      have hmemQ : a * x * a⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 c.L :=
        hcomm.2 x hx.2
      have hbot : a * x * a⁻¹ * x⁻¹ ∈ (⊥ : Subgroup G) := by
        rw [← hdisj.eq_bot]
        exact ⟨hmemPL, hmemQ⟩
      have hcomm1 : a * x * a⁻¹ * x⁻¹ = 1 := Subgroup.mem_bot.mp hbot
      have h2 : a * x * a⁻¹ = x := by
        have := congrArg (fun t => t * x) hcomm1
        simpa [mul_assoc] using this
      have h3 : a * x = x * a := by
        have := congrArg (fun t => t * a) h2
        simpa [mul_assoc] using this
      exact h3.symm
    exact haZ ⟨haL, hcentral⟩
  have hSC : S ≤ CFSG.LocalAnalysis.RankThreeUC.centralizerOnQuotient D.M
      (CFSG.Open.pCoreOf 2 c.L) c.L :=
    sevenSubgroup_le_centralizerOnQuotient c hON haM ha3 hρane hSM
      (Subgroup.map_subtype_le _) hS7
  have hC : CFSG.Open.pRank 7
      (CFSG.LocalAnalysis.RankThreeUC.centralizerOnQuotient D.M
        (CFSG.Open.pCoreOf 2 c.L) c.L) ≤ 1 :=
    SevenRankCentralizerLeOne_proved' c hON h7 hP
  have hpRankS : CFSG.Open.pRank 7 S ≤ 1 :=
    (CFSG.SectionRank.pRank_mono (p := 7) (by norm_num) hSC).trans hC
  apply le_antisymm
  · refine CFSG.SectionRank.pRank_le (p := 7) (by norm_num) ?_
    intro E hEH hE
    have hE7p : IsPGroup 7 E := by
      rw [isPGroup_iff_exists_pow_pow_eq_one]
      exact ⟨1, fun x => Subtype.ext (by simpa using hE.2 x x.2)⟩
    obtain ⟨k, hk⟩ := hE7p.exists_card_eq
    have hEpH : IsPGroup 7 (E.subgroupOf H) :=
      hE7p.comap_of_injective H.subtype H.subtype_injective
    obtain ⟨S_E, hES_E⟩ := hEpH.exists_le_sylow
    obtain ⟨hH, hh⟩ :=
      @MulAction.IsPretransitive.exists_smul_eq (↥H) (Sylow 7 ↥H)
        inferInstance inferInstance S_E S₀
    have hconj_le_S0 : (E.subgroupOf H).map
        (MulAut.conj hH).toMonoidHom ≤ (S₀ : Subgroup ↥H) := by
      have hmap_le : (E.subgroupOf H).map (MulAut.conj hH).toMonoidHom ≤
          (S_E : Subgroup ↥H).map (MulAut.conj hH).toMonoidHom :=
        Subgroup.map_mono hES_E
      have hsmul : (S₀ : Subgroup ↥H) =
          (S_E : Subgroup ↥H).map (MulAut.conj hH).toMonoidHom := by
        rw [← hh, Sylow.coe_subgroup_smul]
        rfl
      exact hsmul ▸ hmap_le
    let F : Subgroup G :=
      ((E.subgroupOf H).map (MulAut.conj hH).toMonoidHom).map H.subtype
    have hFle : F ≤ S := by
      change ((E.subgroupOf H).map (MulAut.conj hH).toMonoidHom).map
        H.subtype ≤ (S₀ : Subgroup ↥H).map H.subtype
      exact Subgroup.map_mono hconj_le_S0
    have hEcomap : CFSG.Open.IsElemAbelian 7 (E.subgroupOf H) := by
      simpa only [Subgroup.subgroupOf] using hE.comap H.subtype_injective
    have hFelem : CFSG.Open.IsElemAbelian 7 F :=
      CFSG.SectionRank.isElemAbelian_map
        (CFSG.SectionRank.isElemAbelian_map hEcomap
          (MulAut.conj hH).toMonoidHom) H.subtype
    have hFcard : Nat.card ↥F = 7 ^ k := by
      change Nat.card ↥(((E.subgroupOf H).map
        (MulAut.conj hH).toMonoidHom).map H.subtype) = 7 ^ k
      rw [Subgroup.card_map_of_injective (f := H.subtype) H.subtype_injective,
        Subgroup.card_map_of_injective (f := (MulAut.conj hH).toMonoidHom)
          (MulAut.conj hH).injective,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEH).toEquiv]
      exact hk
    have hk_le : k ≤ CFSG.Open.pRank 7 S :=
      CFSG.SectionRank.le_pRank (p := 7) (by norm_num) hFle hFelem hFcard
    have hk_le_one : k ≤ 1 := hk_le.trans hpRankS
    rw [hk]
    calc 7 ^ k ≤ 7 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk_le_one
      _ ≤ 7 := by norm_num
  · have hE : CFSG.Open.IsElemAbelian 7 (Subgroup.zpowers y) :=
      CFSG.Open.isElemAbelian_zpowers (p := 7) (x := y) (by
        rw [← hy7]
        exact pow_orderOf_eq_one y)
    have hcard : Nat.card (Subgroup.zpowers y) = 7 ^ 1 := by
      rw [Nat.card_zpowers, hy7]
      norm_num
    exact CFSG.SectionRank.le_pRank (p := 7) (by norm_num)
      (Subgroup.zpowers_le.mpr hyH) hE hcard

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor)
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)
variable {G : Type} [Group G] [Finite G] {D : Data G}

theorem pcore_centralizer_le_theta_P3'
    (hK4 : K4) (c : Ctx82E3 D)
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    {e : G} (he : e ∈ P ⊓ c.L) (he3 : orderOf e = 3) (heZ : e ∉ zSub P c.L) :
    CFSG.Open.pRank 7 (Subgroup.centralizer ({e} : Set G)) = 1 := by
  exact pRank_seven_centralizer_le_one''' (c := c) hON h7 hP hNZ he heZ

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
