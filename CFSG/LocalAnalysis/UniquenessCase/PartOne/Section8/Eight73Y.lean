module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight73YInput
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight73YCyclic
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight73YStrong
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight73YKey
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight73YK35
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight68NotLe
import CFSG.LocalAnalysis.UniquenessCase.UC22P20a
import CFSG.LocalAnalysis.RankThreeUC.StronglyEmbedded
public import CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP
import all CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP
import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import Certificates.Certificate1005
import CFSG.GroupTheory.CardMapInfKer
import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Lemmas
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.LocalAnalysis.UniquenessCase.UC6K35cRed
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal
public import CFSG.GroupTheory.CoprimeActionSupport.AbelianEquivalence
public import CFSG.GroupTheory.CoprimeActionSupport.Geometry
public import CFSG.LocalAnalysis.RankThreeUC.Notation
public import CFSG.LocalAnalysis.RankThreeUC.Section3.CoprimeSpecialGroups.CommPowPow
public import CFSG.LocalAnalysis.RankThreeUC.Section5.ExtraspecialOrder
public import CFSG.LocalAnalysis.RankThreeUC.SourceSetting.AschbacherCommon
public import CFSG.LocalAnalysis.RankThreeUC.WeakModules
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs
public import CFSG.RankThree.OddKernel.CentralCoverComponentModels
public import Certificates.Certificate8052
import CFSG.CharacterTheory.Semidihedral.PrimeOrderCyclicConfinementLift
import CFSG.GroupTheory.SteinbergCBFTCores
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
import CFSG.LocalAnalysis.GLTheoremB.ComponentTools
import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
import CFSG.LocalAnalysis.SignalizerFunctor
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.CoverCentralizerNoncyclic
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.InnerBarDecomp
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.NormalCThreeCentral
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.R69CenterApps
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.StrongQuotient
import CFSG.RankThree.PartTwo.Sec21.Item23Tools
import CFSG.RankThree.PartTwo.Sec21.SylowThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data Bar2 calC)
open CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups (IsExtraspecialExpP)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem false_of_maximal_of_eight73Y (hK35w : UCK.K35w) (hKZ : StronglyEmbeddedCentralFree)
    {D : Data G} (h63 : UC6.R6_3 D) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {L P Q : Subgroup G}
    (hL : L ∈ calC D.M) (hLM : D.M ≤ normalizer (L : Set G))
    (hZ : ¬ p ∣ Nat.card (center (Bar2 L))) (hP : IsSylowOf p P D.M) (hQL : Q ≤ L)
    (hQP : Q ≤ P) (hQexp : ∀ x ∈ Q, x ^ p = 1) (hQcard : p ^ 3 ∣ Nat.card Q)
    (hPQ : P ≤ Q ⊔ centralizerBar P L) (hcyc : IsCyclic (centralizerBar P L))
    (hΓ : rankThreeGamma 1 p Q ≤ D.M) {Y : Subgroup G} (hY : Y ≠ ⊥) (hYP : Y ≤ P)
    (hYN : ¬ normalizer (Y : Set G) ≤ D.M)
    (hmax : ∀ Z : Subgroup G, Y < Z → Z ≤ D.M → IsPGroup p Z → normalizer (Z : Set G) ≤ D.M) :
    False := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hLMle : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le hL.1
  have hQM : Q ≤ D.M := hQL.trans hLMle
  have hYp : IsPGroup p Y := hP.isPGroup.to_le hYP
  have hYcyc : IsCyclic Y :=
    isCyclic_of_maximal_of_eight73Y h63 hp hp2 hP.isPGroup hQL hQP hQexp hQcard hZ
      hPQ hcyc hQM hΓ hYP hYN hmax
  have hYQ : Y ⊓ Q = ⊥ :=
    inf_eq_bot_of_isCyclic_of_rankThreeGamma_le hp hYp hYcyc hΓ hYN
  obtain ⟨y, hYgen⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top Y).mp hYcyc
  have hyP : y ∈ P := hYP (hYgen ▸ Subgroup.mem_zpowers y)
  let C : Subgroup G := centralizerBar P L
  have hcommQC : ∀ q ∈ Q, ∀ c ∈ C, q * c = c * q :=
    fun q hq c hc => commute_of_mem_centralizerBar hp hp2 hP.isPGroup hQL hQP hq hc
  obtain ⟨u, huQ, v, hvC, hyuv⟩ :=
    exists_mul_of_le_sup_centralizerBar hQL hQP hPQ hyP
  have hcomm : u * v = v * u :=
    commute_of_mem_centralizerBar hp hp2 hP.isPGroup hQL hQP huQ hvC
  let H : Subgroup G := Subgroup.centralizer (Y : Set G)
  haveI : IsCyclic ↥Y := hYcyc
  letI : CommGroup ↥Y := IsCyclic.commGroup
  have hYleH : Y ≤ H := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (congrArg Subtype.val (mul_comm (⟨a, ha⟩ : ↥Y) ⟨b, hb⟩)).symm
  have hyH : y ∈ H := hYleH (hYgen ▸ Subgroup.mem_zpowers y)
  have hcomm_vy : v * y = y * v := by
    rw [hyuv]
    calc v * (u * v) = v * u * v := by group
      _ = u * v * v := by rw [← hcomm]
      _ = (u * v) * v := by group
  have hvH : v ∈ H := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [← hYgen] at hz
    change z ∈ Subgroup.zpowers y at hz
    rw [Subgroup.mem_zpowers_iff] at hz
    obtain ⟨k, rfl⟩ := hz
    exact ((Commute.zpow_right hcomm_vy k).eq).symm
  have huH : u ∈ H := by
    have h : u = y * v⁻¹ := by rw [hyuv]; group
    rw [h]
    exact H.mul_mem hyH (H.inv_mem hvH)
  have hYHnorm : (Y.subgroupOf H).Normal := by
    refine Subgroup.normal_of_le_center ?_
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro h
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp h.2 z (Subgroup.mem_subgroupOf.mp hz)).symm
  let uQ : ↥Q := ⟨u, huQ⟩
  have hQne : Q ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hQcard
    have h8 : 8 ≤ p ^ 3 := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ p ^ 3 := Nat.pow_le_pow_left hp.two_le 3
    have hle1 : p ^ 3 ≤ 1 := Nat.le_of_dvd (by norm_num) hQcard
    omega
  haveI hQnt : Nontrivial ↥Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hQne
  have hQp : IsPGroup p ↥Q := hP.isPGroup.to_le hQP
  have huQpow : uQ ^ p = 1 := Subtype.ext (hQexp u huQ)
  let Cq : Subgroup ↥Q := Subgroup.centralizer ({uQ} : Set ↥Q)
  have hCqp : IsPGroup p ↥Cq := hQp.to_subgroup Cq
  have hCqcard : p ^ 2 ≤ Nat.card ↥Cq := by
    by_cases hcentral : uQ ∈ Subgroup.center ↥Q
    · have hCqtop : Cq = ⊤ := by
        rw [eq_top_iff]
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact (Subgroup.mem_center_iff.mp hcentral x).symm
      have hQge : p ^ 2 ≤ Nat.card ↥Q := by
        have hp3le : p ^ 3 ≤ Nat.card ↥Q := Nat.le_of_dvd Nat.card_pos hQcard
        exact (Nat.pow_le_pow_right hp.pos (by norm_num : 2 ≤ 3)).trans hp3le
      rw [hCqtop, Subgroup.card_top]
      exact hQge
    · have huQne : uQ ≠ 1 := by
        intro h1
        exact hcentral (by rw [h1]; exact Subgroup.one_mem _)
      have hord : orderOf uQ = p := orderOf_eq_prime huQpow huQne
      have hzpcard : Nat.card (Subgroup.zpowers uQ) = p := by
        rw [Nat.card_zpowers, hord]
      let Zq : Subgroup ↥Q := Subgroup.center ↥Q
      have hZq_ne : Zq ≠ ⊥ := by
        have hnt : Nontrivial ↥Zq := hQp.center_nontrivial
        exact (Subgroup.nontrivial_iff_ne_bot Zq).mp hnt
      have hZqp : IsPGroup p ↥Zq := hQp.to_subgroup Zq
      have hZqdvd : p ∣ Nat.card ↥Zq := by
        rcases hZqp.card_eq_or_dvd with h1 | h1
        · exact absurd (Subgroup.card_eq_one.mp h1) hZq_ne
        · exact h1
      let Fq : Subgroup ↥Q := Subgroup.zpowers uQ ⊔ Zq
      have hFq_le_Cq : Fq ≤ Cq := by
        refine sup_le ?_ ?_
        · intro x hx
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
          rw [Subgroup.mem_centralizer_iff]
          intro h hh
          rw [Set.mem_singleton_iff] at hh
          subst hh
          exact (Commute.zpow_right (Commute.refl uQ) k).eq
        · intro z hz
          rw [Subgroup.mem_centralizer_iff]
          intro h hh
          rw [Set.mem_singleton_iff] at hh
          subst hh
          exact Subgroup.mem_center_iff.mp hz uQ
      have hFq_card : Nat.card Fq = p * Nat.card ↥Zq := by
        have hcommZ : ∀ x ∈ Subgroup.zpowers uQ, ∀ y ∈ Zq, x * y = y * x :=
          fun x _ y hy => Subgroup.mem_center_iff.mp hy x
        have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
          (Subgroup.zpowers uQ) Zq hcommZ).1
        have hinf : Subgroup.zpowers uQ ⊓ Zq = ⊥ := by
          by_contra hne
          have hdvd : Nat.card ↥(Subgroup.zpowers uQ ⊓ Zq) ∣ p := by
            rw [← hzpcard]
            exact Subgroup.card_dvd_of_le inf_le_left
          have hcard : Nat.card ↥(Subgroup.zpowers uQ ⊓ Zq) = p := by
            rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | h2
            · exact absurd (Subgroup.card_eq_one.mp h1) hne
            · exact h2
          have heq : Subgroup.zpowers uQ ⊓ Zq = Subgroup.zpowers uQ :=
            Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcard, hzpcard])
          have huQZ : uQ ∈ Subgroup.zpowers uQ ⊓ Zq := by
            rw [heq]
            exact Subgroup.mem_zpowers uQ
          exact hcentral huQZ.2
        rw [hinf, Subgroup.card_bot, mul_one] at h
        rw [hzpcard] at h
        exact h
      have hFq_ge : p ^ 2 ≤ Nat.card Fq := by
        rw [hFq_card]
        have h := Nat.mul_le_mul_left p (Nat.le_of_dvd Nat.card_pos hZqdvd)
        simpa [pow_two] using h
      exact hFq_ge.trans (Nat.card_le_card_of_injective
        (Subgroup.inclusion hFq_le_Cq) (Subgroup.inclusion_injective hFq_le_Cq))
  obtain ⟨F0, hF0card⟩ :=
    Sylow.exists_subgroup_card_pow_prime_of_le_card (G := ↥Cq) (n := 2) hp hCqp hCqcard
  have hinj : Function.Injective (Q.subtype.comp Cq.subtype) := by
    intro a b hab
    exact Cq.subtype_injective (Q.subtype_injective hab)
  let E0 : Subgroup G := F0.map (Q.subtype.comp Cq.subtype)
  have hE0card : Nat.card E0 = p ^ 2 := by
    rw [Subgroup.card_map_of_injective hinj, hF0card]
  have hE0Q : E0 ≤ Q := by
    intro x hx
    obtain ⟨f, hf, hfx⟩ := Subgroup.mem_map.mp hx
    rw [← hfx]
    exact f.1.2
  have hE0H : E0 ≤ H := by
    intro x hx
    obtain ⟨f, hf, hfx⟩ := Subgroup.mem_map.mp hx
    rw [← hfx]
    have hfu : (f.1 : G) * u = u * (f.1 : G) := by
      have h := Subgroup.mem_centralizer_iff.mp f.2 uQ (Set.mem_singleton uQ)
      exact (congrArg Subtype.val h).symm
    have hfv : (f.1 : G) * v = v * (f.1 : G) := hcommQC f.1 f.1.2 v hvC
    have hfy : (f.1 : G) * y = y * (f.1 : G) := by
      rw [hyuv]
      calc (f.1 : G) * (u * v) = ((f.1 : G) * u) * v := by group
        _ = (u * (f.1 : G)) * v := by rw [hfu]
        _ = u * ((f.1 : G) * v) := by group
        _ = u * (v * (f.1 : G)) := by rw [hfv]
        _ = (u * v) * (f.1 : G) := by group
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [← hYgen] at hz
    change z ∈ Subgroup.zpowers y at hz
    rw [Subgroup.mem_zpowers_iff] at hz
    obtain ⟨k, rfl⟩ := hz
    exact ((Commute.zpow_right hfy k).eq).symm
  have hE0comm : ∀ a ∈ E0, ∀ b ∈ E0, a * b = b * a := by
    have hcommE0 : ∀ a b : ↥E0, a * b = b * a :=
      IsPGroup.commutative_of_card_eq_prime_sq hE0card
    intro a ha b hb
    exact congrArg Subtype.val (hcommE0 ⟨a, ha⟩ ⟨b, hb⟩)
  have hE0pow : ∀ a ∈ E0, a ^ p = 1 := fun a ha => hQexp a (hE0Q ha)
  have hE0Ybot : E0 ⊓ Y = ⊥ := by
    apply le_bot_iff.mp
    calc E0 ⊓ Y ≤ Q ⊓ Y := inf_le_inf_right Y hE0Q
      _ = ⊥ := by rw [inf_comm]; exact hYQ
  have hE0notY : ¬ E0 ≤ Y := by
    intro hEY
    have hbot : E0 = ⊥ := by
      apply le_bot_iff.mp
      calc E0 = E0 ⊓ Y := (inf_eq_left.mpr hEY).symm
        _ ≤ Q ⊓ Y := inf_le_inf_right Y hE0Q
        _ = ⊥ := by rw [inf_comm]; exact hYQ
    have hcard1 : Nat.card E0 = 1 := by rw [hbot, Subgroup.card_bot]
    rw [hE0card] at hcard1
    have hgt : 1 < p ^ 2 := by
      calc 1 < 2 ^ 2 := by norm_num
        _ ≤ p ^ 2 := Nat.pow_le_pow_left hp.two_le 2
    exact (Nat.ne_of_gt hgt) hcard1
  have hE0p : IsPGroup p E0 := hP.isPGroup.to_le (hE0Q.trans hQP)
  have hE0M : E0 ≤ D.M := hE0Q.trans hQM
  have hHnotM : ¬ H ≤ D.M :=
    not_centralizer_le_of_maximal hp (hYP.trans hP.le) hYp hYleH hYN hmax hE0H hE0p hE0notY
  have hHne_top : H ≠ ⊤ := by
    intro htop
    haveI : IsSimpleGroup G := D.standing.simple
    have hnab : ¬ IsMulCommutative G := by
      intro hcommG
      obtain ⟨a, b, hab⟩ := D.standing.nonab
      exact hab (hcommG.is_comm.comm a b)
    have hcenterbot : Subgroup.center G = ⊥ :=
      TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hnab
    have hYcenter : Y ≤ Subgroup.center G := by
      intro y' hy'
      rw [Subgroup.mem_center_iff]
      intro g
      have hgH : g ∈ H := by rw [htop]; exact Subgroup.mem_top g
      exact (Subgroup.mem_centralizer_iff.mp hgH y' hy').symm
    rw [hcenterbot] at hYcenter
    exact hY (le_bot_iff.mp hYcenter)
  let YH : Subgroup ↥H := Y.subgroupOf H
  haveI hYHnorm' : YH.Normal := hYHnorm
  let π : ↥H →* (↥H ⧸ YH) := QuotientGroup.mk' YH
  let N : Subgroup (↥H ⧸ YH) := ((D.M ⊓ H).subgroupOf H).map π
  have hne : N ≠ ⊤ := by
    simpa [N, π, YH] using
      ne_top_map_quotient_of_not_le hYleH hYHnorm (hYP.trans hP.le) hHnotM
  have hpE : ∃ E : Subgroup G, E ≤ D.M ⊓ H ∧ IsPGroup p E ∧ ¬ E ≤ Y :=
    ⟨E0, le_inf hE0M hE0H, hE0p, hE0notY⟩
  have hNstrong : IsStronglyPEmbedded p N :=
    stronglyPEmbedded_quotient_of_maximal_of_prime hp hYleH hYHnorm
      (hYP.trans hP.le) hYp hmax hne hpE
  have hKH : CFSG.Open.IsKGroup ↥H := D.standing.kProper.isKGroup H hHne_top
  have hX : CFSG.Open.IsKGroup (↥H ⧸ YH) :=
    CFSG.LocalAnalysis.GLTheoremB.isKGroup_quotient' hKH YH
  let E0H : Subgroup ↥H := E0.subgroupOf H
  have hE0H_card : Nat.card ↥E0H = p ^ 2 := by
    rw [CFSG.natCard_subgroupOf_eq E0 H hE0H, hE0card]
  have hE0H_comm : ∀ a b : ↥E0H, a * b = b * a := by
    intro a b
    apply Subtype.ext
    apply Subtype.ext
    exact hE0comm (a.1 : G) (Subgroup.mem_subgroupOf.mp a.2)
      (b.1 : G) (Subgroup.mem_subgroupOf.mp b.2)
  have hE0H_pow : ∀ a : ↥E0H, a ^ p = 1 := by
    intro a
    apply Subtype.ext
    apply Subtype.ext
    exact hE0pow (a.1 : G) (Subgroup.mem_subgroupOf.mp a.2)
  have h2 : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (↥H ⧸ YH)) := by
    let πbar : ↥E0H →* (↥H ⧸ YH) := π.comp E0H.subtype
    have hπbar_inj : Function.Injective πbar := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      have hq : (a.1 : G) * (b.1 : G)⁻¹ ∈ Y := by
        have h1 : π a.1 = π b.1 := hab
        have h2' : π (a.1 * b.1⁻¹) = 1 := by
          rw [map_mul, map_inv, h1, mul_inv_cancel]
        have h3 : a.1 * b.1⁻¹ ∈ YH :=
          (QuotientGroup.eq_one_iff (a.1 * b.1⁻¹)).mp (by
            simpa [π, QuotientGroup.mk'_apply] using h2')
        exact Subgroup.mem_subgroupOf.mp h3
      have haE : (a.1 : G) ∈ E0 := Subgroup.mem_subgroupOf.mp a.2
      have hbE : (b.1 : G) ∈ E0 := Subgroup.mem_subgroupOf.mp b.2
      have hmem : (a.1 : G) * (b.1 : G)⁻¹ ∈ E0 ⊓ Y :=
        ⟨E0.mul_mem haE (E0.inv_mem hbE), hq⟩
      rw [hE0Ybot, Subgroup.mem_bot] at hmem
      calc (a.1 : G) = (a.1 : G) * (b.1 : G)⁻¹ * (b.1 : G) := by group
        _ = 1 * (b.1 : G) := by rw [hmem]
        _ = (b.1 : G) := one_mul _
    exact CFSG.SectionRank.le_pRank_of_injective hp.one_lt hE0H_comm hE0H_pow
      hE0H_card πbar hπbar_inj le_top
  let K4 : Subgroup (↥H ⧸ YH) := ((CFSG.Open.pCoreOf 2 L ⊓ H).subgroupOf H).map π
  have hK4dvd : Nat.card K4 ∣ Nat.card (CFSG.Open.pCoreOf 2 L) := by
    refine (Subgroup.card_map_dvd ((CFSG.Open.pCoreOf 2 L ⊓ H).subgroupOf H) π).trans ?_
    rw [CFSG.natCard_subgroupOf_eq (CFSG.Open.pCoreOf 2 L ⊓ H) H inf_le_right]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hK4 : ¬ p ∣ Nat.card K4 := by
    intro hpdvd
    have hpdvd2 : p ∣ Nat.card (CFSG.Open.pCoreOf 2 L) := hpdvd.trans hK4dvd
    obtain ⟨n, hn⟩ :=
      CFSG.LocalAnalysis.UniquenessCase.UC6S846.isPGroup_pCoreOf L |>.exists_card_eq
    rw [hn] at hpdvd2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hpdvd2))
  by_cases hune1 : u = 1
  ·
    have hyC : y ∈ C := by
      rw [hyuv, hune1, one_mul]
      exact hvC
    have hYleC : Y ≤ C := by
      rw [← hYgen]
      exact Subgroup.zpowers_le.mpr hyC
    have hQleH : Q ≤ H := by
      intro q hq
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [← hYgen] at hz
      change z ∈ Subgroup.zpowers y at hz
      rw [Subgroup.mem_zpowers_iff] at hz
      obtain ⟨k, rfl⟩ := hz
      have hqy : q * y = y * q := by
        rw [hyuv, hune1]
        simpa using hcommQC q hq v hvC
      exact ((Commute.zpow_right hqy k).eq).symm
    let QH : Subgroup ↥H := Q.subgroupOf H
    let Qbar : Subgroup (↥H ⧸ YH) := QH.map π
    have hdisj : QH ⊓ π.ker = ⊥ := by
      rw [show π.ker = YH from QuotientGroup.ker_mk' YH]
      have h1 : QH ⊓ YH = (Q ⊓ Y).subgroupOf H := by
        ext x
        simp [QH, YH, Subgroup.mem_subgroupOf]
      rw [h1]
      have h2 : Q ⊓ Y = ⊥ := by rw [inf_comm]; exact hYQ
      rw [h2]
      simp
    have hQbar_card : Nat.card Qbar = Nat.card Q := by
      rw [CFSG.card_map_eq_card_of_inf_ker_eq_bot π hdisj,
        CFSG.natCard_subgroupOf_eq Q H hQleH]
    have h3X : p ^ 3 ∣ Nat.card (↥H ⧸ YH) := by
      have h1 : p ^ 3 ∣ Nat.card Qbar := by rw [hQbar_card]; exact hQcard
      exact h1.trans (Subgroup.card_subgroup_dvd_card Qbar)
    have hNps : CFSG.HallHigman.IsPSolvable p ↥N :=
      isPSolvable_of_stronglyPEmbedded_of_pow_three_dvd hK35w hX hp hp2 hNstrong h2 h3X
    have hMHps : CFSG.HallHigman.IsPSolvable p ↥(D.M ⊓ H) := by
      have hYHps : CFSG.HallHigman.IsPSolvable p ↥YH :=
        CFSG.LocalAnalysis.UniquenessCase.UCK.isPSolvable_of_isPGroup
          (hYp.of_equiv (Subgroup.subgroupOfEquivOfLe hYleH).symm)
      have hker_eq : ((D.M ⊓ H).subgroupOf H) ⊓ π.ker = YH := by
        rw [show π.ker = YH from QuotientGroup.ker_mk' YH]
        have h1 : ((D.M ⊓ H).subgroupOf H) ⊓ YH = ((D.M ⊓ H) ⊓ Y).subgroupOf H := by
          ext x
          simp [YH, Subgroup.mem_subgroupOf]
        rw [h1]
        have h2 : (D.M ⊓ H) ⊓ Y = Y :=
          inf_eq_right.mpr (le_inf (hYP.trans hP.le) hYleH)
        rw [h2]
      have hkerps :
          CFSG.HallHigman.IsPSolvable p ↥(((D.M ⊓ H).subgroupOf H) ⊓ π.ker) := by
        rw [hker_eq]
        exact hYHps
      have hsub : CFSG.HallHigman.IsPSolvable p ↥((D.M ⊓ H).subgroupOf H) :=
        CFSG.LocalAnalysis.UniquenessCase.UCK.isPSolvable_of_map π
          ((D.M ⊓ H).subgroupOf H) hkerps (by simpa [N] using hNps)
      exact CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe inf_le_right) hsub
    have hLHps : CFSG.HallHigman.IsPSolvable p ↥(L ⊓ H) :=
      CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_of_le hMHps
        (inf_le_inf_right H hLMle)
    have hpL : p ∣ Nat.card L := by
      have hpQ : p ∣ Nat.card Q :=
        (dvd_pow_self p (by norm_num : (3 : ℕ) ≠ 0)).trans hQcard
      exact hpQ.trans (Subgroup.card_dvd_of_le hQL)
    exact false_of_isPSolvable_inf_centralizer hp hp2 hL.2.2 hpL hYp hYleC
      (by simpa [H] using hLHps)
  ·
    let uH : ↥H := ⟨u, huH⟩
    let xq : (↥H ⧸ YH) := π uH
    have hxN : xq ∈ N := by
      refine Subgroup.mem_map.mpr ⟨uH, ?_, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr ⟨hQM huQ, huH⟩
    have huHpow : uH ^ p = 1 := Subtype.ext (by simpa using hQexp u huQ)
    have hxp : ∃ k : ℕ, xq ^ p ^ k = 1 := by
      refine ⟨1, ?_⟩
      rw [pow_one, show xq ^ p = π (uH ^ p) from (map_pow π uH p).symm, huHpow, map_one]
    have hxcomm : ∀ n ∈ N, ⁅n, xq⁆ ∈ K4 := by
      intro n hn
      obtain ⟨cH, hcHmem, rfl⟩ := Subgroup.mem_map.mp hn
      have hcMH : (cH : G) ∈ D.M ⊓ H := Subgroup.mem_subgroupOf.mp hcHmem
      have hcM : (cH : G) ∈ D.M := hcMH.1
      have hcH : (cH : G) ∈ H := hcMH.2
      have huvY : u * v ∈ Y := by
        have hyY : y ∈ Y := hYgen ▸ Subgroup.mem_zpowers y
        rw [← hyuv]
        exact hyY
      have hcy : (u * v) * (cH : G) = (cH : G) * (u * v) :=
        Subgroup.mem_centralizer_iff.mp hcH (u * v) huvY
      have hcuO2 : ⁅(cH : G), u⁆ ∈ CFSG.Open.pCoreOf 2 L :=
        commutatorElement_mem_pCoreOf_of_commute hp hZ (c := (cH : G)) (u := u) (v := v)
          (hLM hcM) (hQL huQ) ⟨1, by simpa using hQexp u huQ⟩ hvC hcy.symm
      have hcuH : ⁅(cH : G), u⁆ ∈ H :=
        Subgroup.commutator_le_self H (Subgroup.commutator_mem_commutator hcH huH)
      have hcoe : (⁅cH, uH⁆ : ↥H) = ⟨⁅(cH : G), u⁆, hcuH⟩ := by
        apply Subtype.ext
        rfl
      change ⁅π cH, π uH⁆ ∈ K4
      rw [← map_commutatorElement, hcoe]
      exact Subgroup.mem_map.mpr
        ⟨⟨⁅(cH : G), u⁆, hcuH⟩,
          Subgroup.mem_subgroupOf.mpr ⟨hcuO2, hcuH⟩, rfl⟩
    have hx1 : xq = 1 :=
      eq_one_of_forall_commutator_mem_of_stronglyPEmbedded hKZ hX hp hp2 h2 hNstrong hK4
        hxN hxp hxcomm
    have huY : u ∈ Y := by
      have h1 : (QuotientGroup.mk uH : (↥H ⧸ YH)) = 1 := by
        simpa [xq, π, QuotientGroup.mk'_apply] using hx1
      exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff uH).mp h1)
    exact hune1 (by
      have hmem : u ∈ Y ⊓ Q := ⟨huY, huQ⟩
      rwa [hYQ, Subgroup.mem_bot] at hmem)

theorem normalizer_le_of_eight73Y (hK35w : UCK.K35w) (hKZ : StronglyEmbeddedCentralFree)
    {D : Data G} (h63 : UC6.R6_3 D) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {L P Q : Subgroup G}
    (hL : L ∈ calC D.M) (hLM : D.M ≤ normalizer (L : Set G))
    (hZ : ¬ p ∣ Nat.card (center (Bar2 L))) (hP : IsSylowOf p P D.M) (hQL : Q ≤ L)
    (hQP : Q ≤ P) (hQexp : ∀ x ∈ Q, x ^ p = 1) (hQcard : p ^ 3 ∣ Nat.card Q)
    (hPQ : P ≤ Q ⊔ centralizerBar P L) (hcyc : IsCyclic (centralizerBar P L))
    (hΓ : rankThreeGamma 1 p Q ≤ D.M) {Y : Subgroup G} (hYM : Y ≤ D.M) (hYp : IsPGroup p Y)
    (hY : Y ≠ ⊥) : normalizer (Y : Set G) ≤ D.M :=
  normalizer_le_of_forall_maximal hp hP
    (fun Y hY hYP hYN hmax =>
      false_of_maximal_of_eight73Y hK35w hKZ h63 hp hp2 hL hLM hZ hP hQL hQP hQexp hQcard
        hPQ hcyc hΓ hY hYP hYN hmax)
    hYM hYp hY

theorem isStronglyPEmbedded_of_eight73Y (hK35w : UCK.K35w) (hKZ : StronglyEmbeddedCentralFree)
    {D : Data G} (h63 : UC6.R6_3 D) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {L P Q : Subgroup G}
    (hL : L ∈ calC D.M) (hLM : D.M ≤ normalizer (L : Set G))
    (hZ : ¬ p ∣ Nat.card (center (Bar2 L))) (hP : IsSylowOf p P D.M) (hQL : Q ≤ L)
    (hQP : Q ≤ P) (hQexp : ∀ x ∈ Q, x ^ p = 1) (hQcard : p ^ 3 ∣ Nat.card Q)
    (hPQ : P ≤ Q ⊔ centralizerBar P L) (hcyc : IsCyclic (centralizerBar P L))
    (hΓ : rankThreeGamma 1 p Q ≤ D.M) : IsStronglyPEmbedded p D.M := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hQM : Q ≤ D.M := hQL.trans (CFSG.Quasithin.A3.subnormal_le hL.1)
  have hpM : p ∣ Nat.card D.M := by
    have hpQ : p ∣ Nat.card Q :=
      (dvd_pow_self p (by norm_num : (3 : ℕ) ≠ 0)).trans hQcard
    exact hpQ.trans (Subgroup.card_dvd_of_le hQM)
  refine CFSG.LocalAnalysis.RankThreeUC.isStronglyPEmbedded_of_normalizer_le
    (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20a_M_ne_top D) hpM ?_
  intro Y hY hYp hYM
  exact normalizer_le_of_eight73Y hK35w hKZ h63 hp hp2 hL hLM hZ hP hQL hQP hQexp hQcard
    hPQ hcyc hΓ hYM hYp hY

theorem isStronglyPEmbedded_of_eight73Y_of_extraspecial (hK35w : UCK.K35w)
    (hKZ : StronglyEmbeddedCentralFree) {D : Data G} (h63 : UC6.R6_3 D) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {L P Q : Subgroup G} (hL : L ∈ calC D.M)
    (hLM : D.M ≤ normalizer (L : Set G)) (hZ : ¬ p ∣ Nat.card (center (Bar2 L)))
    (hP : IsSylowOf p P D.M) (hQ : IsSylowOf p Q L) (hQP : Q ≤ P)
    (hQe : IsExtraspecialExpP p 1 ↥Q) (hPQ : P ≤ Q ⊔ centralizerBar P L)
    (hcyc : IsCyclic (centralizerBar P L)) (hΓ : rankThreeGamma 1 p Q ≤ D.M) :
    IsStronglyPEmbedded p D.M := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hQL : Q ≤ L := hQ.le
  have hQe' := hQe
  unfold CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP at hQe'
  have hcard : Nat.card Q = p ^ 3 := by
    simpa using hQe'.1
  have hQexp : ∀ x ∈ Q, x ^ p = 1 := by
    intro x hx
    have h := Monoid.pow_exponent_eq_one (⟨x, hx⟩ : ↥Q)
    rw [hQe'.2.1] at h
    simpa using congrArg Subtype.val h
  have hQcard : p ^ 3 ∣ Nat.card Q := by rw [hcard]
  exact isStronglyPEmbedded_of_eight73Y hK35w hKZ h63 hp hp2 hL hLM hZ hP hQL hQP hQexp
    hQcard hPQ hcyc hΓ

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
