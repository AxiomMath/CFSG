module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight56Spine
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.CentralizerBar
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight73YCyclic
import CFSG.Goldschmidt.Steps.G63Basic
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight73YKey
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
import CFSG.CGT.PushingUpLit.Transport
import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
import CFSG.RankThree.PartTwo.Sec3.TwoThreeStructure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open scoped commutatorElement
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data Bar2)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08 (IsA6Z3 IsA7Z3 IsM22Z3)

private theorem u14g_le_centralizer_of_isCyclic {G : Type*} [Group G] {Y : Subgroup G}
    (hYc : IsCyclic ↥Y) : Y ≤ Subgroup.centralizer (Y : Set G) := by
  have hYcI : IsCyclic ↥Y := hYc
  let hComm : CommGroup ↥Y := IsCyclic.commGroup
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  exact (congrArg Subtype.val (mul_comm (⟨a, ha⟩ : ↥Y) ⟨b, hb⟩)).symm

private theorem u14g_exists_elemAbelian {G : Type} [Group G] [Finite G]
    {M Q Y : Subgroup G} (hQp : IsPGroup 3 Q) (hYp : IsPGroup 3 Y) (hYc : IsCyclic ↥Y)
    (hΓ : rankThreeGamma 1 3 Q ≤ M) (hYN : ¬ normalizer (Y : Set G) ≤ M)
    (hncyc : ∀ y ∈ Y, ¬ IsCyclic ↥(Q ⊓ centralizer ({y} : Set G))) :
    ∃ E : Subgroup G, E ≤ Q ⊓ centralizer (Y : Set G) ∧ IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ 2 ∧ E ⊓ Y = ⊥ := by
  obtain ⟨y, hYgen⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top Y).mp hYc
  have hyY : y ∈ Y := hYgen ▸ Subgroup.mem_zpowers y
  have hCQyp : IsPGroup 3 (Q ⊓ centralizer ({y} : Set G) : Subgroup G) := hQp.to_le inf_le_left
  obtain ⟨E, hECQy, hEab, hEcard⟩ :=
    CFSG.Goldschmidt.G63.exists_isElemAbelian_card_sq Nat.prime_three (by norm_num)
      hCQyp (hncyc y hyY)
  have hcent : Subgroup.centralizer (Y : Set G) = Subgroup.centralizer ({y} : Set G) := by
    apply le_antisymm
    · intro e he
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact ((Subgroup.mem_centralizer_iff.mp he) y hyY).symm
    · intro e he
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have hb' : b ∈ Subgroup.zpowers y := by rwa [hYgen]
      rw [Subgroup.mem_zpowers_iff] at hb'
      obtain ⟨k, rfl⟩ := hb'
      exact ((Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp he) k).eq).symm
  have hEQ : E ≤ Q ⊓ centralizer (Y : Set G) := by
    rw [hcent]
    exact hECQy
  have hYQ : Y ⊓ Q = ⊥ :=
    inf_eq_bot_of_isCyclic_of_rankThreeGamma_le Nat.prime_three hYp hYc hΓ hYN
  have hEY : E ⊓ Y = ⊥ := by
    apply le_bot_iff.mp
    calc E ⊓ Y ≤ Q ⊓ Y := inf_le_inf_right Y (hECQy.trans inf_le_left)
      _ = ⊥ := by rw [inf_comm]; exact hYQ
  exact ⟨E, hEQ, hEab, hEcard, hEY⟩

private theorem u14g_two_le_pRank_quotient {G : Type} [Group G] [Finite G]
    {H Y E : Subgroup G} [(Y.subgroupOf H).Normal]
    (hEH : E ≤ H) (hEcard : Nat.card E = 3 ^ 2)
    (hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hEpow : ∀ a ∈ E, a ^ 3 = 1) (hEY : E ⊓ Y = ⊥) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (↥H ⧸ Y.subgroupOf H)) := by
  let π : ↥H →* (↥H ⧸ Y.subgroupOf H) := QuotientGroup.mk' (Y.subgroupOf H)
  let EH : Subgroup ↥H := E.subgroupOf H
  have hEH_card : Nat.card ↥EH = 3 ^ 2 := by
    rw [CFSG.natCard_subgroupOf_eq E H hEH, hEcard]
  have hEH_comm : ∀ a b : ↥EH, a * b = b * a := by
    intro a b
    apply Subtype.ext
    apply Subtype.ext
    exact hEcomm (a.1 : G) (Subgroup.mem_subgroupOf.mp a.2)
      (b.1 : G) (Subgroup.mem_subgroupOf.mp b.2)
  have hEH_pow : ∀ a : ↥EH, a ^ 3 = 1 := by
    intro a
    apply Subtype.ext
    apply Subtype.ext
    exact hEpow (a.1 : G) (Subgroup.mem_subgroupOf.mp a.2)
  let πbar : ↥EH →* (↥H ⧸ Y.subgroupOf H) := π.comp EH.subtype
  have hπbar_inj : Function.Injective πbar := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    have hq : (a.1 : G) * (b.1 : G)⁻¹ ∈ Y := by
      have h1 : π a.1 = π b.1 := hab
      have h2 : π (a.1 * b.1⁻¹) = 1 := by
        rw [map_mul, map_inv, h1, mul_inv_cancel]
      have h3 : a.1 * b.1⁻¹ ∈ Y.subgroupOf H :=
        (QuotientGroup.eq_one_iff (a.1 * b.1⁻¹)).mp (by
          simpa [π, QuotientGroup.mk'_apply] using h2)
      exact Subgroup.mem_subgroupOf.mp h3
    have haE : (a.1 : G) ∈ E := Subgroup.mem_subgroupOf.mp a.2
    have hbE : (b.1 : G) ∈ E := Subgroup.mem_subgroupOf.mp b.2
    have hmem : (a.1 : G) * (b.1 : G)⁻¹ ∈ E ⊓ Y :=
      ⟨E.mul_mem haE (E.inv_mem hbE), hq⟩
    rw [hEY, Subgroup.mem_bot] at hmem
    calc (a.1 : G) = (a.1 : G) * (b.1 : G)⁻¹ * (b.1 : G) := by group
      _ = 1 * (b.1 : G) := by rw [hmem]
      _ = (b.1 : G) := one_mul _
  exact CFSG.SectionRank.le_pRank_of_injective (by norm_num : 1 < 3) hEH_comm hEH_pow
    hEH_card πbar hπbar_inj le_top

private theorem u14h_mem_centralizer {G : Type} [Group G] [Finite G] {D : Data G}
    {L Q P X Y : Subgroup G} (hY : ChoiceY D L Q P X Y) (hYcyc : IsCyclic ↥Y)
    {y : G} (hYgen : Subgroup.zpowers y = Y)
    {u v : G} (huQ : u ∈ Q) (hvC : v ∈ centralizerBar P L) (hyuv : y = u * v) :
    u ∈ Subgroup.centralizer (Y : Set G) ∧ v ∈ Subgroup.centralizer (Y : Set G) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcex : Cex856 D L Q P := hY.cx.cex
  have hQL : Q ≤ L := hcex.sylowQ.le
  have hQP : Q ≤ P := hcex.le
  have hP3 : IsPGroup 3 P := hcex.sylowP.isPGroup
  have hcomm : u * v = v * u :=
    commute_of_mem_centralizerBar Nat.prime_three (by norm_num) hP3 hQL hQP huQ hvC
  let H : Subgroup G := Subgroup.centralizer (Y : Set G)
  have : IsCyclic ↥Y := hYcyc
  let : CommGroup ↥Y := IsCyclic.commGroup
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
  exact ⟨huH, hvH⟩

private theorem u14h_commutator_mem_pCore {G : Type} [Group G] [Finite G] {D : Data G}
    {L Q P X Y : Subgroup G} (hY : ChoiceY D L Q P X Y)
    (hLM : D.M ≤ normalizer (L : Set G))
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center (Bar2 L)))
    {y : G} (hYgen : Subgroup.zpowers y = Y)
    {u v : G} (huQ : u ∈ Q) (hvC : v ∈ centralizerBar P L) (hyuv : y = u * v)
    (hup : ∃ k : ℕ, u ^ 3 ^ k = 1)
    {c : G} (hcM : c ∈ D.M) (hcH : c ∈ Subgroup.centralizer (Y : Set G)) :
    ⁅c, u⁆ ∈ CFSG.Open.pCoreOf 2 L := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcex : Cex856 D L Q P := hY.cx.cex
  have hQL : Q ≤ L := hcex.sylowQ.le
  have huvY : u * v ∈ Y := by
    rw [← hyuv]
    exact hYgen ▸ Subgroup.mem_zpowers y
  have hcy : (u * v) * c = c * (u * v) :=
    Subgroup.mem_centralizer_iff.mp hcH (u * v) huvY
  exact commutatorElement_mem_pCoreOf_of_commute Nat.prime_three hZ (c := c) (u := u)
    (v := v) (hLM hcM) (hQL huQ) hup hvC hcy.symm

private theorem u14h_pCore_image_not_three_dvd {G : Type} [Group G] [Finite G]
    {L H : Subgroup G} {X : Type} [Group X] (π : ↥H →* X) :
    ¬ 3 ∣ Nat.card (((CFSG.Open.pCoreOf 2 L ⊓ H).subgroupOf H).map π) := by
  classical
  intro h3dvd
  have hdvd : Nat.card (((CFSG.Open.pCoreOf 2 L ⊓ H).subgroupOf H).map π) ∣
      Nat.card (CFSG.Open.pCoreOf 2 L) := by
    refine (Subgroup.card_map_dvd ((CFSG.Open.pCoreOf 2 L ⊓ H).subgroupOf H) π).trans ?_
    rw [CFSG.natCard_subgroupOf_eq (CFSG.Open.pCoreOf 2 L ⊓ H) H inf_le_right]
    exact Subgroup.card_dvd_of_le inf_le_left
  have h3dvd2 : 3 ∣ Nat.card (CFSG.Open.pCoreOf 2 L) := h3dvd.trans hdvd
  obtain ⟨n, hn⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.isPGroup_pCoreOf L |>.exists_card_eq
  rw [hn] at h3dvd2
  exact (by norm_num : (3 : ℕ) ≠ 2)
    ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3dvd2))

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
