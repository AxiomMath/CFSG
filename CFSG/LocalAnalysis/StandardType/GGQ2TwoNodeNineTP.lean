module

public import CFSG.LocalAnalysis.StandardType.GGQ2TwoNodeNineTB
public import CFSG.LocalAnalysis.StandardType.GGQ2TableBTwA6Row
public import CFSG.LocalAnalysis.StandardType.GGTPNTwA6Defs
public import CFSG.LocalAnalysis.StandardType.GGB36Defs
public import CFSG.LocalAnalysis.StandardType.GGTPNPCompDefs
public import CFSG.LocalAnalysis.StandardType.GGTPNNarrowC6
public import CFSG.LocalAnalysis.StandardType.GGK0ExcB3
public import Certificates.Certificate13659
public import Certificates.Certificate13660
import CFSG.LocalAnalysis.StandardType.GGTPNAtL
import CFSG.LocalAnalysis.StandardType.GGTPNTwA6Final
import CFSG.LocalAnalysis.StandardType.GGB36StepOneK0
import CFSG.LocalAnalysis.StandardType.GGK0CompREMult
import CFSG.LocalAnalysis.StandardType.GGKacExcB2
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGFrameRouteQTwo
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGNbrU63Setup
import CFSG.LocalAnalysis.StandardType.GGQ2TwoNodeI1Rank
import CFSG.LocalAnalysis.StandardType.GGTableBBstar
import CFSG.LocalAnalysis.StandardType.GGStdSubExist

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggQ2TablePAtL_twA6 (hRig : GGLabelRigidInput) (hKn : GGTablePKnownRK GGRegimeTwA6)
    (h1 : GGB36StepOne) (hQ : GGPCompCentQuasisimple fun _ => True) (hP : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) (hI1 : GGQTwoI1 Bs D J) (hcard : Nat.card Bs ≤ 3 ^ 8)
    {y : G} {K : Subgroup G} (hn : GGNbr 3 B x D J y K) {labJ : LargeEvenLabel}
    (hΛJ : LargeEvenInLambda2 labJ) (htJ : labJ.tag = .twA) (hrJ : labJ.rank = 6)
    (hpq : 3 ∣ 2 ^ labJ.n + 1) (hhJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J)) :
    labJ.n = 1 ∧ ∃ labL : LargeEvenLabel, GGQ2TwA6TwoLabel labL ∧
      GGHasLabel labL (↥L ⧸ Subgroup.center ↥L) := by
  obtain ⟨t, r, m⟩ := labJ
  simp only at htJ hrJ hpq ⊢
  subst htJ hrJ
  have hc : GGConfig 3 B Bs x L D J := hS.1.1
  have hL2 : GGInnerDiagOnLabel GGLabQTwo 3 Bs L := hS.2.1
  have hInn : GGInnerDiagOn Bs L := largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.2) hL2
  have hpJ : 3 ∣ Nat.card J := hP G 3 B x L D J hc.1 hc.2.2
  have hI1' : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D := fun b hb =>
    hI1 b hb.1 fun j hj => (Subgroup.mem_centralizer_iff.mp hb.2 j hj).symm
  have hJL : J ≤ L := hc.2.2.1.2.2.2.2.2.1.1.trans inf_le_left
  obtain ⟨labJ', labL', hΛJ', hΛL', hrow, hhJ', hhL'⟩ :=
    ggTPNRow_atL hKn hQ hc hL2 hpJ hn.2.1 hI1' hΛJ hhJ (fun _ => ⟨rfl, hcard, rfl, rfl, hpq⟩)
      (ggTPNRankJ_of_twA6 hRig rfl rfl hΛJ
        (ggHasLabel_quotCenter_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJL).symm hhJ))
  obtain rfl : labJ' = ⟨.twA, 6, m⟩ := ggLabelIso_twA6_left (hRig _ labJ' _ hΛJ hΛJ' hhJ hhJ')
  obtain ⟨labL, hΛL, hhL, -, -, -, -, -, hqL, -⟩ := largeEvenMarking_exists_hasLabel hL2
  have hnL : labL.n = 1 := by
    have h1' : 1 ≤ labL.n := hΛL.1
    have h2' : labL.n < 2 := hqL
    omega
  have hm : ∀ {T : LargeEvenLieTag} {r : ℕ}, labL' = ⟨T, r, m⟩ → T ≠ .A → m = 1 := by
    intro T r h hT
    rcases FrameRoute.ggFrameQTwo_qTwoCompat_of_iso hnL (hRig labL labL' _ hΛL hΛL' hhL hhL')
      with h' | ⟨h', -⟩
    · rw [h] at h'
      exact h'
    · rw [h] at h'
      exact absurd h' hT
  rcases ggTablePRow_three_twA6 hpq hrow with h | h | h | h | h | ⟨htw, -⟩ | h
  · obtain rfl := hm h (by simp)
    exact ⟨rfl, labL', Or.inl h, hhL'⟩
  · obtain rfl := hm h (by simp)
    exact ⟨rfl, labL', Or.inr (Or.inl h), hhL'⟩
  · obtain rfl := hm h (by simp)
    exact ⟨rfl, labL', Or.inr (Or.inr (Or.inl h)), hhL'⟩
  · obtain rfl := hm h (by simp)
    exact ⟨rfl, labL', Or.inr (Or.inr (Or.inr (Or.inl h))), hhL'⟩
  · obtain rfl := hm h (by simp)
    exact ⟨rfl, labL', Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))), hhL'⟩
  ·
    exfalso
    obtain ⟨labJ'', hB36, hΛJ'', hhJ''⟩ :=
      h1 G 3 B Bs x L D J hc hInn rfl labL' hΛL' (Or.inr htw) hhL'
    rw [ggLabelIso_twA6_left (hRig _ labJ'' _ hΛJ hΛJ'' hhJ hhJ'')] at hB36
    simp [GGB36JLabel, htw] at hB36
  · obtain rfl := hm h (by simp)
    exact ⟨rfl, labL', Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))), hhL'⟩

theorem ggQ2_LDatum_twA6_of_label
    [Fact (Nat.Prime 3)] (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    (hcard : Nat.card Bs = 3 ^ 8) {labL : LargeEvenLabel} (hlab : GGQ2TwA6TwoLabel labL)
    (hhasL : GGHasLabel labL (↥L ⧸ Subgroup.center ↥L)) : ∃ M : GGQ2LDatum 3 Bs L x, M.Shape := by
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  obtain ⟨hp3, hBs, hxBs, hLx, -⟩ := hcfg.tableB_facts
  have hSS : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  refine exists_ggQ2LDatum_of_twA6Label hRig hcfg hSS.2.2.1
    (inf_centralizer_eq_zpowers_of_elemAbelian hp3 hBs hxBs hSS.2.2.1 hLx hSS.2.2.2.2)
    hS.1.2.2.1.1 hlab hhasL fun hN => ?_
  have hmul := card_range_ggGamma_mul_of hp3 hBs hxBs hSS.2.2.1 hLx hSS.2.2.2.2 hN
  rw [hcard] at hmul
  norm_num at hmul ⊢
  omega

theorem ggQ2_nbrDatum_twA6_of_tp
    [Fact (Nat.Prime 3)] (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) (hTP : GGNbrTablePNbrInputI1On GGRegimeTwA6) {G : Type} [Group G]
    [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) (hI1 : GGQTwoI1 Bs D J) {y : G} {K : Subgroup G}
    (hnb : GGNbr 3 B x D J y K) (hcard : Nat.card Bs = 3 ^ 8) {labJ : LargeEvenLabel}
    (hΛJ : LargeEvenInLambda2 labJ) (htJ : labJ.tag = .twA) (hrJ : labJ.rank = 6)
    (hJn : labJ.n = 1) (hhasJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J)) :
    ∃ M : GGQ2LDatum 3 Bs K y, M.Shape := by
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  have hIDA : GGInnerDiagAll 3 B Bs x L D J := hS.1.2.2.1
  have hInnK : GGInnerDiagOn Bs K := hIDA.2 y K hnb
  have hBK : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers y :=
    ggQ2_inf_centralizer_nbr_eq_of_I1 hLB hP hS.1 hI1 hnb
  have hy1 : y ≠ 1 := hnb.1.2.2.1
  have hI1' : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D := fun b hb =>
    hI1 b hb.1 fun j hj => (Subgroup.mem_centralizer_iff.mp hb.2 j hj).symm
  obtain ⟨t, r, m⟩ := labJ
  simp only at htJ hrJ hJn
  subst htJ hrJ hJn
  obtain ⟨labK₀, hΛK₀, hhasK₀, -⟩ := largeEvenMarking_exists_hasLabel hInnK
  have hreg : GGRegimeTwA6 3 (Nat.card Bs) ⟨.twA, 6, 1⟩ labK₀ :=
    ⟨rfl, hcard.le, rfl, rfl, by norm_num⟩
  obtain ⟨labJ', labK', hΛJ', -, hrow, hhasJ', hhasK'⟩ :=
    hTP G 3 B Bs x L D J y K hcfg hIDA.1 hInnK hnb hI1' _ labK₀ hΛJ hΛK₀ hreg hhasJ hhasK₀
  obtain rfl : labJ' = ⟨.twA, 6, 1⟩ :=
    ggLabelIso_twA6_left (hRig _ labJ' _ hΛJ hΛJ' hhasJ hhasJ')
  have hlab : GGQ2TwA6TwoLabel labK' := by
    rcases ggTablePRow_three_twA6 (by norm_num) hrow with h | h | h | h | h | ⟨-, h⟩ | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · omega
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  have hy3 : orderOf y = 3 := by
    have hyBs : y ∈ Bs := (hBK.ge (Subgroup.mem_zpowers y)).1
    exact orderOf_eq_prime (hcfg.tableB_facts.2.1.2 y hyBs) hy1
  have hr : ∀ hN : Bs ≤ Subgroup.normalizer (K : Set G),
      3 ^ 7 ≤ Nat.card (ggGamma K hN).range := by
    intro hN
    have h1 := NbrU63.card_range_ggGamma_mul_card_inf hN
    rw [hBK, Nat.card_zpowers, hy3, hcard] at h1
    have h2 : Nat.card (ggGamma K hN).range * 3 = 3 ^ 7 * 3 := by
      rw [h1]
      norm_num
    exact (Nat.eq_of_mul_eq_mul_right (by norm_num) h2).ge
  exact exists_ggQ2LDatum_of_twA6Label hRig hcfg hy1 hBK hInnK hlab hhasK' hr

theorem ggQ2s08_rowTwA9_labJ {G : Type} [Group G] {X J : Subgroup G}
    (hrow : GGQ2S08RowTwA 3 9 X J) :
    ∃ labX labJ : LargeEvenLabel, LargeEvenMarking X (fun lab _ _ _ _ _ => lab = labX) ∧
      labX.tag = .twA ∧ labX.n = labJ.n ∧ LargeEvenInLambda2 labJ ∧ labJ.tag = .twA ∧
      labJ.rank = 6 ∧ 3 ∣ 2 ^ labJ.n + 1 ∧ GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) := by
  obtain ⟨labX, labJ, hmX, hmJ, htJ, htX, -, hn, -, hpq, hNJ⟩ := hrow
  obtain ⟨labJ₁, hΛJ, rfl, hhJ⟩ := FrameRoute.ggFrameQTwo_exists_hasLabel hmJ
  exact ⟨labX, labJ₁, hmX, htX, hn, hΛJ, htJ, by omega, hpq, hhJ⟩

theorem ggQ2s08_tn9L_of_tableP
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) (hNC : GGLNoncyclicInput) (h5 : GGQTwoCentralizerInput)
    (hK : GGReflClassOmegaInput) (hCavH : GGQ2CavOfTBHeartInner)
    (hTP : GGNbrTablePNbrInputI1On GGRegimeTwA6) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hp : p = 3) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting p B Bs x L D J) (hI1 : GGQTwoI1 Bs D J) (hrow : GGQ2S08PosTwA 9 p L J)
    (hx : x ∉ L) :
    Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G) := by
  subst hp
  refine ggQ2s08_tn9L_of_nbrData hRig hLB hP hNC h5 hK hCavH rfl hS hI1 hrow hx ?_
  intro hcard y K hnb
  obtain ⟨labX, labJ, hmX, htX, hn, hΛJ, htJ, hrJ, -, hhJ⟩ := ggQ2s08_rowTwA9_labJ hrow
  have hXn : labX.n < 2 := ggQ2_labQTwo_of_marking_twA hRig hS htX hmX
  have hJ1 : 1 ≤ labJ.n := hΛJ.1
  exact ggQ2_nbrDatum_twA6_of_tp hRig hLB hP hTP hS hI1 hnb hcard hΛJ htJ hrJ (by omega) hhJ

theorem ggQ2s08_tn9K_of_tableP
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) (hNC : GGLNoncyclicInput) (h5 : GGQTwoCentralizerInput)
    (hK : GGReflClassOmegaInput) (hTP : GGNbrTablePNbrInputI1On GGRegimeTwA6)
    (hKn : GGTablePKnownRK GGRegimeTwA6) (h1 : GGB36StepOne)
    (hQ : GGPCompCentQuasisimple fun _ => True) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hp : p = 3) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting p B Bs x L D J) (hI1 : GGQTwoI1 Bs D J) {y : G} {K : Subgroup G}
    (hnb : GGNbr p B x D J y K) (hrow : GGQ2S08PosTwA 9 p K J) (hy : y ∉ K) :
    Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G) := by
  subst hp
  obtain ⟨-, labJ, -, -, -, hΛJ, htJ, hrJ, hpq, hhJ⟩ := ggQ2s08_rowTwA9_labJ hrow
  refine ggQ2s08_tn9K_of_data hRig hLB hP hNC h5 hK rfl hS hI1 hnb hrow hy (fun hcard => ?_) ?_
  · obtain ⟨-, labL, hlab, hhL⟩ :=
      ggQ2TablePAtL_twA6 hRig hKn h1 hQ hP hS hI1 hcard.le hnb hΛJ htJ hrJ hpq hhJ
    exact ggQ2_LDatum_twA6_of_label hRig hS hcard hlab hhL
  · intro hcard y' K' hnb'
    obtain ⟨hJn, -⟩ :=
      ggQ2TablePAtL_twA6 hRig hKn h1 hQ hP hS hI1 hcard.le hnb hΛJ htJ hrJ hpq hhJ
    exact ggQ2_nbrDatum_twA6_of_tp hRig hLB hP hTP hS hI1 hnb' hcard hΛJ htJ hrJ hJn hhJ

theorem ggQ2s08_tn9Rest_of_tableP
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) (hNC : GGLNoncyclicInput) (h5 : GGQTwoCentralizerInput)
    (hK : GGReflClassOmegaInput) (hCavH : GGQ2CavOfTBHeartInner)
    (hTP : GGNbrTablePNbrInputI1On GGRegimeTwA6) (hKn : GGTablePKnownRK GGRegimeTwA6)
    (h1 : GGB36StepOne) (hQ : GGPCompCentQuasisimple fun _ => True) : GGQ2S08TN9RestCell := by
  intro G _ _ p _ hp B Bs x L D J hS hI1 y K hnb hrow _ _
  rcases hrow with ⟨hrow, hx⟩ | ⟨hrow, hy⟩
  · exact ggQ2s08_tn9L_of_tableP hRig hLB hP hNC h5 hK hCavH hTP hp hS hI1 hrow hx
  · exact ggQ2s08_tn9K_of_tableP hRig hLB hP hNC h5 hK hTP hKn h1 hQ hp hS hI1 hnb hrow hy

theorem ggQ2s08_tn9Rest_of_leaves
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput) (hNC : GGLNoncyclicInput)
    (h5 : GGQTwoCentralizerInput) (hK : GGReflClassOmegaInput) (hT : GGTPNTransferBNoCorners)
    (hB3 : GGK0ExcB3) (hQ : GGPCompCentQuasisimple fun _ => True) : GGQ2S08TN9RestCell :=
  ggQ2s08_tn9Rest_of_tableP ggLabelRigidInput_holds hLB hP hNC h5 hK ggQ2_cavOfTBHeartInner_holds
    (ggNbrTablePNbrInputI1On_twA6_of_leaves hT hB3) (ggTablePKnownRK_twA6_of_B3 hB3)
    (ggB36StepOne_of_K0REMult (ggK0CompREMult_of_excB (GGK0ExcB2.toExcB (GGK0ExcB3.toB2 hB3))))
    hQ

end CFSG.StandardType

end
