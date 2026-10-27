module

public import CFSG.RankThree.PartTwo.Sec16.Item166Proof
import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal
import CFSG.RankThree.PartOne.S10.EmbeddingTransport
import CFSG.RankThree.PartTwo.Sec11.FixedCentralizer
import CFSG.RankThree.PartTwo.Sec16.Item166Res2ProofTheta
import CFSG.RankThree.PartTwo.Sec16.Item166ThreeComp
import CFSG.RankThree.PartTwo.Sec16.Item166ThreePerfect
import CFSG.RankThree.PartTwo.Sec16.Item167StepsProofNonsolv
import CFSG.RankThree.PartTwo.Sec17.Item17Res14ProofKF

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof166Three

open CFSG CFSG.Open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec11 CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec16
  CFSG.RankThree.PartTwo.Sec17

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

theorem pRank_five_quot_le (h : Sec17Std G A c L Y₀) {X : Subgroup G}
    (hX : X ∈ scriptY3 A (lB A)) :
    CFSG.Open.pRank 5 (⊤ : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)) ≤ 2 :=
  pRank_quot_pCore_two_le h.toTheoremFourHyp hX.1.2
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X) (by norm_num) (by norm_num)

section Certified


theorem component_facts (h : Sec17Std G A c L Y₀) {X : Subgroup G}
    (hX : X ∈ scriptY3 A (lB A)) (hX3 : ¬ 3 ∣ Nat.card X) :
    ∀ K : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X), CFSG.IsComponent K →
      Subgroup.center K = ⊥ ∧ 5 ∣ Nat.card K := by
  intro K hK
  have hXtop : X ≠ ⊤ := hX.1.1.1
  have hKH : CFSG.IsKGroup (↥X ⧸ CFSG.pCore 2 ↥X) :=
    CFSG.RankThree.PartOne.EmbeddingTransport.isKGroup_quotient
      ((h.toTheoremFourHyp.sectionFourHyp hXtop).kGroup) (CFSG.pCore 2 ↥X)
  have h3 : ¬ 3 ∣ Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) := fun h3 =>
    hX3 (h3.trans (Subgroup.card_quotient_dvd_card _))
  have h2 : CFSG.pCore 2 (↥X ⧸ CFSG.pCore 2 ↥X) = ⊥ :=
    CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot
  obtain ⟨hZ, h5, -⟩ := suzuki_component_facts hKH h3 h2 hK
  exact ⟨hZ, h5⟩

theorem pCore_eq_of_mem_thetaComponents (h : Sec17Std G A c L Y₀) {X : Subgroup G}
    (hX : X ∈ scriptY3 A (lB A)) (hX3 : ¬ 3 ∣ Nat.card X) :
    ∀ L' ∈ thetaComponents 3 ↥X,
      CFSG.pCore 2 L' = aschbacherSolvableCore 3 L' := by
  intro L' hL'
  let K : Subgroup G := L'.map X.subtype
  have hK : K ∈ thetaComponentsIn X := ⟨L', hL', rfl⟩
  obtain ⟨n, hn⟩ := Proof17Res14.exists_suzukiModel_of_mem_thetaComponentsIn
    h.toTheoremFourHyp hX.1.1.1 hX3 hK
  have hθK : CFSG.pCore 2 ↥K = aschbacherSolvableCore 3 ↥K :=
    step166Theta G h.toTheoremFourHyp X K hK n hn
  let e : ↥L' ≃* ↥K := Subgroup.equivMapOfInjective L' X.subtype X.subtype_injective
  have hp : (CFSG.pCore 2 ↥L').map e.toMonoidHom = CFSG.pCore 2 ↥K :=
    CFSG.pCore_map_iso 2 e
  have hθ : (aschbacherSolvableCore 3 ↥L').map e.toMonoidHom =
      aschbacherSolvableCore 3 ↥K :=
    aschbacherSolvableCore_map_mulEquiv Nat.prime_three e
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [hp, hθ, hθK]

theorem commutator_le_inner_thetaQuot_of_mem_thetaComponents (h : Sec17Std G A c L Y₀)
    {X : Subgroup G} (hX : X ∈ scriptY3 A (lB A)) (hX3 : ¬ 3 ∣ Nat.card X)
    {L' : Subgroup ↥X} (hL' : L' ∈ thetaComponents 3 ↥X) :
    commutator (MulAut (↥L' ⧸ aschbacherSolvableCore 3 ↥L')) ≤
      (MulAut.conj : (↥L' ⧸ aschbacherSolvableCore 3 ↥L') →* MulAut _).range := by
  let K : Subgroup G := L'.map X.subtype
  have hK : K ∈ thetaComponentsIn X := ⟨L', hL', rfl⟩
  obtain ⟨n, hn⟩ := Proof17Res14.exists_suzukiModel_of_mem_thetaComponentsIn
    h.toTheoremFourHyp hX.1.1.1 hX3 hK
  have houtK := KFacts.commutator_le_inner_of_suzukiModel hn
  let e : ↥L' ≃* ↥K := Subgroup.equivMapOfInjective L' X.subtype X.subtype_injective
  have hθ : (aschbacherSolvableCore 3 ↥L').map e.toMonoidHom =
      aschbacherSolvableCore 3 ↥K :=
    aschbacherSolvableCore_map_mulEquiv Nat.prime_three e
  let E : (↥L' ⧸ aschbacherSolvableCore 3 ↥L') ≃*
      (↥K ⧸ aschbacherSolvableCore 3 ↥K) :=
    QuotientGroup.congr (aschbacherSolvableCore 3 ↥L')
      (aschbacherSolvableCore 3 ↥K) e hθ
  exact commutator_mulAut_le_conj_range_of_mulEquiv E.symm houtK

theorem pCore_eq_and_subset_of_mem_thetaComponentsIn (h : Sec17Std G A c L Y₀)
    (hgen : Gen166 A c) (hnosz : NoSz166 Y₀) {X : Subgroup G}
    (hX : X ∈ scriptY3 A (lB A)) (hX3 : ¬ 3 ∣ Nat.card X) {K : Subgroup G}
    (hK : K ∈ thetaComponentsIn X) :
    CFSG.pCore 2 ↥K = aschbacherSolvableCore 3 ↥K ∧
      (K : Set G) ⊆ Late.sectionCentralizer (Subgroup.normalizer (Y₀ : Set G)) Y₀
        (CFSG.Open.pCoreOf 2 Y₀) ∧
      ∃ m : ℕ, CFSG.Blueprint.SuzukiModel (↥K ⧸ CFSG.pCore 2 ↥K) 2 m := by
  obtain ⟨n, hn⟩ := Proof17Res14.exists_suzukiModel_of_mem_thetaComponentsIn
    h.toTheoremFourHyp hX.1.1.1 hX3 hK
  have h1 := rank3II_16_6_1_of h step166Theta hgen hnosz hX.1.1 hX.2 hK ⟨n, hn⟩
  exact ⟨h1.1, h1.2,
    ⟨n, suzukiModel_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq h1.1) hn⟩⟩

theorem le_normalizer_of_mem_thetaComponentsIn_of_three (h : Sec17Std G A c L Y₀)
    {X : Subgroup G} (hX : X ∈ scriptY3 A (lB A)) (hX3 : ¬ 3 ∣ Nat.card X)
    {K : Subgroup G} (hK : K ∈ thetaComponentsIn X) :
    A ≤ Subgroup.normalizer (K : Set G) :=
  le_normalizer_of_mem_thetaComponentsIn (pRank_five_quot_le h hX)
    (component_facts h hX hX3) (pCore_eq_of_mem_thetaComponents h hX hX3)
    (HeadProof.isE27_of_std h).isPGroup hX.1.1.2 hK

theorem le_sSup_of_isPerfect_of_three (h : Sec17Std G A c L Y₀) {X : Subgroup G}
    (hX : X ∈ scriptY3 A (lB A)) (hX3 : ¬ 3 ∣ Nat.card X) {P : Subgroup G}
    (hPX : P ≤ X) (hP : Group.IsPerfect P) :
    P ≤ sSup (thetaComponentsIn X) := by
  refine le_sSup_thetaComponentsIn_of_isPerfect hX3 ?_ ?_ hPX hP
  · intro L' hL'
    exact commutator_le_inner_thetaQuot_of_mem_thetaComponents h hX hX3 hL'
  · intro L₁ h₁ L₂ h₂ L₃ h₃
    exact eq_or_eq_or_eq_of_mem_thetaComponents (pRank_five_quot_le h hX)
      (component_facts h hX hX3) (pCore_eq_of_mem_thetaComponents h hX hX3) h₁ h₂ h₃

theorem sSup_subset_sectionCentralizer (h : Sec17Std G A c L Y₀) (hgen : Gen166 A c)
    (hnosz : NoSz166 Y₀) {X : Subgroup G} (hX : X ∈ scriptY3 A (lB A))
    (hX3 : ¬ 3 ∣ Nat.card X) :
    ((sSup (thetaComponentsIn X) : Subgroup G) : Set G) ⊆
      Late.sectionCentralizer (Subgroup.normalizer (Y₀ : Set G)) Y₀
        (CFSG.Open.pCoreOf 2 Y₀) := by
  have hM : Subgroup.normalizer (Y₀ : Set G) ≤ Subgroup.normalizer (Y₀ : Set G) := le_rfl
  have hQ : Subgroup.normalizer (Y₀ : Set G) ≤
      Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y₀ : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) Y₀
  have hle : sSup (thetaComponentsIn X) ≤
      Sec11.sectionCentralizerSubgroup (Subgroup.normalizer (Y₀ : Set G)) Y₀
        (CFSG.Open.pCoreOf 2 Y₀) hM hQ := by
    refine sSup_le fun K hK => ?_
    intro x hx
    exact (Sec11.mem_sectionCentralizerSubgroup (hAX := hM) (hAY := hQ)).mpr
      ((pCore_eq_and_subset_of_mem_thetaComponentsIn h hgen hnosz hX hX3 hK).2.1 hx)
  intro x hx
  exact (Sec11.mem_sectionCentralizerSubgroup (hAX := hM) (hAY := hQ)).mp (hle hx)

end Certified

end CFSG.RankThree.PartTwo.Sec16.Proof166Three