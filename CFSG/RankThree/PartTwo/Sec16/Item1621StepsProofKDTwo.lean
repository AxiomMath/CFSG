module

public import CFSG.RankThree.PartTwo.Sec16.Item1621StepsProofKS
import CFSG.RankThree.Classical.EvenSurvivingScalarRank
import CFSG.RankThree.PartTwo.Sec16.Item16Tail
import CFSG.RankThree.PartOne.S10.EmbeddingFixedResidual

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL)
open scoped commutatorElement

@[expose] def KS1624MaxLocalAct : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M R K V : Subgroup G) (m : ℕ),
    IsKGroup ↥M →
    M ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf 2 M : Set G) ≤ CFSG.Open.pCoreOf 2 M →
    (∀ r : ℕ, r.Prime → 3 < r → CFSG.Open.pRank r M ≤ 2) →
    R ≤ M → M ≤ Subgroup.normalizer (R : Set G) → ¬ 3 ∣ Nat.card R →
    K ≤ M → Group.IsPerfect ↥K → V ≤ K → K ≤ Subgroup.normalizer (V : Set G) →
    CFSG.Assembly.IsElemAbelian 2 V → V = ⁅V, K⁆ → 4 ≤ Nat.card (GaloisField 2 m) →
    (∃ _ : (V.subgroupOf K).Normal,
      Nonempty (↥K ⧸ V.subgroupOf K ≃* projSL 2 (GaloisField 2 m))) →
    ⁅K, R⁆ ≤ CFSG.Open.pCoreOf 2 M

namespace Proof1624KD2

variable {G : Type} [Group G]

theorem le_subgroupOf_iff {M N : Subgroup G} {S : Subgroup ↥M} :
    S ≤ N.subgroupOf M ↔ S.map M.subtype ≤ N := by
  rw [Subgroup.map_le_iff_le_comap]
  rfl

theorem map_commutator_subgroupOf {M X Y : Subgroup G} (hX : X ≤ M) (hY : Y ≤ M) :
    (⁅X.subgroupOf M, Y.subgroupOf M⁆).map M.subtype = ⁅X, Y⁆ := by
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hX,
    Subgroup.map_subgroupOf_eq_of_le hY]

theorem three_subgroups_in {M X Y Z N : Subgroup G} (hX : X ≤ M) (hY : Y ≤ M) (hZ : Z ≤ M)
    (hMN : M ≤ Subgroup.normalizer (N : Set G)) (h1 : ⁅⁅X, Y⁆, Z⁆ ≤ N)
    (h2 : ⁅⁅Y, Z⁆, X⁆ ≤ N) : ⁅⁅Z, X⁆, Y⁆ ≤ N := by
  set N' := N.subgroupOf M with hN'
  have hN'n : N'.Normal := ⟨fun n hn g => by
    rw [hN', Subgroup.mem_subgroupOf] at hn ⊢
    simpa using (Subgroup.mem_normalizer_iff.mp (hMN g.2) n).mp hn⟩
  have key : ∀ A B C : Subgroup G, A ≤ M → B ≤ M → C ≤ M →
      (⁅⁅A, B⁆, C⁆ ≤ N ↔ ⁅⁅(A.subgroupOf M).map (QuotientGroup.mk' N'),
        (B.subgroupOf M).map (QuotientGroup.mk' N')⁆,
          (C.subgroupOf M).map (QuotientGroup.mk' N')⁆ = ⊥) := by
    intro A B C hA hB hC
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk', le_subgroupOf_iff, Subgroup.map_commutator,
      map_commutator_subgroupOf hA hB, Subgroup.map_subgroupOf_eq_of_le hC]
  rw [key X Y Z hX hY hZ] at h1
  rw [key Y Z X hY hZ hX] at h2
  rw [key Z X Y hZ hX hY]
  exact Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2

end Proof1624KD2

open Proof1624KD2

theorem step1624KDTwo_of (h1623 : Step1623) (hKP1 : KS1624ParaKP1)
    (hAct : KS1624MaxLocalAct) : Step1624KDTwo := by
  intro G _ _ A c L h b n p P hD m V X hVX hneg M hM hKM hcM hQK hKD3
  set K := kPara1623 L V with hKdef
  set D := normalClosureSub M (Subgroup.zpowers c) with hDdef
  set R := pPrimeCoreOf 3 D with hRdef
  set Q := CFSG.Open.pCoreOf 2 M with hQdef
  obtain ⟨-, hDM, hMD⟩ := Proof169.normalClosureSub_spec (Subgroup.zpowers_le.mpr hcM)
  have hMQ : M ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
  have hMR : M ≤ Subgroup.normalizer (R : Set G) :=
    hMD.trans (normalizer_le_normalizer_pPrimeCoreOf 3 D)
  have hRD : R ≤ D := pPrimeCoreOf_le 3 D
  have hR3 : ¬ 3 ∣ Nat.card R := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 D)
  have hKperf : Group.IsPerfect ↥K :=
    CFSG.RankThree.PartOne.EmbeddingFixedResidual.isPerfect_inSubgroup_perfectResidual _
  obtain ⟨S, hS1, hS2, hMS⟩ := hM.1
  have hMtop : M ≠ ⊤ := by
    rw [hMS]
    exact Sec14.normalizer_ne_top_of_isPGroup h.isSimpleGroup h.nonabelian hS1 hS2
  have hMK : IsKGroup ↥M := (h.toTheoremFourHyp.sectionFourHyp hMtop).kGroup
  have hchar : M ⊓ Subgroup.centralizer (Q : Set G) ≤ Q := fun x hx =>
    h.charTwoType M hM.1 hx
  have hloc : CFSG.Assembly.IsTwoLocal M := ⟨S, hS1, hS2, hMS⟩
  have hrank : ∀ r : ℕ, r.Prime → 3 < r → CFSG.Open.pRank r M ≤ 2 := fun r hr hr3 => by
    have h1 : CFSG.Open.pRank r M ≤ CFSG.Assembly.RankThreeEven.localRank r G :=
      CFSG.RankThree.Classical.pRank_le_localRank hr.one_lt hloc
    have h2 := h.toTheoremFourHyp.localRank_lt r hr hr3
    omega
  obtain ⟨m', hm', hLm'⟩ := h1623 G A c L h
  obtain ⟨-, -, -, -, hVK⟩ := hKP1 G L m' hm' hLm' b m p P V X hD.prime hD.three_lt hVX
  have hKV : K ≤ Subgroup.normalizer (V : Set G) := by
    obtain ⟨hn, -⟩ := hVX.quot
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hVX.le_V).mp hn
  have hKR : ⁅K, R⁆ ≤ Q :=
    hAct G M R K V m hMK hchar hrank (hRD.trans hDM) hMR hR3 hKM hKperf hVX.le_V hKV
      hVX.elem hVK (Proof1624KS.four_le_card_galoisField hD.prime hD.three_lt hVX) hVX.quot
  have h1 : ⁅⁅K, D⁆, K⁆ ≤ Q :=
    (Subgroup.commutator_mono hKD3 le_rfl).trans (by rw [Subgroup.commutator_comm]; exact hKR)
  have h2 : ⁅⁅D, K⁆, K⁆ ≤ Q := by
    rw [Subgroup.commutator_comm D K]
    exact h1
  have h3 := three_subgroups_in hKM hDM hKM hMQ h1 h2
  have hKK : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hKperf
  rwa [hKK] at h3

end CFSG.RankThree.PartTwo.Sec16
