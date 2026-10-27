module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPairPointNormalizerBasic
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LinearModelPointStructureTransport
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPairLinearOrSuzuki

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.ProperPairModel

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ShultStronglyClosedTI.TwoCoreGrowth CFSG.ShultStronglyClosedTI.CyclicPair

theorem card_sylow_psl2 {k : Type} [Field k] [Finite k] {f : ℕ} (hk : Nat.card k = 2 ^ f)
    (S : Sylow 2 (PSL2MatrixGroup k)) : Nat.card S = Nat.card k := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₀, hS₀⟩ := LinearModel.exists_sylow_eq_rootGroup hk
  rw [card_sylow_eq_of_mulEquiv (MulEquiv.refl _) S S₀, hS₀,
    CFSG.GorensteinWalter.psl2UpperUnipotentSubgroup_card]

theorem card_sylow_suzukiGroup {m : ℕ} {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = 2 ^ (2 * m + 1)) (S : Sylow 2 (CFSG.Blueprint.suzukiGroup m k)) :
    Nat.card S = Nat.card k ^ 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSPA := SuzukiModel.suzukiPointAction_suzukiGroup (a := m) hk
  obtain ⟨S₀, hS₀⟩ := hSPA.exists_sylow
  rw [card_sylow_eq_of_mulEquiv (MulEquiv.refl _) S S₀, hS₀, hSPA.card_U, hk]

variable {G : Type} [Group G] [Finite G]

theorem minimalLocalFailure_proper_pair_hull_point_normalizer
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤) :
    let B := pairPointStabilizer H beta
    let X := rightInvolutionCommutatorSubgroup t (pairOddCore H beta)
    let K := minimalLocalFailureProperPairHull H z beta t
    let Q := minimalLocalFailurePairActionPointHull H z
    let M := H ⊓ K
    let N := Subgroup.normalizer (K : Set G) ⊓ H
    let Δ := {ω : rightCosetSpace H | ∃ x ∈ K, rightCosetMk H x = ω}
    ∃ T : Subgroup G, T ≤ M ∧ IsPGroup 2 T ∧
      (∀ S : Sylow 2 ↥M, (S : Subgroup ↥M).map M.subtype = T) ∧
      B ≤ Subgroup.normalizer (T : Set G) ∧
      (T.subgroupOf M).Normal ∧ M = T ⊔ X ∧ T ⊓ X = ⊥ ∧
      N = T ⊔ B ∧ T ⊓ B = ⊥ ∧
      (∃ _ : (T.subgroupOf N).Normal, Nonempty (↥N ⧸ T.subgroupOf N ≃* ↥B)) ∧
      ((∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = Nat.card Q ∧
          Nonempty (K ≃* PSL2MatrixGroup k)) →
        Nat.card T = Nat.card Q ∧ Nat.card Δ = Nat.card Q + 1) ∧
      ((∃ (m : ℕ) (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ (2 * m + 1) ∧
          Nat.card k = Nat.card Q ∧ Nonempty (K ≃* CFSG.Blueprint.suzukiGroup m k)) →
        Nat.card T = Nat.card Q ^ 2 ∧ Nat.card Δ = Nat.card Q ^ 2 + 1) ∧
      (∀ ω ∈ Δ, ∀ ω' ∈ Δ, ω ≠ rightCosetMk H 1 → ω' ≠ rightCosetMk H 1 →
        ∃! s : T, rightCosetTranslate H ω (s : G) = ω') := by
  intro B X K Q M N Δ
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hKB, hmodel, hBK, -, -⟩ :=
    minimalLocalFailure_proper_pair_hull_linear_or_suzuki h hcomm hsmallerR1 hbeta ht hproper
  have htK : t ∈ K := minimalLocalFailureProperPair_flip_mem H z beta t
  have hbetaeq := flip_coset_eq H ht
  have hBKX : B ⊓ K = X := by rw [inf_comm]; exact hKB
  obtain ⟨-, hQ4, -⟩ := proper_pair_cyclic_commutator h hcomm hsmallerR1 hbeta ht hproper
  have hQ4' : 4 ≤ Nat.card Q := hQ4
  have hsq : Nat.card Q ≠ Nat.card Q ^ 2 := by nlinarith
  rcases hmodel with ⟨e, -, hQe, -, k, _, _, hk, ψ, hψ₀, -, hψB, f, -, hfeq, hfα, -, hdeg⟩ |
    ⟨m, -, hQm, -, k, _, _, hk, ψ, hψ₀, -, hψB, f, -, hfeq, hfα, -, hdeg⟩
  · have hk2 : Nat.card k = 2 ^ e := hk.trans hQe
    have hLPA := LinearModel.linearPointAction_psl2 (K := k) hk2
    obtain ⟨T, hcardT, hsylK, hTM, hTp, hall, hBT, hnormal, hsupG, hinfG, hNeq, hTB, hquot,
      hregT⟩ := point_normalizer_of_aligned H K htK hbetaeq hbeta hBK ψ
        hLPA.sup_eq_stabilizer hLPA.stabilizer_le_normalizer hLPA.inf_eq_bot
        hLPA.exists_sylow hLPA.regular hψ₀ hψB f hfeq hfα
    have hTQ : Nat.card T = Nat.card Q := by rw [hcardT, hLPA.card_U, hQe]
    refine ⟨T, hTM, hTp, hall, hBT, hnormal, hBKX ▸ hsupG, hBKX ▸ hinfG, hNeq, hTB, hquot,
      fun _ => ⟨hTQ, hdeg⟩, ?_, hregT⟩
    rintro ⟨m', k', _, _, hk', hk'Q, ⟨e'⟩⟩
    exfalso
    have h1 := hsylK default
    rw [card_sylow_eq_of_mulEquiv e' default default, card_sylow_suzukiGroup hk', hk'Q,
      hLPA.card_U, ← hQe] at h1
    exact hsq h1.symm
  · have hSPA := SuzukiModel.suzukiPointAction_suzukiGroup (a := m) hk
    have hψ₀' := hψ₀.trans (CFSG.LieType.Ree.suzuki_ovoid_stabilizer hk).2.symm
    obtain ⟨T, hcardT, hsylK, hTM, hTp, hall, hBT, hnormal, hsupG, hinfG, hNeq, hTB, hquot,
      hregT⟩ := point_normalizer_of_aligned H K htK hbetaeq hbeta hBK ψ
        hSPA.sup_eq_stabilizer hSPA.stabilizer_le_normalizer hSPA.inf_eq_bot
        hSPA.exists_sylow hSPA.regular hψ₀' hψB f hfeq hfα
    have hTQ : Nat.card T = Nat.card Q ^ 2 := by rw [hcardT, hSPA.card_U, hQm]
    refine ⟨T, hTM, hTp, hall, hBT, hnormal, hBKX ▸ hsupG, hBKX ▸ hinfG, hNeq, hTB, hquot,
      ?_, fun _ => ⟨hTQ, hdeg⟩, hregT⟩
    rintro ⟨k', _, _, hk'Q, ⟨e'⟩⟩
    exfalso
    have h1 := hsylK default
    rw [card_sylow_eq_of_mulEquiv e' default default,
      card_sylow_psl2 (hk'Q.trans hQm), hk'Q, hSPA.card_U, ← hQm] at h1
    exact hsq h1
