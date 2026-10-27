module

public import CFSG.RankThree.PartTwo.Sec17.Item17ResProof177
public import CFSG.RankThree.PartTwo.Sec17.Item1712StepsProofMain
public import CFSG.RankThree.PartTwo.Sec17.Item177Proof
public import CFSG.RankThree.PartTwo.Sec6.LitScopeProof
import CFSG.RankThree.PartTwo.Sec17.Item176StepsProofTools
import CFSG.RankThree.PartTwo.Sec17.Item17HeadProof
import CFSG.RankThree.PartTwo.Sec17.Item17TailEnd
import CFSG.RankThree.PartTwo.Sec17.Item171ProofKFact
import CFSG.RankThree.PartTwo.Sec15.HypS
import CFSG.RankThree.PartTwo.Sec14.Concl142HJ
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec16.Item163StepsAltProofTools
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.RankThree.PartTwo.Sec6.Item612Local
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.Coprime.ThompsonElementaryComplement
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.RankThree.GF2n.Statements
public import CFSG.RankThree.PartTwo.Sec17.Item1712ProofRoute
public import CFSG.RankThree.PartTwo.Sec6.Item612
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.RankThree.PartTwo.KFacts.K412Alternating
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import Certificates.Certificate8166
import Certificates.Certificate8169

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
open scoped commutatorElement

@[expose] noncomputable def Item177One : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → ∀ V : Subgroup G,
      Maximal (fun V : Subgroup G => V ≤ Subgroup.normalizer (Y₀ : Set G) ∧
        Subgroup.normalizer (Y₀ : Set G) ≤ Subgroup.normalizer (V : Set G) ∧
        CFSG.Assembly.IsElemAbelian 2 V) V →
      ⁅Y₀ ⊔ A, V⁆ ≠ ⊥

theorem item177One_of_item3_10 (h310 : Sec6.Item3_10) : Item177One :=
  fun _ _ _ _ _ _ _ h _ hV => rank3II_17_7_one_of h h310 hV

section Item177

variable {G : Type} [Group G] [Finite G]

open Proof177 Proof17Res in
theorem rank3II_17_7_of_B_one {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀) (h1771 : Item177One) (h1514 : Item1514 A (lB A) c L)
    (hMeets : MeetsY4 A (lB A) L Y₀) (hAY : Claim1715A) (h176 : Item176 A (lB A) c L)
    (hmeet : Step177Meet) (hmain : Step177MainB) : Item177 A (lB A) := by
  intro Y hY V hV
  obtain rfl : Y = Y₀ := h.eq_of_mem_y0Star hY
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : IsE27 A := h.isE27
  have h1 : ⁅Y ⊔ A, V⁆ ≠ ⊥ := h1771 G A c L Y h V hV
  refine ⟨h1, ?_⟩
  obtain ⟨hVM, hMV, hVab⟩ := hV.prop
  have hAM : A ≤ Subgroup.normalizer (Y : Set G) := Subgroup.le_normalizer.trans h.normalizer_le
  have hAV : A ≤ Subgroup.normalizer (V : Set G) := hAM.trans hMV
  have hget : ∀ W : Subgroup G, W ≤ V → W ∈ scriptQ A (lB A) → ⁅W, A⁆ ≠ ⊥ →
      ∃ U ∈ fourGroupsMinus A, U ∈ scriptQPi A (lB A) V (piOf 2) := by
    intro W hWV hW hWA
    obtain ⟨U, hU, hUW⟩ := exists_mem_fourGroupsMinus_le hA (Sec5.isElemAbelian_of_le hVab hWV)
      hW.1.2.2 hWA
    exact ⟨U, hU, ⟨mem_scriptQ_of_le hW hUW hU.1.1.2.2, hUW.trans hWV⟩, hU.1.1.2.1⟩
  by_cases hVY : ⁅V, Y⁆ = ⊥
  ·
    have hYV : ⁅Y, V⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact hVY
    have hcases := h1514 Y hY hMeets
    have hΩ : omegaA A = {Subgroup.zpowers c} := by
      by_contra hΩ
      rcases hcases with ⟨-, -, hΩ', -⟩ | ⟨hA7, -, htr, -⟩ | ⟨-, -, -, hΩ', -⟩
      · exact hΩ hΩ'
      ·
        have hA10 := h.a10_or_omega.resolve_right hΩ
        have hAY0 := hAY G A c L Y h hA10 hA7 htr
        exact h1 (by rw [sup_eq_left.mpr hAY0]; exact hYV)
      · exact hΩ hΩ'
    have hprod : Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L) := by
      rcases hcases with ⟨-, -, -, hp, -⟩ | ⟨-, -, htr, -⟩ | ⟨-, -, -, -, hno, -⟩
      · exact hp
      · have h3 := htr.1
        rw [hΩ, Set.ncard_singleton] at h3
        omega
      · exact absurd h.le_y0 (hno Y hY)
    have hcL : c ∉ L := h.toSec15R.hypS.2.2 c h.zpowers_mem_omegaA L h.mem_lA
    have h9 : Nat.card (A ⊓ L : Subgroup G) = 9 := card_inf_eq_nine_of_prod h hprod
    have hcard := (isElemAbelian_zpowers_sup_of_card_nine h.c_pow_three
      (fun hcB => hcL (Subgroup.mem_inf.mp hcB).2) le_rfl h9
      (fun b hb => hA.1.2 b hb.1) (fun b hb => h.commute_of_mem h.c_mem hb.1)).2
    have hle : Subgroup.zpowers c ⊔ (A ⊓ L) ≤ A :=
      sup_le (Subgroup.zpowers_le.mpr h.c_mem) inf_le_left
    have hAeq : A = Subgroup.zpowers c ⊔ (A ⊓ L) :=
      (Subgroup.eq_of_le_of_card_ge hle (by rw [hA.2, hcard])).symm
    have hcV : ⁅V, Subgroup.zpowers c⁆ ≠ ⊥ := by
      intro hcV
      apply h1
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      have hYC := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hYV
      have hcC : Subgroup.zpowers c ≤ Subgroup.centralizer (V : Set G) := by
        rw [Subgroup.commutator_comm] at hcV
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcV
      refine sup_le hYC ?_
      rw [hAeq]
      exact sup_le hcC ((inf_le_right.trans h.le_y0).trans hYC)
    by_cases hU : ⁅V, Subgroup.zpowers c⁆ ⊓
        pPrimeCoreOf 3 (Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) = ⊥
    · exact (hmain G A c L Y h h1514 h176 hΩ V hV hYV hcV hU).elim
    ·
      have hB : IsHyperplane A (A ⊓ L) := ⟨inf_le_left, by rw [hA.2, h9]⟩
      set W := ⁅V, Subgroup.zpowers c⁆ ⊓
        pPrimeCoreOf 3 (Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) with hWdef
      have hcA : c ∈ A := h.c_mem
      have hAc : A ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := fun a ha =>
        centralizer_singleton_le_normalizer_zpowers c (Subgroup.mem_centralizer_singleton_iff.mpr
          (h.commute_of_mem ha hcA))
      have hOQ : pPrimeCoreOf 3 (Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) ∈
          scriptQ A (lB A) := pPrimeCoreOf_centralizer_hyperplane_mem_scriptQ hA hB
      have hAW : A ≤ Subgroup.normalizer (W : Set G) :=
        le_normalizer_inf (le_normalizer_commutator hAV hAc) hOQ.1.2.2
      have hWV : W ≤ V :=
        inf_le_left.trans (Subgroup.le_normalizer_iff_commutator_le_left.mp
          (Subgroup.zpowers_le.mpr (hAV hcA)))
      have hW : W ∈ scriptQ A (lB A) := mem_scriptQ_of_le hOQ inf_le_right hAW
      refine hget W hWV hW fun hWA => hU ?_
      have hWC : W ≤ Subgroup.centralizer (A : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hWA
      have hV2 : IsPGroup 2 V := Sec5.isPGroup_of_isElemAbelian hVab
      have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers c)) (Nat.card V) := by
        obtain ⟨k, hk⟩ := hV2.exists_card_eq
        rw [h.toSec13Data.card_zpowers, hk]
        exact Nat.Coprime.pow_right k (by norm_num)
      have hfit := CFSG.RankThree.Coprime.commutator_inf_centralizer_eq_bot
        (fun x hx y hy => congrArg Subtype.val (hVab.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
        (Subgroup.zpowers_le.mpr (hAV hcA)) hcop
      rw [Subgroup.commutator_comm] at hfit
      rw [eq_bot_iff, ← hfit]
      refine le_inf inf_le_left (hWC.trans (Subgroup.centralizer_le ?_))
      exact SetLike.coe_subset_coe.mpr (Subgroup.zpowers_le.mpr hcA)
  ·
    obtain ⟨hW, hWA⟩ := hmeet G A c L Y h V hV hVY
    exact hget (V ⊓ Y) inf_le_left hW hWA

theorem item177S17_of_B_one (h1771 : Item177One) (h1514 : Item1514S17)
    (hMeets : Claim1715Meets) (hAY : Claim1715A) (h176 : Item176R) (hmeet : Step177Meet)
    (hmain : Step177MainB) : Item177S17 :=
  fun G _ _ A c L Y₀ h => rank3II_17_7_of_B_one h h1771 (h1514 G A c L Y₀ h)
    (hMeets G A c L Y₀ h) hAY (h176 G A c L h.toSec15R) hmeet hmain

end Item177

end CFSG.RankThree.PartTwo.Sec17
