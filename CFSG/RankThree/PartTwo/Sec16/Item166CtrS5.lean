module

public import CFSG.RankThree.PartTwo.Sec15.Item15Inputs
public import CFSG.RankThree.PartTwo.Sec3.ThompsonFamilyG
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Triple
public import CFSG.RankThree.PartTwo.Sec15.Item153PushProofTools
public import CFSG.RankThree.PartTwo.Sec16.Item163ProofR
import CFSG.RankThree.PartTwo.Sec18.Item187Triple
import CFSG.RankThree.PartTwo.Sec20.Item20Res5ProofNormal
import CFSG.StronglyEmbedded.SteinbergBSMaximalThreePointEvenPoint
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoTransport
import CFSG.GroupTheory.ABGLocalTools.Constraint
import CFSG.RankThree.PartTwo.Sec16.Item165ProofTools
public import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.RankThree.PartTwo.Sec16.Ctr166

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec17
  CFSG.RankThree.LocalRank CFSG.GH74.GLS CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ S : Subgroup G}

theorem map_map_higherElemThompson_eq_jG {S H : Subgroup G} (hSH : S ≤ H) (i : ℕ) :
    ((CFSG.higherElemThompson ↥(S.subgroupOf H) i).map (S.subgroupOf H).subtype).map H.subtype =
      Sec3.jG S i := by
  rw [Sec3.map_higherElemThompson, Sec20.Res5.map_jG_of_injective H.subtype H.subtype_injective,
    Subgroup.map_subgroupOf_eq_of_le hSH]

theorem le_normalizer_jOf_of_normal {S H : Subgroup G} (hSH : S ≤ H)
    (hN : ((CFSG.higherElemThompson ↥(S.subgroupOf H) 0).map (S.subgroupOf H).subtype).Normal) :
    H ≤ Subgroup.normalizer (jOf S : Set G) := by
  haveI := hN
  have h := CFSG.ABGLocalTools.le_normalizer_map_subtype H
    ((CFSG.higherElemThompson ↥(S.subgroupOf H) 0).map (S.subgroupOf H).subtype)
  rw [map_map_higherElemThompson_eq_jG hSH 0, ← Sec18.Item187Proof.jOf_eq_jG_zero] at h
  exact h

theorem le_normalizer_omegaOneZ_jOneOf_of_normal {S H : Subgroup G} (hSH : S ≤ H)
    (hm : 2 ≤ CFSG.pRank 2 ↥S)
    (hN : ((CFSG.higherElemThompson ↥(S.subgroupOf H) 1).map (S.subgroupOf H).subtype).Normal) :
    H ≤ Subgroup.normalizer (omegaOneZ (jOneOf S) : Set G) := by
  haveI := hN
  have h := CFSG.ABGLocalTools.le_normalizer_map_subtype H
    ((CFSG.higherElemThompson ↥(S.subgroupOf H) 1).map (S.subgroupOf H).subtype)
  rw [map_map_higherElemThompson_eq_jG hSH 1, ← Sec18.Item187Proof.jOneOf_eq_jG_one hm] at h
  intro x hx
  exact Sec7.mem_normalizer_of_conj_mem (fun z hz => Sec7.conj_mem_omegaOneZ (h hx) hz)
    (fun z hz => by simpa using Sec7.conj_mem_omegaOneZ (h (H.inv_mem hx)) hz)

theorem omegaOneZ_le_centralizer_of_le_center {S H Y : Subgroup G} (hSH : S ≤ H) (hYH : Y ≤ H)
    (hz : (CFSG.omegaOneCenter (⊤ : Subgroup ↥(S.subgroupOf H))).map (S.subgroupOf H).subtype ≤
      Subgroup.center ↥H) :
    omegaOneZ S ≤ Subgroup.centralizer (Y : Set G) := by
  intro z hzS
  rw [Sec18.Item187Proof.omegaOneZ_eq_omegaG, Sec3.mem_omegaG] at hzS
  obtain ⟨hzS, hzc, hz2⟩ := hzS
  have hzK : (⟨z, hSH hzS⟩ : ↥H) ∈
      (CFSG.omegaOneCenter (⊤ : Subgroup ↥(S.subgroupOf H))).map
        (S.subgroupOf H).subtype := by
    rw [Sec3.map_omegaOneCenter]
    refine Sec3.mem_omegaG.mpr ⟨?_, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨⟨⟨z, hSH hzS⟩, Subgroup.mem_subgroupOf.mpr hzS⟩,
        Subgroup.mem_top _, rfl⟩
    · intro x hx
      obtain ⟨a, -, rfl⟩ := Subgroup.mem_map.mp hx
      exact Subtype.ext (hzc a.1.1 (Subgroup.mem_subgroupOf.mp a.2))
    · exact Subtype.ext hz2
  have hzcenter : (⟨z, hSH hzS⟩ : ↥H) ∈ Subgroup.center ↥H := hz hzK
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hzcenter ⟨y, hYH hy⟩)

theorem two_le_pRank_of_not_le_centralizer {S Y : Subgroup G}
    (hch : CFSG.QuasithinUnique.CharTwo (Y ⊔ S)) (hQS : CFSG.Open.pCoreOf 2 (Y ⊔ S) ≤ S)
    (hZ : ¬ omegaOneZ S ≤ Subgroup.centralizer (Y : Set G)) : 2 ≤ CFSG.pRank 2 ↥S := by
  obtain ⟨z, hz, hzY⟩ := SetLike.not_le_iff_exists.mp hZ
  rw [Sec18.Item187Proof.omegaOneZ_eq_omegaG, Sec3.mem_omegaG] at hz
  obtain ⟨hzS, hzc, hz2⟩ := hz
  have hzH : z ∈ Y ⊔ S := (le_sup_right : S ≤ Y ⊔ S) hzS
  have hzC : z ∈ Subgroup.centralizer (CFSG.Open.pCoreOf 2 (Y ⊔ S) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact (hzc q (hQS hq)).symm
  have hzQ : z ∈ CFSG.Open.pCoreOf 2 (Y ⊔ S) := hch ⟨hzH, hzC⟩
  have hyz : ∃ y ∈ Y, z * y ≠ y * z := by
    by_contra h
    push Not at h
    exact hzY (Subgroup.mem_centralizer_iff.mpr fun y hy => (h y hy).symm)
  obtain ⟨y, hyY, hyz⟩ := hyz
  have hyH : y ∈ Y ⊔ S := (le_sup_left : Y ≤ Y ⊔ S) hyY
  let w : G := y * z * y⁻¹
  have hwQ : w ∈ CFSG.Open.pCoreOf 2 (Y ⊔ S) :=
    (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y ⊔ S) hyH) z).mp hzQ
  have hwS : w ∈ S := hQS hwQ
  have hz1 : z ≠ 1 := by
    intro h
    exact hyz (by rw [h, one_mul, mul_one])
  have hwne : w ≠ z := by
    intro h
    apply hyz
    have h' : y * z * y⁻¹ * y = z * y := congrArg (fun t => t * y) h
    rw [mul_assoc (y * z) y⁻¹ y, inv_mul_cancel, mul_one] at h'
    exact h'.symm
  have hzord : orderOf z = 2 := orderOf_eq_prime (by rwa [pow_two]) hz1
  have hword : orderOf w = 2 := by
    have h := MulEquiv.orderOf_eq (MulAut.conj y) z
    rwa [MulAut.conj_apply, hzord] at h
  have hznew : z ≠ w := fun h => hwne h.symm
  refine CFSG.StronglyEmbedded.two_le_pRank_two_of_commuting_involutions (X := ↥S)
    (x := ⟨z, hzS⟩) (y := ⟨w, hwS⟩) ?_ ?_ ?_ ?_
  · rw [Subgroup.orderOf_mk]; exact hzord
  · rw [Subgroup.orderOf_mk]; exact hword
  · exact Subtype.ext (hzc w hwS)
  · intro h
    exact hznew (congrArg Subtype.val h)

theorem delta_normalizer_tripleOf_le (h : Sec17Std G A c L Y₀) (hS2 : IsPGroup 2 S)
    (hS1 : S ≠ ⊥) (hAS : A ≤ Subgroup.normalizer (S : Set G)) (i : Fin 3)
    (hYi : Y₀ ≤ Subgroup.normalizer (tripleOf S i : Set G)) :
    delta A (lB A) (Subgroup.normalizer (tripleOf S i : Set G)) ≤
      Subgroup.normalizer (Y₀ : Set G) :=
  (delta_le _).trans (Proof165.normalizer_le_M h (Sec7.tripleOf_ne_bot hS2 hS1 i)
    (hS2.to_le (Sec7.tripleOf_le S i)) (sup_le hYi (Sec7.le_normalizer_tripleOf hAS i)))

theorem delta_normalizer_le_of_inf_le (h : Sec17Std G A c L Y₀) (hS2 : IsPGroup 2 S)
    (hS1 : S ≠ ⊥) (hAS : A ≤ Subgroup.normalizer (S : Set G))
    (hQS : CFSG.Open.pCoreOf 2 (Y₀ ⊔ S) ≤ S)
    (hQY : CFSG.Open.pCoreOf 2 Y₀ = CFSG.Open.pCoreOf 2 (Y₀ ⊔ S) ⊓ Y₀)
    (hcov : ∀ s ∈ S, ∃ y ∈ S ⊓ Y₀, y⁻¹ * s ∈ CFSG.Open.pCoreOf 2 (Y₀ ⊔ S))
    (hSY : S ⊓ Y₀ ≤ CFSG.Open.pCoreOf 2 Y₀) :
    delta A (lB A) (Subgroup.normalizer (jOf S : Set G)) ≤ Subgroup.normalizer (Y₀ : Set G) ∧
      delta A (lB A) (Subgroup.normalizer (omegaOneZ (jOneOf S) : Set G)) ≤
        Subgroup.normalizer (Y₀ : Set G) := by
  have hSQ : S = CFSG.Open.pCoreOf 2 (Y₀ ⊔ S) := by
    apply le_antisymm ?_ hQS
    intro s hs
    obtain ⟨y, hy, hys⟩ := hcov s hs
    have hyQ0 : y ∈ CFSG.Open.pCoreOf 2 Y₀ := hSY hy
    have hyQ : y ∈ CFSG.Open.pCoreOf 2 (Y₀ ⊔ S) := by
      rw [hQY] at hyQ0
      exact (Subgroup.mem_inf.mp hyQ0).1
    rw [show s = y * (y⁻¹ * s) by group]
    exact Subgroup.mul_mem _ hyQ hys
  have hY0N : Y₀ ≤ Subgroup.normalizer (S : Set G) := by
    rw [hSQ]
    exact le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y₀ ⊔ S))
  refine ⟨?_, ?_⟩
  · simpa only [Sec7.tripleOf_zero] using
      delta_normalizer_tripleOf_le h hS2 hS1 hAS (0 : Fin 3)
        (Sec7.le_normalizer_tripleOf hY0N 0)
  · simpa only [Sec7.tripleOf_one] using
      delta_normalizer_tripleOf_le h hS2 hS1 hAS (1 : Fin 3)
        (Sec7.le_normalizer_tripleOf hY0N 1)

theorem delta_normalizer_le_of_dichotomy (h : Sec17Std G A c L Y₀) (h153 : Item153MainR)
    (h322 : Item3_22Two) (hS2 : IsPGroup 2 S) (hSM : S ≤ Subgroup.normalizer (Y₀ : Set G))
    (hAS : A ≤ Subgroup.normalizer (S : Set G)) (hQS : CFSG.Open.pCoreOf 2 (Y₀ ⊔ S) ≤ S)
    (hQY : CFSG.Open.pCoreOf 2 Y₀ = CFSG.Open.pCoreOf 2 (Y₀ ⊔ S) ⊓ Y₀)
    (hcov : ∀ s ∈ S, ∃ y ∈ S ⊓ Y₀, y⁻¹ * s ∈ CFSG.Open.pCoreOf 2 (Y₀ ⊔ S))
    (hX : Nonempty (↥(Y₀ ⊔ S) ⧸ CFSG.pCore 2 ↥(Y₀ ⊔ S) ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hdich : S ⊓ Y₀ ≤ CFSG.Open.pCoreOf 2 Y₀ ∨
      (Nonempty ((S.subgroupOf (Y₀ ⊔ S)).map (QuotientGroup.mk' (CFSG.pCore 2 ↥(Y₀ ⊔ S))) ≃*
          Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ∧
        Nonempty (Subgroup.centralizer
            (((S.subgroupOf (Y₀ ⊔ S)).map (QuotientGroup.mk' (CFSG.pCore 2 ↥(Y₀ ⊔ S))) :
              Subgroup (↥(Y₀ ⊔ S) ⧸ CFSG.pCore 2 ↥(Y₀ ⊔ S))) :
              Set (↥(Y₀ ⊔ S) ⧸ CFSG.pCore 2 ↥(Y₀ ⊔ S))) ≃*
          (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) × alternatingGroup (Fin 5))))
    (hZ : ¬ omegaOneZ S ≤ Subgroup.centralizer (Y₀ : Set G)) :
    delta A (lB A) (Subgroup.normalizer (jOf S : Set G)) ≤ Subgroup.normalizer (Y₀ : Set G) ∧
      delta A (lB A) (Subgroup.normalizer (omegaOneZ (jOneOf S) : Set G)) ≤
        Subgroup.normalizer (Y₀ : Set G) := by
  have hSne : S ≠ ⊥ := by
    intro hS
    apply hZ
    rw [hS]
    exact (Sec7.omegaOneZ_le ⊥).trans bot_le
  rcases hdich with hSY | ⟨hc, hd⟩
  · exact delta_normalizer_le_of_inf_le h hS2 hSne hAS hQS hQY hcov hSY
  · have hF0 : generalizedFitting ↥Y₀ = CFSG.pCore 2 ↥Y₀ :=
      (h153 G A c L h.toSec15R Y₀ h.mem_y0Star).2.2
    have hF : generalizedFitting ↥(Y₀ ⊔ S) = CFSG.pCore 2 ↥(Y₀ ⊔ S) :=
      Push153.generalizedFitting_sup_eq hF0 hS2 hSM
    have hYc : CFSG.QuasithinUnique.CharTwo Y₀ :=
      CFSG.QuasithinUnique.charTwo_iff_isCharacteristicP.mpr
        ((isCharacteristicP_iff_generalizedFitting_eq_pCore ↥Y₀ 2).mpr hF0)
    have hch : CFSG.QuasithinUnique.CharTwo (Y₀ ⊔ S) :=
      Push153.charTwo_sup_of_isPGroup hYc hS2 hSM
    have hQR : CFSG.pCore 2 ↥(Y₀ ⊔ S) ≤ S.subgroupOf (Y₀ ⊔ S) := by
      intro q hq
      rw [Subgroup.mem_subgroupOf]
      exact hQS (Subgroup.mem_map_of_mem (Y₀ ⊔ S).subtype hq)
    have hm : 2 ≤ CFSG.pRank 2 ↥S :=
      two_le_pRank_of_not_le_centralizer hch hQS hZ
    have hzc : ¬ (CFSG.omegaOneCenter (⊤ : Subgroup ↥(S.subgroupOf (Y₀ ⊔ S)))).map
        (S.subgroupOf (Y₀ ⊔ S)).subtype ≤ Subgroup.center ↥(Y₀ ⊔ S) :=
      fun hle => hZ (omegaOneZ_le_centralizer_of_le_center le_sup_right le_sup_left hle)
    obtain ⟨hN0, hN1⟩ :=
      h322 ↥(Y₀ ⊔ S) hF hX (S.subgroupOf (Y₀ ⊔ S)) hQR hc hd hzc
    have hY0j : Y₀ ≤ Subgroup.normalizer (jOf S : Set G) :=
      le_sup_left.trans (le_normalizer_jOf_of_normal le_sup_right hN0)
    have hY0Ω : Y₀ ≤ Subgroup.normalizer (omegaOneZ (jOneOf S) : Set G) :=
      le_sup_left.trans (le_normalizer_omegaOneZ_jOneOf_of_normal le_sup_right hm hN1)
    refine ⟨?_, ?_⟩
    · simpa only [Sec7.tripleOf_zero] using
        delta_normalizer_tripleOf_le h hS2 hSne hAS (0 : Fin 3)
          (by simpa only [Sec7.tripleOf_zero] using hY0j)
    · simpa only [Sec7.tripleOf_one] using
        delta_normalizer_tripleOf_le h hS2 hSne hAS (1 : Fin 3)
          (by simpa only [Sec7.tripleOf_one] using hY0Ω)

end CFSG.RankThree.PartTwo.Sec16.Ctr166
