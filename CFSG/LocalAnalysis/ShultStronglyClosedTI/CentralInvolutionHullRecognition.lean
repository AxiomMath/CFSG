module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralInvolutionQuotientData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.HullNativeRecognition

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G] [Finite G]

theorem elementary_ambient_hull_internal_generation (V : Subgroup G)
    (hV : IsElemAbelian 2 V) (hne : V ≠ ⊥)
    (B : Subgroup (Subgroup.normalClosure (V : Set G))) (hB : fusionStronglyEmbedded B) :
    Subgroup.normalClosure
      (V.subgroupOf (Subgroup.normalClosure (V : Set G)) :
        Set (Subgroup.normalClosure (V : Set G))) = ⊤ := by
  let K := Subgroup.normalClosure (V : Set G)
  let W := V.subgroupOf K
  let N := Subgroup.normalClosure (W : Set K)
  have hVK : V ≤ K := Subgroup.le_normalClosure
  obtain ⟨z, hzne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  let zK : K := ⟨(z : G), hVK z.property⟩
  have hzW : zK ∈ W := z.property
  have hzInv : IsInvolution zK := by
    refine ⟨?_, Subtype.ext (hV.2 z z.property)⟩
    intro hone
    exact hzne (Subtype.ext (congrArg (fun a : K => (a : G)) hone))
  have hKN : K ≤ N.map K.subtype := by
    change Subgroup.normalClosure (V : Set G) ≤ N.map K.subtype
    rw [← closure_conjugateInvolutions_eq_normalClosure V]
    apply (Subgroup.closure_le (N.map K.subtype)).mpr
    intro a ha
    have haK : a ∈ K := Subgroup.conjugatesOfSet_subset_normalClosure
      ((Group.conjugatesOfSet_mono Set.sdiff_subset) ha)
    let aK : K := ⟨a, haK⟩
    have haorder : orderOf a = 2 := conjugateInvolutions_order_two V hV ha
    have haInv : IsInvolution aK := by
      refine ⟨?_, Subtype.ext ?_⟩
      · intro hone
        have haone : a = 1 := congrArg Subtype.val hone
        rw [haone, orderOf_one] at haorder
        omega
      · have hsquare := pow_orderOf_eq_one a
        rwa [haorder] at hsquare
    obtain ⟨g, hg⟩ := (native_strong_embedding_of_order_conditions hB).involutions_conjugate
      hzInv haInv
    have hzN : zK ∈ N := Subgroup.subset_normalClosure hzW
    have haN : aK ∈ N := by
      rw [← hg]
      exact (inferInstance : N.Normal).conj_mem' zK hzN g
    exact Subgroup.mem_map_of_mem K.subtype haN
  apply top_unique
  intro a _
  obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.mp (hKN a.property)
  exact (Subtype.ext hba : b = a) ▸ hb

theorem normalizer_elementary_ambient_hull_datum (V : Subgroup G)
    (hV : IsElemAbelian 2 V) (hcard : 4 ≤ Nat.card V)
    (hB : fusionStronglyEmbedded ((Subgroup.normalizer (V : Set G)).subgroupOf
      (Subgroup.normalClosure (V : Set G)))) :
    let K := Subgroup.normalClosure (V : Set G)
    let B := (Subgroup.normalizer (V : Set G)).subgroupOf K
    let W := V.subgroupOf K
    W ≤ B ∧ (W.subgroupOf B).Normal ∧ IsElemAbelian 2 W ∧
      Nat.card W = Nat.card V ∧ 4 ≤ Nat.card W ∧
      Subgroup.normalClosure (W : Set K) = ⊤ := by
  let K := Subgroup.normalClosure (V : Set G)
  let B := (Subgroup.normalizer (V : Set G)).subgroupOf K
  let W := V.subgroupOf K
  have hVK : V ≤ K := Subgroup.le_normalClosure
  have hW : IsElemAbelian 2 W := by
    constructor
    · apply isMulCommutative_iff.mpr
      intro a b
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun a : V => (a : G)) (isMulCommutative_iff.mp hV.1
        (⟨((a : K) : G), a.property⟩ : V) (⟨((b : K) : G), b.property⟩ : V))
    · intro a ha
      exact Subtype.ext (hV.2 a ha)
  have hcardW : Nat.card W = Nat.card V :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVK).toEquiv
  have hne : V ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcard
    omega
  refine ⟨Subgroup.comap_mono Subgroup.le_normalizer, ?_, hW, hcardW,
    hcardW.symm ▸ hcard, elementary_ambient_hull_internal_generation V hV hne B hB⟩
  exact Subgroup.normal_subgroupOf_of_le_normalizer (Subgroup.le_normalizer_comap K.subtype)

theorem normalizer_elementary_ambient_hull_native_recognition
    (V : Subgroup G)
    (hV : IsElemAbelian 2 V) (hcard : 4 ≤ Nat.card V)
    (hB : fusionStronglyEmbedded ((Subgroup.normalizer (V : Set G)).subgroupOf
      (Subgroup.normalClosure (V : Set G)))) :
    let K := Subgroup.normalClosure (V : Set G)
    IsQuasisimple K ∧ Subgroup.center K = oddCore K ∧
      Odd (Nat.card (Subgroup.center K)) ∧ fusionIsBenderGroup (K ⧸ Subgroup.center K) := by
  obtain ⟨hWB, hnormal, hW, _, hcardW, hgen⟩ :=
    normalizer_elementary_ambient_hull_datum V hV hcard hB
  exact normal_elementary_hull_native_recognition
    ((Subgroup.normalizer (V : Set G)).subgroupOf (Subgroup.normalClosure (V : Set G)))
    (V.subgroupOf (Subgroup.normalClosure (V : Set G))) hB hWB hnormal hW hcardW hgen

theorem central_involution_quotient_hull_native_recognition
    (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hU : U ≠ ⊥) (hUel : IsElemAbelian 2 U)
    (hcard : 4 ≤ Nat.card U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G))
    (hTI : fusionIsTI U) (hnormal : ¬ U.Normal) (x : Subgroup.center G)
    (hB : fusionStronglyEmbedded
      ((Subgroup.normalizer
        (U.map (QuotientGroup.mk' (centralLiftKernel x)) : Set (G ⧸ centralLiftKernel x))).subgroupOf
        (Subgroup.normalClosure
          (U.map (QuotientGroup.mk' (centralLiftKernel x)) : Set (G ⧸ centralLiftKernel x))))) :
    let L := Subgroup.normalClosure (U : Set G)
    let K := L.map (QuotientGroup.mk' (centralLiftKernel x))
    IsQuasisimple K ∧ Subgroup.center K = oddCore K ∧
      Odd (Nat.card (Subgroup.center K)) ∧ fusionIsBenderGroup (K ⧸ Subgroup.center K) := by
  let π := QuotientGroup.mk' (centralLiftKernel x)
  let V := U.map π
  have hV : IsElemAbelian 2 V := CFSG.TwoRankLowerBound.Helpers.isElemAbelian_map U hUel π
  have hcardV : 4 ≤ Nat.card V := by
    have heq : Nat.card U = Nat.card V := Nat.card_congr
      (tiCentralQuotientSubgroupEquiv T U hUT hU hUel hclosed hTI hnormal
        (centralLiftKernel x) (centralLiftKernel_le_center x)).toEquiv
    exact heq ▸ hcard
  have hrec := normalizer_elementary_ambient_hull_native_recognition V hV hcardV hB
  have himage : (Subgroup.normalClosure (U : Set G)).map π =
      Subgroup.normalClosure (V : Set (G ⧸ centralLiftKernel x)) :=
    Subgroup.map_normalClosure (U : Set G) π
    (QuotientGroup.mk'_surjective (centralLiftKernel x))
  dsimp only at hrec
  rw [← himage] at hrec
  exact hrec

end CFSG.ShultStronglyClosedTI
