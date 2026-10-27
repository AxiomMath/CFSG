module

public import CFSG.GH74.Uniqueness.Bender.Unitary
public import CFSG.GH74.Uniqueness.Bender.Sylow2Basic
public import CFSG.StronglyEmbedded.BenderCentre
import CFSG.Timmesfeld.Bridge.RootStructR2KOneBender

public section

namespace CFSG.LocalAnalysis.WeakClosure81.TimTI

open Subgroup
open CFSG.GH74.Uniqueness.Bender

theorem timti_isPSL2_sup_rootCenter_of_ne {K : Type} [Group K]
    [Finite K] {m : ℕ} (hm : 2 ≤ m) (e : K ≃* CFSG.Theory.Comparator.PSU3Model m)
    {Q Q' : Sylow 2 K} (hne : Q ≠ Q') :
    Nonempty (↥(rootCenter (Q : Subgroup K) ⊔ rootCenter (Q' : Subgroup K)) ≃*
      CFSG.Theory.Comparator.PSL2Model m) := by
  have hBT : BenderType K m 3 ((2 ^ m + 1) / Nat.gcd 3 (2 ^ m + 1)) :=
    BenderType.unitary m hm e
  have hK : CFSG.BenderSuzuki.IsBenderGroup K :=
    CFSG.BenderSuzuki.IsBenderGroup.isPSU3 m hm e
  have hZcard : ∀ P : Sylow 2 K, Nat.card (rootCenter (P : Subgroup K)) = 2 ^ m := fun P => by
    have h := CFSG.StronglyEmbedded.BenderCentre.card_sylowCenter_psu3 (K := K) hm e P
    rw [show CFSG.ComponentClassification.AschbacherToolkit.Bender.sylowCenter (P : Subgroup K) =
        rootCenter (P : Subgroup K) from rfl] at h
    exact h
  have hZne : ∀ P : Sylow 2 K, rootCenter (P : Subgroup K) ≠ ⊥ := fun P => by
    intro hbot
    have h1 : (2 : ℕ) ^ m = 1 := by rw [← hZcard P, hbot, Subgroup.card_bot]
    have h4 : 4 ≤ 2 ^ m := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    omega
  obtain ⟨⟨t, htZ'⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (hZne Q')
  have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  have ht2 : t * t = 1 :=
    CFSG.Timmesfeld.Bridge.RootKOne.mul_self_eq_one_of_mem_rootCenter hBT Q' htZ'
  have htN : t ∉ borel (Q : Subgroup K) := by
    intro htN'
    have htQ : t ∈ (Q : Subgroup K) := mem_sylow_of_mem_normalizer Q ht2 htN'
    have htZ : t ∈ rootCenter (Q : Subgroup K) :=
      CFSG.Timmesfeld.Bridge.RootKOne.mem_rootCenter_of_commute hBT Q htQ ht1' ht2 ht1' ht2
        (Commute.refl t)
    have hE : (Subgroup.zpowers t : Subgroup K) ≠ ⊥ := by
      intro hbot
      have : t ∈ (⊥ : Subgroup K) := hbot ▸ Subgroup.mem_zpowers t
      exact ht1' (Subgroup.mem_bot.mp this)
    have hET : (Subgroup.zpowers t : Subgroup K) ≤ rootCenter (Q : Subgroup K) :=
      Subgroup.zpowers_le.mpr htZ
    have hET' : (Subgroup.zpowers t : Subgroup K) ≤ rootCenter (Q' : Subgroup K) :=
      Subgroup.zpowers_le.mpr htZ'
    exact hne (CFSG.StronglyEmbedded.BenderCentre.sylow_eq_of_le_sylowCenter hK hE hET hET')
  obtain ⟨⟨z, hzZ⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (hZne Q)
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  obtain ⟨-, ⟨φ⟩⟩ := BenderType.lemma_3_2_h_unitary hBT Q ht2 htN hzZ hz1'
  have hBT' : BenderType ↥(rootCenter (Q : Subgroup K) ⊔ Subgroup.zpowers t) m 1 1 :=
    BenderType.linear m hm φ
  obtain ⟨R, htR⟩ := (isPGroup_two_zpowers_of_mul_self_eq_one
      (z := (⟨t, Subgroup.mem_sup_right (Subgroup.mem_zpowers t)⟩ :
        ↥(rootCenter (Q : Subgroup K) ⊔ Subgroup.zpowers t)))
      (Subtype.ext ht2)).exists_le_sylow
  have hRroot : rootCenter (R : Subgroup ↥(rootCenter (Q : Subgroup K) ⊔ Subgroup.zpowers t)) =
      (R : Subgroup ↥(rootCenter (Q : Subgroup K) ⊔ Subgroup.zpowers t)) :=
    CFSG.StronglyEmbedded.BenderCentre.sylowCenter_eq_of_psl2 hm φ R
  have hRinf : (R : Subgroup ↥(rootCenter (Q : Subgroup K) ⊔ Subgroup.zpowers t)) ⊓
      Subgroup.centralizer
        ((R : Subgroup ↥(rootCenter (Q : Subgroup K) ⊔ Subgroup.zpowers t)) : Set
          ↥(rootCenter (Q : Subgroup K) ⊔ Subgroup.zpowers t)) =
      (R : Subgroup ↥(rootCenter (Q : Subgroup K) ⊔ Subgroup.zpowers t)) := hRroot
  have hRc : (R : Subgroup ↥(rootCenter (Q : Subgroup K) ⊔ Subgroup.zpowers t)) ≤
      Subgroup.centralizer
        ((R : Subgroup ↥(rootCenter (Q : Subgroup K) ⊔ Subgroup.zpowers t)) : Set
          ↥(rootCenter (Q : Subgroup K) ⊔ Subgroup.zpowers t)) := by
    have h2 : (R : Subgroup ↥(rootCenter (Q : Subgroup K) ⊔ Subgroup.zpowers t)) ⊓
        Subgroup.centralizer
          ((R : Subgroup ↥(rootCenter (Q : Subgroup K) ⊔ Subgroup.zpowers t)) : Set
            ↥(rootCenter (Q : Subgroup K) ⊔ Subgroup.zpowers t)) ≤
        Subgroup.centralizer
          ((R : Subgroup ↥(rootCenter (Q : Subgroup K) ⊔ Subgroup.zpowers t)) : Set
            ↥(rootCenter (Q : Subgroup K) ⊔ Subgroup.zpowers t)) := inf_le_right
    rwa [hRinf] at h2
  have hRsq : ∀ v ∈ (R : Subgroup ↥(rootCenter (Q : Subgroup K) ⊔ Subgroup.zpowers t)),
      v * v = 1 := fun v hv =>
    CFSG.Timmesfeld.Bridge.RootKOne.mul_self_eq_one_of_mem_rootCenter hBT' R
      (hRroot.symm ▸ hv)
  have hRmap : (R : Subgroup ↥(rootCenter (Q : Subgroup K) ⊔ Subgroup.zpowers t)).map
      (Subgroup.subtype (rootCenter (Q : Subgroup K) ⊔ Subgroup.zpowers t)) ≤
      rootCenter (Q' : Subgroup K) := by
    intro v hv
    obtain ⟨v₀, hv₀R, rfl⟩ := Subgroup.mem_map.mp hv
    have hv₀sq : (v₀ : K) * (v₀ : K) = 1 := congrArg Subtype.val (hRsq v₀ hv₀R)
    have htL : (⟨t, Subgroup.mem_sup_right (Subgroup.mem_zpowers t)⟩ :
        ↥(rootCenter (Q : Subgroup K) ⊔ Subgroup.zpowers t)) ∈
        (R : Subgroup ↥(rootCenter (Q : Subgroup K) ⊔ Subgroup.zpowers t)) :=
      htR (Subgroup.mem_zpowers _)
    have hcomm : Commute t (v₀ : K) := by
      have h1 := Subgroup.mem_centralizer_iff.mp (hRc hv₀R)
        (⟨t, Subgroup.mem_sup_right (Subgroup.mem_zpowers t)⟩ :
          ↥(rootCenter (Q : Subgroup K) ⊔ Subgroup.zpowers t)) htL
      exact congrArg Subtype.val h1
    by_cases hv₀1 : (v₀ : K) = 1
    · change (v₀ : K) ∈ rootCenter (Q' : Subgroup K)
      rw [hv₀1]
      exact (rootCenter (Q' : Subgroup K)).one_mem
    · exact CFSG.Timmesfeld.Bridge.RootKOne.mem_rootCenter_of_commute hBT Q'
        (rootCenter_le (Q' : Subgroup K) htZ') ht1' ht2 hv₀1 hv₀sq hcomm
  have hRcard : Nat.card (R : Subgroup ↥(rootCenter (Q : Subgroup K) ⊔ Subgroup.zpowers t)) =
      2 ^ m := by
    obtain ⟨tR, hcR⟩ := hBT'.exists_benderCore R
    rw [← hRroot]
    exact hcR.card_center
  have hRmap_card : Nat.card ((R : Subgroup
      ↥(rootCenter (Q : Subgroup K) ⊔ Subgroup.zpowers t)).map
        (Subgroup.subtype (rootCenter (Q : Subgroup K) ⊔ Subgroup.zpowers t))) = 2 ^ m := by
    rw [Subgroup.card_map_of_injective
      (Subgroup.subtype_injective (rootCenter (Q : Subgroup K) ⊔ Subgroup.zpowers t)), hRcard]
  have hQ'card : Nat.card (rootCenter (Q' : Subgroup K)) = 2 ^ m := hZcard Q'
  have hReq : (R : Subgroup ↥(rootCenter (Q : Subgroup K) ⊔ Subgroup.zpowers t)).map
      (Subgroup.subtype (rootCenter (Q : Subgroup K) ⊔ Subgroup.zpowers t)) =
      rootCenter (Q' : Subgroup K) :=
    Subgroup.eq_of_le_of_card_ge hRmap
      (le_of_eq (by rw [hQ'card, hRmap_card]))
  refine ⟨(MulEquiv.subgroupCongr ?_).trans φ⟩
  refine le_antisymm (sup_le le_sup_left ?_) (sup_le le_sup_left ?_)
  · rw [← hReq]
    exact Subgroup.map_subtype_le _
  · exact Subgroup.zpowers_le.mpr (Subgroup.mem_sup_right htZ')

end CFSG.LocalAnalysis.WeakClosure81.TimTI
