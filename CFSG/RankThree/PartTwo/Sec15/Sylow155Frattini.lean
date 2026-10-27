module

import CFSG.Holt.Witt
import CFSG.RankThree.PartTwo.Sec6.Item65One
import CFSG.RankThree.PartTwo.Sec13.Item138ProofTools
import CFSG.RankThree.PartTwo.Sec14.Item1411StepsProofTools
public import CFSG.RankThree.PartTwo.Sec15.Gagen155W315xFacts
public import CFSG.RankThree.PartTwo.Sec16.Item165ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Sylow155F

theorem le_sup_inf_normalizer {p : ℕ} [Fact p.Prime] {S D H : Subgroup G}
    (hS : CFSG.Open.fusionIsSylowIn p S D) (hDH : D ≤ H)
    (hHD : H ≤ Subgroup.normalizer (D : Set G)) :
    H ≤ D ⊔ (H ⊓ Subgroup.normalizer (S : Set G)) := by
  intro h hh
  obtain ⟨k, hk, hkS⟩ := CFSG.Holt.exists_mem_conj_of_fusionIsSylowIn hS
    (Sec6.fusionIsSylowIn_map_conj hS (hHD hh))
  have hn : k⁻¹ * h ∈ Subgroup.normalizer (S : Set G) := by
    refine Sec13.Item138Proof.mem_normalizer_of_map_le ?_
    rintro _ ⟨s, hs, rfl⟩
    have h1 := (hkS _).mp (Subgroup.mem_map_of_mem (MulAut.conj h).toMonoidHom hs)
    have heq : (MulAut.conj (k⁻¹ * h)).toMonoidHom s =
        k⁻¹ * (MulAut.conj h).toMonoidHom s * k := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [heq]
    exact h1
  have hkh : h = k * (k⁻¹ * h) := by group
  rw [hkh]
  exact Subgroup.mul_mem_sup hk ⟨H.mul_mem (H.inv_mem (hDH hk)) hh, hn⟩

theorem sup_le_normalizer_r {A X K Y M T P : Subgroup G} (hE : End155N A X K Y M T P) :
    P ⊔ X ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) := by
  rw [hE.eq_rq]
  exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) (P ⊔ X)

theorem le_n155_of_le_normalizer {A X K Y M T P V : Subgroup G} (hC : Ctx155 A X K Y M T)
    (hE : End155N A X K Y M T P) (hV : V ∈ scriptQ A (lB A))
    (hVR : V ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G)) : V ≤ n155 A K := by
  have hRchar :
      ((CFSG.Open.pCoreOf 2 Y).subgroupOf (CFSG.Open.pCoreOf 2 Y)).Characteristic := by
    rw [Subgroup.subgroupOf_self]
    infer_instance
  exact (le_delta hV hVR).trans (hE.claim _ hC.isY.1.1.2 le_rfl hRchar)

theorem r_le_u155 {A X K Y M T P : Subgroup G} (hE : End155N A X K Y M T P)
    (hRP : CFSG.Open.pCoreOf 2 Y ≤ P) : CFSG.Open.pCoreOf 2 Y ≤ u155 A M X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPle : P ≤ M ⊓ Subgroup.normalizer (X : Set G) := hE.mem_p.prop.1.2
  have hPX : P ≤ Subgroup.normalizer (X : Set G) := hPle.trans inf_le_right
  have hPΔ : P ≤ delta A (lB A) M := le_delta hE.mem_p.prop.1.1 (hPle.trans inf_le_left)
  have hXR : X ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) :=
    le_sup_right.trans (sup_le_normalizer_r hE)
  have hR2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 Y) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y
  have hRX : CFSG.Open.pCoreOf 2 Y ⊓ X ≤ CFSG.Open.pCoreOf 2 X :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer (r := 2) inf_le_right
      (Late.le_normalizer_inf hXR Subgroup.le_normalizer) (hR2.to_le inf_le_left)
  refine le_inf (hRP.trans hPΔ) fun r hr => ?_
  have hrX : r ∈ Subgroup.normalizer (X : Set G) := hPX (hRP hr)
  refine ⟨hrX, CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X hrX,
    fun x hx => hRX ⟨?_, ?_⟩⟩
  ·
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (hXR hx) r).mp hr)
      (Subgroup.inv_mem _ hr)
  ·
    rw [commutatorElement_def, mul_assoc, mul_assoc]
    refine X.mul_mem hx ?_
    have h1 := (Subgroup.mem_normalizer_iff.mp hrX x⁻¹).mp (X.inv_mem hx)
    simpa only [mul_assoc] using h1

theorem inf_u155_eq {A X K Y M T P : Subgroup G} (hE : End155N A X K Y M T P)
    (hRP : CFSG.Open.pCoreOf 2 Y ≤ P) : P ⊓ u155 A M X = CFSG.Open.pCoreOf 2 Y := by
  have hPX : P ≤ Subgroup.normalizer (X : Set G) := hE.mem_p.prop.1.2.trans inf_le_right
  have hP2 : IsPGroup 2 P := isPGroup_of_mem_scriptQPi Nat.prime_two hE.mem_p.prop
  refine le_antisymm ?_ (le_inf hRP (r_le_u155 hE hRP))
  rw [hE.eq_rq]
  exact (inf_le_inf_left P inf_le_right).trans
    (Proof155Wx.inf_centralizerSection_le_pCoreOf hP2 hPX)

theorem sylow_sup {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (h146 : Item146 A (lB A)) {X K Y M T P V : Subgroup G} (hE : End155N A X K Y M T P)
    (hV : V ∈ scriptQ A (lB A)) (hVle : V ≤ M ⊓ Subgroup.normalizer (X : Set G))
    (hPV : P ≤ Subgroup.normalizer (V : Set G)) :
    P ⊔ V ∈ scriptQ A (lB A) ∧ ¬ 3 ∣ Nat.card ↥(P ⊔ V) ∧
      CFSG.Open.fusionIsSylowIn 2 P (P ⊔ V) := by
  have hP𝓠 : P ∈ scriptQ A (lB A) := hE.mem_p.prop.1.1
  have hPV𝓠 : P ⊔ V ∈ scriptQ A (lB A) := sup_mem_scriptQ_of_item146 h.isE27 h146 hP𝓠 hV hPV
  have hPV3 : ¬ 3 ∣ Nat.card ↥(P ⊔ V) :=
    (isPiSubgroup_piCompl_iff Nat.prime_three (P ⊔ V)).mp hPV𝓠.1.2.1
  have hPVle : P ⊔ V ≤ M ⊓ Subgroup.normalizer (X : Set G) := sup_le hE.mem_p.prop.1.2 hVle
  have hstar : P ∈ scriptQPiStar A (lB A) (P ⊔ V) (piOf 2) := by
    refine ⟨⟨⟨hP𝓠, le_sup_left⟩, hE.mem_p.prop.2⟩, fun S hS hPS => ?_⟩
    exact le_of_eq (hE.mem_p.eq_of_le ⟨⟨hS.1.1, hS.1.2.trans hPVle⟩, hS.2⟩ hPS).symm
  exact ⟨hPV𝓠, hPV3,
    Sec16.Proof165.fusionIsSylowIn_of_mem_scriptQPiStar h.isE27 hPV𝓠 hPV3 hstar⟩

end Sylow155F

end CFSG.RankThree.PartTwo.Sec15
