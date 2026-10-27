module

public import CFSG.RankThree.PartTwo.Sec17.Item1721StepsProofDefs
public import CFSG.RankThree.PartTwo.Sec17.Item171StepsProofComm
import CFSG.RankThree.PartTwo.Sec16.Item16Tail
import CFSG.RankThree.PartTwo.Sec16.Item165ProofTools
import CFSG.RankThree.PartTwo.Sec14.Item147
public import CFSG.RankThree.PartTwo.Sec17.Item1721StepsProofS

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS

namespace Proof1721

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

theorem le_pPrimeCoreOf_of_two {V C : Subgroup G} (hVC : V ≤ C)
    (hCV : C ≤ Subgroup.normalizer (V : Set G)) (hV : IsPGroup 2 V) : V ≤ pPrimeCoreOf 3 C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_pPrimeCoreOf hVC hCV ?_
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hV
  rw [hk]
  exact Nat.Coprime.pow_right k (by norm_num)

theorem pCoreOf_y0_mem_scriptQ (hQ : Step171CommQ) (h : Sec17Std G A c L Y₀) :
    CFSG.Open.pCoreOf 2 Y₀ ∈ scriptQ A (lB A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set O := CFSG.Open.pCoreOf 2 Y₀ with hO
  set M := Subgroup.normalizer (Y₀ : Set G) with hM
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y₀
  have hMO : M ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₀
  have hO3 : ¬ 3 ∣ Nat.card O := by
    intro h3
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hO2
    rw [hk] at h3
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
    omega
  have hAM : A ≤ M := fun a ha => h.normalizer_le (Subgroup.le_normalizer ha)
  refine mem_scriptQ_iff.mpr ⟨(isPiSubgroup_piCompl_iff Nat.prime_three O).mpr hO3,
    hAM.trans hMO, fun B hB => ?_⟩
  set V := O ⊓ Subgroup.centralizer (B : Set G) with hV
  have hV2 : IsPGroup 2 V := hO2.to_le inf_le_left
  by_cases hCB : Subgroup.centralizer (B : Set G) ≤ M
  ·
    refine (le_pPrimeCoreOf_of_two inf_le_right ?_ hV2).trans (le_sup_left.trans le_sup_left)
    exact Late.le_normalizer_inf (hCB.trans hMO) Subgroup.le_normalizer
  ·
    have hcB : c ∉ B := fun hcB => hCB ((Subgroup.centralizer_le
      (Set.singleton_subset_iff.mpr hcB)).trans (HeadProof.centralizer_c_le_M h))
    have hB1 : B ≠ ⊥ := by
      intro hbot
      have h2 := hB.2
      rw [hbot, Subgroup.card_bot, h.isE27.2] at h2
      omega
    obtain ⟨⟨b, hbB⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB1
    have hb1' : b ≠ 1 := fun h1 => hb1 (Subtype.ext h1)
    have hCbB : Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer ({b} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbB)
    have hCb : ¬ Subgroup.centralizer ({b} : Set G) ≤ M := fun h' => hCB (hCbB.trans h')
    have hc3 : IsPGroup 3 (Subgroup.zpowers c) :=
      h.isE27.isPGroup.to_le (Subgroup.zpowers_le.mpr h.c_mem)
    have hcM : c ∈ M := hAM h.c_mem
    have hcCB : c ∈ Subgroup.centralizer (B : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun x hx => h.commute_of_mem (hB.1 hx) h.c_mem
    have hcV : Subgroup.zpowers c ≤ Subgroup.normalizer (V : Set G) :=
      Late.le_normalizer_inf (Subgroup.zpowers_le.mpr (hMO hcM))
        (Subgroup.zpowers_le.mpr (Subgroup.le_normalizer hcCB))
    have hV3 : ¬ 3 ∣ Nat.card V := fun h3 => hO3 (h3.trans (Subgroup.card_dvd_of_le inf_le_left))
    refine HeadProof.le_of_commutator_le Nat.prime_three hc3 hV3 hcV ?_ ?_
    ·
      have hle : ⁅V, Subgroup.zpowers c⁆ ≤
          ⁅O ⊓ Subgroup.centralizer ({b} : Set G), Subgroup.zpowers c⁆ ⊓
            Subgroup.centralizer (B : Set G) := by
        refine le_inf (Subgroup.commutator_mono (inf_le_inf_left _ hCbB) le_rfl) ?_
        exact (Subgroup.le_normalizer_iff_commutator_le_left.mp hcV).trans inf_le_right
      exact hle.trans (hQ G A c L Y₀ h b (hB.1 hbB) hb1' hCb B hB hbB hcB)
    ·
      have hA : A ≤ Subgroup.zpowers c ⊔ B := Proof169.le_zpowers_sup_of_not_mem hB h.c_mem hcB
      have hCA : V ⊓ Subgroup.centralizer ((Subgroup.zpowers c : Subgroup G) : Set G) ≤
          O ⊓ Subgroup.centralizer (A : Set G) := by
        rintro x ⟨⟨hxO, hxB⟩, hxc⟩
        refine ⟨hxO, ?_⟩
        have hsub : Subgroup.zpowers c ⊔ B ≤ Subgroup.centralizer ({x} : Set G) := by
          refine sup_le (fun y hy => ?_) (fun y hy => ?_)
          · exact Subgroup.mem_centralizer_singleton_iff.mpr
              (Subgroup.mem_centralizer_iff.mp hxc y hy)
          · exact Subgroup.mem_centralizer_singleton_iff.mpr
              (Subgroup.mem_centralizer_iff.mp hxB y hy)
        exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
          (Subgroup.mem_centralizer_singleton_iff.mp (hsub (hA hy)))
      refine hCA.trans ((le_pPrimeCoreOf_of_two inf_le_right ?_ (hO2.to_le inf_le_left)).trans
        (le_sup_right.trans le_sup_left))
      exact Late.le_normalizer_inf ((HeadProof.centralizer_le_M h).trans hMO)
        Subgroup.le_normalizer

end Proof1721

open Proof1721 in
theorem claim17O2Y0_of (hQ : Step171CommQ) (h146 : Item146S14) (h166 : Item166S17)
    (h168 : Item168S17) (hbot : Item145BotS17) : Claim17O2Y0 := by
  intro G _ _ A c L Y₀ Y₁ S p P h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hs := h.toSec17Std
  set O := CFSG.Open.pCoreOf 2 Y₀ with hO
  have hOQ : O ∈ scriptQ A (lB A) := pCoreOf_y0_mem_scriptQ hQ hs
  obtain ⟨hSG, -, -, -⟩ := h.item168_at (h166 G A c L Y₀ hs) (hbot G A c L Y₀ hs)
    (h168 G A c L Y₀ hs)
  have hSQ : S ∈ scriptQ A (lB A) := h.mem_qStar_two.prop.1.1
  have hS2 : IsPGroup 2 S := isPGroup_of_mem_scriptQPi Nat.prime_two hSG.prop
  have hSO : S ≤ Subgroup.normalizer (O : Set G) :=
    (hs.qStar_le S hSG).trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₀)
  have hSO2 : IsPGroup 2 (S ⊔ O : Subgroup G) := IsPGroup.to_sup_of_normal_right' hS2
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y₀) hSO
  have hSO3 : ¬ 3 ∣ Nat.card (S ⊔ O : Subgroup G) := by
    intro h3
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hSO2
    rw [hk] at h3
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  have hΔ : S ⊔ O = delta A (lB A) (S ⊔ O) :=
    le_antisymm (sup_le (le_delta hSQ le_sup_left) (le_delta hOQ le_sup_right)) (delta_le _)
  have hAN : A ≤ Subgroup.normalizer ((S ⊔ O : Subgroup G) : Set G) :=
    Sec14.le_normalizer_sup hSQ.1.2.2 hOQ.1.2.2
  have hmem : S ⊔ O ∈ scriptQPi A (lB A) ⊤ (piOf 2) :=
    ⟨⟨Proof165.mem_scriptQ_of_three hs.isE27 (h146 G A c L hs.toSec14Std) hΔ hAN hSO3, le_top⟩,
      (isPiSubgroup_piOf_iff Nat.prime_two _).mpr hSO2⟩
  exact le_sup_right.trans (hSG.2 hmem le_sup_left)

end CFSG.RankThree.PartTwo.Sec17
