module

public import CFSG.RankThree.PartTwo.Sec16.Item168StepsProofEmpty
import CFSG.RankThree.PartTwo.Sec16.Item166Res4ProofHost
import CFSG.RankThree.PartTwo.Sec16.Item16TailMore
import CFSG.Goldschmidt.Steps.G310Basic

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec16
  CFSG.RankThree.PartTwo.Late CFSG.RankThree.LocalRank CFSG.GH74.GLS

section Statement

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def OneZero168 (A : Subgroup G) : Prop :=
  ∀ Y ∈ scriptY3 A (lB A), ∀ T : Subgroup G, CFSG.Open.fusionIsSylowIn 2 T Y →
    A ≤ Subgroup.normalizer (T : Set G) →
    ∀ I₁ ∈ scriptY3Star A (lB A), ∀ I₂ ∈ scriptY3Star A (lB A), Y ≤ I₁ → Y ≤ I₂ →
      CFSG.Open.fusionIsSylowIn 2 T I₁ → deltaZero A (lB A) I₁ = ⊥ → I₁ = I₂

end Statement

@[expose] noncomputable def Step168OneZero : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Empty168 G A c L → OneZero168 A

namespace Proof168Res4

open Sec16.Proof165 Proof168

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G}

theorem mem_scriptY3_of_isPGroup {S N : Subgroup G} (hSQ : S ∈ scriptQ A (lB A))
    (hS2 : IsPGroup 2 S) (hS1 : S ≠ ⊥) (hSN : S ≤ N) (hN : N ∈ scriptY3 A (lB A)) :
    S ∈ scriptY3 A (lB A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨⟨⟨fun htop => hN.1.1.1 (top_le_iff.mp (htop ▸ hSN)), hSQ.1.2.2⟩, fun h0 => hS1 ?_⟩,
    le_antisymm (le_delta hSQ le_rfl) (delta_le S)⟩
  have hle : S ≤ CFSG.Open.pCoreOf 2 S :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_rfl Subgroup.le_normalizer hS2
  rw [h0] at hle
  exact le_bot_iff.mp hle

theorem bot_mem_omega168_of_empty (h : Empty168 G A c L) : (⊥ : Subgroup G) ∈ omega168 A (lB A) :=
  bot_mem_omega168 h.1.isSimpleGroup.toNontrivial fun _ hY => h.2.2.1 ▸ hY

theorem item168_of_one168 (h : Empty168 G A c L) (h146 : Item146 A (lB A)) (hOne : One168 A) :
    Item168 A (lB A) c L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbot := bot_mem_omega168_of_empty h
  obtain ⟨hR, -, -, -⟩ := h
  have hA : IsE27 A := hR.toSec14Std.isE27
  intro _ V hV Y hY hVY
  obtain ⟨N, hN, hYN⟩ := hOne V hV Y hY hVY
  refine ⟨N, hN, hYN, fun S hS => ?_⟩
  have hN3 : N ∈ scriptY3 A (lB A) := hN.prop.1
  have hYN' : Y ≤ N := hYN Y hY le_rfl
  have hNmax : ∀ Y₃ ∈ scriptY3 A (lB A), N ≤ Y₃ → Y₃ ≤ N :=
    fun Z hZ hNZ => hYN Z hZ (hYN'.trans hNZ)
  have hN3' : ¬ 3 ∣ Nat.card N := not_three_dvd_of_mem_scriptY1 hN.prop
  have hNQ : N ∈ scriptQ A (lB A) := mem_scriptQ_of_three hA h146 hN3.2 hN3.1.1.2 hN3'
  have hSsyl : CFSG.Open.fusionIsSylowIn 2 S N :=
    fusionIsSylowIn_of_mem_scriptQPiStar hA hNQ hN3' hS
  have hS2 : IsPGroup 2 S := hSsyl.2.1
  have hAS : A ≤ Subgroup.normalizer (S : Set G) := hS.prop.1.1.1.2.2
  have hSQ : S ∈ scriptQ A (lB A) := hS.prop.1.1
  have hS1 : S ≠ ⊥ := by
    intro hS0
    apply hN3.1.2
    have := hSsyl.2.2 (CFSG.Open.pCoreOf 2 N) (CFSG.LieType.BorelTits.pCoreOf_le 2 N)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N) (hS0 ▸ bot_le)
    rw [this, hS0]
  have hSN : ∀ Y₃ ∈ scriptY3 A (lB A), S ≤ Y₃ → Y₃ ≤ N := by
    intro Y₃ hY₃ hSY₃
    have hS3 := mem_scriptY3_of_isPGroup hSQ hS2 hS1 hSsyl.1 hN3
    obtain ⟨N', hN', hN'Y⟩ := hOne ⊥ hbot S hS3 bot_le
    have hNN' : N ≤ N' := hN'Y N hN3 hSsyl.1
    exact (hN'Y Y₃ hY₃ hSY₃).trans (hNmax N' hN'.prop.1 hNN')
  have hmax : S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2) := by
    refine ⟨⟨⟨hSQ, le_top⟩, (isPiSubgroup_piOf_iff Nat.prime_two S).mpr hS2⟩,
      fun S' hS' hSS' => ?_⟩
    by_contra hS'S
    have hne : S ≠ S' := fun heq => hS'S (heq ▸ le_rfl)
    have hS'2 : IsPGroup 2 S' := isPGroup_of_mem_scriptQPi Nat.prime_two hS'
    have hlt : S < S' ⊓ Subgroup.normalizer (S : Set G) :=
      CFSG.Goldschmidt.G310.lt_inf_normalizer hS'2 hSS' hne
    have hAX : A ≤ Subgroup.normalizer ((S' ⊓ Subgroup.normalizer (S : Set G) :
        Subgroup G) : Set G) :=
      le_normalizer_inf hS'.1.1.1.2.2 (hAS.trans Subgroup.le_normalizer)
    have hXQ : S' ⊓ Subgroup.normalizer (S : Set G) ∈ scriptQ A (lB A) :=
      mem_scriptQ_of_le hS'.1.1 inf_le_left hAX
    have hX3 : S' ⊓ Subgroup.normalizer (S : Set G) ∈ scriptY3 A (lB A) := by
      refine ⟨⟨⟨fun htop => ?_, hAX⟩, fun h0 => hS1 ?_⟩,
        le_antisymm (le_delta hXQ le_rfl) (delta_le _)⟩
      ·
        have : IsSimpleGroup G := hR.isSimpleGroup
        have hNt : Subgroup.normalizer (S : Set G) = ⊤ := top_le_iff.mp (htop ▸ inf_le_right)
        rcases (Subgroup.normalizer_eq_top_iff.mp hNt).eq_bot_or_eq_top with h0 | h1
        · exact hS1 h0
        · exact hN3.1.1.1 (top_le_iff.mp (h1 ▸ hSsyl.1))
      · have hle : S' ⊓ Subgroup.normalizer (S : Set G) ≤
            CFSG.Open.pCoreOf 2 (S' ⊓ Subgroup.normalizer (S : Set G)) :=
          CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_rfl Subgroup.le_normalizer
            (hS'2.to_le inf_le_left)
        rw [h0] at hle
        exact le_bot_iff.mp (hlt.le.trans hle)
    have hXN : S' ⊓ Subgroup.normalizer (S : Set G) ≤ N := hSN _ hX3 hlt.le
    have hXmem : S' ⊓ Subgroup.normalizer (S : Set G) ∈ scriptQPi A (lB A) N (piOf 2) :=
      ⟨⟨hXQ, hXN⟩, (isPiSubgroup_piOf_iff Nat.prime_two _).mpr (hS'2.to_le inf_le_left)⟩
    exact hlt.not_ge (hS.2 hXmem hlt.le)
  refine ⟨hmax, fun Y₁ hY₁ hSY₁ => hSN Y₁ hY₁.1 hSY₁, ?_, ?_⟩
  ·
    exact hSN _ (delta_normalizer_mem_scriptY3 hR.isSimpleGroup hR.nonabelian hS1 hS2 hSQ)
      (le_delta hSQ Subgroup.le_normalizer)
  ·
    intro w hw
    obtain ⟨hwA, hwS⟩ := Subgroup.mem_inf.mp hw
    set Nw := N.map (MulAut.conj w).toMonoidHom with hNw
    have hNw1 : Nw ∈ scriptY1Star A (lB A) := HeadProof.map_conj_mem_scriptY1Star hwA hN
    have hSw : S.map (MulAut.conj w).toMonoidHom = S := Late.map_conj_eq_of_mem_normalizer hwS
    have hSNw : S ≤ Nw := by
      rw [← hSw]
      exact Subgroup.map_mono hSsyl.1
    have hNwN : Nw ≤ N := hSN Nw hNw1.prop.1 hSNw
    have hcard : Nat.card Nw = Nat.card N :=
      Subgroup.card_map_of_injective (MulAut.conj w).injective
    have heq : Nw = N := Subgroup.eq_of_le_of_card_ge hNwN hcard.ge
    exact mem_normalizer_of_map_conj_eq heq

theorem uniq_of_zero (h : Empty168 G A c L) (hst : StellmacherKP)
    (h146 : Item146 A (lB A)) (h167 : Item167 A (lB A) c L) (hZ : OneZero168 A) (n : ℕ) :
    ∀ Y ∈ scriptY3 A (lB A), ∀ T : Subgroup G,
      CFSG.Open.fusionIsSylowIn 2 T Y → A ≤ Subgroup.normalizer (T : Set G) →
      Nat.card G - Nat.card T = n →
      ∀ I₁ ∈ scriptY3Star A (lB A), ∀ I₂ ∈ scriptY3Star A (lB A), Y ≤ I₁ → Y ≤ I₂ →
        I₁ = I₂ := by
  obtain ⟨hR, -, h3s, hpre⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA : IsE27 A := hR.toSec14Std.isE27
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Y hY T hT hAT hn I₁ hI₁ I₂ hI₂ hYI₁ hYI₂
  by_cases hD1 : CFSG.Open.fusionIsSylowIn 2 T I₁ ∧ deltaZero A (lB A) I₁ = ⊥
  · exact hZ Y hY T hT hAT I₁ hI₁ I₂ hI₂ hYI₁ hYI₂ hD1.1 hD1.2
  by_cases hD2 : CFSG.Open.fusionIsSylowIn 2 T I₂ ∧ deltaZero A (lB A) I₂ = ⊥
  · exact (hZ Y hY T hT hAT I₂ hI₂ I₁ hI₁ hYI₂ hYI₁ hD2.1 hD2.2).symm
  have hYs : Y ∈ scriptYs A (lB A) := h3s ▸ hY
  have hY3 : ¬ 3 ∣ Nat.card Y := not_three_dvd_of_mem_scriptY1 hYs.1
  have hYQ : Y ∈ scriptQ A (lB A) := mem_scriptQ_of_three hA h146 hY.2 hY.1.1.2 hY3
  have hT2 : IsPGroup 2 T := hT.2.1
  have hT1 : T ≠ ⊥ := by
    intro hT0
    apply hY.1.2
    have := hT.2.2 (CFSG.Open.pCoreOf 2 Y) (CFSG.LieType.BorelTits.pCoreOf_le 2 Y)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y) (hT0 ▸ bot_le)
    rw [this, hT0]
  obtain ⟨hCT, hC1, hNC, hhost⟩ := stellmacherSub_spec hst hR.toTheoremFourHyp hT2 hT1
  set C := stellmacherSub T with hC
  have hC2 : IsPGroup 2 C := hT2.to_le hCT
  have hAC : A ≤ Subgroup.normalizer (C : Set G) := hAT.trans hNC
  have hTQ : T ∈ scriptQ A (lB A) := mem_scriptQ_of_le hYQ hT.1 hAT
  have hCQ : C ∈ scriptQ A (lB A) := mem_scriptQ_of_le hTQ hCT hAC
  set D := delta A (lB A) (Subgroup.normalizer (C : Set G)) with hD
  have hD3 : D ∈ scriptY3 A (lB A) :=
    delta_normalizer_mem_scriptY3 hR.isSimpleGroup hR.nonabelian hC1 hC2 hCQ
  have key : ∀ I ∈ scriptY3Star A (lB A), Y ≤ I →
      (CFSG.Open.fusionIsSylowIn 2 T I → deltaZero A (lB A) I ≠ ⊥) →
      I = D ∨ ∀ I' ∈ scriptY3Star A (lB A), D ≤ I' → I' = I := by
    intro I hI hYI hDI
    have hIs : I ∈ scriptYs A (lB A) := h3s ▸ hI.prop
    have hI1 : I ∈ scriptY1Star A (lB A) := ⟨hIs.1, fun Z hZ hIZ => hI.2 hZ.1 hIZ⟩
    have hI3 : ¬ 3 ∣ Nat.card I := not_three_dvd_of_mem_scriptY1 hIs.1
    have hIQ : I ∈ scriptQ A (lB A) := mem_scriptQ_of_three hA h146 hI.prop.2 hI.prop.1.1.2 hI3
    have hIhost : CFSG.Open.fusionIsSylowIn 2 T I → I ≤ Subgroup.normalizer (C : Set G) := by
      intro hsyl
      obtain ⟨-, hF⟩ := (h167 I hI1).2.2 hI hIs.2 (hDI hsyl) (fun _ => hpre)
      rcases hF with hF | ⟨-, hF⟩
      · exact hhost I hsyl.1 hI3 hsyl
          ((isCharacteristicP_iff_generalizedFitting_eq_pCore ↥I 2).mpr hF)
      · exact Sec16.Proof166Res4.le_normalizer_stellmacherSub_of_center hst.2 hR.toTheoremFourHyp
          hsyl.1 hI3 hsyl hF
    have hAI : A ≤ Subgroup.normalizer (I : Set G) := hI.prop.1.1.2
    obtain ⟨TI, hTI, hTTI, hATI⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
      Nat.prime_three Nat.prime_two hA.isPGroup hI3 hAI (hT.1.trans hYI) hT2 hAT
    by_cases hTeq : T = TI
    ·
      left
      have hID : I ≤ D := le_delta hIQ (hIhost (hTeq ▸ hTI))
      exact le_antisymm hID (hI.2 hD3 hID)
    ·
      right
      have hTI2 : IsPGroup 2 TI := hTI.2.1
      have hlt : T < TI ⊓ Subgroup.normalizer (T : Set G) :=
        CFSG.Goldschmidt.G310.lt_inf_normalizer hTI2 hTTI hTeq
      set J := I ⊓ Subgroup.normalizer (T : Set G) with hJ
      have hJI : J ≤ I := inf_le_left
      have hJC : J ≤ Subgroup.normalizer (C : Set G) := inf_le_right.trans hNC
      have hAJ : A ≤ Subgroup.normalizer (J : Set G) :=
        le_normalizer_inf hAI (hAT.trans Subgroup.le_normalizer)
      have hJQ : J ∈ scriptQ A (lB A) := mem_scriptQ_of_le hIQ hJI hAJ
      have hJD : J ≤ D := le_delta hJQ hJC
      have hCJ : C ≤ J := le_inf (hCT.trans (hT.1.trans hYI)) (hCT.trans Subgroup.le_normalizer)
      have hJ3 : J ∈ scriptY3 A (lB A) := by
        refine ⟨⟨⟨fun htop => hI.prop.1.1.1 (top_le_iff.mp (htop ▸ hJI)), hAJ⟩, ?_⟩, ?_⟩
        · intro h0
          have hCO : C ≤ CFSG.Open.pCoreOf 2 J :=
            CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hCJ hJC hC2
          rw [h0] at hCO
          exact hC1 (le_bot_iff.mp hCO)
        · exact le_antisymm (le_delta hJQ le_rfl) (delta_le J)
      have hJ3' : ¬ 3 ∣ Nat.card J := fun h3 => hI3 (h3.trans (Subgroup.card_dvd_of_le hJI))
      have hNTI : TI ⊓ Subgroup.normalizer (T : Set G) ≤ J := inf_le_inf_right _ hTI.1
      have hANTI : A ≤ Subgroup.normalizer ((TI ⊓ Subgroup.normalizer (T : Set G) :
          Subgroup G) : Set G) :=
        le_normalizer_inf hATI (hAT.trans Subgroup.le_normalizer)
      obtain ⟨TJ, hTJ, hNTJ, hATJ⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
        Nat.prime_three Nat.prime_two hA.isPGroup hJ3' hAJ hNTI (hTI2.to_le inf_le_left) hANTI
      have hcardlt : Nat.card T < Nat.card TJ :=
        (Subgroup.card_lt_of_lt hlt).trans_le (Subgroup.card_le_of_le hNTJ)
      have hTJG : Nat.card TJ ≤ Nat.card G := Subgroup.card_le_card_group TJ
      have hnJ : Nat.card G - Nat.card TJ < n := by omega
      intro I' hI' hDI'
      exact ih _ hnJ J hJ3 TJ hTJ hATJ rfl I' hI' I hI (hJD.trans hDI') hJI
  rcases key I₁ hI₁ hYI₁ (fun hs h0 => hD1 ⟨hs, h0⟩) with h1 | h1 <;>
    rcases key I₂ hI₂ hYI₂ (fun hs h0 => hD2 ⟨hs, h0⟩) with h2 | h2
  · exact h1.trans h2.symm
  · exact h2 I₁ hI₁ h1.ge
  · exact (h1 I₂ hI₂ h2.ge).symm
  · obtain ⟨I, hDI, hI⟩ := Finite.exists_le_maximal (p := (· ∈ scriptY3 A (lB A))) hD3
    exact (h1 I hI hDI).symm.trans (h2 I hI hDI)

theorem one168_of_zero (h : Empty168 G A c L) (hst : StellmacherKP)
    (h146 : Item146 A (lB A)) (h167 : Item167 A (lB A) c L) (hZ : OneZero168 A) : One168 A := by
  intro V hV Y hY hVY
  have hA : IsE27 A := h.1.toSec14Std.isE27
  have h3s := h.2.2.1
  have hY3 : ¬ 3 ∣ Nat.card Y := not_three_dvd_of_mem_scriptY1 (h3s ▸ hY : Y ∈ scriptYs A _).1
  obtain ⟨T, hT, -, hAT⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    Nat.prime_three Nat.prime_two hA.isPGroup hY3 hY.1.1.2 bot_le IsPGroup.of_bot
    (by rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]; exact le_top)
  obtain ⟨N, hYN, hN⟩ := Finite.exists_le_maximal (p := (· ∈ scriptY3 A (lB A))) hY
  have hN1 : N ∈ scriptY1Star A (lB A) :=
    ⟨(h3s ▸ hN.prop : N ∈ scriptYs A _).1, fun Z hZ hNZ => hN.2 hZ.1 hNZ⟩
  refine ⟨N, hN1, fun Y₃ hY₃ hYY₃ => ?_⟩
  obtain ⟨I, hY₃I, hI⟩ := Finite.exists_le_maximal (p := (· ∈ scriptY3 A (lB A))) hY₃
  have := uniq_of_zero h hst h146 h167 hZ _ Y hY T hT hAT rfl I hI N hN (hYY₃.trans hY₃I) hYN
  exact hY₃I.trans this.le

end Proof168Res4

theorem step168OneE_of_zero (hst : StellmacherKP)
    (h146 : Item146S14) (h167 : Item167R) (hZ : Step168OneZero) : Step168OneE :=
  fun G _ _ A c L hE => Proof168Res4.one168_of_zero hE hst (h146 G A c L hE.1.toSec14Std)
    (h167 G A c L hE.1) (hZ G A c L hE)

theorem step168NE_of_oneE (h146 : Item146S14) (hOne : Step168OneE) : Step168NE :=
  fun G _ _ A c L hE => Proof168Steps.notChar168_of_item168 hE
    (Proof168Res4.item168_of_one168 hE (h146 G A c L hE.1.toSec14Std) (hOne G A c L hE))

theorem step168TwoE_of_oneE (h146 : Item146S14) (hOne : Step168OneE) : Step168TwoE :=
  fun G _ _ A c L hE => Proof168Steps.twoE168_of_item168 hE
    (Proof168Res4.item168_of_one168 hE (h146 G A c L hE.1.toSec14Std) (hOne G A c L hE))

end CFSG.RankThree.PartTwo.Sec17
