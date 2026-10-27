module

public import CFSG.RankThree.PartTwo.Sec16.Item168Proof
import CFSG.Goldschmidt.Steps.G310Basic

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec16
  CFSG.RankThree.PartTwo.Late CFSG.RankThree.LocalRank CFSG.GH74.GLS

namespace Proof168Res7

open Sec16.Proof165

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

theorem isCharacteristicP_inf_normalizer {X R : Subgroup G} (hX : IsCharacteristicP 2 ↥X)
    (hRX : R ≤ X) (hR : IsPGroup 2 R) :
    IsCharacteristicP 2 ↥(X ⊓ Subgroup.normalizer (R : Set G)) := by
  have h1 : CFSG.QuasithinUnique.CharTwo X := by
    rw [CFSG.QuasithinUnique.charTwo_iff_internal]
    unfold IsCharacteristicP at hX
    assumption
  have h2 := h1.inf_normalizer hRX hR
  rw [CFSG.QuasithinUnique.charTwo_iff_internal] at h2
  unfold IsCharacteristicP
  assumption

theorem uniq_of_char2 (h : Sec17Std G A c L Y₀)
    (hst : StellmacherKP) (h146 : Item146 A (lB A))
    (h167 : Item167 A (lB A) c L) (n : ℕ) :
    ∀ V ∈ omega168 A (lB A), ∀ Y ∈ scriptY3 A (lB A), V ≤ Y → IsCharacteristicP 2 ↥Y →
      ∀ T : Subgroup G, CFSG.Open.fusionIsSylowIn 2 T Y → A ≤ Subgroup.normalizer (T : Set G) →
      Nat.card G - Nat.card T = n →
      ∀ I₁ ∈ scriptY3Star A (lB A), ∀ I₂ ∈ scriptY3Star A (lB A), Y ≤ I₁ → Y ≤ I₂ →
        I₁ = I₂ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V hV Y hY hVY hYc T hT hAT hn I₁ hI₁ I₂ hI₂ hYI₁ hYI₂
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA : IsE27 A := h.toSec14Std.isE27
  have hYs : Y ∈ scriptYs A (lB A) := hV.2.2 Y hY hVY
  have hY3 : ¬ 3 ∣ Nat.card Y := not_three_dvd_of_mem_scriptY1 hYs.1
  have hYQ : Y ∈ scriptQ A (lB A) := mem_scriptQ_of_three hA h146 hY.2 hY.1.1.2 hY3
  have hT2 : IsPGroup 2 T := hT.2.1
  have hT1 : T ≠ ⊥ := by
    intro hT0
    apply hY.1.2
    have := hT.2.2 (CFSG.Open.pCoreOf 2 Y) (CFSG.LieType.BorelTits.pCoreOf_le 2 Y)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y) (hT0 ▸ bot_le)
    rw [this, hT0]
  obtain ⟨hCT, hC1, hNC, hhost⟩ := stellmacherSub_spec hst h.toTheoremFourHyp hT2 hT1
  set C := stellmacherSub T with hC
  have hYC : Y ≤ Subgroup.normalizer (C : Set G) := hhost Y hT.1 hY3 hT hYc
  have hC2 : IsPGroup 2 C := hT2.to_le hCT
  have hAC : A ≤ Subgroup.normalizer (C : Set G) := hAT.trans hNC
  have hTQ : T ∈ scriptQ A (lB A) := mem_scriptQ_of_le hYQ hT.1 hAT
  have hCQ : C ∈ scriptQ A (lB A) := mem_scriptQ_of_le hTQ hCT hAC
  set D := delta A (lB A) (Subgroup.normalizer (C : Set G)) with hD
  have hD3 : D ∈ scriptY3 A (lB A) :=
    delta_normalizer_mem_scriptY3 h.isSimpleGroup h.nonabelian hC1 hC2 hCQ
  have key : ∀ I ∈ scriptY3Star A (lB A), Y ≤ I →
      I = D ∨ ∀ I' ∈ scriptY3Star A (lB A), D ≤ I' → I' = I := by
    intro I hI hYI
    obtain ⟨-, hI3, hIQ, hIc⟩ := Proof168.facts_of_mem_scriptY3Star h h146 h167 hV hI
      (hVY.trans hYI)
    have hAI : A ≤ Subgroup.normalizer (I : Set G) := hI.prop.1.1.2
    obtain ⟨TI, hTI, hTTI, hATI⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
      Nat.prime_three Nat.prime_two hA.isPGroup hI3 hAI (hT.1.trans hYI) hT2 hAT
    by_cases hTeq : T = TI
    ·
      left
      have hIC : I ≤ Subgroup.normalizer (C : Set G) :=
        hhost I (hT.1.trans hYI) hI3 (hTeq ▸ hTI) hIc
      have hID : I ≤ D := le_delta hIQ hIC
      exact le_antisymm hID (hI.2 hD3 hID)
    ·
      right
      have hTI2 : IsPGroup 2 TI := hTI.2.1
      have hlt : T < TI ⊓ Subgroup.normalizer (T : Set G) :=
        CFSG.Goldschmidt.G310.lt_inf_normalizer hTI2 hTTI hTeq
      set J := I ⊓ Subgroup.normalizer (C : Set G) with hJ
      have hJI : J ≤ I := inf_le_left
      have hJC : J ≤ Subgroup.normalizer (C : Set G) := inf_le_right
      have hYJ : Y ≤ J := le_inf hYI hYC
      have hAJ : A ≤ Subgroup.normalizer (J : Set G) :=
        le_normalizer_inf hAI (hAC.trans Subgroup.le_normalizer)
      have hJQ : J ∈ scriptQ A (lB A) := mem_scriptQ_of_le hIQ hJI hAJ
      have hJD : J ≤ D := le_delta hJQ hJC
      have hCJ : C ≤ J := hCT.trans (hT.1.trans hYJ)
      have hJ3 : J ∈ scriptY3 A (lB A) := by
        refine ⟨⟨⟨fun htop => hI.prop.1.1.1 (top_le_iff.mp (htop ▸ hJI)), hAJ⟩, ?_⟩, ?_⟩
        · intro h0
          have hCO : C ≤ CFSG.Open.pCoreOf 2 J :=
            CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hCJ hJC hC2
          rw [h0] at hCO
          exact hC1 (le_bot_iff.mp hCO)
        · exact le_antisymm (le_delta hJQ le_rfl) (delta_le J)
      have hJ3' : ¬ 3 ∣ Nat.card J := fun h3 => hI3 (h3.trans (Subgroup.card_dvd_of_le hJI))
      have hJc : IsCharacteristicP 2 ↥J :=
        isCharacteristicP_inf_normalizer hIc (hCJ.trans hJI) hC2
      have hNTI : TI ⊓ Subgroup.normalizer (T : Set G) ≤ J :=
        le_inf (inf_le_left.trans hTI.1) (inf_le_right.trans hNC)
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
      exact ih _ hnJ V hV J hJ3 (hVY.trans hYJ) hJc TJ hTJ hATJ rfl I' hI' I hI (hJD.trans hDI')
        hJI
  rcases key I₁ hI₁ hYI₁ with h1 | h1 <;> rcases key I₂ hI₂ hYI₂ with h2 | h2
  · exact h1.trans h2.symm
  · exact h2 I₁ hI₁ h1.ge
  · exact (h1 I₂ hI₂ h2.ge).symm
  · obtain ⟨I, hDI, hI⟩ := Finite.exists_le_maximal (p := (· ∈ scriptY3 A (lB A))) hD3
    exact (h1 I hI hDI).symm.trans (h2 I hI hDI)

theorem uniq (h : Sec17Std G A c L Y₀) (hst : StellmacherKP)
    (h146 : Item146 A (lB A)) (h167 : Item167 A (lB A) c L) :
    ∀ V ∈ omega168 A (lB A), ∀ Y ∈ scriptY3 A (lB A), V ≤ Y →
      ∀ I₁ ∈ scriptY3Star A (lB A), ∀ I₂ ∈ scriptY3Star A (lB A), Y ≤ I₁ → Y ≤ I₂ →
        I₁ = I₂ := by
  intro V hV Y hY hVY I₁ hI₁ I₂ hI₂ hYI₁ hYI₂
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA : IsE27 A := h.toSec14Std.isE27
  have hY3 : ¬ 3 ∣ Nat.card Y := not_three_dvd_of_mem_scriptY1 (hV.2.2 Y hY hVY).1
  have hYQ : Y ∈ scriptQ A (lB A) := mem_scriptQ_of_three hA h146 hY.2 hY.1.1.2 hY3
  set P := CFSG.Open.pCoreOf 2 Y with hP
  have hP2 : IsPGroup 2 P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y
  have hP1 : P ≠ ⊥ := hY.1.2
  have hPY : P ≤ Y := CFSG.LieType.BorelTits.pCoreOf_le 2 Y
  have hYP : Y ≤ Subgroup.normalizer (P : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  have hAP : A ≤ Subgroup.normalizer (P : Set G) :=
    hY.1.1.2.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  have hPQ : P ∈ scriptQ A (lB A) := mem_scriptQ_of_le hYQ hPY hAP
  set D := delta A (lB A) (Subgroup.normalizer (P : Set G)) with hD
  have hD3 : D ∈ scriptY3 A (lB A) :=
    delta_normalizer_mem_scriptY3 h.isSimpleGroup h.nonabelian hP1 hP2 hPQ
  obtain ⟨I, hDI, hI⟩ := Finite.exists_le_maximal (p := (· ∈ scriptY3 A (lB A))) hD3
  have step : ∀ I' ∈ scriptY3Star A (lB A), Y ≤ I' → I' = I := by
    intro I' hI' hYI'
    obtain ⟨-, hI3, hIQ, hIc⟩ := Proof168.facts_of_mem_scriptY3Star h h146 h167 hV hI'
      (hVY.trans hYI')
    have hAI : A ≤ Subgroup.normalizer (I' : Set G) := hI'.prop.1.1.2
    set Y' := I' ⊓ Subgroup.normalizer (P : Set G) with hY'
    have hY'I : Y' ≤ I' := inf_le_left
    have hYY' : Y ≤ Y' := le_inf hYI' hYP
    have hAY' : A ≤ Subgroup.normalizer (Y' : Set G) :=
      le_normalizer_inf hAI (hAP.trans Subgroup.le_normalizer)
    have hY'Q : Y' ∈ scriptQ A (lB A) := mem_scriptQ_of_le hIQ hY'I hAY'
    have hY'D : Y' ≤ D := le_delta hY'Q inf_le_right
    have hPY' : P ≤ Y' := hPY.trans hYY'
    have hY'3 : Y' ∈ scriptY3 A (lB A) := by
      refine ⟨⟨⟨fun htop => hI'.prop.1.1.1 (top_le_iff.mp (htop ▸ hY'I)), hAY'⟩, ?_⟩, ?_⟩
      · intro h0
        have hPO : P ≤ CFSG.Open.pCoreOf 2 Y' :=
          CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hPY' inf_le_right hP2
        rw [h0] at hPO
        exact hP1 (le_bot_iff.mp hPO)
      · exact le_antisymm (le_delta hY'Q le_rfl) (delta_le Y')
    have hY'3' : ¬ 3 ∣ Nat.card Y' := fun h3 => hI3 (h3.trans (Subgroup.card_dvd_of_le hY'I))
    have hY'c : IsCharacteristicP 2 ↥Y' :=
      isCharacteristicP_inf_normalizer hIc (hPY.trans hYI') hP2
    obtain ⟨T, hT, -, hAT⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
      Nat.prime_three Nat.prime_two hA.isPGroup hY'3' hAY' bot_le IsPGroup.of_bot
      (by rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]; exact le_top)
    exact uniq_of_char2 h hst h146 h167 _ V hV Y' hY'3 (hVY.trans hYY') hY'c T hT hAT rfl
      I' hI' I hI hY'I (hY'D.trans hDI)
  exact (step I₁ hI₁ hYI₁).trans (step I₂ hI₂ hYI₂).symm

theorem one168_of_char2 (h : Sec17Std G A c L Y₀)
    (hst : StellmacherKP) (h146 : Item146 A (lB A))
    (h167 : Item167 A (lB A) c L) : One168 A := by
  intro V hV Y hY hVY
  obtain ⟨N, hYN, hN⟩ := Finite.exists_le_maximal (p := (· ∈ scriptY3 A (lB A))) hY
  obtain ⟨hN1, -⟩ := Proof168.facts_of_mem_scriptY3Star h h146 h167 hV hN (hVY.trans hYN)
  refine ⟨N, hN1, fun Y₃ hY₃ hYY₃ => ?_⟩
  obtain ⟨I, hY₃I, hI⟩ := Finite.exists_le_maximal (p := (· ∈ scriptY3 A (lB A))) hY₃
  exact hY₃I.trans (uniq h hst h146 h167 V hV Y hY hVY I hI N hN (hYY₃.trans hY₃I) hYN).le

end Proof168Res7

theorem step168One_of_char2 (hst : StellmacherKP)
    (h146 : Sec14.Item146S14) (h167 : Item167R) : Step168One :=
  fun G _ _ A c L _ hs => Proof168Res7.one168_of_char2 hs hst (h146 G A c L hs.toSec14Std)
    (h167 G A c L hs.toSec15R)

end CFSG.RankThree.PartTwo.Sec17
