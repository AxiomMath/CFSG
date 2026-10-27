module

public import CFSG.RankThree.PartTwo.Sec16.Item165ProofTools
public import CFSG.RankThree.PartTwo.Sec16.Item167Proof
import CFSG.Goldschmidt.Steps.G310Basic
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item14Tools

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec16
  CFSG.RankThree.PartTwo.Late CFSG.RankThree.LocalRank CFSG.GH74.GLS

section Steps

variable {G : Type} [Group G] [Finite G]

@[expose] def One168 (A : Subgroup G) : Prop :=
  ∀ V ∈ omega168 A (lB A), ∀ Y ∈ scriptY3 A (lB A), V ≤ Y →
    ∃ N ∈ scriptY1Star A (lB A), ∀ Y₃ ∈ scriptY3 A (lB A), Y ≤ Y₃ → Y₃ ≤ N

@[expose] def Two168 (A : Subgroup G) : Prop :=
  ∀ V ∈ omega168 A (lB A), ∀ Y ∈ scriptY3 A (lB A), V ≤ Y →
    ∀ N ∈ scriptY1Star A (lB A), (∀ Y₃ ∈ scriptY3 A (lB A), Y ≤ Y₃ → Y₃ ≤ N) →
      ∀ S ∈ scriptQPiStar A (lB A) N (piOf 2), ∀ Y₁ ∈ scriptY1 A (lB A), S ≤ Y₁ →
        ¬ IsCharacteristicP 2 ↥Y₁ → ¬ Y₁ ≤ Subgroup.normalizer (S : Set G) → Y₁ ≤ N

end Steps

@[expose] def Step168One : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → One168 A

@[expose] def Step168Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → Two168 A

namespace Proof168

open Sec16.Proof165

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

theorem y0_mem_scriptY3 (h : Sec17Std G A c L Y₀) : Y₀ ∈ scriptY3 A (lB A) := by
  obtain ⟨⟨-, -, hYΔ, -⟩, hY2⟩ := h.mem_y0Star.prop
  exact ⟨hY2, hYΔ⟩

theorem ne_bot_of_mem_omega168 (h : Sec17Std G A c L Y₀) {V : Subgroup G}
    (hV : V ∈ omega168 A (lB A)) : V ≠ ⊥ := by
  rintro rfl
  obtain ⟨⟨-, hY3eq, -, -⟩, hY2⟩ := h.mem_y0Star.prop
  have h0 : oPrimeResidualOf 3 Y₀ = ⊥ := (hV.2.2 Y₀ (y0_mem_scriptY3 h) bot_le).1.2
  exact hY2.2 (le_bot_iff.mp ((CFSG.LieType.BorelTits.pCoreOf_le 2 Y₀).trans
    (hY3eq.trans h0).le))

theorem le_deltaZero_of_mem_omega168 {V Y : Subgroup G} (hV : V ∈ omega168 A (lB A))
    (hVY : V ≤ Y) : V ≤ deltaZero A (lB A) Y := by
  rw [hV.1]
  exact (inSubgroup_oResidual_le_self 2 _).trans (deltaZero_mono hVY)

theorem facts_of_mem_scriptY3Star (h : Sec17Std G A c L Y₀) (h146 : Item146 A (lB A))
    (h167 : Item167 A (lB A) c L) {V I : Subgroup G} (hV : V ∈ omega168 A (lB A))
    (hI : I ∈ scriptY3Star A (lB A)) (hVI : V ≤ I) :
    I ∈ scriptY1Star A (lB A) ∧ ¬ 3 ∣ Nat.card I ∧ I ∈ scriptQ A (lB A) ∧
      IsCharacteristicP 2 ↥I := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA : IsE27 A := h.toSec14Std.isE27
  have hIs : I ∈ scriptYs A (lB A) := hV.2.2 I hI.prop hVI
  have hI1 : I ∈ scriptY1Star A (lB A) := ⟨hIs.1, fun Z hZ hIZ => hI.2 hZ.1 hIZ⟩
  have hI3 : ¬ 3 ∣ Nat.card I := not_three_dvd_of_mem_scriptY1 hIs.1
  have hIQ : I ∈ scriptQ A (lB A) := mem_scriptQ_of_three hA h146 hI.prop.2 hI.prop.1.1.2 hI3
  have hD0 : deltaZero A (lB A) I ≠ ⊥ := fun h0 =>
    ne_bot_of_mem_omega168 h hV (le_bot_iff.mp (h0 ▸ le_deltaZero_of_mem_omega168 hV hVI))
  have hne : scriptY0 A (lB A) ≠ ∅ := fun h0 =>
    (Set.eq_empty_iff_forall_notMem.mp h0) Y₀ h.mem_y0Star.prop
  obtain ⟨-, hF⟩ := (h167 I hI1).2.2 hI hIs.2 hD0 (fun h0 => absurd h0 hne)
  have hF' : generalizedFitting ↥I = CFSG.pCore 2 ↥I := by
    rcases hF with hF | ⟨h0, -⟩
    · exact hF
    · exact absurd h0 hne
  exact ⟨hI1, hI3, hIQ, (isCharacteristicP_iff_generalizedFitting_eq_pCore ↥I 2).mpr hF'⟩

end Proof168

section Item

open Sec16.Proof165 Proof168

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

theorem rank3II_16_8_of (h : Sec17Std G A c L Y₀)
    (hst : StellmacherKP) (h146 : Item146 A (lB A))
    (h167 : Item167 A (lB A) c L) (hOne : One168 A) (hTwo : Two168 A) :
    Item168 A (lB A) c L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro _ V hV Y hY hVY
  obtain ⟨N, hN, hYN⟩ := hOne V hV Y hY hVY
  refine ⟨N, hN, hYN, fun S hS => ?_⟩
  have hA : IsE27 A := h.toSec14Std.isE27
  have hN3 : N ∈ scriptY3 A (lB A) := hN.prop.1
  have hYN' : Y ≤ N := hYN Y hY le_rfl
  have hVN : V ≤ N := hVY.trans hYN'
  have hNmax : N ∈ scriptY3Star A (lB A) :=
    ⟨hN3, fun Z hZ hNZ => hYN Z hZ (hYN'.trans hNZ)⟩
  obtain ⟨-, hN3', hNQ, hNc⟩ := facts_of_mem_scriptY3Star h h146 h167 hV hNmax hVN
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
  obtain ⟨hCS, hC1, hNC, hhost⟩ := stellmacherSub_spec hst h.toTheoremFourHyp hS2 hS1
  set C := stellmacherSub S with hC
  have hNCC : N ≤ Subgroup.normalizer (C : Set G) := hhost N hSsyl.1 hN3' hSsyl hNc
  have hC2 : IsPGroup 2 C := hS2.to_le hCS
  have hAC : A ≤ Subgroup.normalizer (C : Set G) := hAS.trans hNC
  have hCQ : C ∈ scriptQ A (lB A) := mem_scriptQ_of_le hSQ hCS hAC
  have hD3 : delta A (lB A) (Subgroup.normalizer (C : Set G)) ∈ scriptY3 A (lB A) :=
    delta_normalizer_mem_scriptY3 h.isSimpleGroup h.nonabelian hC1 hC2 hCQ
  have hND : N ≤ delta A (lB A) (Subgroup.normalizer (C : Set G)) := le_delta hNQ hNCC
  have hDN : delta A (lB A) (Subgroup.normalizer (C : Set G)) = N :=
    le_antisymm (hYN _ hD3 (hYN'.trans hND)) hND
  have hle : ∀ Y₁ U : Subgroup G, Y₁ = delta A (lB A) Y₁ → Y₁ ≤ U → S ≤ U →
      ¬ 3 ∣ Nat.card U → CFSG.Open.fusionIsSylowIn 2 S U → IsCharacteristicP 2 ↥U → Y₁ ≤ N := by
    intro Y₁ U hY₁ hY₁U hSU hU3 hUsyl hUc
    have hUC := hhost U hSU hU3 hUsyl hUc
    rw [hY₁, ← hDN]
    exact delta_mono (hY₁U.trans hUC)
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
    have hXN : S' ⊓ Subgroup.normalizer (S : Set G) ≤ N := by
      rw [← hDN]
      exact le_delta hXQ (inf_le_right.trans hNC)
    have hXmem : S' ⊓ Subgroup.normalizer (S : Set G) ∈ scriptQPi A (lB A) N (piOf 2) :=
      ⟨⟨hXQ, hXN⟩, (isPiSubgroup_piOf_iff Nat.prime_two _).mpr (hS'2.to_le inf_le_left)⟩
    exact hlt.not_ge (hS.2 hXmem hlt.le)
  refine ⟨hmax, fun Y₁ hY₁ hSY₁ => ?_, hDN ▸ delta_mono hNC, ?_⟩
  ·
    by_cases hc : IsCharacteristicP 2 ↥Y₁
    ·
      have hY₁3 : ¬ 3 ∣ Nat.card Y₁ := not_three_dvd_of_mem_scriptY1 hY₁
      have hY₁Q : Y₁ ∈ scriptQ A (lB A) :=
        mem_scriptQ_of_three hA h146 hY₁.1.2 hY₁.1.1.1.2 hY₁3
      have hSY₁' : S ∈ scriptQPiStar A (lB A) Y₁ (piOf 2) :=
        ⟨⟨⟨hSQ, hSY₁⟩, (isPiSubgroup_piOf_iff Nat.prime_two S).mpr hS2⟩,
          fun S' hS' hSS' => hmax.2 ⟨⟨hS'.1.1, le_top⟩, hS'.2⟩ hSS'⟩
      exact hle Y₁ Y₁ hY₁.1.2 le_rfl hSY₁ hY₁3
        (fusionIsSylowIn_of_mem_scriptQPiStar hA hY₁Q hY₁3 hSY₁') hc
    · by_cases hYS : Y₁ ≤ Subgroup.normalizer (S : Set G)
      ·
        rw [hY₁.1.2, ← hDN]
        exact delta_mono (hYS.trans hNC)
      · exact hTwo V hV Y hY hVY N hN hYN S hS Y₁ hY₁ hSY₁ hc hYS
  ·
    intro w hw
    obtain ⟨hwA, hwS⟩ := Subgroup.mem_inf.mp hw
    set Nw := N.map (MulAut.conj w).toMonoidHom with hNw
    have hNw1 : Nw ∈ scriptY1Star A (lB A) := HeadProof.map_conj_mem_scriptY1Star hwA hN
    have hSw : S.map (MulAut.conj w).toMonoidHom = S := Late.map_conj_eq_of_mem_normalizer hwS
    have hSNw : S ∈ scriptQPiStar A (lB A) Nw (piOf 2) := by
      have := HeadProof.map_conj_mem_scriptQPiStar hwA hS
      rwa [hSw] at this
    have hcard : Nat.card Nw = Nat.card N :=
      Subgroup.card_map_of_injective (MulAut.conj w).injective
    have hNw3 : ¬ 3 ∣ Nat.card Nw := by
      rw [hcard]
      exact hN3'
    have hNwQ : Nw ∈ scriptQ A (lB A) :=
      mem_scriptQ_of_three hA h146 hNw1.prop.1.2 hNw1.prop.1.1.1.2 hNw3
    have hNwsyl : CFSG.Open.fusionIsSylowIn 2 S Nw :=
      fusionIsSylowIn_of_mem_scriptQPiStar hA hNwQ hNw3 hSNw
    have hNwc : IsCharacteristicP 2 ↥Nw :=
      Sec14.isCharacteristicP_of_mulEquiv'
        (N.equivMapOfInjective _ (MulAut.conj w).injective) hNc
    have hNwN : Nw ≤ N := hle Nw Nw hNw1.prop.1.2 le_rfl hNwsyl.1 hNw3 hNwsyl hNwc
    have heq : Nw = N := Subgroup.eq_of_le_of_card_ge hNwN hcard.ge
    exact mem_normalizer_of_map_conj_eq heq

end Item

theorem item168S17_of (hst : StellmacherKP)
    (h146 : Sec14.Item146S14) (h167 : Item167R) (hOne : Step168One) (hTwo : Step168Two) :
    Item168S17 :=
  fun G _ _ A c L Y₀ hs => rank3II_16_8_of hs hst (h146 G A c L hs.toSec14Std)
    (h167 G A c L hs.toSec15R) (hOne G A c L Y₀ hs) (hTwo G A c L Y₀ hs)

end CFSG.RankThree.PartTwo.Sec17
