module

public import CFSG.RankThree.PartTwo.Sec16.Item168Proof
public import CFSG.RankThree.PartTwo.Sec17.RouteWire16
import CFSG.Goldschmidt.Steps.G310Basic
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item14Tools

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec16
  CFSG.RankThree.PartTwo.Late CFSG.RankThree.LocalRank CFSG.GH74.GLS

section Statements

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def Empty168 (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G)
    (L : Subgroup G) : Prop :=
  Sec15R G A c L ∧ scriptY0 A (lB A) = ∅ ∧ scriptY3 A (lB A) = scriptYs A (lB A) ∧
    ∃ n : ℕ, 2 < n ∧ Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 n ∧
      Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L)

@[expose] noncomputable def NotChar168 (A : Subgroup G) : Prop :=
  ∀ V ∈ omega168 A (lB A), ∀ Y ∈ scriptY3 A (lB A), V ≤ Y →
    ∀ N ∈ scriptY1Star A (lB A), (∀ Y₃ ∈ scriptY3 A (lB A), Y ≤ Y₃ → Y₃ ≤ N) →
      ¬ IsCharacteristicP 2 ↥N →
      (deltaZero A (lB A) N = ⊥ ∨
        generalizedFitting ↥N = CFSG.pCore 2 ↥N ⊔ Subgroup.center ↥N) →
      ∀ S ∈ scriptQPiStar A (lB A) N (piOf 2),
        S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2) ∧ (∀ Y₁ ∈ scriptY1 A (lB A), S ≤ Y₁ → Y₁ ≤ N) ∧
          delta A (lB A) (Subgroup.normalizer (S : Set G)) ≤ N ∧
          Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (S : Set G) ≤
            Subgroup.normalizer (N : Set G)

@[expose] noncomputable def TwoE168 (A : Subgroup G) : Prop :=
  ∀ V ∈ omega168 A (lB A), ∀ Y ∈ scriptY3 A (lB A), V ≤ Y →
    ∀ N ∈ scriptY1Star A (lB A), (∀ Y₃ ∈ scriptY3 A (lB A), Y ≤ Y₃ → Y₃ ≤ N) →
      IsCharacteristicP 2 ↥N →
      ∀ S ∈ scriptQPiStar A (lB A) N (piOf 2), ∀ Y₁ ∈ scriptY1 A (lB A), S ≤ Y₁ →
        ¬ IsCharacteristicP 2 ↥Y₁ → ¬ Y₁ ≤ Subgroup.normalizer (S : Set G) →
          ∃ U ∈ scriptY3 A (lB A), Y₁ ≤ U ∧ IsCharacteristicP 2 ↥U

end Statements

@[expose] noncomputable def Step168OneE : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Empty168 G A c L → One168 A

@[expose] noncomputable def Step168NE : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Empty168 G A c L → NotChar168 A

@[expose] noncomputable def Step168TwoE : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Empty168 G A c L → TwoE168 A

namespace Proof168Steps

open Sec16.Proof165 Proof168

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G}

theorem rank3II_16_8_empty_of (h : Empty168 G A c L)
    (hst : StellmacherKP) (h146 : Item146 A (lB A))
    (h167 : Item167 A (lB A) c L) (hOne : One168 A) (hNot : NotChar168 A) (hTwo : TwoE168 A) :
    Item168 A (lB A) c L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hR, h0, h3s, hpre⟩ := h
  intro _ V hV Y hY hVY
  obtain ⟨N, hN, hYN⟩ := hOne V hV Y hY hVY
  refine ⟨N, hN, hYN, fun S hS => ?_⟩
  have hA : IsE27 A := hR.toSec14Std.isE27
  have hN3 : N ∈ scriptY3 A (lB A) := hN.prop.1
  have hYN' : Y ≤ N := hYN Y hY le_rfl
  have hNmax : N ∈ scriptY3Star A (lB A) :=
    ⟨hN3, fun Z hZ hNZ => hYN Z hZ (hYN'.trans hNZ)⟩
  have hNs : Group.IsSolvable ↥N := (h3s ▸ hN3 : N ∈ scriptYs A (lB A)).2
  have hN3' : ¬ 3 ∣ Nat.card N := not_three_dvd_of_mem_scriptY1 hN.prop
  have hNQ : N ∈ scriptQ A (lB A) := mem_scriptQ_of_three hA h146 hN3.2 hN3.1.1.2 hN3'
  by_cases hNc : IsCharacteristicP 2 ↥N
  swap
  ·
    have hcase : deltaZero A (lB A) N = ⊥ ∨
        generalizedFitting ↥N = CFSG.pCore 2 ↥N ⊔ Subgroup.center ↥N := by
      by_cases hD0 : deltaZero A (lB A) N = ⊥
      · exact Or.inl hD0
      · obtain ⟨-, hF⟩ := (h167 N hN).2.2 hNmax hNs hD0 (fun _ => hpre)
        rcases hF with hF | ⟨-, hF⟩
        · exact absurd ((isCharacteristicP_iff_generalizedFitting_eq_pCore ↥N 2).mpr hF) hNc
        · exact Or.inr hF
    exact hNot V hV Y hY hVY N hN hYN hNc hcase S hS
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
  obtain ⟨hCS, hC1, hNC, hhost⟩ := stellmacherSub_spec hst hR.toTheoremFourHyp hS2 hS1
  set C := stellmacherSub S with hC
  have hNCC : N ≤ Subgroup.normalizer (C : Set G) := hhost N hSsyl.1 hN3' hSsyl hNc
  have hC2 : IsPGroup 2 C := hS2.to_le hCS
  have hAC : A ≤ Subgroup.normalizer (C : Set G) := hAS.trans hNC
  have hCQ : C ∈ scriptQ A (lB A) := mem_scriptQ_of_le hSQ hCS hAC
  have hD3 : delta A (lB A) (Subgroup.normalizer (C : Set G)) ∈ scriptY3 A (lB A) :=
    delta_normalizer_mem_scriptY3 hR.isSimpleGroup hR.nonabelian hC1 hC2 hCQ
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
  have hhostU : ∀ Y₁ U : Subgroup G, Y₁ = delta A (lB A) Y₁ → Y₁ ≤ U → S ≤ U →
      U ∈ scriptY3 A (lB A) → IsCharacteristicP 2 ↥U → Y₁ ≤ N := by
    intro Y₁ U hY₁ hY₁U hSU hU hUc
    have hU3 : ¬ 3 ∣ Nat.card U := not_three_dvd_of_mem_scriptY1 (h3s ▸ hU : U ∈ scriptYs A _).1
    have hUQ : U ∈ scriptQ A (lB A) := mem_scriptQ_of_three hA h146 hU.2 hU.1.1.2 hU3
    have hSU' : S ∈ scriptQPiStar A (lB A) U (piOf 2) :=
      ⟨⟨⟨hSQ, hSU⟩, (isPiSubgroup_piOf_iff Nat.prime_two S).mpr hS2⟩,
        fun S' hS' hSS' => hmax.2 ⟨⟨hS'.1.1, le_top⟩, hS'.2⟩ hSS'⟩
    exact hle Y₁ U hY₁ hY₁U hSU hU3 (fusionIsSylowIn_of_mem_scriptQPiStar hA hUQ hU3 hSU') hUc
  refine ⟨hmax, fun Y₁ hY₁ hSY₁ => ?_, hDN ▸ delta_mono hNC, ?_⟩
  ·
    by_cases hc : IsCharacteristicP 2 ↥Y₁
    · exact hhostU Y₁ Y₁ hY₁.1.2 le_rfl hSY₁ hY₁.1 hc
    · by_cases hYS : Y₁ ≤ Subgroup.normalizer (S : Set G)
      · rw [hY₁.1.2, ← hDN]
        exact delta_mono (hYS.trans hNC)
      · obtain ⟨U, hU, hY₁U, hUc⟩ := hTwo V hV Y hY hVY N hN hYN hNc S hS Y₁ hY₁ hSY₁ hc hYS
        exact hhostU Y₁ U hY₁.1.2 hY₁U (hSY₁.trans hY₁U) hU hUc
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

theorem notChar168_of_item168 (h : Empty168 G A c L) (h168 : Item168 A (lB A) c L) :
    NotChar168 A := by
  obtain ⟨-, -, h3s, hpre⟩ := h
  intro V hV Y hY hVY N hN hYN _ _ S hS
  obtain ⟨N', hN', hYN', hS'⟩ := h168 (fun _ => ⟨h3s, hpre⟩) V hV Y hY hVY
  have hNN' : N = N' := le_antisymm (hYN' N hN.prop.1 (hYN Y hY le_rfl))
    (hYN N' hN'.prop.1 (hYN' Y hY le_rfl))
  subst hNN'
  exact hS' S hS

theorem twoE168_of_item168 (h : Empty168 G A c L) (h168 : Item168 A (lB A) c L) :
    TwoE168 A := by
  obtain ⟨-, -, h3s, hpre⟩ := h
  intro V hV Y hY hVY N hN hYN hNc S hS Y₁ hY₁ hSY₁ _ _
  obtain ⟨N', hN', hYN', hS'⟩ := h168 (fun _ => ⟨h3s, hpre⟩) V hV Y hY hVY
  have hNN' : N = N' := le_antisymm (hYN' N hN.prop.1 (hYN Y hY le_rfl))
    (hYN N' hN'.prop.1 (hYN' Y hY le_rfl))
  subst hNN'
  exact ⟨N, hN.prop.1, (hS' S hS).2.1 Y₁ hY₁ hSY₁, hNc⟩

end Proof168Steps

theorem item168REmpty_of (hst : StellmacherKP)
    (h146 : Item146S14) (h167 : Item167R) (hOne : Step168OneE) (hNot : Step168NE)
    (hTwo : Step168TwoE) : Item168REmpty := by
  intro G _ _ A c L hR h0 hpre
  obtain ⟨h3s, hn⟩ := hpre h0
  have hE : Empty168 G A c L := ⟨hR, h0, h3s, hn⟩
  exact Proof168Steps.rank3II_16_8_empty_of hE hst (h146 G A c L hR.toSec14Std)
    (h167 G A c L hR) (hOne G A c L hE) (hNot G A c L hE) (hTwo G A c L hE) hpre

end CFSG.RankThree.PartTwo.Sec17
