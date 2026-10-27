module

public import CFSG.RankThree.PartTwo.Sec16.Item168Proof
import CFSG.Goldschmidt.Steps.G310Basic
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec17.Item17HeadProof

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec16
  CFSG.RankThree.PartTwo.Late CFSG.RankThree.LocalRank CFSG.GH74.GLS

section Statement

variable {G : Type} [Group G] [Finite G]

@[expose] def Two168Out (A Y₀ : Subgroup G) : Prop :=
  ∀ V ∈ omega168 A (lB A), ∀ Y ∈ scriptY3 A (lB A), V ≤ Y →
    ∀ N ∈ scriptY1Star A (lB A), (∀ Y₃ ∈ scriptY3 A (lB A), Y ≤ Y₃ → Y₃ ≤ N) →
      ∀ S ∈ scriptQPiStar A (lB A) N (piOf 2), ∀ Y₁ ∈ scriptY1 A (lB A), S ≤ Y₁ →
        ¬ IsCharacteristicP 2 ↥Y₁ → ¬ Y₁ ≤ Subgroup.normalizer (S : Set G) →
        Y₁ ≤ Subgroup.normalizer (Y₀ : Set G) →
        ¬ CFSG.Open.pCoreOf 2 (Subgroup.normalizer (Y₀ : Set G)) ≤ S →
          ∃ Y' ∈ scriptY3 A (lB A), Y₁ ≤ Y' ∧ ¬ Y' ≤ Subgroup.normalizer (Y₀ : Set G)

end Statement

@[expose] def Step168TwoOut : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → Two168Out A Y₀

namespace Proof168Steps

open Sec16.Proof165 Proof168

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

theorem isCharacteristicP_of_pCoreOf_le (hchar : CFSG.Assembly.IsCharTwoType G)
    {M X : Subgroup G} (hM : CFSG.Assembly.IsTwoLocal M) (hXM : X ≤ M)
    (hOX : CFSG.Open.pCoreOf 2 M ≤ X) : IsCharacteristicP 2 ↥X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : CFSG.Open.pCoreOf 2 M ≤ CFSG.Open.pCoreOf 2 X :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hOX
      (hXM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)
  intro x hx
  have hxG : (x : G) ∈ Subgroup.centralizer (CFSG.Open.pCoreOf 2 X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hx y hy)
  have hxM : (x : G) ∈ CFSG.Open.pCoreOf 2 M :=
    hchar M hM ⟨hXM x.2, Subgroup.centralizer_le h1 hxG⟩
  obtain ⟨y, hy, hyx⟩ := h1 hxM
  have hyx' : y = x := Subtype.ext hyx
  rw [← hyx']
  exact hy

theorem isTwoLocal_M (h : Sec17Std G A c L Y₀) :
    CFSG.Assembly.IsTwoLocal (Subgroup.normalizer (Y₀ : Set G)) := by
  have hmem : Subgroup.normalizer (Y₀ : Set G) ∈
      CFSG.maximalTwoLocalsContaining ((Y₀ ⊔ A : Subgroup G) : Set G) :=
    h.scriptM_eq ▸ Set.mem_singleton _
  obtain ⟨P, hP1, hP2, hP⟩ := hmem.1.1
  exact ⟨P, hP1, hP2, hP⟩

theorem not_le_M_of_mem_omega168 (h : Sec17Std G A c L Y₀) {V : Subgroup G}
    (hV : V ∈ omega168 A (lB A)) : ¬ V ≤ Subgroup.normalizer (Y₀ : Set G) := by
  intro hVM
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨⟨hY₀Y, hY₀3, hY₀Δ, -⟩, hY₀2⟩, -⟩ := h.mem_y0Star
  set Z := Y₀ ⊔ V with hZ
  have hZM : Z ≤ Subgroup.normalizer (Y₀ : Set G) := sup_le Subgroup.le_normalizer hVM
  have hAZ : A ≤ Subgroup.normalizer (Z : Set G) := Sec14.le_normalizer_sup hY₀Y.2 hV.2.1.2
  have hOZ : CFSG.Open.pCoreOf 2 Y₀ ≤ CFSG.Open.pCoreOf 2 Z :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 Y₀).trans le_sup_left)
      (hZM.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₀))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y₀)
  have hVΔ : V ≤ delta A (lB A) V :=
    (le_deltaZero_of_mem_omega168 hV le_rfl).trans (deltaZero_le_delta V)
  have hZ3 : Z ∈ scriptY3 A (lB A) := by
    refine ⟨⟨⟨fun htop => HeadProof.M_ne_top h (top_le_iff.mp (htop ▸ hZM)), hAZ⟩,
      fun h0 => hY₀2.2 (le_bot_iff.mp (h0 ▸ hOZ))⟩, le_antisymm ?_ (delta_le Z)⟩
    refine sup_le ?_ ?_
    · exact hY₀Δ.le.trans (delta_mono le_sup_left)
    · exact hVΔ.trans (delta_mono le_sup_right)
  have hZ1 : oPrimeResidualOf 3 Z = ⊥ := (hV.2.2 Z hZ3 le_sup_right).1.2
  have hY₀1 : Y₀ = ⊥ := by
    rw [hY₀3]
    exact le_bot_iff.mp (hZ1 ▸ oPrimeResidualOf_mono' le_sup_left)
  apply hY₀2.2
  rw [eq_bot_iff, ← hY₀1]
  exact CFSG.LieType.BorelTits.pCoreOf_le 2 Y₀

theorem facts_of_mem_scriptY3Star_not_le_M (h : Sec17Std G A c L Y₀)
    (h146 : Item146 A (lB A)) (h166 : Item166 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) (h167 : Item167 A (lB A) c L)
    {I : Subgroup G} (hI : I ∈ scriptY3Star A (lB A))
    (hIM : ¬ I ≤ Subgroup.normalizer (Y₀ : Set G)) :
    I ∈ scriptY1Star A (lB A) ∧ ¬ 3 ∣ Nat.card I ∧ I ∈ scriptQ A (lB A) ∧
      IsCharacteristicP 2 ↥I := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA : IsE27 A := h.toSec14Std.isE27
  obtain ⟨hI1, hIs⟩ := HeadProof.mem_scriptY1_of_not_le_M h h166 hbot hI.prop hIM
  have hI1s : I ∈ scriptY1Star A (lB A) := ⟨hI1, fun Z hZ hIZ => hI.2 hZ.1 hIZ⟩
  have hI3 : ¬ 3 ∣ Nat.card I := not_three_dvd_of_mem_scriptY1 hI1
  have hIQ : I ∈ scriptQ A (lB A) := mem_scriptQ_of_three hA h146 hI.prop.2 hI.prop.1.1.2 hI3
  have hD0 : deltaZero A (lB A) I ≠ ⊥ := by
    intro h0
    obtain ⟨hdelta, -, -⟩ := rank3II_14_5_lB hA hbot hI.prop.1.1.2
    apply hIM
    calc I = delta A (lB A) I := hI.prop.2
      _ = deltaZero A (lB A) I ⊔ (pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊓ I) :=
          hdelta
      _ = pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊓ I := by rw [h0, bot_sup_eq]
      _ ≤ Subgroup.normalizer (Y₀ : Set G) :=
          inf_le_left.trans ((pPrimeCoreOf_le 3 _).trans (HeadProof.centralizer_le_M h))
  have hne : scriptY0 A (lB A) ≠ ∅ := fun h0 =>
    (Set.eq_empty_iff_forall_notMem.mp h0) Y₀ h.mem_y0Star.prop
  obtain ⟨-, hF⟩ := (h167 I hI1s).2.2 hI hIs hD0 (fun h0 => absurd h0 hne)
  have hF' : generalizedFitting ↥I = CFSG.pCore 2 ↥I := by
    rcases hF with hF | ⟨h0, -⟩
    · exact hF
    · exact absurd h0 hne
  exact ⟨hI1s, hI3, hIQ, (isCharacteristicP_iff_generalizedFitting_eq_pCore ↥I 2).mpr hF'⟩

theorem facts_at_N (h : Sec17Std G A c L Y₀) (hst : StellmacherKP)
    (h146 : Item146 A (lB A)) (h167 : Item167 A (lB A) c L) {V Y N S : Subgroup G}
    (hV : V ∈ omega168 A (lB A)) (hY : Y ∈ scriptY3 A (lB A)) (hVY : V ≤ Y)
    (hN : N ∈ scriptY1Star A (lB A)) (hYN : ∀ Y₃ ∈ scriptY3 A (lB A), Y ≤ Y₃ → Y₃ ≤ N)
    (hS : S ∈ scriptQPiStar A (lB A) N (piOf 2)) :
    S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2) ∧
      delta A (lB A) (Subgroup.normalizer (stellmacherSub S : Set G)) = N ∧
      ∀ U : Subgroup G, S ≤ U → ¬ 3 ∣ Nat.card U → CFSG.Open.fusionIsSylowIn 2 S U →
        IsCharacteristicP 2 ↥U → U ≤ Subgroup.normalizer (stellmacherSub S : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
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
  refine ⟨?_, hDN, hhost⟩
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

theorem two168_of (h : Sec17Std G A c L Y₀) (hst : StellmacherKP)
    (h146 : Item146 A (lB A)) (h166 : Item166 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) (h167 : Item167 A (lB A) c L)
    (hOut : Two168Out A Y₀) : Two168 A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro V hV Y hY hVY N hN hYN S hS Y₁ hY₁ hSY₁ hc hYS
  have hA : IsE27 A := h.toSec14Std.isE27
  obtain ⟨hSG, hDN, hhost⟩ := facts_at_N h hst h146 h167 hV hY hVY hN hYN hS
  obtain ⟨Y', hY', hY₁Y', hY'M⟩ : ∃ Y' ∈ scriptY3 A (lB A), Y₁ ≤ Y' ∧
      ¬ Y' ≤ Subgroup.normalizer (Y₀ : Set G) := by
    by_cases hY₁M : Y₁ ≤ Subgroup.normalizer (Y₀ : Set G)
    · by_cases hOS : CFSG.Open.pCoreOf 2 (Subgroup.normalizer (Y₀ : Set G)) ≤ S
      · exact absurd (isCharacteristicP_of_pCoreOf_le h.charTwoType (isTwoLocal_M h) hY₁M
          (hOS.trans hSY₁)) hc
      · exact hOut V hV Y hY hVY N hN hYN S hS Y₁ hY₁ hSY₁ hc hYS hY₁M hOS
    · exact ⟨Y₁, hY₁.1, le_rfl, hY₁M⟩
  obtain ⟨I, hY'I, hI⟩ := Finite.exists_le_maximal (p := (· ∈ scriptY3 A (lB A))) hY'
  have hIM : ¬ I ≤ Subgroup.normalizer (Y₀ : Set G) := fun hle => hY'M (hY'I.trans hle)
  obtain ⟨-, hI3, hIQ, hIc⟩ := facts_of_mem_scriptY3Star_not_le_M h h146 h166 hbot h167 hI hIM
  have hY₁I : Y₁ ≤ I := hY₁Y'.trans hY'I
  have hSI' : S ∈ scriptQPiStar A (lB A) I (piOf 2) :=
    ⟨⟨⟨hSG.prop.1.1, hSY₁.trans hY₁I⟩, hSG.prop.2⟩,
      fun S' hS' hSS' => hSG.2 ⟨⟨hS'.1.1, le_top⟩, hS'.2⟩ hSS'⟩
  have hIsyl := fusionIsSylowIn_of_mem_scriptQPiStar hA hIQ hI3 hSI'
  have hIC := hhost I (hSY₁.trans hY₁I) hI3 hIsyl hIc
  calc Y₁ ≤ I := hY₁I
    _ = delta A (lB A) I := hI.prop.2
    _ ≤ delta A (lB A) (Subgroup.normalizer (stellmacherSub S : Set G)) := delta_mono hIC
    _ = N := hDN

end Proof168Steps

theorem step168Two_of (hst : StellmacherKP)
    (h146 : Item146S14) (h166 : Item166S17) (hbot : Item145BotS17) (h167 : Item167R)
    (hOut : Step168TwoOut) : Step168Two :=
  fun G _ _ A c L Y₀ hs => Proof168Steps.two168_of hs hst (h146 G A c L hs.toSec14Std)
    (h166 G A c L Y₀ hs) (hbot G A c L Y₀ hs) (h167 G A c L hs.toSec15R) (hOut G A c L Y₀ hs)

end CFSG.RankThree.PartTwo.Sec17
