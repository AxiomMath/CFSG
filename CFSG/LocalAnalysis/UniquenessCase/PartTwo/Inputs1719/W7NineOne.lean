module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W7NineOneFourHolds
public import CFSG.LocalAnalysis.RankThreeUC.SourceSetting.TwoGroupNormalizerMaxLocal.TwoGroupNormalizerMaxLocal
public import CFSG.Goldschmidt75.Closure
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09R912A5
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.RankThreeUC.SourceSetting.TwoGroupNormalizerMaxLocal
  (normalizer_le_of_maxTwoLocalsContaining_eq_singleton)

variable {G : Type} [Group G] [Finite G]

theorem calCGS_le_of_uniqueMax {R Z M : Subgroup G} (hR2 : IsPGroup 2 R)
    (hZ : Z ≤ normalizer (R : Set G)) (hZM : calMOf Z = {M}) :
    CFSG.LocalAnalysis.UniquenessCase.UC6.calCGS R ≤ M := by
  refine iSup_le fun C => iSup_le fun hC1 => iSup_le fun hCR => iSup_le fun hchar => ?_
  exact normalizer_le_of_maxTwoLocalsContaining_eq_singleton
    hC1 (hR2.to_le hCR) (hZ.trans (F09.normalizer_le_normalizer_of_char hCR hchar)) hZM

theorem w7_9_1_5 {M I X Y H P : Subgroup G} (hIM : I ≤ M) (hIn : (I.subgroupOf M).Normal)
    (hXM : X ≤ M)
    (heta : ∀ R : Subgroup G, R ≤ M → IsPGroup 2 R → X ≤ normalizer (R : Set G) →
      pCoreOf 2 I ≤ R → calMOf (M ⊓ normalizer (R : Set G)) = {M})
    (hYM : Y ≤ M) (hY : Y = X ⊔ pCoreOf 2 Y) (hYne : pCoreOf 2 Y ≠ ⊥)
    (hmax : ∀ Z : Subgroup G, Z ≤ M → Z = X ⊔ pCoreOf 2 Z → pCoreOf 2 Z ≠ ⊥ →
      calMOf Z ≠ {M} → Y ≤ Z → Z = Y)
    (hYH : Y ≤ H) (hSP : pCoreOf 2 (H ⊓ M) ≤ P) (hPM : P ≤ M) (hP2 : IsPGroup 2 P)
    (hYP : Y ≤ normalizer (P : Set G)) :
    CFSG.LocalAnalysis.UniquenessCase.UC6.calCGS P ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXY : X ≤ Y := le_sup_left.trans hY.ge
  have hMO : M ≤ normalizer (pCoreOf 2 I : Set G) :=
    (le_normalizer_of_normal_subgroupOf hIM).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 I)
  have hO2 : IsPGroup 2 (pCoreOf 2 I) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 I
  by_cases hOP : pCoreOf 2 I ≤ P
  · exact calCGS_le_of_uniqueMax hP2 inf_le_right (heta P hPM hP2 (hXY.trans hYP) hOP)
  · obtain ⟨W, hWdef⟩ : ∃ W : Subgroup G, W = pCoreOf 2 I ⊓ normalizer (P : Set G) :=
      ⟨_, rfl⟩
    have hQ2 : IsPGroup 2 ↥(pCoreOf 2 I ⊔ P) :=
      IsPGroup.to_sup_of_normal_left' hO2 hP2 (hPM.trans hMO)
    have hlt : P < pCoreOf 2 I ⊔ P :=
      lt_of_le_of_ne le_sup_right (fun h => hOP (h ▸ le_sup_left))
    obtain ⟨q, hq, hqP⟩ := SetLike.exists_of_lt (CFSG.Goldschmidt75.lt_inf_normalizer hQ2 hlt)
    have hqmem : q ∈ ((pCoreOf 2 I ⊔ P : Subgroup G) : Set G) := hq.1
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ (hPM.trans hMO)] at hqmem
    obtain ⟨a, ha, b, hb, rfl⟩ := hqmem
    have hbN : b ∈ normalizer (P : Set G) := le_normalizer hb
    have haN : a ∈ normalizer (P : Set G) := by
      have := (normalizer (P : Set G)).mul_mem hq.2 ((normalizer (P : Set G)).inv_mem hbN)
      simpa using this
    have haP : a ∉ P := fun haP => hqP (P.mul_mem haP hb)
    have hWY : ¬ W ≤ Y := by
      intro hle
      apply haP
      apply hSP
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (N := pCoreOf 2 I ⊓ H)
        (le_inf inf_le_right
          (inf_le_left.trans ((CFSG.LieType.BorelTits.pCoreOf_le 2 I).trans hIM)))
        ((le_inf (inf_le_right.trans hMO) (inf_le_left.trans le_normalizer)).trans
          inf_normalizer_le_normalizer_inf)
        (hO2.to_le inf_le_left) ⟨ha, hYH (hle (hWdef ▸ ⟨ha, haN⟩))⟩
    have hWnorm : Y ≤ normalizer (W : Set G) := by
      rw [hWdef]
      exact (le_inf (hYM.trans hMO) (hYP.trans le_normalizer)).trans
        inf_normalizer_le_normalizer_inf
    have hW2 : IsPGroup 2 W := hWdef ▸ hO2.to_le inf_le_left
    have hWM : W ≤ M :=
      hWdef ▸ inf_le_left.trans ((CFSG.LieType.BorelTits.pCoreOf_le 2 I).trans hIM)
    have hWP : W ≤ normalizer (P : Set G) := hWdef ▸ inf_le_right
    have hR2 : IsPGroup 2 (pCoreOf 2 Y) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y
    have hRW2 : IsPGroup 2 ↥(W ⊔ pCoreOf 2 Y) :=
      IsPGroup.to_sup_of_normal_left' hW2 hR2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 Y).trans hWnorm)
    have hZnorm : Y ⊔ W ≤ normalizer ((W ⊔ pCoreOf 2 Y : Subgroup G) : Set G) := by
      refine sup_le ((le_inf hWnorm (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)).trans
        (inf_normalizer_le_normalizer_sup _ _)) (le_sup_left.trans le_normalizer)
    have hRWZ : W ⊔ pCoreOf 2 Y ≤ pCoreOf 2 (Y ⊔ W) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        (sup_le le_sup_right ((CFSG.LieType.BorelTits.pCoreOf_le 2 Y).trans le_sup_left))
        hZnorm hRW2
    have hZM : Y ⊔ W ≤ M := sup_le hYM hWM
    have hZeq : Y ⊔ W = X ⊔ pCoreOf 2 (Y ⊔ W) := by
      apply le_antisymm
      · refine sup_le (hY.le.trans (sup_le le_sup_left ?_)) ?_
        · exact (le_sup_right.trans hRWZ).trans le_sup_right
        · exact (le_sup_left.trans hRWZ).trans le_sup_right
      · exact sup_le (hXY.trans le_sup_left) (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
    have hZne : pCoreOf 2 (Y ⊔ W) ≠ ⊥ := fun h =>
      hYne (le_bot_iff.mp (h ▸ (le_sup_right.trans hRWZ)))
    have hZcal : calMOf (Y ⊔ W) = {M} := by
      by_contra hne
      have := hmax (Y ⊔ W) hZM hZeq hZne hne le_sup_left
      exact hWY (le_sup_right.trans this.le)
    exact calCGS_le_of_uniqueMax hP2 (sup_le hYP hWP) hZcal

theorem w7_9_1_3 (hct : CFSG.Open.IsCharTwoType G) {M I X Y H : Subgroup G} (hIM : I ≤ M)
    (hIn : (I.subgroupOf M).Normal) (hXM : X ≤ M)
    (heta : ∀ R : Subgroup G, R ≤ M → IsPGroup 2 R → X ≤ normalizer (R : Set G) →
      pCoreOf 2 I ≤ R → calMOf (M ⊓ normalizer (R : Set G)) = {M})
    (hYM : Y ≤ M) (hY : Y = X ⊔ pCoreOf 2 Y) (hYne : pCoreOf 2 Y ≠ ⊥)
    (hmax : ∀ Z : Subgroup G, Z ≤ M → Z = X ⊔ pCoreOf 2 Z → pCoreOf 2 Z ≠ ⊥ →
      calMOf Z ≠ {M} → Y ≤ Z → Z = Y)
    (hYH : Y ≤ H) (hHM : ¬ H ≤ M) (hHne : pCoreOf 2 H ≠ ⊥) :
    CFSG.QuasithinUnique.CharTwo H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : Subgroup G, N₁ = normalizer (pCoreOf 2 H : Set G) := ⟨_, rfl⟩
  have hHN : H ≤ N₁ := hN₁ ▸ CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hloc : IsTwoLocal N₁ :=
    ⟨pCoreOf 2 H, hHne, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H, hN₁⟩
  have hleN : pCoreOf 2 H ≤ pCoreOf 2 N₁ :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 H).trans hHN) hN₁.le
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)
  have hN₁ne : pCoreOf 2 N₁ ≠ ⊥ := fun h => hHne (le_bot_iff.mp (h ▸ hleN))
  have hle : pCoreOf 2 N₁ ≤ pCoreOf 2 Y :=
    w7_9_1_4_le_pCore hYM hY hYne
      (w7_9_1_4_normalizer_pCore_le hIM hIn hXM heta hYM hY hYne hmax) hmax (hYH.trans hHN)
      (fun h => hHM (hHN.trans h)) hN₁ne (CFSG.LieType.BorelTits.pCoreOf_le 2 N₁)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N₁)
      ((hYH.trans hHN).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N₁))
  have hle2 : pCoreOf 2 N₁ ≤ pCoreOf 2 H :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (hle.trans ((CFSG.LieType.BorelTits.pCoreOf_le 2 Y).trans hYH))
      (hHN.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N₁))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N₁)
  have hchar := hct N₁ hloc
  rw [le_antisymm hle2 hleN] at hchar
  intro x hx
  exact hchar ⟨hHN hx.1, hx.2⟩

theorem w7_asc81bHyp (hct : CFSG.Open.IsCharTwoType G) {M I X Y H : Subgroup G} (hIM : I ≤ M)
    (hIn : (I.subgroupOf M).Normal) (hXM : X ≤ M)
    (heta : ∀ R : Subgroup G, R ≤ M → IsPGroup 2 R → X ≤ normalizer (R : Set G) →
      pCoreOf 2 I ≤ R → calMOf (M ⊓ normalizer (R : Set G)) = {M})
    (hYM : Y ≤ M) (hY : Y = X ⊔ pCoreOf 2 Y) (hYne : pCoreOf 2 Y ≠ ⊥)
    (hmax : ∀ Z : Subgroup G, Z ≤ M → Z = X ⊔ pCoreOf 2 Z → pCoreOf 2 Z ≠ ⊥ →
      calMOf Z ≠ {M} → Y ≤ Z → Z = Y)
    (hYH : Y ≤ H) (hHM : ¬ H ≤ M) (hHne : pCoreOf 2 H ≠ ⊥) :
    CFSG.AGLEmbedding.Asc81bHyp H (pCoreOf 2 (H ⊓ M)) ∧
      H ⊓ normalizer (pCoreOf 2 (H ⊓ M) : Set G) = H ⊓ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hSdef⟩ : ∃ S : Subgroup G, S = pCoreOf 2 (H ⊓ M) := ⟨_, rfl⟩
  rw [← hSdef]
  have hS2 : IsPGroup 2 S := hSdef ▸ CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hSHM : S ≤ H ⊓ M := hSdef ▸ CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hHMS : H ⊓ M ≤ normalizer (S : Set G) :=
    hSdef ▸ CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hO2Y : pCoreOf 2 H ≤ pCoreOf 2 Y :=
    w7_9_1_4_le_pCore hYM hY hYne
      (w7_9_1_4_normalizer_pCore_le hIM hIn hXM heta hYM hY hYne hmax) hmax hYH hHM hHne
      (CFSG.LieType.BorelTits.pCoreOf_le 2 H) (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)
      (hYH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
  have hO2S : pCoreOf 2 H ≤ S := hSdef ▸ CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
      (hO2Y.trans ((CFSG.LieType.BorelTits.pCoreOf_le 2 Y).trans hYM)))
    (inf_le_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)
  have hS1 : S ≠ ⊥ := fun h => hHne (le_bot_iff.mp (h ▸ hO2S))
  have hcal : CFSG.LocalAnalysis.UniquenessCase.UC6.calCGS S ≤ M :=
    w7_9_1_5 hIM hIn hXM heta hYM hY hYne hmax hYH hSdef.ge (hSHM.trans inf_le_right) hS2
      ((le_inf hYH hYM).trans hHMS)
  have hNC : ∀ C : Subgroup G, C ≤ S → C ≠ ⊥ → (C.subgroupOf S).Characteristic →
      normalizer (C : Set G) ≤ M := fun C hCS hC1 hCc =>
    (le_iSup_of_le C (le_iSup_of_le hC1 (le_iSup_of_le hCS
      (le_iSup (fun _ => normalizer (C : Set G)) hCc)))).trans hcal
  have hNS : normalizer (S : Set G) ≤ M :=
    hNC S le_rfl hS1 (by rw [Subgroup.subgroupOf_self]; infer_instance)
  have hinf : H ⊓ normalizer (S : Set G) = H ⊓ M :=
    le_antisymm (le_inf inf_le_left (inf_le_right.trans hNS)) (le_inf inf_le_left hHMS)
  refine ⟨⟨⟨hSHM.trans inf_le_left, hS1, ?_⟩,
    w7_9_1_3 hct hIM hIn hXM heta hYM hY hYne hmax hYH hHM hHne, ?_⟩, hinf⟩
  · rw [hinf, hSdef]
  · refine le_antisymm (iSup_le fun C => iSup_le fun hCS => iSup_le fun hC1 => iSup_le fun hCc =>
      (le_inf inf_le_left (inf_le_right.trans (hNC C hCS hC1 hCc))).trans
        (le_inf inf_le_left hHMS)) ?_
    have hSc : (S.subgroupOf S).Characteristic := by
      rw [Subgroup.subgroupOf_self]; infer_instance
    exact le_iSup_of_le S (le_iSup_of_le le_rfl (le_iSup_of_le hS1
      (le_iSup (fun _ => H ⊓ normalizer (S : Set G)) hSc)))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
