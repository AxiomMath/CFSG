module

public import CFSG.Milestones.ASVolI.C121.Red2
public import CFSG.Milestones.ASVolI.C121.P1g

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC CFSG.LieType.BorelTits
open scoped MatrixGroups commutatorElement

theorem burnsideC121_part3 (h610 : B_6_10) (h123 : I_2_3) {Ω : Type} [Group Ω] [Finite Ω]
    {C₁ C₂ : Subgroup Ω → Subgroup Ω} (hC : IsGNChoice C₁ C₂) {X L T R : Subgroup Ω}
    (hX : CharTwo X) (hLX : L = oTwoUpper X) (hLc : L ∈ cComp X)
    (hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hT : IsPGroup 2 T) (hSR : baum T ≤ R) (hRT : R ≤ T) (hQR : pCoreOf 2 X ≤ R) (hRX : R ≤ X) :
    ∀ Y : Subgroup Ω, InYSet X R (baum T) Y →
        X = (X ⊓ Subgroup.normalizer (baum T : Set Ω)) ⊔ Y →
        ((∃ D : Subgroup Ω, D ≠ ⊥ ∧ D ≤ baum T ∧ (D.subgroupOf (baum T)).Characteristic ∧
            X ≤ Subgroup.normalizer (D : Set Ω)) ∨
          (IsShort2 L ∧ ∃ hU : IsElemAbelian 2 (blockU L),
            IsFFInt (L ⊔ baum T) (blockU L) hU)) := by
  intro Y hY hXY
  obtain ⟨W, hW, -⟩ := hY.natural
  have c : burnsideC121_YCtx X R T Y W := ⟨hX, hT, hSR, hRT, hQR, hRX, hY, hW⟩
  obtain ⟨n, F, _, _, ⟨Dn⟩⟩ := burnsideC121_exists_natD hY hW
  have hT0 := c.T_ne_bot Dn
  have hS0 := c.S_ne_bot Dn
  have hSp := c.S_pGroup
  obtain ⟨h1ne, h1Z, h1char, h2ne, h2B, h2char, -⟩ := hC.pair (baum T) hSp hS0
  rw [C1GN.baum_baum] at h2B h2char
  have hc2 : C₂ T = C₂ (baum T) := hC.c2_eq T hT hT0
  have hNC2 : Subgroup.normalizer (baum T : Set Ω) ≤ Subgroup.normalizer (C₂ T : Set Ω) := by
    rw [hc2]
    exact normalizer_le_normalizer_of_characteristic_subgroupOf h2B h2char
  have h1S : C₁ (baum T) ≤ baum T := h1Z.trans (C1GN.omegaOneCenterOf_le_self _)
  have hNC1 : Subgroup.normalizer (baum T : Set Ω) ≤
      Subgroup.normalizer (C₁ (baum T) : Set Ω) :=
    normalizer_le_normalizer_of_characteristic_subgroupOf h1S h1char
  obtain ⟨h1, h2⟩ := burnsideC121_part1 h610 h123 hC hX hT hSR hRT hQR hRX hY
  by_cases ha : Y ≤ Subgroup.normalizer (C₂ T : Set Ω)
  ·
    left
    refine ⟨C₂ T, ?_, ?_, ?_, hXY.le.trans (sup_le (inf_le_right.trans hNC2) ha)⟩
    · rw [hc2]; exact h2ne
    · rw [hc2]; exact h2B
    · rw [hc2]; exact h2char
  · by_cases hb : Y ≤ Subgroup.centralizer (C₁ T : Set Ω) ∧
        Y ≤ Subgroup.centralizer (C₁ (baum T) : Set Ω)
    ·
      left
      exact ⟨C₁ (baum T), h1ne, h1S, h1char, hXY.le.trans (sup_le (inf_le_right.trans hNC1)
        (hb.2.trans (Subgroup.centralizer_le_normalizer _)))⟩
    ·
      right
      have hblk : IsL2OrA3Block Y Y := by
        rcases h1 with h | h | h
        · exact absurd h ha
        · exact absurd h hb
        · exact h
      have hYS : ¬ Y ≤ Subgroup.normalizer (baum T : Set Ω) := fun h => ha (h.trans hNC2)
      exact c.reduction hLX hLc hLq hblk (h2.resolve_left hYS).2

theorem burnsideC121_part2 (h610 : B_6_10) (h123 : I_2_3) {Ω : Type} [Group Ω] [Finite Ω]
    {C₁ C₂ : Subgroup Ω → Subgroup Ω} (hC : IsGNChoice C₁ C₂) {X L T R : Subgroup Ω}
    (hX : CharTwo X) (hLX : L = oTwoUpper X) (hLc : L ∈ cComp X)
    (hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hT : IsPGroup 2 T) (hSR : baum T ≤ R) (hRT : R ≤ T) (hQR : pCoreOf 2 X ≤ R) (hRX : R ≤ X) :
    ∀ 𝒴 : Set (Subgroup Ω), (∀ Y ∈ 𝒴, InYSet X R (baum T) Y) →
        X = (⨆ Y ∈ 𝒴, Y) ⊔ (X ⊓ Subgroup.centralizer (omegaOneCenterOf R : Set Ω)) →
        (∀ Y ∈ 𝒴, X = (X ⊓ Subgroup.normalizer (baum T : Set Ω)) ⊔ Y) →
        (C₁ T ≤ centerOf X ∨ X ≤ Subgroup.normalizer (C₂ T : Set Ω) ∨
          (IsShort2 L ∧ ∃ hU : IsElemAbelian 2 (blockU L),
            IsFFInt (L ⊔ baum T) (blockU L) hU)) := by
  intro 𝒴 h𝒴 hgen hNY
  by_cases hT0 : T = ⊥
  ·
    right; left
    have hQ : pCoreOf 2 X = ⊥ := le_bot_iff.1 (hQR.trans (hRT.trans hT0.le))
    have hX' := hX
    unfold CharTwo at hX'
    rw [hQ] at hX'
    intro x hx
    have hx1 : x ∈ (⊥ : Subgroup Ω) := hX' ⟨hx, Subgroup.mem_centralizer_iff.2 fun g hg => by
      rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hg
      rw [hg, one_mul, mul_one]⟩
    rw [Subgroup.mem_bot.1 hx1]
    exact Subgroup.one_mem _
  have hS0 : baum T ≠ ⊥ := C1GN.baum_ne_bot hT hT0
  have hSp : IsPGroup 2 (baum T) := (hT.to_le hRT).to_le hSR
  obtain ⟨-, h1Z, -, -, h2B, h2char, -⟩ := hC.pair (baum T) hSp hS0
  rw [C1GN.baum_baum] at h2B h2char
  have hc2 : C₂ T = C₂ (baum T) := hC.c2_eq T hT hT0
  have hNC2 : Subgroup.normalizer (baum T : Set Ω) ≤ Subgroup.normalizer (C₂ T : Set Ω) := by
    rw [hc2]
    exact normalizer_le_normalizer_of_characteristic_subgroupOf h2B h2char
  by_cases hred : ∃ Y ∈ 𝒴, ¬ Y ≤ Subgroup.normalizer (C₂ T : Set Ω) ∧
      ¬ (Y ≤ Subgroup.centralizer (C₁ T : Set Ω) ∧
        Y ≤ Subgroup.centralizer (C₁ (baum T) : Set Ω))
  ·
    obtain ⟨Y, hY𝒴, ha, hb⟩ := hred
    right; right
    have hY := h𝒴 Y hY𝒴
    obtain ⟨W, hW, -⟩ := hY.natural
    have c : burnsideC121_YCtx X R T Y W := ⟨hX, hT, hSR, hRT, hQR, hRX, hY, hW⟩
    obtain ⟨h1, h2⟩ := burnsideC121_part1 h610 h123 hC hX hT hSR hRT hQR hRX hY
    have hblk : IsL2OrA3Block Y Y := by
      rcases h1 with h | h | h
      · exact absurd h ha
      · exact absurd h hb
      · exact h
    have hYS : ¬ Y ≤ Subgroup.normalizer (baum T : Set Ω) := fun h => ha (h.trans hNC2)
    exact c.reduction hLX hLc hLq hblk (h2.resolve_left hYS).2
  · by_cases ha : ∃ Y ∈ 𝒴, Y ≤ Subgroup.normalizer (C₂ T : Set Ω)
    ·
      obtain ⟨Y, hY𝒴, hYa⟩ := ha
      right; left
      exact (hNY Y hY𝒴).le.trans (sup_le (inf_le_right.trans hNC2) hYa)
    ·
      left
      have hb : ∀ Y ∈ 𝒴, Y ≤ Subgroup.centralizer (C₁ T : Set Ω) := by
        intro Y hY
        by_contra hYb
        exact hred ⟨Y, hY, fun h => ha ⟨Y, hY, h⟩, fun h => hYb h.1⟩
      have hC1R : C₁ T ≤ omegaOneCenterOf R := by
        intro z hz
        rw [hC.c1_eq T hT hT0] at hz
        have hzS : z ∈ omegaOneCenterOf (baum T) := h1Z hz.2
        have hzR : z ∈ R := hSR (C1GN.omegaOneCenterOf_le_self _ hzS)
        have hzC : z ∈ Subgroup.centralizer (R : Set Ω) := Subgroup.centralizer_le hRT hz.1.2
        exact Subgroup.subset_closure ⟨⟨hzR, hzC⟩, (B2F.isElemAbelian_omegaOneCenterOf _).2 z hzS⟩
      have hXC : X ≤ Subgroup.centralizer (C₁ T : Set Ω) :=
        hgen.le.trans (sup_le (iSup₂_le hb) (inf_le_right.trans (Subgroup.centralizer_le hC1R)))
      exact le_inf (hC1R.trans ((C1GN.omegaOneCenterOf_le_self R).trans hRX))
        (Subgroup.le_centralizer_iff.1 hXC)

end CFSG.ASVolI
