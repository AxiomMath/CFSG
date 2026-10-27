module

public import CFSG.Quasithin.Background.C124AsmBlock
public import CFSG.Quasithin.Background.C124L2PClass
public import CFSG.Quasithin.Background.C124Z3Class

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]

theorem conclude_of_Y {C₁ C₂ : Subgroup G → Subgroup G} (hC : IsGNChoice C₁ C₂)
    (hE23 : E2.E23Statement) {X T V L R : Subgroup G} {m : ℕ} {hV : IsElemAbelian 2 V}
    (E : EntryPlus X T V L R m hV) {Y : Subgroup G} (hY : YData X V L R hV Y)
    (hblk : BlockData V L → IsChiBlock X L ∨
      (IsBlock2 X L ∧ (IsExcA7Block L ∨ IsAltBlockType L 6 ∨ IsHatA6Block L))) :
    (∃ C : Subgroup G, C ≠ ⊥ ∧ C ≤ baum R ∧ (C.subgroupOf (baum R)).Characteristic ∧
        X ≤ Subgroup.normalizer (C : Set G)) ∨
      IsChiBlock X L ∨
      (IsBlock2 X L ∧ (IsExcA7Block L ∨ IsAltBlockType L 6 ∨ IsHatA6Block L)) := by
  have hR2 : IsPGroup 2 R := E.sylow.2.1.to_le E.RT
  have hR0 : R ≠ ⊥ := by
    intro hR
    apply E.VL
    have hV0 : V = ⊥ := le_bot_iff.1 (hR ▸ (le_pCoreOf_of_reduced E.red).trans E.QR)
    rw [hV0, Subgroup.commutator_bot_left]
  have hSp : IsPGroup 2 (baum R) := hR2.to_le inf_le_left
  have hS0 : baum R ≠ ⊥ := C1GN.baum_ne_bot hR2 hR0
  obtain ⟨hC1ne, hC1Z, hC1char, hC2ne, h2B, h2char, -⟩ := hC.pair (baum R) hSp hS0
  rw [C1GN.baum_baum] at h2B h2char
  have hC1B : C₁ (baum R) ≤ baum R := hC1Z.trans (C1GN.omegaOneCenterOf_le_self _)
  have hN₁ := normalizer_le_normalizer_of_characteristic_subgroupOf hC1B hC1char
  have hN₂ := normalizer_le_normalizer_of_characteristic_subgroupOf h2B h2char
  have hdich : Y ≤ Subgroup.centralizer (C₁ (baum R) : Set G) ∨
      Y ≤ Subgroup.normalizer (C₂ (baum R) : Set G) ∨ IsShort2 Y := by
    rcases hY.setup with s | s
    · rcases s.dichotomy_all hE23 hC with h | h | ⟨hb, -⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr hb.1)
    · rcases s.dichotomy_all hC with h | h | ⟨hb, -⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr hb.1)
  rcases hdich with h | h | h
  · left
    refine ⟨C₁ (baum R), hC1ne, hC1B, hC1char, ?_⟩
    rw [hY.gen]
    exact sup_le (h.trans (Subgroup.centralizer_le_normalizer _)) (inf_le_right.trans hN₁)
  · left
    refine ⟨C₂ (baum R), hC2ne, h2B, h2char, ?_⟩
    rw [hY.gen]
    exact sup_le h (inf_le_right.trans hN₂)
  · exact Or.inr (hblk (E.blockData_of_short hY h))

end CFSG.Quasithin.C124
