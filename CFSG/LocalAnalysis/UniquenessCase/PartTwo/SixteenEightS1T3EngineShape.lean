module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3BranchIrr
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Engine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Sig

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

private theorem s16t3_engine_shape_hcase (h : S16gRowCtx D V₀ V L hV) (h3 : 3 ∈ D.sig)
    {I : Subgroup (Vtil V₀ V hV)}
    (hTI : StableUnder (barSub V₀ V hV D.T) I)
    (hS : NatShapeGood (lBar V₀ V hV L) I (I ⊓ fixV (lBar V₀ V hV L))) (a : ℕ) :
    V₀ ≠ ⊥ ∨ 3 ≤ a ∨ ∃ v ∈ V, (∀ t ∈ D.T, t * v = v * t) ∧
      Subgroup.centralizer ({v} : Set G) ≤ D.M := by
  by_cases hV₀ : V₀ = ⊥
  · obtain ⟨v, hvV, -, hvT, hvC⟩ := h.exists_good_vector h3 hV₀ hTI hS
    exact Or.inr (Or.inr ⟨v, hvV, hvT, hvC⟩)
  · exact Or.inl hV₀

theorem S16gRowCtx.false_of_engine_shape (h : S16gRowCtx D V₀ V L hV)
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSchur : CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput)
    (hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L) (barSub V₀ V hV D.T))
    (h3 : 3 ∈ D.sig)
    (hE : T3EngineBranch (lBar V₀ V hV L) ⊤ (fixV (lBar V₀ V hV L)) 3) : False := by
  have hE0 := hE
  obtain ⟨n, hSL | hSp | hOP | hOM | hAlt⟩ := hE
  · obtain ⟨hsimple, hmult⟩ :=
      s16t3_simple_and_mult hGA hSchur (Or.inl ⟨hSL.1, by omega⟩)
    obtain ⟨I, hI, hTI, -⟩ := hT.exists_stable_natural
    have hS := hT.natShapeGood_of_mem_irrSet hE0 hI
    have hS0 := hS
    obtain ⟨m, hSL' | hSp' | hOP' | hOM' | hAlt'⟩ := hS
    · obtain ⟨hSLm, hmSL, hnat⟩ := hSL'
      have hP := ThreeNat.parab_sl hT (n := m) (by omega) hSLm hTI hnat
      exact h.false_of_t3Parab h3 hT hsimple hmult hP (by omega)
        (s16t3_engine_shape_hcase h h3 hTI hS0 (m / 2))
    · obtain ⟨hSpm, hmSp, hnat⟩ := hSp'
      have hP := ThreeNat.parab_sp hT (n := m) (by omega) hSpm hTI hnat
      exact h.false_of_t3Parab h3 hT hsimple hmult hP (by omega)
        (s16t3_engine_shape_hcase h h3 hTI hS0 ((m + 2) / 4))
    · obtain ⟨hOPm, hmOP, hnat⟩ := hOP'
      have hP := ThreeNat.parab_omegaPlus hT (n := m) (by omega) hOPm hTI hnat
      exact h.false_of_t3Parab h3 hT hsimple hmult hP (by omega)
        (s16t3_engine_shape_hcase h h3 hTI hS0 ((m + 4) / 4))
    · obtain ⟨hOMm, hmOM, hnat⟩ := hOM'
      have hP := ThreeNat.parab_omegaMinus hT (n := m) (by omega) hOMm hTI hnat
      exact h.false_of_t3Parab h3 hT hsimple hmult hP (by omega)
        (s16t3_engine_shape_hcase h h3 hTI hS0 ((m + 2) / 4))
    · obtain ⟨hAltm, hmAlt, hnat⟩ := hAlt'
      have hP := ThreeNat.parab_alt hT (n := m) (by omega) hAltm hTI hnat
      exact h.false_of_t3Parab h3 hT hsimple hmult hP (by omega)
        (s16t3_engine_shape_hcase h h3 hTI hS0 ((m + 1) / 4))
  · obtain ⟨hsimple, hmult⟩ :=
      s16t3_simple_and_mult hGA hSchur (Or.inr (Or.inl ⟨hSp.1, by omega⟩))
    obtain ⟨I, hI, hTI, -⟩ := hT.exists_stable_natural
    have hS := hT.natShapeGood_of_mem_irrSet hE0 hI
    have hS0 := hS
    obtain ⟨m, hSL' | hSp' | hOP' | hOM' | hAlt'⟩ := hS
    · obtain ⟨hSLm, hmSL, hnat⟩ := hSL'
      have hP := ThreeNat.parab_sl hT (n := m) (by omega) hSLm hTI hnat
      exact h.false_of_t3Parab h3 hT hsimple hmult hP (by omega)
        (s16t3_engine_shape_hcase h h3 hTI hS0 (m / 2))
    · obtain ⟨hSpm, hmSp, hnat⟩ := hSp'
      have hP := ThreeNat.parab_sp hT (n := m) (by omega) hSpm hTI hnat
      exact h.false_of_t3Parab h3 hT hsimple hmult hP (by omega)
        (s16t3_engine_shape_hcase h h3 hTI hS0 ((m + 2) / 4))
    · obtain ⟨hOPm, hmOP, hnat⟩ := hOP'
      have hP := ThreeNat.parab_omegaPlus hT (n := m) (by omega) hOPm hTI hnat
      exact h.false_of_t3Parab h3 hT hsimple hmult hP (by omega)
        (s16t3_engine_shape_hcase h h3 hTI hS0 ((m + 4) / 4))
    · obtain ⟨hOMm, hmOM, hnat⟩ := hOM'
      have hP := ThreeNat.parab_omegaMinus hT (n := m) (by omega) hOMm hTI hnat
      exact h.false_of_t3Parab h3 hT hsimple hmult hP (by omega)
        (s16t3_engine_shape_hcase h h3 hTI hS0 ((m + 2) / 4))
    · obtain ⟨hAltm, hmAlt, hnat⟩ := hAlt'
      have hP := ThreeNat.parab_alt hT (n := m) (by omega) hAltm hTI hnat
      exact h.false_of_t3Parab h3 hT hsimple hmult hP (by omega)
        (s16t3_engine_shape_hcase h h3 hTI hS0 ((m + 1) / 4))
  · obtain ⟨hsimple, hmult⟩ :=
      s16t3_simple_and_mult hGA hSchur (Or.inr (Or.inr (Or.inl ⟨hOP.1, by omega⟩)))
    obtain ⟨I, hI, hTI, -⟩ := hT.exists_stable_natural
    have hS := hT.natShapeGood_of_mem_irrSet hE0 hI
    have hS0 := hS
    obtain ⟨m, hSL' | hSp' | hOP' | hOM' | hAlt'⟩ := hS
    · obtain ⟨hSLm, hmSL, hnat⟩ := hSL'
      have hP := ThreeNat.parab_sl hT (n := m) (by omega) hSLm hTI hnat
      exact h.false_of_t3Parab h3 hT hsimple hmult hP (by omega)
        (s16t3_engine_shape_hcase h h3 hTI hS0 (m / 2))
    · obtain ⟨hSpm, hmSp, hnat⟩ := hSp'
      have hP := ThreeNat.parab_sp hT (n := m) (by omega) hSpm hTI hnat
      exact h.false_of_t3Parab h3 hT hsimple hmult hP (by omega)
        (s16t3_engine_shape_hcase h h3 hTI hS0 ((m + 2) / 4))
    · obtain ⟨hOPm, hmOP, hnat⟩ := hOP'
      have hP := ThreeNat.parab_omegaPlus hT (n := m) (by omega) hOPm hTI hnat
      exact h.false_of_t3Parab h3 hT hsimple hmult hP (by omega)
        (s16t3_engine_shape_hcase h h3 hTI hS0 ((m + 4) / 4))
    · obtain ⟨hOMm, hmOM, hnat⟩ := hOM'
      have hP := ThreeNat.parab_omegaMinus hT (n := m) (by omega) hOMm hTI hnat
      exact h.false_of_t3Parab h3 hT hsimple hmult hP (by omega)
        (s16t3_engine_shape_hcase h h3 hTI hS0 ((m + 2) / 4))
    · obtain ⟨hAltm, hmAlt, hnat⟩ := hAlt'
      have hP := ThreeNat.parab_alt hT (n := m) (by omega) hAltm hTI hnat
      exact h.false_of_t3Parab h3 hT hsimple hmult hP (by omega)
        (s16t3_engine_shape_hcase h h3 hTI hS0 ((m + 1) / 4))
  · obtain ⟨hsimple, hmult⟩ :=
      s16t3_simple_and_mult hGA hSchur (Or.inr (Or.inr (Or.inr (Or.inl ⟨hOM.1, by omega⟩))))
    obtain ⟨I, hI, hTI, -⟩ := hT.exists_stable_natural
    have hS := hT.natShapeGood_of_mem_irrSet hE0 hI
    have hS0 := hS
    obtain ⟨m, hSL' | hSp' | hOP' | hOM' | hAlt'⟩ := hS
    · obtain ⟨hSLm, hmSL, hnat⟩ := hSL'
      have hP := ThreeNat.parab_sl hT (n := m) (by omega) hSLm hTI hnat
      exact h.false_of_t3Parab h3 hT hsimple hmult hP (by omega)
        (s16t3_engine_shape_hcase h h3 hTI hS0 (m / 2))
    · obtain ⟨hSpm, hmSp, hnat⟩ := hSp'
      have hP := ThreeNat.parab_sp hT (n := m) (by omega) hSpm hTI hnat
      exact h.false_of_t3Parab h3 hT hsimple hmult hP (by omega)
        (s16t3_engine_shape_hcase h h3 hTI hS0 ((m + 2) / 4))
    · obtain ⟨hOPm, hmOP, hnat⟩ := hOP'
      have hP := ThreeNat.parab_omegaPlus hT (n := m) (by omega) hOPm hTI hnat
      exact h.false_of_t3Parab h3 hT hsimple hmult hP (by omega)
        (s16t3_engine_shape_hcase h h3 hTI hS0 ((m + 4) / 4))
    · obtain ⟨hOMm, hmOM, hnat⟩ := hOM'
      have hP := ThreeNat.parab_omegaMinus hT (n := m) (by omega) hOMm hTI hnat
      exact h.false_of_t3Parab h3 hT hsimple hmult hP (by omega)
        (s16t3_engine_shape_hcase h h3 hTI hS0 ((m + 2) / 4))
    · obtain ⟨hAltm, hmAlt, hnat⟩ := hAlt'
      have hP := ThreeNat.parab_alt hT (n := m) (by omega) hAltm hTI hnat
      exact h.false_of_t3Parab h3 hT hsimple hmult hP (by omega)
        (s16t3_engine_shape_hcase h h3 hTI hS0 ((m + 1) / 4))
  · obtain ⟨hsimple, hmult⟩ :=
      s16t3_simple_and_mult hGA hSchur
        (Or.inr (Or.inr (Or.inr (Or.inr ⟨hAlt.1, by omega⟩))))
    obtain ⟨I, hI, hTI, -⟩ := hT.exists_stable_natural
    have hS := hT.natShapeGood_of_mem_irrSet hE0 hI
    have hS0 := hS
    obtain ⟨m, hSL' | hSp' | hOP' | hOM' | hAlt'⟩ := hS
    · obtain ⟨hSLm, hmSL, hnat⟩ := hSL'
      have hP := ThreeNat.parab_sl hT (n := m) (by omega) hSLm hTI hnat
      exact h.false_of_t3Parab h3 hT hsimple hmult hP (by omega)
        (s16t3_engine_shape_hcase h h3 hTI hS0 (m / 2))
    · obtain ⟨hSpm, hmSp, hnat⟩ := hSp'
      have hP := ThreeNat.parab_sp hT (n := m) (by omega) hSpm hTI hnat
      exact h.false_of_t3Parab h3 hT hsimple hmult hP (by omega)
        (s16t3_engine_shape_hcase h h3 hTI hS0 ((m + 2) / 4))
    · obtain ⟨hOPm, hmOP, hnat⟩ := hOP'
      have hP := ThreeNat.parab_omegaPlus hT (n := m) (by omega) hOPm hTI hnat
      exact h.false_of_t3Parab h3 hT hsimple hmult hP (by omega)
        (s16t3_engine_shape_hcase h h3 hTI hS0 ((m + 4) / 4))
    · obtain ⟨hOMm, hmOM, hnat⟩ := hOM'
      have hP := ThreeNat.parab_omegaMinus hT (n := m) (by omega) hOMm hTI hnat
      exact h.false_of_t3Parab h3 hT hsimple hmult hP (by omega)
        (s16t3_engine_shape_hcase h h3 hTI hS0 ((m + 2) / 4))
    · obtain ⟨hAltm, hmAlt, hnat⟩ := hAlt'
      have hP := ThreeNat.parab_alt hT (n := m) (by omega) hAltm hTI hnat
      exact h.false_of_t3Parab h3 hT hsimple hmult hP (by omega)
        (s16t3_engine_shape_hcase h h3 hTI hS0 ((m + 1) / 4))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
