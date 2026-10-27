module

public import CFSG.LocalAnalysis.StandardType.GGFinModelG5Defs
public import CFSG.LieType.Chevalley.E6GraphInvolutionForms

public section

namespace CFSG.StandardType.GGFinModel.G5

open CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.Open CFSG.Assembly CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.E6GraphInvolution
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LocalAnalysis.ComponentInitial
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Assembly.LowTwoRank

section Datum

private theorem g5_sl2Upper_eq_uSL (c : GGL) : sl2Upper GGL c = uSL c := rfl

private theorem g5_sl2Lower_eq_vSL (c : GGL) : sl2Lower GGL c = vSL c := rfl

private theorem g5_map_uSL (f : ℕ) (c : GGL) :
    Matrix.SpecialLinearGroup.map (ggFrobT f) (uSL c) = uSL (c ^ 2 ^ f) := by
  apply Subtype.ext
  show (↑(Matrix.SpecialLinearGroup.map (ggFrobT f) (uSL c)) : Matrix (Fin 2) (Fin 2) GGL) =
    (↑(uSL (c ^ 2 ^ f)) : Matrix (Fin 2) (Fin 2) GGL)
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [RingHom.mapMatrix_apply, Matrix.map_apply, ggFrobT_apply, uSL]

private theorem g5_map_vSL (f : ℕ) (c : GGL) :
    Matrix.SpecialLinearGroup.map (ggFrobT f) (vSL c) = vSL (c ^ 2 ^ f) := by
  apply Subtype.ext
  show (↑(Matrix.SpecialLinearGroup.map (ggFrobT f) (vSL c)) : Matrix (Fin 2) (Fin 2) GGL) =
    (↑(vSL (c ^ 2 ^ f)) : Matrix (Fin 2) (Fin 2) GGL)
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [RingHom.mapMatrix_apply, Matrix.map_apply, ggFrobT_apply, vSL]

theorem ggG5_datum_of_lang
    {t : StatedLieTag} {p f : ℕ} (ht : GGExcFive t)
    {w : WeylGroup (langTag t)} (hw : GGWeylLaw t p f ht w) {g : ModGL (langTag t) GGL}
    (hg : g ∈ adjointGroup (langTag t) GGL)
    (hlang : ggPhi t f g = g * canonicalRep (coxeterSystem (langTag t)) GGL w) :
    ∃ M : GGDatumModel t f p ht, M.w = w ∧ M.D.g0 = g := by
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · refine ⟨⟨w, hw, LangDatum.ofFrobenius (ggFrobT f) (2 ^ f) (ggFrobT_apply f) w hg hlang,
      rfl, rfl, rfl⟩, rfl, rfl⟩
  · refine ⟨⟨w, hw, LangDatum.ofFrobenius (ggFrobT f) (2 ^ f) (ggFrobT_apply f) w hg hlang,
      rfl, rfl, rfl⟩, rfl, rfl⟩
  · refine ⟨⟨w, hw, LangDatum.ofFrobenius (ggFrobT f) (2 ^ f) (ggFrobT_apply f) w hg hlang,
      rfl, rfl, rfl⟩, rfl, rfl⟩
  · refine ⟨⟨w, hw, LangDatum.ofFrobenius (ggFrobT f) (2 ^ f) (ggFrobT_apply f) w hg hlang,
      rfl, rfl, rfl⟩, rfl, rfl⟩
  · refine ⟨⟨w, hw, LangDatum.ofTwist TwistTag.E6 (ggFrobT f) (2 ^ f) (ggFrobT_apply f) w hg
      hlang, rfl, rfl, rfl⟩, rfl, rfl⟩

theorem ggG5_phi_rootSL2
    {t : StatedLieTag} (ht : GGExcFive t) (f : ℕ)
    {β : Fin (langTag t).rank → ℤ} (hβ : IsRoot (langTag t) β) (hfix : ggGraphLat t β = β)
    (A : SL2 GGL) :
    ggPhi t f (rootSL2 (langTag t) GGL β A) =
      rootSL2 (langTag t) GGL β (Matrix.SpecialLinearGroup.map (ggFrobT f) A) := by
  have h2 : (2 : GGL) = 0 := CharP.cast_eq_zero GGL 2
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · have heq : (ggPhi .F4 f).comp (rootSL2 (langTag .F4) GGL β) =
        (rootSL2 (langTag .F4) GGL β).comp (Matrix.SpecialLinearGroup.map (ggFrobT f)) := by
      refine MonoidHom.eq_of_eqOn_dense sl2_closure_upper_lower ?_
      rintro x (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · simp only [MonoidHom.comp_apply]
        rw [g5_sl2Upper_eq_uSL c, rootSL2_uSL_of_two h2 β c,
          ggPhi_pinnedX_untw (Or.inl rfl) f hβ c, g5_map_uSL f c,
          rootSL2_uSL_of_two h2 β (c ^ 2 ^ f)]
      · simp only [MonoidHom.comp_apply]
        rw [g5_sl2Lower_eq_vSL c, rootSL2_vSL_of_two h2 hβ c,
          ggPhi_pinnedX_untw (Or.inl rfl) f (IsRoot.neg hβ) c, g5_map_vSL f c,
          rootSL2_vSL_of_two h2 hβ (c ^ 2 ^ f)]
    exact congrArg (fun φ : SL2 GGL →* ModGL (langTag .F4) GGL => φ A) heq
  · have heq : (ggPhi .E6 f).comp (rootSL2 (langTag .E6) GGL β) =
        (rootSL2 (langTag .E6) GGL β).comp (Matrix.SpecialLinearGroup.map (ggFrobT f)) := by
      refine MonoidHom.eq_of_eqOn_dense sl2_closure_upper_lower ?_
      rintro x (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · simp only [MonoidHom.comp_apply]
        rw [g5_sl2Upper_eq_uSL c, rootSL2_uSL_of_two h2 β c,
          ggPhi_pinnedX_untw (Or.inr (Or.inl rfl)) f hβ c, g5_map_uSL f c,
          rootSL2_uSL_of_two h2 β (c ^ 2 ^ f)]
      · simp only [MonoidHom.comp_apply]
        rw [g5_sl2Lower_eq_vSL c, rootSL2_vSL_of_two h2 hβ c,
          ggPhi_pinnedX_untw (Or.inr (Or.inl rfl)) f (IsRoot.neg hβ) c, g5_map_vSL f c,
          rootSL2_vSL_of_two h2 hβ (c ^ 2 ^ f)]
    exact congrArg (fun φ : SL2 GGL →* ModGL (langTag .E6) GGL => φ A) heq
  · have heq : (ggPhi .E7 f).comp (rootSL2 (langTag .E7) GGL β) =
        (rootSL2 (langTag .E7) GGL β).comp (Matrix.SpecialLinearGroup.map (ggFrobT f)) := by
      refine MonoidHom.eq_of_eqOn_dense sl2_closure_upper_lower ?_
      rintro x (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · simp only [MonoidHom.comp_apply]
        rw [g5_sl2Upper_eq_uSL c, rootSL2_uSL_of_two h2 β c,
          ggPhi_pinnedX_untw (Or.inr (Or.inr (Or.inl rfl))) f hβ c, g5_map_uSL f c,
          rootSL2_uSL_of_two h2 β (c ^ 2 ^ f)]
      · simp only [MonoidHom.comp_apply]
        rw [g5_sl2Lower_eq_vSL c, rootSL2_vSL_of_two h2 hβ c,
          ggPhi_pinnedX_untw (Or.inr (Or.inr (Or.inl rfl))) f (IsRoot.neg hβ) c, g5_map_vSL f c,
          rootSL2_vSL_of_two h2 hβ (c ^ 2 ^ f)]
    exact congrArg (fun φ : SL2 GGL →* ModGL (langTag .E7) GGL => φ A) heq
  · have heq : (ggPhi .E8 f).comp (rootSL2 (langTag .E8) GGL β) =
        (rootSL2 (langTag .E8) GGL β).comp (Matrix.SpecialLinearGroup.map (ggFrobT f)) := by
      refine MonoidHom.eq_of_eqOn_dense sl2_closure_upper_lower ?_
      rintro x (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · simp only [MonoidHom.comp_apply]
        rw [g5_sl2Upper_eq_uSL c, rootSL2_uSL_of_two h2 β c,
          ggPhi_pinnedX_untw (Or.inr (Or.inr (Or.inr rfl))) f hβ c, g5_map_uSL f c,
          rootSL2_uSL_of_two h2 β (c ^ 2 ^ f)]
      · simp only [MonoidHom.comp_apply]
        rw [g5_sl2Lower_eq_vSL c, rootSL2_vSL_of_two h2 hβ c,
          ggPhi_pinnedX_untw (Or.inr (Or.inr (Or.inr rfl))) f (IsRoot.neg hβ) c, g5_map_vSL f c,
          rootSL2_vSL_of_two h2 hβ (c ^ 2 ^ f)]
    exact congrArg (fun φ : SL2 GGL →* ModGL (langTag .E8) GGL => φ A) heq
  · have heq : (ggPhi .twistedE6 f).comp (rootSL2 (langTag .twistedE6) GGL β) =
        (rootSL2 (langTag .twistedE6) GGL β).comp (Matrix.SpecialLinearGroup.map (ggFrobT f)) := by
      refine MonoidHom.eq_of_eqOn_dense sl2_closure_upper_lower ?_
      rintro x (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · simp only [MonoidHom.comp_apply]
        rw [g5_sl2Upper_eq_uSL c, rootSL2_uSL_of_two h2 β c,
          ggPhi_pinnedX_twistedE6 f hβ c]
        change pinnedX (langTag .twistedE6) GGL (ggGraphLat .twistedE6 β) (c ^ 2 ^ f) =
          rootSL2 (langTag .twistedE6) GGL β
            (Matrix.SpecialLinearGroup.map (ggFrobT f) (uSL c))
        rw [hfix, g5_map_uSL f c, rootSL2_uSL_of_two h2 β (c ^ 2 ^ f)]
      · simp only [MonoidHom.comp_apply]
        rw [g5_sl2Lower_eq_vSL c, rootSL2_vSL_of_two h2 hβ c,
          ggPhi_pinnedX_twistedE6 f (IsRoot.neg hβ) c]
        change pinnedX (langTag .twistedE6) GGL (-(ggGraphLat .twistedE6 β)) (c ^ 2 ^ f) =
          rootSL2 (langTag .twistedE6) GGL β
            (Matrix.SpecialLinearGroup.map (ggFrobT f) (vSL c))
        rw [hfix, g5_map_vSL f c, rootSL2_vSL_of_two h2 hβ (c ^ 2 ^ f)]
    exact congrArg (fun φ : SL2 GGL →* ModGL (langTag .twistedE6) GGL => φ A) heq

end Datum

end CFSG.StandardType.GGFinModel.G5
