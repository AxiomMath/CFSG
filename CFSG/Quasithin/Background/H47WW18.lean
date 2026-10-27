module

public import CFSG.Milestones.ASVolI.H1
public import CFSG.Quasithin.Vol2.Ch9L34M18
public import CFSG.Quasithin.Vol2.Ch9L34Norm18
public import CFSG.Quasithin.Background.HL3NineW9
public import CFSG.CharacterTheory.Semidihedral.FixedFieldData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPrimeCompatibility
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.Quasithin.Background.HFixSylBase
public import CFSG.Quasithin.Background.HTriSolv
public import CFSG.Quasithin.Background.HTriU3
public import CFSG.Quasithin.Background.HZ82Base
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

namespace CFSG.Quasithin.H47W

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.Ch9.L34M
  CFSG.Quasithin.H13.Ch9.Herm9 CFSG.Quasithin.H.L3W9 CFSG.ASVolI.ChH CFSG.Fischer

theorem rho18GL_apply_snd (g : GL (Fin 3) F4) (v : W18) :
    (rho18GL g v).2 = rho9 (grGL g) v.2 := rfl

theorem not_irr_w18 {V : Type} [CommGroup V] (L : Subgroup (MulAut V)) (e : V ≃* W18)
    (he : L.map (MulAut.congr e).toMonoidHom =
      (rho18GL.comp Matrix.SpecialLinearGroup.toGL).range)
    (hirr : IsIrredOn L ⊤) : False := by
  haveI : Nontrivial W9 := Finite.one_lt_card_iff_nontrivial.1
    (by rw [card_of_coords (MaskCoords.std 9)]; norm_num)
  obtain ⟨y, hy⟩ := exists_ne (1 : W9)
  set U0 : Subgroup W18 := (⊤ : Subgroup W9).prod ⊥ with hU0
  set U : Subgroup V := U0.comap (e.toMonoidHom : V →* W18) with hU
  have hmemU : ∀ v : V, v ∈ U ↔ (e v).2 = 1 := by
    intro v
    rw [hU, Subgroup.mem_comap, hU0, Subgroup.mem_prod]
    simp
  have hinv : ∀ l ∈ L, ∀ u ∈ U, l u ∈ U := by
    intro l hl u hu
    have hl' : MulAut.congr e l ∈ (rho18GL.comp Matrix.SpecialLinearGroup.toGL).range := by
      rw [← he]
      exact Subgroup.mem_map_of_mem _ hl
    obtain ⟨g, hg⟩ := hl'
    rw [hmemU]
    have hcomm : e (l u) = MulAut.congr e l (e u) := by
      simp [MulAut.congr_apply]
    rw [hcomm, ← hg]
    have h2 : (e u).2 = 1 := (hmemU u).1 hu
    show (rho18GL (Matrix.SpecialLinearGroup.toGL g) (e u)).2 = 1
    rw [rho18GL_apply_snd, h2, map_one]
  rcases hirr.2 U le_top hinv with h | h
  ·
    have hmem : e.symm (y, 1) ∈ U := by
      rw [hmemU]
      simp
    rw [h, Subgroup.mem_bot] at hmem
    have : e.symm (y, 1) = 1 := hmem
    have h1 : (y, (1 : W9)) = 1 := by
      have := congrArg e this
      simpa using this
    exact hy (congrArg Prod.fst h1)
  ·
    have hmem : e.symm (1, y) ∈ U := by rw [h]; exact Subgroup.mem_top _
    rw [hmemU] at hmem
    simp at hmem
    exact hy hmem

end CFSG.Quasithin.H47W
