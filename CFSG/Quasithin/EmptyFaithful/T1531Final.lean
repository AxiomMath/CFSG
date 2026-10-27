module

public import CFSG.Quasithin.EmptyFaithful.T1531Close

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

section Final

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t : G}

theorem exists_goldLine153 (h : Hyp153 G T Mc M) (D : Decomp153 T M V₁ V₂ t)
    (r66 : Res15366 T Mc M V₁ V₂ E) : ∃ s : G, GoldLine153 T V₁ E s := by
  by_contra hno
  push Not at hno
  have hST : Sgp153 T V₁ ≤ TE153 T E := fun s hs => by
    by_contra hs'
    exact hno s ⟨hs, hs'⟩
  have hiS : (Sgp153 T V₁).relIndex T = 2 := D.relIndex_nS h
  have hiE : (TE153 T E).relIndex T = 2 := r66.relIndex_two
  have hmul := Subgroup.relIndex_mul_relIndex (Sgp153 T V₁) (TE153 T E) T hST inf_le_left
  rw [hiS, hiE] at hmul
  have h1 : (Sgp153 T V₁).relIndex (TE153 T E) = 1 := by omega
  have hTS : TE153 T E ≤ Sgp153 T V₁ := Subgroup.relIndex_eq_one.mp h1
  exact r66.barTE_klein.2 (by rw [le_antisymm hTS hST])

end Final

theorem stageTheorem1531_of_inputs (h113 : StageLemma14113) (hF : F6.TheoremF618)
    (i44 : Stage15344) (i46 : Stage15346) (i47 : Stage15347)
    (i48 : Stage15348) (i49 : Stage15349) (i50 : Stage15350) (i62 : Stage15362)
    (i63 : Stage15363) (i65 : Stage15365One) (i66 : Stage15366) (i67 : Stage15367)
    (i68 : Stage15368) (iI : Stage1531Inspect) : StageTheorem1531 := by
  intro G _ _ T Mc M hq hMf hO
  have h : Hyp153 G T Mc M := ⟨hq, hMf, hO⟩
  obtain ⟨V₁, V₂, t, D⟩ := h.exists_decomp
  have c : Ctx153 G T Mc M V₁ V₂ t := ⟨h, D⟩
  have r45 := lemma_15_3_45 i44 h113 c
  have r46 := i46 G T Mc M V₁ V₂ t c r45
  have r47 := i47 G T Mc M V₁ V₂ t c r45 r46
  have r48 := i48 G T Mc M V₁ V₂ t c r45 r46 r47
  have r49 := i49 G T Mc M V₁ V₂ t c r45 r46 r47 r48
  have hF91 : ∀ H : Subgroup G, IsHTM153 T M H →
      HypF91 T (VZ T M) (Y153 Mc M) (quasithinOmegaOneCenter T) (ZS153 T M V₁) H :=
    fun H hH => hypF91_of_stage15348 i48 c r45 r46 r47 r49 hH
  have r50 := i50 G T Mc M V₁ V₂ t c r45 r46 r47 r49 hF91
  have r62 := i62 G T Mc M V₁ V₂ t c r45 r46 r50
  have r63 := i63 G T Mc M V₁ V₂ t c r45 r46 r50 r62
  have r64 := lemma_15_3_64 c r47 r62
  have r65 := i65 G T Mc M V₁ V₂ t c r45 r46 r50 r49 r62 r63 r64
  have r65two := lemma_15_3_65_two c r46 r63 r65
  obtain ⟨E, L⟩ := exists_lineData153 c r46 r65two
  have r66 := i66 G T Mc M V₁ V₂ E t c r45 r46 L
  have r67 := i67 G T Mc M V₁ V₂ E t c r45 r46 r49 r50 L r66
  obtain ⟨s, gl⟩ := exists_goldLine153 h D r66
  have r68 := i68 G T Mc M V₁ V₂ E t s c r45 r46 r49 r50 L r66 r67 gl
  exact (closing_153 hF iI c r45 r46 r49 L r66 r67 gl r68).elim

end CFSG.Quasithin
