module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114E3Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R3LDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3KC
public import CFSG.LocalAnalysis.UniquenessCase.UC22S214U

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem s21_8XT_mono {D : Data G} {Ch Ch' : Choice2011 G}
    (h : ∀ L₀ B₀ : Subgroup G, Ch' L₀ B₀ → Ch L₀ B₀) (hX : S21_8XT D Ch) : S21_8XT D Ch' :=
  fun hH c => hX hH (c.mono h)

theorem s21_14R3LF_mono {D : Data G} {Ch Ch' : Choice2011 G}
    (h : ∀ L₀ B₀ : Subgroup G, Ch' L₀ B₀ → Ch L₀ B₀) (hF : S21_14R3LF D Ch) :
    S21_14R3LF D Ch' :=
  fun hH c => hF hH (c.mono h)

theorem s21_14R3LK2_mono {D : Data G} {Ch Ch' : Choice2011 G}
    (h : ∀ L₀ B₀ : Subgroup G, Ch' L₀ B₀ → Ch L₀ B₀) (hK : S21_14R3LK2 D Ch) :
    S21_14R3LK2 D Ch' :=
  fun hH c => hK hH (c.mono h)

theorem s21_14D4T_mono {D : Data G} {Ch Ch' : Choice2011 G}
    (h : ∀ L₀ B₀ : Subgroup G, Ch' L₀ B₀ → Ch L₀ B₀) (hD : S21_14D4T D Ch) :
    S21_14D4T D Ch' :=
  fun hH c => hD hH (c.mono h)

theorem s21_14K2T_mono {D : Data G} {Ch Ch' : Choice2011 G}
    (h : ∀ L₀ B₀ : Subgroup G, Ch' L₀ B₀ → Ch L₀ B₀) (hK : S21_14K2T D Ch) :
    S21_14K2T D Ch' :=
  fun hH c => hK hH (c.mono h)

theorem s21_22R3F3SzQ5T_mono {D : Data G} {Ch Ch' : Choice2011 G}
    (h : ∀ L₀ B₀ : Subgroup G, Ch' L₀ B₀ → Ch L₀ B₀) (hT : S21_22R3F3SzQ5T D Ch) :
    S21_22R3F3SzQ5T D Ch' :=
  fun hH c => hT hH (c.mono h)

end CFSG.LocalAnalysis.UniquenessCase.UC22
