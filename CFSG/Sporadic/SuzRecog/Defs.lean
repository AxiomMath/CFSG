module

public import CFSG.Sporadic.Co1Patterson.GlueForm
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Omega

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.SuzRecog

open CFSG.Open CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.AS81.Sec2Omega
  CFSG.Sporadic.Co1Patterson

noncomputable abbrev Lm : Subgroup ((Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)) :=
  timmesfeldOmega qMinus

@[expose] noncomputable def bilM : (Fin 6 → ZMod 2) → (Fin 6 → ZMod 2) → ZMod 2 :=
  QuadraticMap.polar qMinusForm

abbrev SuzType (H : Type) [Group H] : Type :=
  ExtraspecialTypeSystem 6 Lm Lm.subtype qMinus bilM H

theorem bilM_apply (u v : Fin 6 → ZMod 2) : bilM u v = polarMinus u v :=
  polar_qMinusForm u v

theorem nondeg_bilM : Nondeg bilM where
  exists_eq_one := ⟨Pi.single 0 1, Pi.single 1 1, by rw [bilM_apply, polarMinus]; decide⟩
  exists_eq D hD := by
    refine ⟨![D (Pi.single 1 1), D (Pi.single 0 1), D (Pi.single 3 1), D (Pi.single 2 1),
      D (Pi.single 5 1), D (Pi.single 4 1)], fun v => ?_⟩
    rw [additive_eq_sum hD v, bilM_apply, polarMinus, Fin.sum_univ_six]
    simp
    ring

end CFSG.Sporadic.SuzRecog
