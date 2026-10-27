module

public import CFSG.LocalAnalysis.StandardType.GGFinModelRat
public import CFSG.LocalAnalysis.StandardType.GGExcKGSFDefs

public section

namespace CFSG.StandardType.GGFinModel

open CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.HardMathSupport.Timmesfeld.LangTorus

section Kb


abbrev GGKb (t : StatedLieTag) (n f : ℕ) : Type :=
  (ggU t n f).K ⧸ Subgroup.center (ggU t n f).K

end Kb

section Pkg


structure GGLangPkg {τ : Tag} {C : Type} [Group C] (D : LangDatum τ GGL)
    (ι₀ : C →* ModGL τ GGL) : Prop where
  inj : Function.Injective ι₀
  desc : LangDescent D 5 ι₀
  cent_triv : ∀ z ∈ adjointGroup τ GGL, (∀ x : C, z * ι₀ x = ι₀ x * z) → z = 1
  index_le : ι₀.range.relIndex D.fix ≤ 3

theorem GGLangPkg.of_equiv {τ : Tag} {C C' : Type} [Group C] [Group C'] {D : LangDatum τ GGL}
    {ι₀ : C →* ModGL τ GGL} (h : GGLangPkg D ι₀) (e : C' ≃* C) :
    GGLangPkg D (ι₀.comp e.toMonoidHom) := by
  have hr : (ι₀.comp e.toMonoidHom).range = ι₀.range := by
    ext x
    refine ⟨fun ⟨y, hy⟩ => ⟨e y, hy⟩, fun ⟨y, hy⟩ => ⟨e.symm y, ?_⟩⟩
    simpa using hy
  refine ⟨h.inj.comp e.injective, ?_, fun z hz hc => h.cent_triv z hz fun x => ?_, ?_⟩
  · refine ⟨h.desc.finite_fix, ?_, fun P hP hpP => ?_, ?_⟩
    · rw [hr]
      exact h.desc.range_le
    · rw [hr]
      exact h.desc.pgroup_le P hP hpP
    · rw [hr]
      exact h.desc.derived
  · simpa using hc (e.symm x)
  · rw [hr]
    exact h.index_le

end Pkg

end CFSG.StandardType.GGFinModel
