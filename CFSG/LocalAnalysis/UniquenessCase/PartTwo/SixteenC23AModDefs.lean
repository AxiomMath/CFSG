module

public import CFSG.Quasithin.Background.FFC5Coh3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.FFC

variable {V : Type} [CommGroup V]

structure C23ABlock (L : Subgroup (MulAut V)) (E Z : Subgroup V) : Prop where
  nat : Nonempty (NatQuot3 L E Z)
  perf : commSub E L = E
  fix : Z = E ⊓ fixV L

theorem c23a_toGL_bijective :
    Function.Bijective (Matrix.SpecialLinearGroup.toGL :
      SL3F2 →* GL (Fin 3) (ZMod 2)) := by
  refine ⟨Matrix.SpecialLinearGroup.toGL_injective, fun g => ?_⟩
  have hdet : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).det = 1 := by
    have hu : IsUnit (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).det :=
      g.isUnit.map Matrix.detMonoidHom
    obtain ⟨u, hu⟩ := hu
    rw [← hu, Subsingleton.elim u 1, Units.val_one]
  exact ⟨⟨g, hdet⟩, Units.ext rfl⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
