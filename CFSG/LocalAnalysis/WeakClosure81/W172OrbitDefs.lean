module

public import CFSG.LocalAnalysis.WeakClosure81.SixFour

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

@[expose] def w172R (D : Data G) (V₀ V : Subgroup G) : Subgroup G :=
  D.T ⊓ F11.CTilde D.M V₀ V ⊓ Subgroup.centralizer (V₀ : Set G)

theorem w172R_le_T (D : Data G) (V₀ V : Subgroup G) : w172R D V₀ V ≤ D.T :=
  inf_le_left.trans inf_le_left

theorem w172R_le_M (D : Data G) (V₀ V : Subgroup G) : w172R D V₀ V ≤ D.M :=
  (w172R_le_T D V₀ V).trans D.sylowM.le

theorem w172R_isPGroup (D : Data G) (V₀ V : Subgroup G) : IsPGroup 2 ↥(w172R D V₀ V) :=
  D.sylowM.isPGroup.to_le (w172R_le_T D V₀ V)

@[expose] def W172Lem26 (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ x : G, InCalO 1 D.M V₀ V x → Hyp64 1 D.M V₀ V x

end CFSG.LocalAnalysis.WeakClosure81

end
