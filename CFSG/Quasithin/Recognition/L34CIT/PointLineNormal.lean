module

public import CFSG.Quasithin.Recognition.L34CIT.Opposite

public section

namespace CFSG.Quasithin.L34CIT

open Subgroup CFSG.Open
open scoped Pointwise

variable {A : Type} [Group A]

namespace Config

theorem point_normal (C : Config A) [Finite A] (P : Sylow 2 A) :
    (P : Subgroup A) ≤ normalizer (C.point P : Set A) := by
  obtain ⟨a, rfl⟩ := MulAction.exists_smul_eq A C.T P
  rw [C.point_smul, Subgroup.pointwise_smul_def]
  rw [show ((a • C.T : Sylow 2 A) : Subgroup A) =
      Subgroup.map (MulAut.conj a).toMonoidHom (C.T : Subgroup A) from rfl]
  rw [show Subgroup.map
        ((MulDistribMulAction.toMonoidEnd (MulAut A) A) (MulAut.conj a)) (C.L : Subgroup A) =
      Subgroup.map (MulAut.conj a).toMonoidHom (C.L : Subgroup A) from rfl]
  rw [← Subgroup.map_equiv_normalizer_eq (C.L) (MulAut.conj a)]
  exact Subgroup.map_mono C.T_le_normalizer_L

theorem line_normal (C : Config A) [Finite A] (P : Sylow 2 A) :
    (P : Subgroup A) ≤ normalizer (C.line P : Set A) := by
  obtain ⟨a, rfl⟩ := MulAction.exists_smul_eq A C.T P
  rw [C.line_smul, Subgroup.pointwise_smul_def]
  rw [show ((a • C.T : Sylow 2 A) : Subgroup A) =
      Subgroup.map (MulAut.conj a).toMonoidHom (C.T : Subgroup A) from rfl]
  rw [show Subgroup.map
        ((MulDistribMulAction.toMonoidEnd (MulAut A) A) (MulAut.conj a)) (C.M : Subgroup A) =
      Subgroup.map (MulAut.conj a).toMonoidHom (C.M : Subgroup A) from rfl]
  rw [← Subgroup.map_equiv_normalizer_eq (C.M) (MulAut.conj a)]
  exact Subgroup.map_mono C.T_le_normalizer_M

end Config

end CFSG.Quasithin.L34CIT
