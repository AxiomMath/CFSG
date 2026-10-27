module

public import CFSG.Quasithin.AppendixH.H9.H92.CoreRad.DualAction
public import CFSG.Quasithin.AppendixH.H9.H92.CoreRad.PCoreOfBasic
public import CFSG.Quasithin.AppendixH.H9.H92.RadCard

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

open CFSG.Open

theorem isPGroup_two_radMat (n : ℕ) (D : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    IsPGroup 2 (RadMat n D) := fun g =>
  ⟨1, Subtype.ext (by
    rw [Subgroup.coe_pow, pow_one, pow_two]
    exact (radMat_comm_sq D).2 g.1 g.2)⟩

theorem pCoreOf_stabMat_eq_radMat (n : ℕ) (D : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    pCoreOf 2 (stabMat n D) = RadMat n D :=
  le_antisymm
    (normal_two_subgroup_le_radMat D _ (isPGroup_pCoreOf 2 _) (pCoreOf_le_self 2 _)
      fun _ hs _ hk => pCoreOf_conj_mem hs hk)
    (le_pCoreOf_of_isPGroup_normal (radMat_le_stabMat n D)
      (fun _ hs _ hk => conj_mem_radMat hs hk) (isPGroup_two_radMat n D))

end CFSG.ASVolI.ChH
