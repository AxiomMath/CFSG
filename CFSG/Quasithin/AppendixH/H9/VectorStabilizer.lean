module

public import CFSG.Quasithin.AppendixH.H9.H91Clauses
public import CFSG.Quasithin.AppendixH.H9.VectorStabilizer.Model
public import CFSG.Quasithin.AppendixH.H9.VectorStabilizer.Perfect
public import CFSG.Quasithin.AppendixH.H9.VectorStabilizer.Extension
public import CFSG.Quasithin.AppendixH.H9.VectorStabilizer.Hyperplane
public import CFSG.Quasithin.AppendixH.H9.VectorStabilizer.Commutators
public import CFSG.Quasithin.AppendixH.H9.VectorStabilizer.Induced
public import CFSG.Quasithin.AppendixH.H9.VectorStabilizer.Sylow

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open CFSG.ASVolI.ChH.VectorStabilizer

private theorem inducesOn_congr {V : Type*} [CommGroup V] {G G' : Subgroup (MulAut V)}
    {U U' Z : Subgroup V} {A : Type*} [CommGroup A] {Γ : Subgroup (MulAut A)}
    (hG : G = G') (hU : U = U') : InducesOn G U Z A Γ ↔ InducesOn G' U' Z A Γ := by
  subst hG hU
  exact Iff.rfl

theorem clause3_normal (m : ℕ) (hm : 3 ≤ m) : H91Clause3 (m + 1) (T0 (m + 1)) (pairVec (ez m) 0) := by
  have hC := twoResidual_Cv hm
  have hM := Mg_inf_centSub_eq m
  have h3c := commOn_V1n_Cv (m := m) (by omega)
  have h3d := (congrArg (commOn (V2n (m + 1))) hC).trans (commOn_V2n_Cv (m := m) (by omega))
  unfold H91Clause3
  refine ⟨hM.trans hC.symm, ?_, (congrArg (commOn (V1n (m + 1))) hC).trans h3c, h3d,
    relIndex_V2n_perpN m, ?_, T0_inf_stabSub_V1n_eq_centSub m, isSylowIn_T0_inf_stabSub m⟩
  · rw [hM]
    exact exists_elemAbelian_isExtOf m
  · exact (inducesOn_congr hC h3d).mpr (inducesOn_Cv m)

end CFSG.ASVolI.ChH
