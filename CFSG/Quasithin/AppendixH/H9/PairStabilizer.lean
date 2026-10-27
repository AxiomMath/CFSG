module

public import CFSG.Quasithin.AppendixH.H9.H91Clauses
public import CFSG.Quasithin.AppendixH.H9.AutPairStabilizer
public import CFSG.Quasithin.AppendixH.H9.PairStabilizer.LeviEmbedding
public import CFSG.Quasithin.AppendixH.H9.PairStabilizer.CentralizerOfV
public import CFSG.Quasithin.AppendixH.H9.PairStabilizer.StabilizerSubgroups
public import CFSG.Quasithin.AppendixH.H9.PairStabilizer.SylowOfCentralizer
public import CFSG.Quasithin.AppendixH.H9.PairStabilizer.ComplementSpaces

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

private theorem pairVec_ez_mem_Oorb_two (m : ℕ) : pairVec (ez m) (ez m) ∈ Oorb (m + 1) 2 := by
  have h1 : (ez m : Fin (m + 1) → ZMod 2) ≠ 0 := fun h => by
    have := congrFun h 0
    simp [PairStab.ez_zero] at this
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact h1 (ofAdd_eq_one.1 h)
  · intro h
    exact h1 (ofAdd_eq_one.1 h)
  · rw [pairQn_pairVec]
    simp [ez, dotProduct, Pi.single_apply]

theorem clause4_normal (m : ℕ) (hm : 3 ≤ m) :
    H91Clause4 (m + 1) (T0 (m + 1)) (pairVec (ez m) 0) (pairVec 0 (ez m)) := by
  have hnonempty := nonempty_mulEquiv_aut_pairStab m hm
  have hres : twoResidual (Lg (m + 1) ⊓ centSub (Subgroup.zpowers (pairVec (ez m) (ez m)))) =
      (PairStab.leviAct m).range := by
    rw [PairStab.Lg_inf_centSub_eq_range, PairStab.twoResidual_range hm]
  unfold H91Clause4
  rw [PairStab.pairVec_ez_mul_pairVec_ez] at hnonempty ⊢
  rw [PairStab.Mg_inf_centSub_sup_eq_range, PairStab.Lg_inf_centSub_eq_range,
    PairStab.twoResidual_range hm, PairStab.T0_inf_centSub_eq_Pv (by omega)]
  refine ⟨pairVec_ez_mem_Oorb_two m, ⟨PairStab.Sv m, PairStab.isSylowIn_Sv_Mv,
    PairStab.Sv_inf_Lg, PairStab.tInv m, Subgroup.mem_sup_right (Subgroup.mem_zpowers _),
    PairStab.tInv_not_mem_Lg, PairStab.tInv_sq, PairStab.tInv_apply_v1, PairStab.tInv_apply_v2,
    PairStab.Mv_eq_sup, hnonempty, rfl, PairStab.isSylowIn_Pv_range⟩,
    ⟨PairStab.V1n_decomp.1, PairStab.V1n_decomp.2, PairStab.V2n_decomp.1, PairStab.V2n_decomp.2⟩,
    ?_, PairStab.polar_W1_W2, PairStab.polar_W2_W1⟩
  have key := congrArg (fun G : Subgroup (MulAut (PairN (m + 1))) =>
    InducesOn G (PairStab.W1sub m) ⊥ (Multiplicative (Fin m → ZMod 2)) (natSub m (ZMod 2) ⊤)) hres
  exact Eq.mpr key PairStab.inducesOn_W1sub

end CFSG.ASVolI.ChH
