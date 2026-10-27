module

public import CFSG.Quasithin.H13.NQS1346

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.Quasithin.InternalSec
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

namespace NZ134

variable {z : G} (N : NZ134 G T L V z)
include N

theorem z_ne_one : z ≠ 1 := fun h => N.zL (h ▸ one_mem _)

theorem z_sq : z ^ 2 = 1 := (mem_quasithinOmegaOneCenter_iff.1 N.zV1.2).2.2

theorem T_le_Gz : T ≤ centralizer ({z} : Set G) := fun t ht =>
  mem_centralizer_singleton_iff.mpr
    (mem_centralizer_iff.mp (U3.s134_Z_le_center T N.zV1.2).2 t ht)

theorem exists_inH : ∃ H : Subgroup G, InH T H ∧ ¬ H ≤ normalizer (L : Set G) :=
  ⟨centralizer ({z} : Set G), ⟨N.T_le_Gz, pCoreOf_centralizer_ne_bot N.z_ne_one N.z_sq⟩, N.zM⟩

theorem inHz (h1332 : Stmt13_3_2) (hC58 : TheoremC58) (h317 : AS317Sylow) (h56 : AsB56) :
    U3.InHz T L V z (centralizer ({z} : Set G)) := by
  have hL1Z := U3.s134_L1_le_centralizer_Z h1332 hC58 h317 h56 N.S N.exists_inH
  refine ⟨⟨sup_le (fun x hx => ?_) N.T_le_Gz,
    pCoreOf_centralizer_ne_bot N.z_ne_one N.z_sq⟩, le_rfl, N.zM⟩
  exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hL1Z hx) z N.zV1.2).symm

end NZ134

theorem oTwoRes_sup_eq_of_faithful {K : Subgroup G} (hKf : quasithinIsFaithfulLocal T K)
    (hTK : T ≤ normalizer (K : Set G)) : oTwoRes (K ⊔ T) = K :=
  le_antisymm (U3.oTwoRes_le_of_le_sup le_rfl hKf.1.1 hTK)
    ((A5.oTwoRes_eq_of_faithful hKf).symm.le.trans (U3.oTwoRes_mono' le_sup_left))

end CFSG.Quasithin.H13.NQS134
