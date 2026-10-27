module

public import CFSG.Quasithin.H13.A5S1522
public import CFSG.Quasithin.H13.A5S1523
public import CFSG.Quasithin.H13.A5SitBridge5
public import CFSG.Quasithin.H13.A5Top

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model CFSG.Blueprint

theorem InK4_cube : ∀ σ : Equiv.Perm (Fin 5), σ.sign = 1 → σ 4 = 4 → InK4 (σ ^ 3) := by
  decide +kernel

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem cube_mem_pCoreOf_L1
    {x : G} (hx : x ∈ S.L1) : x ^ 3 ∈ pCoreOf 2 S.L1 := by
  obtain ⟨hs, h4⟩ := S.rho_L1' (x := ⟨x, S.frame.L_le (S.L1_le_L hx)⟩) hx
  have h := S.mem_pCoreOf_L1_of_InK4 (x := ⟨x, S.frame.L_le (S.L1_le_L hx)⟩ ^ 3)
    (by simpa using S.L1.pow_mem hx 3) (by rw [map_pow]; exact InK4_cube _ hs h4)
  simpa using h

end Setting

theorem input13518_of
    (h1323 : Input1323Two) (h1326 : Input1326Two) (h1336 : Input1336)
    (hF956 : StmtF956i) (h38 : A38ForSQTK) (hF : Facts1321) (hR : FactRankRows1321)
    (hA7 : FactA7Grp1321) (hL3 : FactL3Grp1321) (hO : FactOutRows1321)
    (hQ : FactQuadRows1321) : Input13518 := by
  intro G _ _ T L V S hna
  by_contra hcon
  push Not at hcon
  have hH := S.G1_mem_Hz h1336
  obtain ⟨u, hu, huc, hu2⟩ := (S.toA5Sit h1323 h1326 h1336 hH hna).exists_comm_sq_ne_one hF956
    h38 (S.toA5SitY h1323 h1326 h1336 hH hna) (S.lemma_13_5_19_two h1323 hcon hH)
    (fun _ hl => S.cube_mem_pCoreOf_L1 hl) hF hR hA7 hL3 hO hQ S.cL1_mem S.cL1_cube
    S.cL1_not_mem_Q
  exact hu2 (S.sq_eq_one_of_comm_cL1 h1323 hH hna hu huc)

end CFSG.Quasithin.H13.A5
