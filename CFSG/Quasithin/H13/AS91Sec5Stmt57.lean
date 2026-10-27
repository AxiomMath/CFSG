module

public import CFSG.Quasithin.H13.AS91Sec5Stmt57a
public import CFSG.Quasithin.H13.AS91Sec5Stmt57b

public section

namespace CFSG.Quasithin.H13.AS91

theorem stmt5_7_of
    (hres : ∀ (G : Type) [Group G] [Finite G] (z : G) (_ : HypJ4 G z) (c : Loc49 G z),
      Nonempty (ResM24 c))
    (h121 : M24G.Stmt3_12_1M24) (h2c : Stmt5_2c) (h532 : Stmt5_3_2) : Stmt5_7 := by
  intro G _ _ z hJ c y hd _ hyP u hu huy
  obtain ⟨hx0y, hxy, -⟩ := hd
  have hyx : y ≠ c.x0 := fun h => hx0y h.symm
  have hyP' : c.OnP y c.pi0 := hyP
  have hLU : Stmt5_LineU := stmt5_lineU_of_2c h2c
  have hzu : z • u = u := c.z_smul_of_adj_far hLU hJ hyP' hyx hxy hu huy
  obtain ⟨-, m, hx0m, hum⟩ := colGraph_adj.mp hu
  obtain ⟨-, n, hyn, hun⟩ := colGraph_adj.mp huy
  obtain ⟨f, hf, -⟩ := c.exists_frame hum
  by_cases hzf : f⁻¹ * z * f ∈ c.E
  · exact c.onP_of_conj_mem_E hJ (h2c G z hJ c) hu hf hzf
  ·
    obtain ⟨ρ⟩ := hres G z hJ c
    obtain ⟨gy, hgyG3, hgy⟩ := c.exists_G3_smul_x0 hyP'
    have hgx : (1 : G) • c.x0 = c.x0 := by rw [one_smul]
    have hwx : (1 : G)⁻¹ * z * 1 ∈ c.E := by simpa using c.z_mem_E
    have hwy : gy⁻¹ * z * gy ∈ c.E := by
      rw [c.G3_comm_z hgyG3]
      exact c.z_mem_E
    obtain ⟨σ, hmσ, hnσ⟩ :=
      ρ.coL_of_not_mem_Q h121 hLU hJ hu huy hgx hgy hf hwx hwy hzu hzf hum hx0m hun hyn
    have hx0σ : c.OnP c.x0 σ := c.inc_pt_plane hx0m hmσ
    have huσ : c.OnP u σ := c.inc_pt_plane hum hmσ
    have hyσ : c.OnP y σ := c.inc_pt_plane hyn hnσ
    have hx0π : c.OnP c.x0 c.pi0 := c.x0_mem_ptsP
    have hσ : σ = c.pi0 := c.plane_unique h532 hJ hx0π hyP' hyx hxy hx0σ hyσ
    rw [hσ] at huσ
    exact huσ

end CFSG.Quasithin.H13.AS91
