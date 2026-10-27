module

public import CFSG.Quasithin.Background.F6CatShapeG22
public import CFSG.Quasithin.Vol2.GoldschmidtF431q2G2Tab

public section

namespace CFSG.Quasithin.H13.F431.G2Two

open CFSG.Quasithin CFSG.Quasithin.F6 CFSG.Quasithin.F6.G22Perm CFSG.Quasithin.F6.G22Shape
  CFSG.Sporadic.Bridge

namespace Model

variable {k : Type} [Field k] (h2 : (2 : k) = 0) (hk2 : ∀ c : k, c = 0 ∨ c = 1)

include hk2

theorem sEl_mulT {i j : ℕ} (hi : i < 64) (hj : j < 64) :
    sEl h2 i * sEl h2 j = sEl h2 (Tab.mulT i j) :=
  sEl_mul h2 hk2 hi hj (Tab.mulT_spec i hi j hj).1 (Tab.mulT_spec i hi j hj).2

theorem sEl_ne {i j : ℕ} (hi : i < 64) (hj : j < 64) (h : i ≠ j) : sEl h2 i ≠ sEl h2 j :=
  fun e => h (sEl_injective h2 hk2 hi hj e)

theorem sEl_inv {i : ℕ} (hi : i < 64) : (sEl h2 i)⁻¹ = sEl h2 (Tab.invT i) := by
  have h := Tab.invT_spec i hi
  refine inv_eq_of_mul_eq_one_right ?_
  rw [sEl_mul h2 hk2 hi h.1 (l := 0) (by norm_num) (by rw [Tab.xl_zero]; exact h.2)]
  exact sEl_zero h2 hk2

theorem sEl_comm {i j : ℕ} (hi : i < 64) (hj : j < 64) :
    sEl h2 i * sEl h2 j * (sEl h2 i)⁻¹ * (sEl h2 j)⁻¹ = sEl h2 (Tab.commT i j) := by
  have h1 := (Tab.mulT_spec i hi j hj).1
  have h2' := (Tab.invT_spec i hi).1
  have h3 := (Tab.mulT_spec (Tab.mulT i j) h1 (Tab.invT i) h2').1
  rw [sEl_inv h2 hk2 hi, sEl_inv h2 hk2 hj, sEl_mulT h2 hk2 hi hj,
    sEl_mulT h2 hk2 h1 h2', sEl_mulT h2 hk2 h3 (Tab.invT_spec j hj).1]
  rfl

theorem conjG {g : ℕ} (hg : g < 5) {j l : ℕ} (hj : j < 64) (hl : l < 64)
    (h : compL (compL (g22gl g) (u33XL j)) (g22gil g) = u33XL l) :
    g2HomC h2 (u33GenPG g) * sEl h2 j * (g2HomC h2 (u33GenPG g))⁻¹ = sEl h2 l :=
  eqN h2 hk2 (reprN_mul h2 hk2 (reprN_mul h2 hk2 (reprN_gen h2 hk2 g hg)
    (repL_psi_sEl h2 hk2 j hj)) (reprN_genInv h2 hk2 g hg)) (h ▸ repL_psi_sEl h2 hk2 l hl)

theorem x_mem : g2HomC h2 (u33GenPG 3) ∈ (lat h2 hk2).P₁ :=
  (g2IndexTwoData h2 hk2).map_le_ext u33Phi'_A ⟨u33Data.x, u33Data.x_mem_A, rfl⟩

theorem y_mem : g2HomC h2 (u33GenPG 4) ∈ (lat h2 hk2).P₂ :=
  (g2IndexTwoData h2 hk2).map_le_ext u33Phi'_B ⟨u33Data.y, u33Data.y_mem_B, rfl⟩

end Model

end CFSG.Quasithin.H13.F431.G2Two
