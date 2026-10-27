module

public import CFSG.Quasithin.Recognition.SzVBEvenBasic

public section

namespace CFSG.Quasithin.SzVB

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [Finite G] {G₀ G₁ G₂ T V : Subgroup G} {z : G}

section Dist

variable (hC : GeoCtx G₀ G₁ G₂ T V z)

include hC

theorem Vv_le_pCoreOf_of_dist_lt {x y : CosetGeom G₀ G₁ G₂} (hx : vtype x = false)
    (hd : dist x y < critDist G₀ G₁ G₂ V) : Vv V x ≤ pCoreOf 2 (stab y) := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₀ hx
  obtain ⟨nb, hnb⟩ := exists_adj y
  have h1 := (conjSub_V_le_pCoreOf hC.hyp (V_ne_bot hC) g (γ := y) (δ := nb) hd hnb).1
  rw [Vv_smul_γ₀ hC.hyp.normalizes]
  refine h1.trans ?_
  rw [ballStab_one_eq_pCoreOf hC y]
  exact CFSG.LieType.BorelTits.pCoreOf_le 2 _

theorem Vv_le_stab_of_dist_le {x y : CosetGeom G₀ G₁ G₂} (hx : vtype x = false)
    (hd : dist x y ≤ critDist G₀ G₁ G₂ V) : Vv V x ≤ stab y := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₀ hx
  have hd' : dist (γ₀ G₀ G₁ G₂) (g⁻¹ • y) ≤ critDist G₀ G₁ G₂ V := by
    have := dist_smul g (γ₀ G₀ G₁ G₂) (g⁻¹ • y)
    rw [smul_inv_smul] at this
    rw [← this]
    exact hd
  have h1 := V_le_stab_of_dist_le hC.hyp (V_ne_bot hC) hd'
  rw [stab_smul, Subgroup.coe_inv] at h1
  rw [Vv_smul_γ₀ hC.hyp.normalizes, conjSub_le_iff]
  exact h1

theorem Vv_le_pCoreOf_of_dist_lt_B {y x : CosetGeom G₀ G₁ G₂} (hy : vtype y = true)
    (hd : dist y x + 1 < critDist G₀ G₁ G₂ V) : Vv V y ≤ pCoreOf 2 (stab x) := by
  rw [Vv_B_le_iff hy]
  intro u hu
  refine Vv_le_pCoreOf_of_dist_lt hC (vtype_eq_false_of_adj hu hy) ?_
  have h1 : dist u y = 1 := dist_eq_one_iff_adj.mpr hu.symm
  have h2 := dist_triangle hC.hyp.gen u y x
  omega

theorem Vv_le_stab_of_dist_le_B {y x : CosetGeom G₀ G₁ G₂} (hy : vtype y = true)
    (hd : dist y x + 1 ≤ critDist G₀ G₁ G₂ V) : Vv V y ≤ stab x := by
  rw [Vv_B_le_iff hy]
  intro u hu
  refine Vv_le_stab_of_dist_le hC (vtype_eq_false_of_adj hu hy) ?_
  have h1 : dist u y = 1 := dist_eq_one_iff_adj.mpr hu.symm
  have h2 := dist_triangle hC.hyp.gen u y x
  omega

omit [Finite G] in
theorem vtype_geo_false_iff {p : ℕ → CosetGeom G₀ G₁ G₂} {n : ℕ} (hp : IsGeo p n)
    (h0 : vtype (p 0) = false) {i : ℕ} (hi : i ≤ n) : vtype (p i) = false ↔ Even i := by
  have h := vtype_eq_iff_even_dist hC.hyp.gen (p 0) (p i)
  rw [hp 0 i (Nat.zero_le _) hi, Nat.sub_zero, h0] at h
  exact eq_comm.trans h

end Dist

end CFSG.Quasithin.SzVB
