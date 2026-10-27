module

public import CFSG.Quasithin.H13.NQCatLieCentralCore
public import CFSG.Quasithin.H13.NQCatLieMultL34

public section

namespace CFSG.Quasithin.H13.NQCat.LieCentral.L3

open Matrix CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Quasithin.H13.NQCat.SL3

variable {K : Type} [Field K]

theorem commute_of_proj {u v : SpecialLinearGroup (Fin 3) K} (hu : u ∈ unitriangular 3 K)
    (hv : v ∈ unitriangular 3 K) (h : proj 3 K v * proj 3 K u = proj 3 K u * proj 3 K v) :
    v * u = u * v := by
  have h1 : proj 3 K (v * u * v⁻¹ * u⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h]
    group
  have h2 := LieMult.eq_one_of_mem_unitriangular_of_mem_scalars
    (mul_mem (mul_mem (mul_mem hv hu) (inv_mem hv)) (inv_mem hu)) (proj_eq_one_iff.1 h1)
  calc v * u = (v * u * v⁻¹ * u⁻¹) * (u * v) := by group
    _ = u * v := by rw [h2, one_mul]

theorem entry_one_two_eq_zero_of_commute {u : SpecialLinearGroup (Fin 3) K}
    (hu : u ∈ unitriangular 3 K) {s : K} (hs : s ≠ 0)
    (h : proj 3 K (tv (show (0 : Fin 3) ≠ 1 by decide) s) * proj 3 K u =
      proj 3 K u * proj 3 K (tv (show (0 : Fin 3) ≠ 1 by decide) s)) :
    (u : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 := by
  have hm := congrArg Subtype.val
    (commute_of_proj hu (tv_mem_unitriangular (show (0 : Fin 3) < 1 by decide) s) h)
  change (transvection 0 1 s : Matrix (Fin 3) (Fin 3) K) * (u : Matrix (Fin 3) (Fin 3) K) =
    (u : Matrix (Fin 3) (Fin 3) K) * transvection 0 1 s at hm
  have e := congrFun (congrFun hm 0) 2
  have e22 := hu.2 2
  simp [transvection, Matrix.mul_apply, Fin.sum_univ_three, single_apply, Matrix.one_apply,
    e22] at e
  exact e.resolve_left hs

theorem entry_zero_one_eq_zero_of_commute {u : SpecialLinearGroup (Fin 3) K}
    (hu : u ∈ unitriangular 3 K) {s : K} (hs : s ≠ 0)
    (h : proj 3 K (tv (show (1 : Fin 3) ≠ 2 by decide) s) * proj 3 K u =
      proj 3 K u * proj 3 K (tv (show (1 : Fin 3) ≠ 2 by decide) s)) :
    (u : Matrix (Fin 3) (Fin 3) K) 0 1 = 0 := by
  have hm := congrArg Subtype.val
    (commute_of_proj hu (tv_mem_unitriangular (show (1 : Fin 3) < 2 by decide) s) h)
  change (transvection 1 2 s : Matrix (Fin 3) (Fin 3) K) * (u : Matrix (Fin 3) (Fin 3) K) =
    (u : Matrix (Fin 3) (Fin 3) K) * transvection 1 2 s at hm
  have e := congrFun (congrFun hm 0) 2
  have e00 := hu.2 0
  simp [transvection, Matrix.mul_apply, Fin.sum_univ_three, single_apply, Matrix.one_apply,
    e00] at e
  exact e.resolve_right hs

theorem commute_of_entries_eq_zero {u v : SpecialLinearGroup (Fin 3) K}
    (hu : u ∈ unitriangular 3 K) (hv : v ∈ unitriangular 3 K)
    (h01 : (u : Matrix (Fin 3) (Fin 3) K) 0 1 = 0)
    (h12 : (u : Matrix (Fin 3) (Fin 3) K) 1 2 = 0) : v * u = u * v := by
  apply Subtype.ext
  change (v : Matrix (Fin 3) (Fin 3) K) * (u : Matrix (Fin 3) (Fin 3) K) =
    (u : Matrix (Fin 3) (Fin 3) K) * (v : Matrix (Fin 3) (Fin 3) K)
  have hu10 : (u : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 := hu.1 1 0 (by decide)
  have hu20 : (u : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := hu.1 2 0 (by decide)
  have hu21 : (u : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 := hu.1 2 1 (by decide)
  have hv10 : (v : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 := hv.1 1 0 (by decide)
  have hv20 : (v : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := hv.1 2 0 (by decide)
  have hv21 : (v : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 := hv.1 2 1 (by decide)
  have hu0 := hu.2 0
  have hu1 := hu.2 1
  have hu2 := hu.2 2
  have hv0 := hv.2 0
  have hv1 := hv.2 1
  have hv2 := hv.2 2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, hu10, hu20, hu21, hv10, hv20, hv21, hu0, hu1,
      hu2, hv0, hv1, hv2, h01, h12]
  all_goals ring

@[expose] noncomputable def tvHom {a b : Fin 3} (hab : a ≠ b) :
    Multiplicative K →* projectiveSL 3 K where
  toFun s := proj 3 K (tv hab (Multiplicative.toAdd s))
  map_one' := by
    rw [toAdd_one, show tv hab (0 : K) = 1 from Subtype.ext (by rw [coe_tv]; simp [transvection]),
      map_one]
  map_mul' s t := by rw [toAdd_mul, ← tv_mul, map_mul]

theorem tvHom_injective {a b : Fin 3} (hab : a < b) : Function.Injective (tvHom (K := K) hab.ne) :=
  fun s t h => by
    have h1 : proj 3 K (tv hab.ne (Multiplicative.toAdd s)) =
        proj 3 K (tv hab.ne (Multiplicative.toAdd t)) := h
    rw [proj_eq_proj_iff] at h1
    have h2 := LieMult.eq_one_of_mem_unitriangular_of_mem_scalars
      (mul_mem (inv_mem (tv_mem_unitriangular hab _)) (tv_mem_unitriangular hab _)) h1
    have h3 : tv hab.ne (Multiplicative.toAdd s) = tv hab.ne (Multiplicative.toAdd t) :=
      inv_mul_eq_one.1 h2
    have h4 := congrFun (congrFun (congrArg Subtype.val h3) a) b
    simp [coe_tv, transvection, hab.ne] at h4
    exact Multiplicative.toAdd.injective h4

theorem centralIndex_l3 [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K) :
    CentralIndex (projectiveSL 3 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := 3) (by norm_num)
  have hU : IsSylowTwoOf (projUnitriangular 3 K) ⊤ := hQ ▸ isSylowTwoOf_top_of_sylow Q
  refine centralIndex_of_sylow hU fun x hx hidx => ?_
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨s, hs, hsx⟩ := exists_ne_zero_commute_of_hom (P := projUnitriangular 3 K) (tvHom (K := K)
    (show (0 : Fin 3) < 1 by decide).ne) (tvHom_injective (show (0 : Fin 3) < 1 by decide))
    (fun s => ⟨_, tv_mem_unitriangular (show (0 : Fin 3) < 1 by decide) _, rfl⟩) (by omega) hidx
  obtain ⟨t, ht, htx⟩ := exists_ne_zero_commute_of_hom (P := projUnitriangular 3 K) (tvHom (K := K)
    (show (1 : Fin 3) < 2 by decide).ne) (tvHom_injective (show (1 : Fin 3) < 2 by decide))
    (fun s => ⟨_, tv_mem_unitriangular (show (1 : Fin 3) < 2 by decide) _, rfl⟩) (by omega) hidx
  have h12 := entry_one_two_eq_zero_of_commute hu hs hsx
  have h01 := entry_zero_one_eq_zero_of_commute hu ht htx
  rintro _ ⟨v, hv, rfl⟩
  rw [← map_mul, ← map_mul, commute_of_entries_eq_zero hu hv h01 h12]

end CFSG.Quasithin.H13.NQCat.LieCentral.L3
