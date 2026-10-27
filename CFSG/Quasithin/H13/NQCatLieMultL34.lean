module

public import CFSG.Quasithin.H13.NQCatLieMult
public import CFSG.Quasithin.H13.NQCatParabolicSL3

public section

namespace CFSG.Quasithin.H13.NQCat.LieMult

open Matrix CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.QuasithinUnique.Setup.X7a
  CFSG.Quasithin.H13.NQCat.SL3

variable {K : Type} [Field K]

theorem eq_one_of_mem_unitriangular_of_mem_scalars {u : SpecialLinearGroup (Fin 3) K}
    (hu : u ∈ unitriangular 3 K) (hs : u ∈ scalars 3 K) : u = 1 := by
  obtain ⟨c, -, hc⟩ := hs
  have h0 := hu.2 0
  rw [hc, scalar_apply, diagonal_apply_eq] at h0
  apply Subtype.ext
  rw [hc, h0]
  simp

theorem entries_eq_zero_of_commute {u : SpecialLinearGroup (Fin 3) K}
    (hu : u ∈ unitriangular 3 K)
    (h01 : proj 3 K (tv (show (0 : Fin 3) ≠ 1 by decide) 1) * proj 3 K u =
      proj 3 K u * proj 3 K (tv (show (0 : Fin 3) ≠ 1 by decide) 1))
    (h12 : proj 3 K (tv (show (1 : Fin 3) ≠ 2 by decide) 1) * proj 3 K u =
      proj 3 K u * proj 3 K (tv (show (1 : Fin 3) ≠ 2 by decide) 1)) :
    (u : Matrix (Fin 3) (Fin 3) K) 0 1 = 0 ∧ (u : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 := by
  have hc : ∀ v ∈ unitriangular 3 K, proj 3 K v * proj 3 K u = proj 3 K u * proj 3 K v →
      v * u = u * v := by
    intro v hv h
    have h1 : proj 3 K (v * u * v⁻¹ * u⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, h]
      group
    have h2 := eq_one_of_mem_unitriangular_of_mem_scalars
      (mul_mem (mul_mem (mul_mem hv hu) (inv_mem hv)) (inv_mem hu)) (proj_eq_one_iff.1 h1)
    calc v * u = (v * u * v⁻¹ * u⁻¹) * (u * v) := by group
      _ = u * v := by rw [h2, one_mul]
  have hm1 : (transvection 0 1 1 : Matrix (Fin 3) (Fin 3) K) * (u : Matrix (Fin 3) (Fin 3) K) =
      (u : Matrix (Fin 3) (Fin 3) K) * transvection 0 1 1 :=
    congrArg Subtype.val (hc _ (tv_mem_unitriangular (show (0 : Fin 3) < 1 by decide) 1) h01)
  have hm2 : (transvection 1 2 1 : Matrix (Fin 3) (Fin 3) K) * (u : Matrix (Fin 3) (Fin 3) K) =
      (u : Matrix (Fin 3) (Fin 3) K) * transvection 1 2 1 :=
    congrArg Subtype.val (hc _ (tv_mem_unitriangular (show (1 : Fin 3) < 2 by decide) 1) h12)
  have e1 := congrFun (congrFun hm1 0) 2
  have e2 := congrFun (congrFun hm2 0) 2
  have e00 := hu.2 0
  have e22 := hu.2 2
  simp [transvection, Matrix.mul_apply, Fin.sum_univ_three, single_apply, Matrix.one_apply, e00,
    e22] at e1 e2
  exact ⟨e2, e1⟩

variable [Finite K]

theorem card_le_of_le_centralizer_projUnitriangular {E : Subgroup (projectiveSL 3 K)}
    (hEU : E ≤ projUnitriangular 3 K)
    (hEC : E ≤ Subgroup.centralizer (projUnitriangular 3 K : Set (projectiveSL 3 K))) :
    Nat.card E ≤ Nat.card K := by
  have hb : ∀ x : E, ∃ u : SpecialLinearGroup (Fin 3) K, u ∈ unitriangular 3 K ∧
      proj 3 K u = x := fun x => hEU x.2
  choose u hu hux using hb
  have hz : ∀ x : E, (u x : Matrix (Fin 3) (Fin 3) K) 0 1 = 0 ∧
      (u x : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 := by
    intro x
    have hcomm : ∀ {a b : Fin 3} (hab : a < b),
        proj 3 K (tv hab.ne 1) * proj 3 K (u x) = proj 3 K (u x) * proj 3 K (tv hab.ne 1) := by
      intro a b hab
      rw [hux x]
      exact Subgroup.mem_centralizer_iff.mp (hEC x.2) _
        ⟨tv hab.ne 1, tv_mem_unitriangular hab 1, rfl⟩
    exact entries_eq_zero_of_commute (hu x) (hcomm (show (0 : Fin 3) < 1 by decide))
      (hcomm (show (1 : Fin 3) < 2 by decide))
  refine Nat.card_le_card_of_injective (fun x => (u x : Matrix (Fin 3) (Fin 3) K) 0 2)
    fun x y hxy => ?_
  have hxy' : u x = u y := by
    have hx := eq_tv_mul_of_mem_unitriangular (hu x)
    have hy := eq_tv_mul_of_mem_unitriangular (hu y)
    rw [(hz x).1, (hz x).2] at hx
    rw [(hz y).1, (hz y).2] at hy
    rw [hx, hy]
    simp only at hxy
    rw [hxy]
  apply Subtype.ext
  rw [← hux x, ← hux y, hxy']

theorem l34NoCentralE16_holds : L34NoCentralE16 := by
  intro S _ _ hS
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hS
  have := charP_two_of_card hF
  obtain ⟨Q, hQ⟩ := exists_sylow_projUnitriangular (K := F) 2 (n := 3) (by norm_num)
  have hU₀ : IsSylowTwoOf (projUnitriangular 3 F) ⊤ := hQ ▸ isSylowTwoOf_top_of_sylow Q
  refine NoCentralE16.of_mulEquiv (e.trans (statedSLEquivProjectiveSL 3 F))
    (noCentralE16_of_sylow hU₀ fun E hEU hEC => ?_)
  have h1 := card_le_of_le_centralizer_projUnitriangular hEU hEC
  rw [hF] at h1
  norm_num at h1
  omega

end CFSG.Quasithin.H13.NQCat.LieMult
