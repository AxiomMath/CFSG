module

public import CFSG.RankThree.PartOne.S12.ReflectionFacts
public import CFSG.RankThree.PartOne.Assembly

public section

namespace CFSG.RankThree.PartOne.Q1327T

open CFSG CFSG.RankThree.PartOne

theorem eq_one_of_sq_eq_one_of_pow_eq_one {M : Type*} [Group M] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {x : M} (hx2 : x ^ 2 = 1) (hxp : x ^ p = 1) : x = 1 := by
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
  rw [hk, pow_succ, pow_mul, hx2, one_pow, one_mul] at hxp
  exact hxp

theorem exists_eq_sq_pow_of_pow_eq_one {M : Type*} [Group M] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {x : M} (hxp : x ^ p = 1) : ∃ m : ℕ, x = (x ^ 2) ^ m := by
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
  refine ⟨k + 1, ?_⟩
  have h1 : (x ^ 2) ^ (k + 1) = x ^ p * x := by
    rw [← pow_mul, hk, ← pow_succ]
    congr 1
  rw [h1, hxp, one_mul]

variable {G : Type} [Group G]

theorem zs_mul_u_eq_inv {p : ℕ} {E : Subgroup G} (hd : RefFacts.ElemData p E) {c : E}
    {zs u : MulAut E} (hzs2 : zs * zs = 1) (hu2 : u * u = 1)
    (hcomm : zs * u = u * zs) (hczs : zs c = c⁻¹) (hcu : u c = c)
    (hmov : ∀ x : E, zs x * x⁻¹ ∈ Subgroup.zpowers c)
    (hfix : ∀ x : E, u x = x → x ∈ Subgroup.zpowers c) : ∀ e : E, zs (u e) = e⁻¹ := by
  classical
  have hp := hd.prime
  have hp2 := hd.ne_two
  let _ : CommGroup E := { (inferInstance : Group E) with mul_comm := hd.comm }
  have hzz : ∀ x : E, zs (zs x) = x := fun x => by
    have := congrArg (fun m : MulAut E => m x) hzs2
    simpa [MulAut.mul_apply] using this
  have huu : ∀ x : E, u (u x) = x := fun x => by
    have := congrArg (fun m : MulAut E => m x) hu2
    simpa [MulAut.mul_apply] using this
  have hzu : ∀ x : E, zs (u x) = u (zs x) := fun x => by
    have := congrArg (fun m : MulAut E => m x) hcomm
    simpa [MulAut.mul_apply] using this
  have hboth : ∀ x : E, zs x = x → u x = x → x = 1 := by
    intro x hzx hux
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hfix x hux)
    rw [map_zpow, hczs, inv_zpow] at hzx
    have h2 : (c ^ j) ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 1 [← hzx]
      exact inv_mul_cancel _
    exact eq_one_of_sq_eq_one_of_pow_eq_one hp hp2 h2 (hd.pow _)
  have hν : ∀ x : E, zs (u x) = x → x = 1 := by
    intro x hx
    have hux : u x = zs x := by
      have := congrArg zs hx
      rwa [hzz] at this
    have huzx : u (zs x) = x := by rw [← hzu, hux, hzz]
    have hw : x * zs x = 1 := by
      refine hboth (x * zs x) ?_ ?_
      · rw [map_mul, hzz, mul_comm]
      · rw [map_mul, hux, huzx, mul_comm]
    have hzx : zs x = x⁻¹ := eq_inv_of_mul_eq_one_right hw
    have hx2 : x ^ 2 ∈ Subgroup.zpowers c := by
      have h1 := hmov x
      rw [hzx, ← mul_inv, ← sq] at h1
      simpa using h1
    obtain ⟨m, hm⟩ := exists_eq_sq_pow_of_pow_eq_one hp hp2 (hd.pow x)
    have hxc : x ∈ Subgroup.zpowers c := by
      rw [hm]
      exact Subgroup.pow_mem _ hx2 m
    have hux' : u x = x := by
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hxc
      rw [map_zpow, hcu]
    have hxx : x = x⁻¹ := by rw [← hzx, ← hux, hux']
    have hx2' : x ^ 2 = 1 := by
      rw [sq]
      exact mul_eq_one_iff_eq_inv.2 hxx
    exact eq_one_of_sq_eq_one_of_pow_eq_one hp hp2 hx2' (hd.pow x)
  intro e
  have hνν : ∀ x : E, zs (u (zs (u x))) = x := fun x => by
    have h1 : u (zs (u x)) = zs (u (u x)) := (hzu (u x)).symm
    rw [h1, huu, hzz]
  have hy : zs (u (e * zs (u e))) = e * zs (u e) := by
    rw [map_mul, map_mul, hνν, mul_comm]
  exact eq_inv_of_mul_eq_one_right (hν _ hy)

end CFSG.RankThree.PartOne.Q1327T
