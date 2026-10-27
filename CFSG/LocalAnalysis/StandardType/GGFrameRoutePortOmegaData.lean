module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortOmegaRefl

public section

namespace CFSG.StandardType.FrameRoute.OmegaTen

open CFSG.Assembly
open scoped commutatorElement

@[expose] def vec (l : List Idx) : Idx → ZMod 2 := fun i => if i ∈ l then 1 else 0

@[expose] def av : Fin 5 → Idx → ZMod 2 :=
  ![vec [ix 0, iy 0], vec [ix 0, iy 0, iy 1], vec [ix 2, iy 2], vec [ix 2, iy 2, iy 3], vec [iu]]

@[expose] def bv : Fin 5 → Idx → ZMod 2 :=
  ![vec [ix 0, ix 1, iy 1], vec [ix 1, iy 1], vec [ix 2, ix 3, iy 3], vec [ix 3, iy 3], vec [iv]]

theorem quadTen_av (i : Fin 5) : quadTen (av i) = 1 := by
  revert i
  decide +kernel

theorem quadTen_bv (i : Fin 5) : quadTen (bv i) = 1 := by
  revert i
  decide +kernel

@[expose] def rho (i : Fin 5) : GL Idx (ZMod 2) := ⁅reflGL (bv i), reflGL (av i)⁆

theorem rho_mem (i : Fin 5) : rho i ∈ LargeEvenOmega quadTen :=
  commutator_reflGL_mem (quadTen_bv i) (quadTen_av i)

@[expose] def gen : Fin 4 → GL Idx (ZMod 2) := ![rho 0, rho 1, rho 2, rho 3 * rho 4]

theorem gen_mem (i : Fin 4) : gen i ∈ LargeEvenOmega quadTen := by
  fin_cases i
  · exact rho_mem 0
  · exact rho_mem 1
  · exact rho_mem 2
  · exact Subgroup.mul_mem _ (rho_mem 3) (rho_mem 4)

theorem gen_pow_three (i : Fin 4) : gen i ^ 3 = 1 := by
  revert i
  decide +kernel

theorem gen_commute (i j : Fin 4) : gen i * gen j = gen j * gen i := by
  revert i j
  decide +kernel

@[expose] def genProd (c : Fin 4 → ZMod 3) : GL Idx (ZMod 2) :=
  gen 0 ^ (c 0).val * gen 1 ^ (c 1).val * gen 2 ^ (c 2).val * gen 3 ^ (c 3).val

@[expose] def tInv : GL Idx (ZMod 2) :=
  ⁅reflGL (vec [ix 2, ix 3, iy 3]) * reflGL (vec [ix 2, iv]),
    reflGL (vec [ix 2, iy 2]) * reflGL (vec [iy 3, iu])⁆

theorem tInv_mem : tInv ∈ LargeEvenOmega quadTen := by
  have h : ∀ l : List Idx, quadTen (vec l) = 1 → reflGL (vec l) ∈ LargeEvenOrthGroup quadTen :=
    fun l hl => reflGL_mem_largeEvenOrthGroup hl
  rw [largeEvenOmega_def]
  exact Subgroup.commutator_mem_commutator
    (Subgroup.mul_mem _ (h _ (by decide +kernel)) (h _ (by decide +kernel)))
    (Subgroup.mul_mem _ (h _ (by decide +kernel)) (h _ (by decide +kernel)))

theorem tInv_sq : tInv ^ 2 = 1 := by
  decide +kernel

theorem tInv_mul_gen (i : Fin 4) : tInv * gen i = gen i * tInv := by
  revert i
  decide +kernel

@[expose] def gTest : GL Idx (ZMod 2) := ⁅reflGL (bv 4), reflGL (vec [iy 1, iy 3, iu])⁆

theorem gTest_mem : gTest ∈ LargeEvenOmega quadTen :=
  commutator_reflGL_mem (quadTen_bv 4) (by decide +kernel)

theorem gTest_mul_tInv : gTest * tInv ≠ tInv * gTest := by
  decide +kernel

theorem gTest_commute_genProd_vecCons : ∀ c₀ c₁ c₂ c₃ : ZMod 3,
    ((gTest * genProd ![c₀, c₁, c₂, c₃] : GL Idx (ZMod 2)) : Matrix Idx Idx (ZMod 2)) =
      ((genProd ![c₀, c₁, c₂, c₃] * gTest : GL Idx (ZMod 2)) : Matrix Idx Idx (ZMod 2)) →
    c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0 ∧ c₃ = 0 := by
  decide +kernel

theorem eq_zero_of_gTest_commute {c : Fin 4 → ZMod 3}
    (h : gTest * genProd c = genProd c * gTest) : c = 0 := by
  have hc : ![c 0, c 1, c 2, c 3] = c := by
    ext i
    fin_cases i <;> rfl
  obtain ⟨h₀, h₁, h₂, h₃⟩ :=
    gTest_commute_genProd_vecCons (c 0) (c 1) (c 2) (c 3) (by rw [hc, h])
  ext i
  fin_cases i
  exacts [h₀, h₁, h₂, h₃]

end CFSG.StandardType.FrameRoute.OmegaTen

end
