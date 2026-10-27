module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CosetInvolutionCount
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-! # Conjugation invariance of involution coset fibers -/

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-- Conjugating a right coset by an element of the subgroup preserves the
number of involutions in that coset. -/
public theorem involution_coset_fiber_card_conjugate
    {G : Type u} [Group G] [Finite G]
    (M : Subgroup G) {g y : G} (hgM : g ∈ M) :
    Nat.card {x : G // IsInvolution x ∧
      x ∈ (M : Set G) * ({y} : Set G)} =
    Nat.card {x : G // IsInvolution x ∧
      x ∈ (M : Set G) * ({g * y * g⁻¹} : Set G)} := by
  classical
  let cg : G ≃* G := MulAut.conj g
  have hcgM {x : G} (hx : x ∈ M) : cg x ∈ M := by
    change g * x * g⁻¹ ∈ M
    exact M.mul_mem (M.mul_mem hgM hx) (M.inv_mem hgM)
  have hcginvM {x : G} (hx : x ∈ M) : cg.symm x ∈ M := by
    have hginvM : g⁻¹ ∈ M := M.inv_mem hgM
    rw [show cg.symm x = g⁻¹ * x * g by
      simp [cg, MulAut.conj_symm_apply]]
    exact M.mul_mem (M.mul_mem hginvM hx) hgM
  let e : {x : G // IsInvolution x ∧
        x ∈ (M : Set G) * ({y} : Set G)} ≃
      {x : G // IsInvolution x ∧
        x ∈ (M : Set G) * ({g * y * g⁻¹} : Set G)} :=
    { toFun := fun x => ⟨cg x.1, by
        constructor
        · constructor
          · intro hone
            apply x.2.1.1
            apply cg.injective
            simpa using hone
          · calc
              (cg x.1) ^ 2 = cg (x.1 ^ 2) := by
                simp only [pow_two, map_mul]
              _ = 1 := by rw [x.2.1.2]; simp
        · rcases Set.mem_mul.mp x.2.2 with ⟨a, ha, z, hz, hax⟩
          have hzy : z = y := by simpa using hz
          refine Set.mem_mul.mpr ⟨cg a, hcgM ha,
            g * y * g⁻¹, by simp, ?_⟩
          change cg a * cg y = cg x.1
          have hay : a * y = x.1 := by
            calc
              a * y = a * z := by rw [hzy]
              _ = x.1 := hax
          calc
            cg a * cg y = cg (a * y) := (cg.map_mul a y).symm
            _ = cg x.1 := congrArg cg hay⟩
      invFun := fun x => ⟨cg.symm x.1, by
        constructor
        · constructor
          · intro hone
            apply x.2.1.1
            apply cg.symm.injective
            simpa using hone
          · calc
              (cg.symm x.1) ^ 2 = cg.symm (x.1 ^ 2) := by
                simp only [pow_two, map_mul]
              _ = 1 := by rw [x.2.1.2]; simp
        · rcases Set.mem_mul.mp x.2.2 with ⟨a, ha, z, hz, hax⟩
          have hzy : z = g * y * g⁻¹ := by simpa using hz
          refine Set.mem_mul.mpr ⟨cg.symm a, hcginvM ha, y, by simp, ?_⟩
          have hay : a * cg y = x.1 := by
            calc
              a * cg y = a * (g * y * g⁻¹) := by rfl
              _ = a * z := by rw [hzy]
              _ = x.1 := hax
          calc
            cg.symm a * y = cg.symm a * cg.symm (cg y) := by simp
            _ = cg.symm (a * cg y) := (cg.symm.map_mul a (cg y)).symm
            _ = cg.symm x.1 := congrArg cg.symm hay⟩
      left_inv := by
        intro x
        apply Subtype.ext
        exact cg.symm_apply_apply x.1
      right_inv := by
        intro x
        apply Subtype.ext
        exact cg.apply_symm_apply x.1 }
  exact Nat.card_congr e

end CFSG.GorensteinWalter
