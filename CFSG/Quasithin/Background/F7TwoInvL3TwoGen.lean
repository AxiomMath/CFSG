module

public import CFSG.Quasithin.Background.F7TwoInvL3TwoBlock
public import CFSG.Quasithin.Background.F7TwoInvU3TwoBlock
public import CFSG.LinearAlgebra.LinearGroups.Generation
public import CFSG.Quasithin.Background.F7TwoInvL3TwoSl2

public section

namespace CFSG.Quasithin.F7Two

open Matrix CFSG.CGT.Timmesfeld75
open CFSG.LieType.Steinberg.SL (blockHom blockMat blockMat_transvection_upper
  blockMat_transvection_lower)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups commutatorElement

variable {K : Type} [Field K]

theorem coe_matrix_utriElt (c : K) : (utriElt c : Matrix (Fin 2) (Fin 2) K) = !![1, c; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [utriElt_apply_00, utriElt_apply_01, utriElt_apply_10, utriElt_apply_11]

theorem coe_matrix_ltriElt (c : K) : (ltriElt c : Matrix (Fin 2) (Fin 2) K) = !![1, 0; c, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ltriElt_apply_00, ltriElt_apply_01, ltriElt_apply_10, ltriElt_apply_11]

theorem blockHom_zero_utriElt (c : K) :
    blockHom K 0 (utriElt c) = SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) c :=
  Subtype.ext (by rw [coe_blockHom_matrix, coe_matrix_utriElt, blockMat_transvection_upper]; rfl)

theorem blockHom_zero_ltriElt (c : K) :
    blockHom K 0 (ltriElt c) = SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) c :=
  Subtype.ext (by rw [coe_blockHom_matrix, coe_matrix_ltriElt, blockMat_transvection_lower]; rfl)

theorem blockHom_one_utriElt (c : K) :
    blockHom K 1 (utriElt c) = SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) c :=
  Subtype.ext (by rw [coe_blockHom_matrix, coe_matrix_utriElt, blockMat_transvection_upper]; rfl)

theorem blockHom_one_ltriElt (c : K) :
    blockHom K 1 (ltriElt c) = SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) c :=
  Subtype.ext (by rw [coe_blockHom_matrix, coe_matrix_ltriElt, blockMat_transvection_lower]; rfl)

theorem commutatorElement_mem_of_mem {G : Type*} [Group G] {H : Subgroup G} {x y : G} (hx : x ∈ H)
    (hy : y ∈ H) : ⁅x, y⁆ ∈ H := by
  rw [commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx)) (H.inv_mem hy)

theorem eq_top_of_sl3_transvections {H : Subgroup (SpecialLinearGroup (Fin 3) K)}
    (h : ∀ (i j : Fin 3) (hij : i ≠ j) (c : K), SpecialLinearGroup.transvection hij c ∈ H) :
    H = ⊤ := by
  rw [eq_top_iff, ← CFSG.LinearGroups.special_linear_elementary_generation (K := K) (n := 3),
    Subgroup.closure_le]
  rintro _ ⟨i, j, hij, c, rfl⟩
  exact h i j hij c

theorem eq_top_of_adjacent_transvections {H : Subgroup (SpecialLinearGroup (Fin 3) K)}
    (h01 : ∀ c : K, SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) c ∈ H)
    (h10 : ∀ c : K, SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) c ∈ H)
    (h12 : ∀ c : K, SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) c ∈ H)
    (h21 : ∀ c : K, SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) c ∈ H) :
    H = ⊤ := by
  refine eq_top_of_sl3_transvections fun i j hij c => ?_
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact h01 c
  · have := commutatorElement_mem_of_mem (h01 c) (h12 1)
    rwa [SpecialLinearGroup.commutatorElement_transvection (by decide) (by decide) hij,
      mul_one] at this
  · exact h10 c
  · exact absurd rfl hij
  · exact h12 c
  · have := commutatorElement_mem_of_mem (h21 1) (h10 c)
    rwa [SpecialLinearGroup.commutatorElement_transvection (by decide) (by decide) hij,
      one_mul] at this
  · exact h21 c
  · exact absurd rfl hij

theorem invAutGen_of_transvections {α : MulAut (projectiveSL 3 K)}
    (h : ∀ (i j : Fin 3) (hij : i ≠ j) (c : K),
      proj 3 K (SpecialLinearGroup.transvection hij c) ∈ Subgroup.closure (invXiAut α)) :
    InvAutGen (projectiveSL 3 K) α := by
  have htop := eq_top_of_sl3_transvections (H := (Subgroup.closure (invXiAut α)).comap (proj 3 K)) h
  rw [invAutGen_iff_closure_invXiAut, eq_top_iff]
  intro x _
  obtain ⟨g, rfl⟩ := proj_surjective 3 K x
  have hg : g ∈ (Subgroup.closure (invXiAut α)).comap (proj 3 K) := by
    rw [htop]
    trivial
  exact hg

theorem proj_transvection_mem_of_sl3BlockRho {S : Subgroup (projectiveSL 3 K)} {i : Fin 2}
    (hS : (sl3BlockRho K i).range ≤ S) {x : SpecialLinearGroup (Fin 3) K} {g : SL(2, K)}
    (hx : blockHom K i g = x) : proj 3 K x ∈ S :=
  hS ⟨g, by rw [sl3BlockRho_apply, hx]⟩

theorem invAutGen_of_block_ranges {α : MulAut (projectiveSL 3 K)}
    (h0 : (sl3BlockRho K 0).range ≤ Subgroup.closure (invXiAut α))
    (h1 : (sl3BlockRho K 1).range ≤ Subgroup.closure (invXiAut α)) :
    InvAutGen (projectiveSL 3 K) α := by
  refine invAutGen_of_transvections fun i j hij c => ?_
  have key := eq_top_of_adjacent_transvections
    (H := (Subgroup.closure (invXiAut α)).comap (proj 3 K))
    (fun c => proj_transvection_mem_of_sl3BlockRho h0 (blockHom_zero_utriElt c))
    (fun c => proj_transvection_mem_of_sl3BlockRho h0 (blockHom_zero_ltriElt c))
    (fun c => proj_transvection_mem_of_sl3BlockRho h1 (blockHom_one_utriElt c))
    (fun c => proj_transvection_mem_of_sl3BlockRho h1 (blockHom_one_ltriElt c))
  have hg : SpecialLinearGroup.transvection hij c ∈
      (Subgroup.closure (invXiAut α)).comap (proj 3 K) := by
    rw [key]
    trivial
  exact hg

theorem invAutGen_of_blocks [Finite K] (hK : ∃ f : ℕ, 2 ≤ f ∧ Nat.card K = 2 ^ f)
    {α : MulAut (projectiveSL 3 K)} {β : MulAut SL(2, K)} (hβ2 : β * β = 1) (hβ1 : β ≠ 1)
    (hα : ∀ (i : Fin 2) (g : SL(2, K)), α (sl3BlockRho K i g) = sl3BlockRho K i (β g)) :
    InvAutGen (projectiveSL 3 K) α :=
  invAutGen_of_block_ranges
    (range_le_closure_invXiAut (sl3BlockRho K 0) (sl3BlockRho_injective 0) (hα 0)
      (invAutGen_sl2_involution hK β hβ2 hβ1))
    (range_le_closure_invXiAut (sl3BlockRho K 1) (sl3BlockRho_injective 1) (hα 1)
      (invAutGen_sl2_involution hK β hβ2 hβ1))

end CFSG.Quasithin.F7Two
