module

public import CFSG.Quasithin.AppendixH.H9.H92.RadHyperplane
public import CFSG.Quasithin.AppendixH.H9.H92.RadCard.NatCardSubmodule

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

theorem radV1_apply_pairVec_natural {n : ℕ} {U : Subgroup (PairN n)} {g : MulAut (PairN n)}
    (hg : g ∈ RadV1 n U) (a : Fin n → ZMod 2) :
    ∃ e ∈ v1Space n U, g (pairVec a 0) = pairVec (a + e) 0 := by
  obtain ⟨B, hB, rfl⟩ := hg
  refine ⟨((B : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) *ᵥ a, hB.1 a, ?_⟩
  rw [pairActN_pairVec, Matrix.mulVec_zero, Matrix.sub_mulVec, Matrix.one_mulVec]
  congr 1
  abel

theorem radV1_apply_pairVec_dual {n : ℕ} {U : Subgroup (PairN n)} {g : MulAut (PairN n)}
    (hg : g ∈ RadV1 n U) (b : Fin n → ZMod 2) :
    ∃ e ∈ dotPerp n (v1Space n U), g (pairVec 0 b) = pairVec 0 (b + e) := by
  obtain ⟨B, hB, rfl⟩ := hg
  have hN := transpose_mem_radNil n (v1Space n U) _
    ((mem_radMat_iff_sub_mem_radNil _).1 (inv_mem hB))
  refine ⟨(((B⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) - 1)ᵀ *ᵥ b,
    hN.1 b, ?_⟩
  rw [pairActN_pairVec, Matrix.mulVec_zero, dualGLn_val, Matrix.transpose_sub,
    Matrix.transpose_one, Matrix.sub_mulVec, Matrix.one_mulVec]
  congr 1
  abel

theorem ncard_image_submodule_le_two_pow_finrank {n : ℕ} {β : Type*}
    (D : Submodule (ZMod 2) (Fin n → ZMod 2)) (f : (Fin n → ZMod 2) → β) :
    (f '' (D : Set (Fin n → ZMod 2))).ncard ≤ 2 ^ Module.finrank (ZMod 2) D := by
  refine (Set.ncard_image_le (Set.toFinite _)).trans ?_
  rw [← natCard_submodule_zmod_two, ← Nat.card_coe_set_eq]
  rfl

end CFSG.ASVolI.ChH
