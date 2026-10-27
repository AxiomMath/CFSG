module

public import CFSG.RankThree.SteinbergR3EUnitaryBlockDescent
public import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG.RankThree.Classical2 CFSG.RankThree.UnitaryBlock
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (blockSL)
open scoped MatrixGroups

variable {ℓ f : ℕ} {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω]

theorem sln_fixed_contains_block_split (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hk : Nat.card k = ℓ ^ f) [IsAlgClosure k Ω] {m : ℕ} (hm : 1 ≤ m)
    (π : Equiv.Perm (Fin (2 + m))) (Φ : SL(2 + m, Ω) ≃* SL(2 + m, Ω))
    (b : Fin (2 + m) → Fin (2 + m) → Ωˣ)
    (hΦ : ∀ (i j : Fin (2 + m)) (hij : i ≠ j) (t : Ω),
      ((Φ (Matrix.SpecialLinearGroup.transvection hij t) : SL(2 + m, Ω)) :
        Matrix (Fin (2 + m)) (Fin (2 + m)) Ω) =
          1 + single (π i) (π j) ((b i j : Ω) * t ^ ℓ ^ f)) :
    ∃ J : SL(2 + m, Ω), ∀ Y : SL(2, k),
      J * blockSL Ω 2 m (Matrix.SpecialLinearGroup.map (algebraMap k Ω) Y) * J⁻¹ ∈
        fixSubgroup Φ := by
  obtain ⟨-, ⟨H, hH⟩, -, -, -, -⟩ :=
    sln_root_permuting_frobenius_fixed_split hℓ hf hk (by omega) π Φ b hΦ
  refine ⟨H, fun Y => (hH _).mpr ⟨blockSL k 2 m Y, ?_⟩⟩
  exact congrArg (fun Z : SL(2 + m, Ω) => H * Z * H⁻¹) (map_blockSL (algebraMap k Ω) Y).symm

theorem sln_fixed_contains_block_unitary (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hk : Nat.card k = ℓ ^ f) [IsAlgClosure k Ω] {m : ℕ} (hm : 1 ≤ m)
    (π : Equiv.Perm (Fin (2 + m))) (Φ : SL(2 + m, Ω) ≃* SL(2 + m, Ω))
    (b : Fin (2 + m) → Fin (2 + m) → Ωˣ)
    (hΦ : ∀ (i j : Fin (2 + m)) (hij : i ≠ j) (t : Ω),
      ((Φ (Matrix.SpecialLinearGroup.transvection hij t) : SL(2 + m, Ω)) :
        Matrix (Fin (2 + m)) (Fin (2 + m)) Ω) =
          1 + single (π j) (π i) ((b i j : Ω) * t ^ ℓ ^ f)) :
    ∃ J : SL(2 + m, Ω), ∀ Y : SL(2, k),
      J * blockSL Ω 2 m (Matrix.SpecialLinearGroup.map (algebraMap k Ω) Y) * J⁻¹ ∈
        fixSubgroup Φ := by
  obtain ⟨-, ⟨H, hH⟩, -, -, -⟩ :=
    sln_root_permuting_frobenius_fixed_unitary hℓ hf hk (by omega) π Φ b hΦ
  obtain ⟨C, hC⟩ := exists_blockSL_conj_mem_unitarySet (Ω := Ω) hℓ hf hk
  refine ⟨H * blockSL Ω 2 m C⁻¹, fun Y => ?_⟩
  refine (hH _).mpr ⟨_, hC m Y, ?_⟩
  have hJ : (H * blockSL Ω 2 m C⁻¹) *
      (blockSL Ω 2 m (Matrix.SpecialLinearGroup.map (algebraMap k Ω) Y) : SL(2 + m, Ω)) *
        (H * blockSL Ω 2 m C⁻¹)⁻¹ =
      H * blockSL Ω 2 m (C⁻¹ * Matrix.SpecialLinearGroup.map (algebraMap k Ω) Y * C) * H⁻¹ := by
    simp only [map_mul, map_inv]
    group
  rw [hJ, map_mul, map_mul, map_inv]

end CFSG.RankThree.PartOne.KE
