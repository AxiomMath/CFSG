module

public import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups
public import CFSG.RankThree.SteinbergR3EUnitaryBlockDescent

public section

namespace CFSG.RankThree.SL3RootPermuting

open Matrix CFSG.RankThree.Classical CFSG.RankThree.Classical2 CFSG.RankThree.UnitaryBlock
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (blockSL)
open scoped MatrixGroups

theorem odd_gcd_three (x : ℕ) : Odd (Nat.gcd 3 x) := by
  rcases (Nat.dvd_prime Nat.prime_three).mp (Nat.gcd_dvd_left 3 x) with h | h <;> rw [h] <;>
    decide

variable {ℓ f : ℕ} {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω]

theorem sl3_root_permuting_frobenius_fixed_split (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hk : Nat.card k = ℓ ^ f) [IsAlgClosure k Ω] (π : Equiv.Perm (Fin 3))
    (Φ : SL(3, Ω) ≃* SL(3, Ω)) (b : Fin 3 → Fin 3 → Ωˣ)
    (hΦ : ∀ (i j : Fin 3) (hij : i ≠ j) (t : Ω),
      ((Φ (Matrix.SpecialLinearGroup.transvection hij t) : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) =
        1 + single (π i) (π j) ((b i j : Ω) * t ^ ℓ ^ f)) :
    (∃ A : GL (Fin 3) Ω, ∀ X : SL(3, Ω), ((Φ X : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) =
      (A : Matrix (Fin 3) (Fin 3) Ω) * (X : Matrix (Fin 3) (Fin 3) Ω).map (· ^ ℓ ^ f) *
        (↑A⁻¹ : Matrix (Fin 3) (Fin 3) Ω)) ∧
    (∃ H : SL(3, Ω), ∀ X : SL(3, Ω), X ∈ fixSubgroup Φ ↔
      ∃ Y : SL(3, k), X = H * Matrix.SpecialLinearGroup.map (algebraMap k Ω) Y * H⁻¹) ∧
    (∃ J : SL(3, Ω), ∀ Y : SL(2, k),
      J * (blockSL Ω 2 1 (Matrix.SpecialLinearGroup.map (algebraMap k Ω) Y) : SL(3, Ω)) * J⁻¹ ∈
        fixSubgroup Φ) ∧
    Finite (fixSubgroup Φ) ∧ CFSG.IsQuasisimple (fixSubgroup Φ) ∧
    (∀ x : fixSubgroup Φ, x ∈ Subgroup.center (fixSubgroup Φ) ↔
      ∃ c : Ω, ((x : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) = scalar (Fin 3) c) ∧
    Nat.card (Subgroup.center (fixSubgroup Φ)) = Nat.gcd 3 (ℓ ^ f - 1) ∧
    Odd (Nat.card (Subgroup.center (fixSubgroup Φ))) := by
  obtain ⟨hA, ⟨H, hH⟩, hfin, hQ, hcent, hcard⟩ :=
    sln_root_permuting_frobenius_fixed_split hℓ hf hk (by norm_num) π Φ b hΦ
  refine ⟨hA, ⟨H, hH⟩, ⟨H, fun Y => (hH _).mpr ⟨blockSL k 2 1 Y, ?_⟩⟩, hfin, hQ, hcent, hcard,
    hcard ▸ odd_gcd_three _⟩
  exact congrArg (fun Z : SL(3, Ω) => H * Z * H⁻¹) (map_blockSL (algebraMap k Ω) Y).symm

theorem sl3_root_permuting_frobenius_fixed_unitary (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hk : Nat.card k = ℓ ^ f) [IsAlgClosure k Ω] (π : Equiv.Perm (Fin 3))
    (Φ : SL(3, Ω) ≃* SL(3, Ω)) (b : Fin 3 → Fin 3 → Ωˣ)
    (hΦ : ∀ (i j : Fin 3) (hij : i ≠ j) (t : Ω),
      ((Φ (Matrix.SpecialLinearGroup.transvection hij t) : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) =
        1 + single (π j) (π i) ((b i j : Ω) * t ^ ℓ ^ f)) :
    (∃ A : GL (Fin 3) Ω, ∀ X : SL(3, Ω), ((Φ X : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) =
      (A : Matrix (Fin 3) (Fin 3) Ω) * (((X : Matrix (Fin 3) (Fin 3) Ω).map (· ^ ℓ ^ f))⁻¹)ᵀ *
        (↑A⁻¹ : Matrix (Fin 3) (Fin 3) Ω)) ∧
    (∃ H : SL(3, Ω), ∀ X : SL(3, Ω), X ∈ fixSubgroup Φ ↔
      ∃ Y ∈ unitarySet (ℓ ^ f) 3, Matrix.SpecialLinearGroup.toGL X =
        Matrix.SpecialLinearGroup.toGL H * Y * (Matrix.SpecialLinearGroup.toGL H)⁻¹) ∧
    (∃ J : SL(3, Ω), ∀ Y : SL(2, k),
      J * (blockSL Ω 2 1 (Matrix.SpecialLinearGroup.map (algebraMap k Ω) Y) : SL(3, Ω)) * J⁻¹ ∈
        fixSubgroup Φ) ∧
    Finite (fixSubgroup Φ) ∧
    (2 < ℓ ^ f → CFSG.IsQuasisimple (fixSubgroup Φ) ∧
      (∀ x : fixSubgroup Φ, x ∈ Subgroup.center (fixSubgroup Φ) ↔
        ∃ c : Ω, ((x : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) = scalar (Fin 3) c) ∧
      Nat.card (Subgroup.center (fixSubgroup Φ)) = Nat.gcd 3 (ℓ ^ f + 1) ∧
      Odd (Nat.card (Subgroup.center (fixSubgroup Φ)))) := by
  obtain ⟨hA, ⟨H, hH⟩, hfin, hbig, -⟩ :=
    sln_root_permuting_frobenius_fixed_unitary hℓ hf hk (by norm_num) π Φ b hΦ
  obtain ⟨C, hC⟩ := exists_blockSL_conj_mem_unitarySet (Ω := Ω) hℓ hf hk
  refine ⟨hA, ⟨H, hH⟩, ⟨H * blockSL Ω 2 1 C⁻¹, fun Y => ?_⟩, hfin, fun hq => ?_⟩
  · refine (hH _).mpr ⟨_, hC 1 Y, ?_⟩
    have hJ : (H * blockSL Ω 2 1 C⁻¹) *
        (blockSL Ω 2 1 (Matrix.SpecialLinearGroup.map (algebraMap k Ω) Y) : SL(3, Ω)) *
          (H * blockSL Ω 2 1 C⁻¹)⁻¹ =
        H * blockSL Ω 2 1 (C⁻¹ * Matrix.SpecialLinearGroup.map (algebraMap k Ω) Y * C) * H⁻¹ := by
      simp only [map_mul, map_inv]
      group
    rw [hJ, map_mul, map_mul, map_inv]
  · obtain ⟨hQ, hcent, hcard⟩ := hbig (by
      intro h32
      have : ℓ ^ f = 2 := (Prod.mk.inj h32).2
      omega)
    exact ⟨hQ, hcent, hcard, hcard ▸ odd_gcd_three _⟩

end CFSG.RankThree.SL3RootPermuting
