module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Embed
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Pairs
public import CFSG.Open.Defs

public section

namespace CFSG.StandardType.SpRootBig

open Matrix CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.Open (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)

def cmp7 : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 0, 1; 1, 0, 1; 0, 1, 0]

def blk7 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  Matrix.fromBlocks cmp7 0 0 (cmp7 ^ 6)ᵀ

theorem blk7_symp : blk7ᵀ * Matrix.fromBlocks 0 (1 : Matrix (Fin 3) (Fin 3) (ZMod 2))
    (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 * blk7 =
      Matrix.fromBlocks 0 (1 : Matrix (Fin 3) (Fin 3) (ZMod 2))
        (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 := by
  decide

theorem blk7_pow : blk7 ^ 7 = 1 := by
  decide

theorem blk7_ne : blk7 ≠ 1 := by
  decide

theorem map_gram_castHom {K : Type} [Field K] [CharP K 2] :
    (Matrix.fromBlocks (0 : Matrix (Fin 3) (Fin 3) (ZMod 2))
      (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0).map
      (ZMod.castHom (dvd_refl 2) K) =
        Matrix.fromBlocks (0 : Matrix (Fin 3) (Fin 3) K) (1 : Matrix (Fin 3) (Fin 3) K)
          (1 : Matrix (Fin 3) (Fin 3) K) 0 := by
  rw [Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _),
    Matrix.map_one _ (map_zero _) (map_one _)]

theorem blk7_map_symp {K : Type} [Field K] [CharP K 2] :
    (blk7.map (ZMod.castHom (dvd_refl 2) K))ᵀ *
        Matrix.fromBlocks (0 : Matrix (Fin 3) (Fin 3) K) (1 : Matrix (Fin 3) (Fin 3) K)
          (1 : Matrix (Fin 3) (Fin 3) K) 0 *
          blk7.map (ZMod.castHom (dvd_refl 2) K) =
      Matrix.fromBlocks (0 : Matrix (Fin 3) (Fin 3) K) (1 : Matrix (Fin 3) (Fin 3) K)
        (1 : Matrix (Fin 3) (Fin 3) K) 0 := by
  have h := congrArg (fun M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) =>
    M.map (ZMod.castHom (dvd_refl 2) K)) blk7_symp
  simp only [Matrix.map_mul, Matrix.transpose_map, map_gram_castHom] at h
  exact h

theorem gram_char_two {K : Type} [Field K] [CharP K 2] :
    CFSG.ClassicalInvolution.Models.SymplecticPairs.gram K 3 =
      Matrix.fromBlocks (0 : Matrix (Fin 3) (Fin 3) K) (1 : Matrix (Fin 3) (Fin 3) K)
        (1 : Matrix (Fin 3) (Fin 3) K) 0 := by
  have hn : (-1 : Matrix (Fin 3) (Fin 3) K) = 1 := by
    ext i j
    by_cases h : i = j
    · subst h; simp [Matrix.one_apply, CharTwo.neg_eq]
    · simp [Matrix.one_apply, h]
  unfold CFSG.ClassicalInvolution.Models.SymplecticPairs.gram
  rw [hn]

noncomputable def sp7 (K : Type) [Field K] [CharP K 2] : StatedSp 3 K :=
  ofSymplecticMat (blk7.map (ZMod.castHom (dvd_refl 2) K)) (by
    rw [gram_char_two]
    exact blk7_map_symp)

theorem mat_sp7 (K : Type) [Field K] [CharP K 2] :
    mat 3 K (sp7 K) = blk7.map (ZMod.castHom (dvd_refl 2) K) :=
  mat_ofSymplecticMat _ _

theorem orderOf_sp7 (K : Type) [Field K] [CharP K 2] : orderOf (sp7 K) = 7 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h7 : sp7 K ^ 7 = 1 := by
    apply mat_injective
    have hp : (blk7.map (ZMod.castHom (dvd_refl 2) K)) ^ 7 =
        (blk7 ^ 7).map (ZMod.castHom (dvd_refl 2) K) := by
      have h0 := map_pow (RingHom.mapMatrix (ZMod.castHom (dvd_refl 2) K)) blk7 7
      simpa only [RingHom.mapMatrix_apply] using h0.symm
    rw [map_pow, mat_sp7, hp, blk7_pow, map_one, Matrix.map_one _ (map_zero _) (map_one _)]
  have h1 : sp7 K ≠ 1 := by
    intro h
    apply blk7_ne
    apply Matrix.map_injective (ZMod.castHom (dvd_refl 2) K).injective
    dsimp only
    have hm := congrArg (mat 3 K) h
    rw [mat_sp7, map_one] at hm
    rw [hm, Matrix.map_one _ (map_zero _) (map_one _)]
  exact orderOf_eq_prime h7 h1

theorem seven_dvd_card_statedSp (K : Type) [Field K] [Finite K] [CharP K 2] {k : ℕ}
    (hk : 3 ≤ k) : 7 ∣ Nat.card (StatedSp k K) := by
  haveI : Finite (StatedSp k K) := Finite.of_injective (fun x => mat k K x) mat_injective
  have hσ : Function.Injective (Fin.castLE hk) := Fin.castLE_injective hk
  have h7 : orderOf (spEmbed (K := K) (Fin.castLE hk) hσ (sp7 K)) = 7 := by
    rw [orderOf_injective _ (spEmbed_injective hσ), orderOf_sp7]
  rw [← h7]
  exact orderOf_dvd_natCard _

end CFSG.StandardType.SpRootBig
