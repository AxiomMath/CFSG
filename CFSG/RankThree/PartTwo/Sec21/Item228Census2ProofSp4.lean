module

public import CFSG.RankThree.PartTwo.Sec21.Item228CensusProofSplit
public import CFSG.RankThree.PartTwo.Sec21.Item228Census2ProofTools
public import CFSG.RankThree.PartTwo.Sec21.Item228Census2ProofSp4Lin
public import CFSG.RankThree.PartTwo.Sec21.Item228CensusProofCharThree

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSp)
open CFSG.Assembly.LowTwoRank (StatedSp StatedProj StatedScalars)
open Matrix

namespace Item228Census2Proof

variable {K : Type} [Field K]

theorem sympJ_mul_self (n : ℕ) :
    (fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
      fromBlocks 0 1 (-1) 0 = -1 := by
  rw [fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]
  simp

theorem sympJ_nondegenerate {n : ℕ} (w : Fin n ⊕ Fin n → K)
    (h : ∀ v, Matrix.toBilin' (fromBlocks 0 1 (-1) 0) v w = 0) : w = 0 := by
  have hJw : (fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ w = 0 := by
    funext i
    have := h (Pi.single i 1)
    rw [Matrix.toBilin'_apply'] at this
    simpa using this
  have hw : w = -((fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ
      ((fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ w)) := by
    rw [mulVec_mulVec, sympJ_mul_self, neg_mulVec, one_mulVec, neg_neg]
  rw [hw, hJw, mulVec_zero, neg_zero]

theorem sympJ_isometry {n : ℕ} {A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (hA : Aᵀ * fromBlocks 0 1 (-1) 0 * A = fromBlocks 0 1 (-1) 0) (v w : Fin n ⊕ Fin n → K) :
    Matrix.toBilin' (fromBlocks 0 1 (-1) 0) (Matrix.toLin' A v) (Matrix.toLin' A w) =
      Matrix.toBilin' (fromBlocks 0 1 (-1) 0) v w := by
  have h := congrArg (fun B : LinearMap.BilinForm K (Fin n ⊕ Fin n → K) => B v w)
    (Matrix.toBilin'_comp (fromBlocks 0 1 (-1) 0) A A)
  simp only [LinearMap.BilinForm.comp_apply] at h
  rw [h, hA]

theorem mem_statedSp_iff_gram {n : ℕ} {g : GL (Fin n ⊕ Fin n) K} :
    g ∈ StatedSp n K ↔ (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ * fromBlocks 0 1 (-1) 0 *
      (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = fromBlocks 0 1 (-1) 0 :=
  CFSG.Open.StatedAPI.mem_statedSp_iff

variable [Fintype K]

theorem orderOf_ne_fifteen_statedSp_two (hq5 : Fintype.card K % 5 = 2 ∨ Fintype.card K % 5 = 3)
    (hq3 : Fintype.card K % 3 ≠ 0) (g : StatedSp 2 K) : orderOf g ≠ 15 := by
  intro hg
  set M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := ((g : GL (Fin 2 ⊕ Fin 2) K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) with hM
  have hcoe : ∀ k : ℕ, (((g ^ k : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = M ^ k := by
    intro k
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]
  have hsp : ∀ k : ℕ, (M ^ k)ᵀ * fromBlocks 0 1 (-1) 0 * M ^ k = fromBlocks 0 1 (-1) 0 := by
    intro k
    rw [← hcoe]
    exact mem_statedSp_iff_gram.mp (g ^ k).2
  have hpow : ∀ k : ℕ, M ^ k = 1 ↔ g ^ k = 1 := by
    intro k
    rw [← hcoe]
    constructor
    · intro h
      exact Subtype.ext (Units.ext h)
    · intro h
      rw [h]
      rfl
  have h15 : M ^ 15 = 1 := (hpow 15).mpr (hg ▸ pow_orderOf_eq_one g)
  set φ := (Matrix.toLinAlgEquiv' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K ≃ₐ[K]
    Module.End K (Fin 2 ⊕ Fin 2 → K)) with hφ
  have hφM : ∀ k : ℕ, φ (M ^ k) = Matrix.toLin' (M ^ k) := fun k => rfl
  have hne : ∀ k : ℕ, ¬ 15 ∣ k → φ (M ^ k) ≠ 1 := by
    intro k hk h1
    have h1' : M ^ k = 1 := φ.injective (h1.trans (map_one φ).symm)
    exact hk (hg ▸ orderOf_dvd_of_pow_eq_one ((hpow k).mp h1'))
  have hV : Module.finrank K (Fin 2 ⊕ Fin 2 → K) = 4 := by simp
  refine no_commuting_isometries_three_five hV hq5 hq3
    (Matrix.toBilin' (fromBlocks 0 1 (-1) 0)) (sympJ_nondegenerate)
    (a := φ (M ^ 5)) (c := φ (M ^ 3)) (fun x y => by rw [hφM]; exact sympJ_isometry (hsp 5) x y)
    (fun x y => by rw [hφM]; exact sympJ_isometry (hsp 3) x y) ?_ ?_ (hne 5 (by norm_num)) ?_
    (hne 3 (by norm_num))
  · rw [← map_mul, ← map_mul, ← pow_add, ← pow_add, add_comm]
  · rw [← map_pow, ← pow_mul, h15, map_one]
  · rw [← map_pow, ← pow_mul, h15, map_one]

theorem noL2Normal228_statedSp_two (hq5 : Fintype.card K % 5 = 2 ∨ Fintype.card K % 5 = 3)
    (hq3 : Fintype.card K % 3 ≠ 0) (hZ : Subgroup.center (StatedSp 2 K) = ⊥) :
    NoL2Normal228 (StatedSp 2 K) := by
  refine Item22Res4Proof.noL2Normal228_of_hom (MonoidHom.id _) (by rw [MonoidHom.ker_id, hZ])
    (by rw [hZ, Subgroup.card_bot]; norm_num) fun x hx => ?_
  exact Item22Res4Proof.not_five_dvd_centralizer_of_no15
    (orderOf_ne_fifteen_statedSp_two hq5 hq3) hx

end Item228Census2Proof

open Item228Census2Proof

theorem census228Sp4Two_holds : Census228Sp4Two := by
  intro Y _ _ ⟨n, hn, hodd, ⟨eY⟩⟩
  set K := GaloisField 2 n with hKdef
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  have hK : Fintype.card K = 2 ^ n := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 2 n (by omega)]
  have h2 := two_pow_sq_mod_five hodd
  have hq5 : Fintype.card K % 5 = 2 ∨ Fintype.card K % 5 = 3 := by
    rw [hK]
    have : (2 ^ n) ^ 2 % 5 = (2 ^ n % 5) ^ 2 % 5 := Nat.pow_mod _ _ _
    have hlt : 2 ^ n % 5 < 5 := Nat.mod_lt _ (by norm_num)
    interval_cases h : 2 ^ n % 5 <;> simp_all
  have hq3 : Fintype.card K % 3 ≠ 0 := by
    rw [hK]
    intro h
    have h3 : 3 ∣ 2 ^ n := Nat.dvd_of_mod_eq_zero h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hZ : Subgroup.center (StatedSp 2 K) = ⊥ := by
    rw [CFSG.LieType.Universal.Symplectic.center_eq]
    exact CFSG.RankThree.PartOne.KFU.statedScalars_subgroupOf_statedSp_eq_bot (by norm_num)
  have e₁ : projSp 2 K ≃* StatedSp 2 K :=
    (CFSG.RankThree.PartTwo.Census.statedProjEquivProjImage (StatedSp 2 K)).symm.trans
      (CFSG.RankThree.PartOne.KFU.spEquivProj (K := K) (by norm_num)).symm
  exact Or.inr (Item228CensusProof.noL2Normal228_of_mulEquiv (eY.trans e₁)
    (noL2Normal228_statedSp_two hq5 hq3 hZ))

end CFSG.RankThree.PartTwo.Sec21
