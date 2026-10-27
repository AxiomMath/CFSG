module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ParDef
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL3
public import CFSG.Quasithin.EmptyFaithful.SzN2Lin
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieLinCent

public section

namespace CFSG.Quasithin.Rk2

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X7a CFSG.QuasithinUnique.Setup.X6
  CFSG.QuasithinUnique.Vol2Native.A312L CFSG.Quasithin
open CFSG.Assembly.LowTwoRank

theorem charTwo_perfectCore {Y : Type*} [Group Y] [Finite Y] {P : Subgroup Y} (h : CharTwo P) :
    CharTwo (perfectCore P) :=
  CharTwo.of_normal h (perfectCore_le P) (perfectCore_normal P)

section Three

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem proj3_injOn_perfectCore (j : Fin 2) :
    ∀ x ∈ perfectCore (Q3 K j), ∀ y ∈ perfectCore (Q3 K j), proj 3 K x = proj 3 K y → x = y := by
  intro x hx y hy hxy
  have hz : x⁻¹ * y ∈ (proj 3 K).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
  have hzN : x⁻¹ * y ∈ perfectCore (Q3 K j) := mul_mem (inv_mem hx) hy
  have h1 := blk3_scalars j ⟨x⁻¹ * y, hzN⟩ ((ker_proj 3 K).le hz)
  exact inv_mul_eq_one.mp (congrArg Subtype.val h1)

theorem charTwo_perfectCore_Q3 (j : Fin 2) : CharTwo (perfectCore (Q3 K j)) := by
  have hP : CharTwo ((Q3 K j).map (proj 3 K)) :=
    CFSG.QuasithinUnique.B113Lie.Lin.charTwo_projStabilizer (n := 3) (by omega)
      (by have := j.isLt; omega)
  have h1 : CharTwo (perfectCore ((Q3 K j).map (proj 3 K))) := charTwo_perfectCore hP
  exact charTwo_of_equiv (perfectCoreMapEquiv (proj 3 K) (Q3 K j) (proj3_injOn_perfectCore j)).symm
    h1

theorem rank2Levi_Q3 {f : ℕ} (hf : Nat.card K = 2 ^ f) (hf2 : 2 ≤ f) (j : Fin 2) :
    Rank2Levi (Q3 K j) := by
  have hK : ∃ k : ℕ, Nat.card K = 2 ^ k := ⟨f, hf⟩
  have hK4 : ∃ s : Finset K, s.card = 4 := by
    refine exists_finset_card_four ?_
    rw [hf]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  exact ⟨K, inferInstance, inferInstance, inferInstance, f, hf, hf2, blk3 j, blk3_surjective hK4 j,
    blk3_ker_isPGroup hK j⟩

theorem rank2Levi_projQ3 {f : ℕ} (hf : Nat.card K = 2 ^ f) (hf2 : 2 ≤ f) (j : Fin 2) :
    Rank2Levi ((Q3 K j).map (proj 3 K)) := by
  have hK : ∃ k : ℕ, Nat.card K = 2 ^ k := ⟨f, hf⟩
  have hK4 : ∃ s : Finset K, s.card = 4 := by
    refine exists_finset_card_four ?_
    rw [hf]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  let eN := perfectCoreMapEquiv (proj 3 K) (Q3 K j) (proj3_injOn_perfectCore j)
  refine ⟨K, inferInstance, inferInstance, inferInstance, f, hf, hf2,
    (blk3 j).comp eN.symm.toMonoidHom, (blk3_surjective hK4 j).comp eN.symm.surjective, ?_⟩
  intro z
  obtain ⟨k, hk⟩ := blk3_ker_isPGroup hK j ⟨eN.symm z.1, z.2⟩
  have h1 : (eN.symm z.1) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  refine ⟨k, Subtype.ext ?_⟩
  show z.1 ^ 2 ^ k = 1
  have : eN.symm (z.1 ^ 2 ^ k) = 1 := by rw [map_pow]; exact h1
  exact (map_eq_one_iff _ eN.symm.injective).mp this

theorem rank2Pkg_sl3 {f : ℕ} (hf : Nat.card K = 2 ^ f) (hf2 : 2 ≤ f) :
    Rank2Pkg (SpecialLinearGroup (Fin 3) K) (unitriangular 3 K) (fun j : Fin 2 => Q3 K j) where
  res := SzN2.sl3_residualOvergroupsAt ⟨f, hf⟩
  norm j := by
    rw [normalizer_unitriangular]
    exact upperTriangular_le_Q3 j
  levi j := rank2Levi_Q3 hf hf2 j
  charTwo j := charTwo_perfectCore_Q3 j

theorem rank2Pkg_proj3 {f : ℕ} (hf : Nat.card K = 2 ^ f) (hf2 : 2 ≤ f) :
    Rank2Pkg (projectiveSL 3 K) ((unitriangular 3 K).map (proj 3 K))
      (fun j : Fin 2 => (Q3 K j).map (proj 3 K)) where
  res := linear_three_residual_of_cover ⟨f, hf⟩ (proj 3 K) (proj_surjective 3 K) (ker_proj 3 K).le
  norm j := by
    have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact (normalizer_projUnitriangular (K := K) 2).le.trans
      (Subgroup.map_mono (upperTriangular_le_Q3 j))
  levi j := rank2Levi_projQ3 hf hf2 j
  charTwo j := charTwo_perfectCore
    (CFSG.QuasithinUnique.B113Lie.Lin.charTwo_projStabilizer (n := 3) (by omega)
      (by have := j.isLt; omega))

end Three

end CFSG.Quasithin.Rk2
