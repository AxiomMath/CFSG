module

import Lean
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  {f n : ℕ} {ψ : Su K 2 f n →* G}

theorem ggNSDiag_torus_le (h : GGNSLocalHyp p B Bs K f n ψ) (hd : GGActsDiagonally (p := 2) (f := f) ψ Bs) (g : Su K 2 f n)
    (hg : ∃ d : Fin n → K, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Matrix.diagonal d ∧ ∀ i, d i ^ p = 1) :
    ψ g ∈ Bs := by
  obtain ⟨d, hgd, hdp⟩ := hg
  have hcent : ψ g ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    obtain ⟨gb, hdiag, hind⟩ := hd b hb
    obtain ⟨db, hdb⟩ := hdiag
    obtain ⟨y, hy, hby⟩ := hind.2 g
    have hcomm_mat : (gb : Matrix (Fin n) (Fin n) K) * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (gb : Matrix (Fin n) (Fin n) K) := by
      rw [hdb, hgd, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      exact mul_comm _ _
    have hcomm : gb * (g : GL (Fin n) K) = (g : GL (Fin n) K) * gb := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul]
      exact hcomm_mat
    have hy_val : (y : GL (Fin n) K) = (g : GL (Fin n) K) := by
      rw [hy, hcomm]
      group
    have hy_eq : y = g := Subtype.ext hy_val
    rw [hy_eq] at hby
    have hb' : b * ψ g = ψ g * b := by
      have := congrArg (fun z => z * b) hby
      simpa [mul_assoc] using this
    exact hb'
  have hgpow : g ^ p = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hgd, Matrix.diagonal_pow]
    rw [show d ^ p = (1 : Fin n → K) by funext i; simpa using hdp i]
    simp [Matrix.diagonal_one]
  have hpow : (ψ g) ^ p = 1 := by
    rw [← map_pow, hgpow, map_one]
  exact h.bstar.2.2.2 (ψ g) hcent hpow

end CFSG.StandardType

end
