module

public import CFSG.RankThree.SubgroupLists.MitchellIcosaGraph
import CFSG.RankThree.SubgroupLists.MitchellFourFrame

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank Module

local notation "V₄" => Fin 2 ⊕ Fin 2

local notation "⟪" x "⟫" => Units.val x

variable {K K' : Type} [Field K] [Field K']

theorem commute_units_of_mem_closure_pair {R : Type*} [Ring R] {x y h : Rˣ} {a : R}
    (hx : Commute (x : R) a) (hy : Commute (y : R) a) (hh : h ∈ Subgroup.closure {x, y}) :
    Commute (h : R) a := by
  induction hh using Subgroup.closure_induction with
  | mem g hg => rcases hg with rfl | rfl <;> assumption
  | one => exact Commute.one_left a
  | mul g₁ g₂ _ _ h₁ h₂ => rw [Units.val_mul]; exact h₁.mul_left h₂
  | inv g _ hg => exact hg.units_inv_left

theorem frameMat_anticomm_tStd (φ : K →+* K') (k : GL V₄ K') {v w : Matrix V₄ V₄ K} {s : K'}
    (hv : frameMat φ k v = s • tStdMat) (hs : s ≠ 0) (hvw : v * w = -(w * v)) :
    tStdMat * frameMat φ k w = -(frameMat φ k w * tStdMat) := by
  have h := congrArg (frameMat φ k) hvw
  rw [frameMat_mul, frameMat_neg, frameMat_mul, hv, Matrix.smul_mul, Matrix.mul_smul] at h
  refine smul_right_injective _ hs ?_
  show s • (tStdMat * frameMat φ k w) = s • -(frameMat φ k w * tStdMat)
  rw [smul_neg]
  exact h

theorem mul_comm_or_neg_of_blocks (h2 : (2 : K') ≠ 0) {C W : Matrix V₄ V₄ K'}
    (hC : C * tStdMat = tStdMat * C) (hW : tStdMat * W = -(W * tStdMat))
    (hp : plusBlock C = 1 ∨ plusBlock C = -1) (hm : minusBlock C = 1 ∨ minusBlock C = -1) :
    C * W = W * C ∨ C * W = -(W * C) := by
  obtain ⟨a, ha, hpa⟩ := exists_scalar_of_eq_one_or_neg hp
  obtain ⟨b, hb, hmb⟩ := exists_scalar_of_eq_one_or_neg hm
  have hC' := eq_of_blocks h2 hC hpa hmb
  have h22 : (2 : K')⁻¹ * 2 = 1 := inv_mul_cancel₀ h2
  have h22' : (2 : K')⁻¹ * -2 = -1 := by rw [mul_neg, h22]
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · left
    have : C = 1 := by
      rw [hC']
      have : (1 : K') • ((1 : Matrix V₄ V₄ K') + tStdMat) +
          (1 : K') • ((1 : Matrix V₄ V₄ K') - tStdMat) = (2 : K') • (1 : Matrix V₄ V₄ K') := by
        module
      rw [this, smul_smul, h22, one_smul]
    rw [this, Matrix.one_mul, Matrix.mul_one]
  · right
    have : C = tStdMat := by
      rw [hC']
      have : (1 : K') • ((1 : Matrix V₄ V₄ K') + tStdMat) +
          (-1 : K') • ((1 : Matrix V₄ V₄ K') - tStdMat) = (2 : K') • tStdMat := by
        module
      rw [this, smul_smul, h22, one_smul]
    rw [this, hW]
  · right
    have : C = -tStdMat := by
      rw [hC']
      have : (-1 : K') • ((1 : Matrix V₄ V₄ K') + tStdMat) +
          (1 : K') • ((1 : Matrix V₄ V₄ K') - tStdMat) = (-2 : K') • tStdMat := by
        module
      rw [this, smul_smul, h22', neg_one_smul]
    rw [this, Matrix.neg_mul, Matrix.mul_neg, hW, neg_neg]
  · left
    have : C = -1 := by
      rw [hC']
      have : (-1 : K') • ((1 : Matrix V₄ V₄ K') + tStdMat) +
          (-1 : K') • ((1 : Matrix V₄ V₄ K') - tStdMat) = (-2 : K') • (1 : Matrix V₄ V₄ K') := by
        module
      rw [this, smul_smul, h22', neg_one_smul]
    rw [this, Matrix.neg_mul, Matrix.one_mul, Matrix.mul_neg, Matrix.mul_one]

section Graph

variable [Finite K'] {p : ℕ} [Fact p.Prime] [CharP K' p]

theorem mul_comm_or_neg_of_graph (hp5 : 5 ≤ p)
    {G : Subgroup (GL V₄ K)} (hGS : G ≤ StatedSp 2 K) (hq : CFSG.IsQuasisimple G)
    (hZ : ∀ z ∈ Subgroup.center G, (z : GL V₄ K) = 1 ∨ (z : GL V₄ K) = -1)
    (hneg : (-1 : GL V₄ K) ∈ G) (hU0 : ∀ x ∈ G, IsSqZero x → x = 1) (φ : K →+* K')
    {k : GL V₄ K'} (hk : k ∈ StatedSp 2 K') {s : K'} (hs : s ≠ 0) {v w : Matrix V₄ V₄ K}
    (hv : frameMat φ k v = s • tStdMat) (hvw : v * w = -(w * v))
    (hA5 : Nonempty (plusImage (two_ne_zero_of_charP (p := p) (by omega))
      (frameGroup φ (k * swapGL) G) ≃* alternatingGroup (Fin 5)))
    {x y : GL V₄ K} (hxG : x ∈ G) (hyG : y ∈ G)
    (hxv : (x : Matrix V₄ V₄ K) * v = v * x) (hyv : (y : Matrix V₄ V₄ K) * v = v * y)
    (hxw : (x : Matrix V₄ V₄ K) * w = w * x) (hyw : (y : Matrix V₄ V₄ K) * w = w * y)
    (hgraph : ∀ c ∈ frameGroup φ k G, c ∈ stdCent K' → ∃ h ∈ Subgroup.closure
      {frameHom φ k x, frameHom φ k y},
        plusBlock ⟪c⟫ = plusBlock ⟪h⟫ ∨ plusBlock ⟪c⟫ = -plusBlock ⟪h⟫)
    {z : GL V₄ K} (hzG : z ∈ G) (hzv : (z : Matrix V₄ V₄ K) * v = v * z) :
    (z : Matrix V₄ V₄ K) * w = w * z ∨ (z : Matrix V₄ V₄ K) * w = -(w * z) := by
  have hp2 : p ≠ 2 := by omega
  have h2 : (2 : K') ≠ 0 := two_ne_zero_of_charP hp2
  have hzC := frameHom_mem_stdCent φ hk hv hs (hGS hzG) hzv
  obtain ⟨h, hh, hzh⟩ := hgraph _ (mem_frameGroup φ k hzG) hzC
  have hh' : h ∈ (Subgroup.closure {x, y}).map (frameHom φ k) := by
    rw [MonoidHom.map_closure, Set.image_pair]
    exact hh
  obtain ⟨h₀, hh₀, rfl⟩ := Subgroup.mem_map.mp hh'
  have hh₀G : h₀ ∈ G :=
    (Subgroup.closure_le G).mpr (by rintro _ (rfl | rfl) <;> assumption) hh₀
  have hh₀v : (h₀ : Matrix V₄ V₄ K) * v = v * h₀ :=
    (commute_units_of_mem_closure_pair (hxv : Commute _ _) hyv hh₀).eq
  have hh₀w : (h₀ : Matrix V₄ V₄ K) * w = w * h₀ :=
    (commute_units_of_mem_closure_pair (hxw : Commute _ _) hyw hh₀).eq
  have hh₀iv : ((h₀⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * v = v * (h₀⁻¹ : GL V₄ K) :=
    (Commute.units_inv_left (hh₀v : Commute _ _)).eq
  have hcv : ((h₀⁻¹ * z : GL V₄ K) : Matrix V₄ V₄ K) * v = v * ((h₀⁻¹ * z : GL V₄ K) :
      Matrix V₄ V₄ K) := by
    rw [Units.val_mul]
    exact ((Commute.units_inv_left (hh₀v : Commute _ _)).mul_left (hzv : Commute _ _)).eq
  have hA := frameMat_comm_tStd φ k hv hs hh₀v
  have hAi := frameMat_comm_tStd φ k hv hs hh₀iv
  have hY := frameMat_comm_tStd φ k hv hs hzv
  have hct := frameMat_comm_tStd φ k hv hs hcv
  have h1 : plusBlock (frameMat φ k ⟪h₀⁻¹⟫) * plusBlock (frameMat φ k ⟪h₀⟫) = 1 := by
    rw [← plusBlock_mul h2 hAi hA, ← frameMat_mul, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, frameMat_one, plusBlock_one]
  have hc : plusBlock (frameMat φ k ⟪h₀⁻¹ * z⟫) =
      plusBlock (frameMat φ k ⟪h₀⁻¹⟫) * plusBlock (frameMat φ k ⟪z⟫) := by
    rw [Units.val_mul, frameMat_mul]
    exact plusBlock_mul h2 hAi hY
  simp only [coe_frameHom] at hzh
  have hcp : plusBlock (frameMat φ k ⟪h₀⁻¹ * z⟫) = 1 ∨
      plusBlock (frameMat φ k ⟪h₀⁻¹ * z⟫) = -1 := by
    rcases hzh with h' | h'
    · left
      rw [hc, h', h1]
    · right
      rw [hc, h', Matrix.mul_neg, h1]
  have hcm := minusBlock_eq_one_or_neg_of_plusBlock hp5 hGS hq hZ hneg hU0 φ hk hA5
    (G.mul_mem (G.inv_mem hh₀G) hzG) hct hcp
  have hC := mul_comm_or_neg_of_blocks h2 hct (frameMat_anticomm_tStd φ k hv hs hvw) hcp hcm
  have hAW : frameMat φ k ⟪h₀⟫ * frameMat φ k w = frameMat φ k w * frameMat φ k ⟪h₀⟫ := by
    rw [← frameMat_mul, ← frameMat_mul, hh₀w]
  have hzc : frameMat φ k ⟪z⟫ = frameMat φ k ⟪h₀⟫ * frameMat φ k ⟪h₀⁻¹ * z⟫ := by
    rw [← frameMat_mul, ← Units.val_mul, mul_inv_cancel_left]
  rcases hC with hC | hC
  · left
    refine frameMat_injective φ k ?_
    rw [frameMat_mul, frameMat_mul, hzc, Matrix.mul_assoc, hC, ← Matrix.mul_assoc, hAW,
      Matrix.mul_assoc]
  · right
    refine frameMat_injective φ k ?_
    rw [frameMat_neg, frameMat_mul, frameMat_mul, hzc, Matrix.mul_assoc, hC, Matrix.mul_neg,
      ← Matrix.mul_assoc, hAW, Matrix.mul_assoc]

end Graph

end CFSG.RankThree.SubgroupLists
