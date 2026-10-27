module

public import CFSG.RankThree.SubgroupLists.MitchellFrame
public import CFSG.RankThree.SubgroupLists.MitchellThmEightFull
public import CFSG.RankThree.SubgroupLists.MitchellOrthogonal
import CFSG.Foundations.QuasisimpleMulEquiv
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {K K' : Type} [Field K] [Field K']

theorem frameGroup_isQuasisimple (φ : K →+* K') (k : GL V₄ K') {G : Subgroup (GL V₄ K)}
    (hq : CFSG.IsQuasisimple G) : CFSG.IsQuasisimple (frameGroup φ k G) :=
  CFSG.IsQuasisimple.of_mulEquiv (G.equivMapOfInjective _ (frameHom_injective φ k)).symm hq

theorem frameGroup_center (φ : K →+* K') (k : GL V₄ K') {G : Subgroup (GL V₄ K)}
    (hZ : ∀ z ∈ Subgroup.center G, (z : GL V₄ K) = 1 ∨ (z : GL V₄ K) = -1) :
    ∀ z ∈ Subgroup.center (frameGroup φ k G), (z : GL V₄ K') = 1 ∨ (z : GL V₄ K') = -1 := by
  rintro ⟨_, g, hgG, rfl⟩ hz
  rw [Subgroup.mem_center_iff] at hz
  have hg : (⟨g, hgG⟩ : G) ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    apply frameHom_injective φ k
    simpa using congrArg Subtype.val (hz ⟨frameHom φ k y, mem_frameGroup φ k y.2⟩)
  rcases hZ _ hg with h | h
  · left
    change frameHom φ k g = 1
    rw [show g = 1 from h, map_one]
  · right
    change frameHom φ k g = -1
    rw [show g = -1 from h, frameHom_neg_one]

theorem frameMat_mul_swap (φ : K →+* K') (k : GL V₄ K') (Z : Matrix V₄ V₄ K) :
    frameMat φ (k * swapGL) Z = swapMat * frameMat φ k Z * swapMat := by
  simp only [frameMat, _root_.mul_inv_rev, swapGL_inv, Units.val_mul, coe_swapGL, Matrix.mul_assoc]

theorem false_of_frame_oneSided [Finite K'] {p : ℕ} [Fact p.Prime]
    [CharP K' p] (hp2 : p ≠ 2) {G : Subgroup (GL V₄ K)} (hGS : G ≤ StatedSp 2 K)
    (hq : CFSG.IsQuasisimple G)
    (hZ : ∀ z ∈ Subgroup.center G, (z : GL V₄ K) = 1 ∨ (z : GL V₄ K) = -1)
    (hneg : (-1 : GL V₄ K) ∈ G) (hU0 : ∀ x ∈ G, IsSqZero x → x = 1) (φ : K →+* K')
    {k : GL V₄ K'} (hk : k ∈ StatedSp 2 K') {g₀ : GL V₄ K} (hg₀G : g₀ ∈ G)
    (hg₀ : frameMat φ k (g₀ : Matrix V₄ V₄ K) = tStdMat) {z : GL V₄ K} (hzG : z ∈ G)
    (hzt : frameMat φ k (z : Matrix V₄ V₄ K) * tStdMat =
      tStdMat * frameMat φ k (z : Matrix V₄ V₄ K))
    {eps : K'} (heps : eps * eps = 1)
    (hzm : minusBlock (frameMat φ k (z : Matrix V₄ V₄ K)) = eps • 1)
    (hord : ∀ j, 1 ≤ j → j < 6 →
      plusBlock (frameMat φ k (z : Matrix V₄ V₄ K)) ^ j ≠ eps ^ j • 1) : False := by
  have h2' : (2 : K') ≠ 0 := two_ne_zero_of_charP hp2
  have hGS' := frameGroup_le φ hk hGS
  have hU0' := frameGroup_U0 φ k hU0
  have hg₀' : frameHom φ k g₀ = tStd := Units.ext (by rw [coe_frameHom, hg₀, coe_tStd])
  have hzM := coe_frameHom φ k z
  have hNC : IsNCInv (frameHom φ k g₀) := by
    rw [hg₀']
    exact isNCInv_tStd h2'
  refine false_of_forall_cliffB_trivial hp2 hGS' (frameGroup_isQuasisimple φ k hq)
    (frameGroup_center φ k hZ) (frameGroup_neg φ k hneg) hU0'
    (t := ⟨frameHom φ k g₀, mem_frameGroup φ k hg₀G⟩) hNC (mem_frameGroup φ k hg₀G) hNC ?_
  intro w hwG hw
  rw [hg₀', coe_tStd]
  exact cliffB_tStd_of_thm_eight' p hp2 hGS' hU0' (mem_frameGroup φ k hzG) hwG hw
    (by rw [hzM]; exact hzt) heps (by rw [hzM]; exact hzm) (by rw [hzM]; exact hord)

theorem exists_frame_tStd_of_relOrder_ten (h2 : (2 : K') ≠ 0) {G : Subgroup (GL V₄ K)}
    (hneg : (-1 : GL V₄ K) ∈ G) (φ : K →+* K') (k : GL V₄ K') {z : GL V₄ K} (hzG : z ∈ G)
    (hzt : frameMat φ k (z : Matrix V₄ V₄ K) * tStdMat =
      tStdMat * frameMat φ k (z : Matrix V₄ V₄ K))
    {eps : K'} (heps : eps * eps = 1)
    (hzm : minusBlock (frameMat φ k (z : Matrix V₄ V₄ K)) = eps • 1)
    (h5 : plusBlock (frameMat φ k (z : Matrix V₄ V₄ K)) ^ 5 = (-eps ^ 5) • 1) :
    ∃ g₀ ∈ G, frameMat φ k (g₀ : Matrix V₄ V₄ K) = tStdMat := by
  set M := frameMat φ k (z : Matrix V₄ V₄ K) with hM
  have hMn : ∀ n : ℕ, M ^ n * tStdMat = tStdMat * M ^ n := fun n =>
    (Commute.pow_left (hzt : Commute M tStdMat) n).eq
  have hmin : ∀ n : ℕ, minusBlock (M ^ n) = eps ^ n • 1 := by
    intro n
    induction n with
    | zero => rw [pow_zero, pow_zero, minusBlock_one, one_smul]
    | succ n ih =>
      rw [pow_succ, minusBlock_mul h2 (hMn n), ih, hzm, smul_mul_smul_comm, one_mul, pow_succ]
  have heps5 : eps ^ 5 = eps := by
    calc eps ^ 5 = (eps * eps) * (eps * eps) * eps := by ring
      _ = eps := by rw [heps, one_mul, one_mul]
  have hp5 : plusBlock (M ^ 5) = (-eps ^ 5) • 1 := by rw [plusBlock_pow h2 hzt, h5]
  have hM5 : M ^ 5 = (-eps) • tStdMat := by
    rw [eq_of_blocks h2 (hMn 5) hp5 (hmin 5), heps5]
    calc (2 : K')⁻¹ • ((-eps) • ((1 : Matrix V₄ V₄ K') + tStdMat) + eps • (1 - tStdMat))
        = (2 : K')⁻¹ • ((2 : K') • ((-eps) • (tStdMat : Matrix V₄ V₄ K'))) := by
          congr 1
          module
      _ = (-eps) • tStdMat := by rw [smul_smul, inv_mul_cancel₀ h2, one_smul]
  have hz5 : frameMat φ k ((z ^ 5 : GL V₄ K) : Matrix V₄ V₄ K) = M ^ 5 := by
    rw [hM, ← coe_frameHom, map_pow, Units.val_pow_eq_pow_val, coe_frameHom]
  rcases mul_self_eq_one_iff.mp heps with rfl | rfl
  · refine ⟨-z ^ 5, by simpa using G.mul_mem hneg (G.pow_mem hzG 5), ?_⟩
    rw [Units.val_neg, show -((z ^ 5 : GL V₄ K) : Matrix V₄ V₄ K) =
      (-1 : K) • ((z ^ 5 : GL V₄ K) : Matrix V₄ V₄ K) by rw [neg_one_smul], frameMat_smul, hz5,
      hM5, map_neg, map_one, smul_smul]
    simp
  · exact ⟨z ^ 5, G.pow_mem hzG 5, by rw [hz5, hM5, neg_neg, one_smul]⟩

end CFSG.RankThree.SubgroupLists
