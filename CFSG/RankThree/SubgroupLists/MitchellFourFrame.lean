module

public import CFSG.RankThree.SubgroupLists.MitchellFrameGroup
public import CFSG.RankThree.SubgroupLists.MitchellFourBlocks

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {K K' : Type} [Field K] [Field K']

theorem frameMat_neg (φ : K →+* K') (k : GL V₄ K') (Z : Matrix V₄ V₄ K) :
    frameMat φ k (-Z) = -frameMat φ k Z := by
  rw [← neg_one_smul K Z, frameMat_smul, map_neg, map_one, neg_one_smul]

theorem frameMat_commutator (φ : K →+* K') (k : GL V₄ K') (x y : GL V₄ K) :
    frameMat φ k ((x * y * x⁻¹ * y⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) =
      ((frameHom φ k x * frameHom φ k y * (frameHom φ k x)⁻¹ * (frameHom φ k y)⁻¹ : GL V₄ K') :
        Matrix V₄ V₄ K') := by
  rw [← coe_frameHom, map_mul, map_mul, map_mul, map_inv, map_inv]

theorem frameMat_comm_tStd (φ : K →+* K') (k : GL V₄ K') {v : Matrix V₄ V₄ K} {s : K'}
    (hv : frameMat φ k v = s • tStdMat) (hs : s ≠ 0) {x : GL V₄ K}
    (hxv : (x : Matrix V₄ V₄ K) * v = v * (x : Matrix V₄ V₄ K)) :
    frameMat φ k (x : Matrix V₄ V₄ K) * tStdMat =
      tStdMat * frameMat φ k (x : Matrix V₄ V₄ K) := by
  have h := congrArg (frameMat φ k) hxv
  rw [frameMat_mul, frameMat_mul, hv, Matrix.mul_smul, Matrix.smul_mul] at h
  exact smul_right_injective _ hs h

theorem frameHom_mem_stdCent (φ : K →+* K') {k : GL V₄ K'} (hk : k ∈ StatedSp 2 K')
    {v : Matrix V₄ V₄ K} {s : K'} (hv : frameMat φ k v = s • tStdMat) (hs : s ≠ 0)
    {x : GL V₄ K} (hxS : x ∈ StatedSp 2 K)
    (hxv : (x : Matrix V₄ V₄ K) * v = v * (x : Matrix V₄ V₄ K)) : frameHom φ k x ∈ stdCent K' :=
  mem_stdCent.mpr ⟨frameHom_mem_statedSp φ hk hxS, by
    rw [coe_frameHom]
    exact frameMat_comm_tStd φ k hv hs hxv⟩

theorem frameMat_commutator_comm_tStd (φ : K →+* K') {k : GL V₄ K'} (hk : k ∈ StatedSp 2 K')
    {v : Matrix V₄ V₄ K} {s : K'} (hv : frameMat φ k v = s • tStdMat) (hs : s ≠ 0)
    {x y : GL V₄ K} (hxS : x ∈ StatedSp 2 K) (hyS : y ∈ StatedSp 2 K)
    (hxv : (x : Matrix V₄ V₄ K) * v = v * (x : Matrix V₄ V₄ K))
    (hyv : (y : Matrix V₄ V₄ K) * v = v * (y : Matrix V₄ V₄ K)) :
    frameMat φ k ((x * y * x⁻¹ * y⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * tStdMat =
      tStdMat * frameMat φ k ((x * y * x⁻¹ * y⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) := by
  have hxC := frameHom_mem_stdCent φ hk hv hs hxS hxv
  have hyC := frameHom_mem_stdCent φ hk hv hs hyS hyv
  rw [frameMat_commutator]
  exact (mem_stdCent.mp (mul_mem (mul_mem (mul_mem hxC hyC) (inv_mem hxC)) (inv_mem hyC))).2

private theorem sq_comm_of_comm {x : GL V₄ K} {v : Matrix V₄ V₄ K}
    (hxv : (x : Matrix V₄ V₄ K) * v = v * (x : Matrix V₄ V₄ K)) :
    ((x ^ 2 : GL V₄ K) : Matrix V₄ V₄ K) * v = v * ((x ^ 2 : GL V₄ K) : Matrix V₄ V₄ K) := by
  rw [Units.val_pow_eq_pow_val]
  exact (Commute.pow_left hxv 2).eq

theorem frameMat_swap_of (φ : K →+* K') (k : GL V₄ K') {v : Matrix V₄ V₄ K} {s : K'}
    (hv : frameMat φ k v = s • tStdMat) : frameMat φ (k * swapGL) v = (-s) • tStdMat := by
  rw [frameMat_mul_swap, hv, Matrix.mul_smul, Matrix.smul_mul, swap_conj_tStdMat, smul_neg,
    neg_smul]

theorem plusBlock_frameMat_swap (φ : K →+* K') (k : GL V₄ K') (Z : Matrix V₄ V₄ K) :
    plusBlock (frameMat φ (k * swapGL) Z) = minusBlock (frameMat φ k Z) := by
  rw [frameMat_mul_swap, plusBlock_swap_conj]

theorem minusBlock_frameMat_swap (φ : K →+* K') (k : GL V₄ K') (Z : Matrix V₄ V₄ K) :
    minusBlock (frameMat φ (k * swapGL) Z) = plusBlock (frameMat φ k Z) := by
  rw [← plusBlock_swap_conj, frameMat_mul_swap]
  simp only [← Matrix.mul_assoc, swapMat_mul_self, Matrix.one_mul]
  rw [Matrix.mul_assoc, swapMat_mul_self, Matrix.mul_one]

theorem plusBlock_frameMat_sq_commutator [Finite K'] {p : ℕ}
    [Fact p.Prime] [CharP K' p] (hp2 : p ≠ 2) {G : Subgroup (GL V₄ K)} (hGS : G ≤ StatedSp 2 K)
    (hneg : (-1 : GL V₄ K) ∈ G) (hU0 : ∀ x ∈ G, IsSqZero x → x = 1) (φ : K →+* K')
    {k : GL V₄ K'} (hk : k ∈ StatedSp 2 K') {v : Matrix V₄ V₄ K} {s : K'}
    (hv : frameMat φ k v = s • tStdMat) (hs : s ≠ 0) {x y : GL V₄ K} (hxG : x ∈ G) (hyG : y ∈ G)
    (hxv : (x : Matrix V₄ V₄ K) * v = v * (x : Matrix V₄ V₄ K))
    (hyv : (y : Matrix V₄ V₄ K) * v = v * (y : Matrix V₄ V₄ K)) (hx4 : x ^ 4 = -1)
    (hy4 : y ^ 4 = -1) :
    plusBlock (frameMat φ k ((x ^ 2 * y ^ 2 * (x ^ 2)⁻¹ * (y ^ 2)⁻¹ : GL V₄ K) :
        Matrix V₄ V₄ K)) = 1 ∨
      plusBlock (frameMat φ k ((x ^ 2 * y ^ 2 * (x ^ 2)⁻¹ * (y ^ 2)⁻¹ : GL V₄ K) :
        Matrix V₄ V₄ K)) = -1 := by
  rw [frameMat_commutator, map_pow, map_pow]
  exact plusBlock_sq_commutator_eq_one_or_neg hp2 (frameGroup_U0 φ k hU0)
    (frameGroup_neg φ k hneg) (mem_frameGroup φ k hxG)
    (frameHom_mem_stdCent φ hk hv hs (hGS hxG) hxv) (mem_frameGroup φ k hyG)
    (frameHom_mem_stdCent φ hk hv hs (hGS hyG) hyv) (by rw [← map_pow, hx4, frameHom_neg_one])
    (by rw [← map_pow, hy4, frameHom_neg_one])

theorem false_of_frame_signs [Finite K'] {p : ℕ} [Fact p.Prime]
    [CharP K' p] (hp2 : p ≠ 2) {G : Subgroup (GL V₄ K)} (hGS : G ≤ StatedSp 2 K)
    (hq : CFSG.IsQuasisimple G)
    (hZ : ∀ z ∈ Subgroup.center G, (z : GL V₄ K) = 1 ∨ (z : GL V₄ K) = -1)
    (hneg : (-1 : GL V₄ K) ∈ G) (hU0 : ∀ x ∈ G, IsSqZero x → x = 1) (φ : K →+* K')
    {k : GL V₄ K'} (hk : k ∈ StatedSp 2 K') {v : Matrix V₄ V₄ K} {s : K'}
    (hv : frameMat φ k v = s • tStdMat) (hs : s ≠ 0) {x y : GL V₄ K} (hxG : x ∈ G) (hyG : y ∈ G)
    (hxv : (x : Matrix V₄ V₄ K) * v = v * (x : Matrix V₄ V₄ K))
    (hyv : (y : Matrix V₄ V₄ K) * v = v * (y : Matrix V₄ V₄ K)) (hx4 : x ^ 4 = -1)
    (hy4 : y ^ 4 = -1)
    (hcp : plusBlock (frameMat φ k ((x ^ 2 * y ^ 2 * (x ^ 2)⁻¹ * (y ^ 2)⁻¹ : GL V₄ K) :
      Matrix V₄ V₄ K)) = -1)
    (hcm : minusBlock (frameMat φ k ((x ^ 2 * y ^ 2 * (x ^ 2)⁻¹ * (y ^ 2)⁻¹ : GL V₄ K) :
      Matrix V₄ V₄ K)) = 1) : False := by
  have h2 : (2 : K') ≠ 0 := two_ne_zero_of_charP hp2
  have hkσ : k * swapGL ∈ StatedSp 2 K' := mul_mem hk swapGL_mem
  have hvσ := frameMat_swap_of φ k hv
  have hsσ : -s ≠ 0 := neg_ne_zero.mpr hs
  have hxC := frameHom_mem_stdCent φ hk hv hs (hGS hxG) hxv
  have hyC := frameHom_mem_stdCent φ hk hv hs (hGS hyG) hyv
  have hx4' : ∀ l : GL V₄ K', frameHom φ l x ^ 4 = -1 := fun l => by
    rw [← map_pow, hx4, frameHom_neg_one]
  have hy4' : ∀ l : GL V₄ K', frameHom φ l y ^ 4 = -1 := fun l => by
    rw [← map_pow, hy4, frameHom_neg_one]
  have hwm : minusBlock (frameMat φ k ((x * y * x⁻¹ * y⁻¹ : GL V₄ K) : Matrix V₄ V₄ K)) = 1 := by
    rw [← plusBlock_frameMat_swap, frameMat_commutator]
    refine plusBlock_commutator_eq_one_of_sq h2
      (frameHom_mem_stdCent φ hkσ hvσ hsσ (hGS hxG) hxv)
      (frameHom_mem_stdCent φ hkσ hvσ hsσ (hGS hyG) hyv) (hx4' _) (hy4' _) ?_
    rw [← map_pow, ← map_pow, ← frameMat_commutator, plusBlock_frameMat_swap, hcm]
  obtain ⟨hm3, hm1, hmn1⟩ := plusBlock_commutator_cube hp2 (frameGroup_U0 φ k hU0)
    (frameGroup_neg φ k hneg) (mem_frameGroup φ k hxG) hxC (mem_frameGroup φ k hyG) hyC
    (hx4' k) (hy4' k) (by rw [← map_pow, ← map_pow, ← frameMat_commutator, hcp])
  rw [← frameMat_commutator] at hm3 hm1 hmn1
  have hcG : x ^ 2 * y ^ 2 * (x ^ 2)⁻¹ * (y ^ 2)⁻¹ ∈ G :=
    G.mul_mem (G.mul_mem (G.mul_mem (G.pow_mem hxG 2) (G.pow_mem hyG 2))
      (G.inv_mem (G.pow_mem hxG 2))) (G.inv_mem (G.pow_mem hyG 2))
  have hwG : x * y * x⁻¹ * y⁻¹ ∈ G :=
    G.mul_mem (G.mul_mem (G.mul_mem hxG hyG) (G.inv_mem hxG)) (G.inv_mem hyG)
  have hct := frameMat_commutator_comm_tStd φ hk hv hs (pow_mem (hGS hxG) 2)
    (pow_mem (hGS hyG) 2) (sq_comm_of_comm hxv) (sq_comm_of_comm hyv)
  have hwt := frameMat_commutator_comm_tStd φ hk hv hs (hGS hxG) (hGS hyG) hxv hyv
  have hc : frameMat φ k ((x ^ 2 * y ^ 2 * (x ^ 2)⁻¹ * (y ^ 2)⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) =
      -tStdMat := by
    rw [eq_of_blocks h2 hct (a := -1) (b := 1) (by rw [hcp, neg_one_smul])
      (by rw [hcm, one_smul])]
    calc _ = (2 : K')⁻¹ • ((2 : K') • -(tStdMat : Matrix V₄ V₄ K')) := by congr 1; module
      _ = -tStdMat := inv_smul_smul₀ h2 _
  have hg₀ : frameMat φ k ((-(x ^ 2 * y ^ 2 * (x ^ 2)⁻¹ * (y ^ 2)⁻¹) : GL V₄ K) :
      Matrix V₄ V₄ K) = tStdMat := by
    rw [Units.val_neg, frameMat_neg, hc, neg_neg]
  have hg₀G : -(x ^ 2 * y ^ 2 * (x ^ 2)⁻¹ * (y ^ 2)⁻¹) ∈ G := by
    rw [← neg_one_mul]
    exact G.mul_mem hneg hcG
  rcases hm3 with hm3 | hm3
  ·
    refine false_of_frame_oneSided hp2 hGS hq hZ hneg hU0 φ hk hg₀G hg₀ (G.mul_mem hcG hwG) ?_
      (eps := 1) (mul_one 1) ?_ ?_
    · rw [Units.val_mul, frameMat_mul]
      exact ((show Commute _ tStdMat from hct).mul_left (show Commute _ tStdMat from hwt)).eq
    · rw [Units.val_mul, frameMat_mul, minusBlock_mul h2 hct, hcm, hwm, one_mul, one_smul]
    · intro j hj1 hj6
      rw [one_pow, one_smul, Units.val_mul, frameMat_mul, plusBlock_mul h2 hct hwt, hcp,
        neg_one_mul]
      refine pow_ne_one_of_pow_three_eq_neg_one h2 ?_ (fun h => hmn1 (neg_eq_iff_eq_neg.mp h))
        (fun h => hm1 (neg_inj.mp h)) hj1 hj6
      rw [(show Odd 3 from ⟨1, rfl⟩).neg_pow, hm3]
  ·
    refine false_of_frame_oneSided hp2 hGS hq hZ hneg hU0 φ hk hg₀G hg₀ hwG hwt (eps := 1)
      (mul_one 1) (by rw [hwm, one_smul]) ?_
    intro j hj1 hj6
    rw [one_pow, one_smul]
    exact pow_ne_one_of_pow_three_eq_neg_one h2 hm3 hm1 hmn1 hj1 hj6

theorem sq_mul_sq_of_nonisotropic [Finite K] {p : ℕ} [Fact p.Prime]
    [CharP K p] (hp2 : p ≠ 2) {G : Subgroup (GL V₄ K)} (hGS : G ≤ StatedSp 2 K)
    (hq : CFSG.IsQuasisimple G)
    (hZ : ∀ z ∈ Subgroup.center G, (z : GL V₄ K) = 1 ∨ (z : GL V₄ K) = -1)
    (hneg : (-1 : GL V₄ K) ∈ G) (hU0 : ∀ x ∈ G, IsSqZero x → x = 1)
    {v : Matrix V₄ V₄ K} (hvM : v ∈ (cliffSpace : Submodule K _)) (hQv : cliffB v v ≠ 0)
    {x y : GL V₄ K} (hxG : x ∈ G) (hyG : y ∈ G)
    (hxv : (x : Matrix V₄ V₄ K) * v = v * (x : Matrix V₄ V₄ K))
    (hyv : (y : Matrix V₄ V₄ K) * v = v * (y : Matrix V₄ V₄ K)) (hx4 : x ^ 4 = -1)
    (hy4 : y ^ 4 = -1) :
    x ^ 2 * y ^ 2 = y ^ 2 * x ^ 2 ∨ x ^ 2 * y ^ 2 = -(y ^ 2 * x ^ 2) := by
  obtain ⟨K', iF, iFin, iCh, φ, k, s, hk, hs, hv⟩ := exists_frame hp2 hvM hQv
  have h2 : (2 : K') ≠ 0 := two_ne_zero_of_charP hp2
  have hkσ : k * swapGL ∈ StatedSp 2 K' := mul_mem hk swapGL_mem
  have hvσ := frameMat_swap_of φ k hv
  have hsσ : -s ≠ 0 := neg_ne_zero.mpr hs
  have hct := frameMat_commutator_comm_tStd φ hk hv hs (pow_mem (hGS hxG) 2)
    (pow_mem (hGS hyG) 2) (sq_comm_of_comm hxv) (sq_comm_of_comm hyv)
  have hp := plusBlock_frameMat_sq_commutator hp2 hGS hneg hU0 φ hk hv hs hxG hyG hxv hyv hx4 hy4
  have hm := plusBlock_frameMat_sq_commutator hp2 hGS hneg hU0 φ hkσ hvσ hsσ hxG hyG hxv hyv hx4
    hy4
  rw [plusBlock_frameMat_swap] at hm
  have e : x ^ 2 * y ^ 2 = x ^ 2 * y ^ 2 * (x ^ 2)⁻¹ * (y ^ 2)⁻¹ * (y ^ 2 * x ^ 2) := by group
  rcases hp with hp | hp <;> rcases hm with hm | hm
  · left
    have hc : x ^ 2 * y ^ 2 * (x ^ 2)⁻¹ * (y ^ 2)⁻¹ = 1 := by
      apply frameHom_injective φ k
      apply Units.ext
      rw [coe_frameHom, map_one, Units.val_one, eq_of_blocks h2 hct (a := 1) (b := 1)
        (by rw [hp, one_smul]) (by rw [hm, one_smul])]
      calc _ = (2 : K')⁻¹ • ((2 : K') • (1 : Matrix V₄ V₄ K')) := by congr 1; module
        _ = 1 := inv_smul_smul₀ h2 _
    rw [e, hc, one_mul]
  · exact (false_of_frame_signs hp2 hGS hq hZ hneg hU0 φ hkσ hvσ hsσ hxG hyG hxv hyv hx4 hy4
      (by rw [plusBlock_frameMat_swap, hm]) (by rw [minusBlock_frameMat_swap, hp])).elim
  · exact (false_of_frame_signs hp2 hGS hq hZ hneg hU0 φ hk hv hs hxG hyG hxv hyv hx4 hy4 hp
      hm).elim
  · right
    have hc : x ^ 2 * y ^ 2 * (x ^ 2)⁻¹ * (y ^ 2)⁻¹ = -1 := by
      apply frameHom_injective φ k
      apply Units.ext
      rw [coe_frameHom, frameHom_neg_one, Units.val_neg, Units.val_one, eq_of_blocks h2 hct
        (a := -1) (b := -1) (by rw [hp, neg_one_smul]) (by rw [hm, neg_one_smul])]
      calc _ = (2 : K')⁻¹ • ((2 : K') • (-1 : Matrix V₄ V₄ K')) := by congr 1; module
        _ = -1 := inv_smul_smul₀ h2 _
    rw [e, hc, neg_one_mul]

end CFSG.RankThree.SubgroupLists
