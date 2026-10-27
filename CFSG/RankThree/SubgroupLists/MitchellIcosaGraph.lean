module

public import CFSG.RankThree.SubgroupLists.MitchellFrameBar
public import CFSG.RankThree.SubgroupLists.MitchellPlusImage
import CFSG.RankThree.SubgroupLists.MitchellDicksonTwo
import CFSG.RankThree.SubgroupLists.MitchellFourFrame

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank Module
open scoped MatrixGroups

local notation "V₄" => Fin 2 ⊕ Fin 2

local notation "⟪" x "⟫" => Units.val x

variable {K K' : Type} [Field K] [Field K']

theorem plusBlock_frameMat_mul_pow (h2 : (2 : K') ≠ 0) (φ : K →+* K') (k : GL V₄ K')
    {x y : GL V₄ K} (hx : frameHom φ k x ∈ stdCent K') (hy : frameHom φ k y ∈ stdCent K')
    (j : ℕ) : plusBlock (frameMat φ k ⟪x * y ^ j⟫) =
      plusBlock (frameMat φ k ⟪x⟫) * plusBlock (frameMat φ k ⟪y⟫) ^ j := by
  have hx' := (mem_stdCent.mp hx).2
  have hy' := (mem_stdCent.mp hy).2
  rw [coe_frameHom] at hx' hy'
  rw [Units.val_mul, frameMat_mul, frameMat_pow, plusBlock_mul_of_left h2 hx',
    plusBlock_pow h2 hy']

theorem exists_scalar_of_eq_one_or_neg {A : Matrix (Fin 2) (Fin 2) K'} (h : A = 1 ∨ A = -1) :
    ∃ e : K', (e = 1 ∨ e = -1) ∧ A = e • 1 := by
  rcases h with h | h
  · exact ⟨1, Or.inl rfl, by rw [h, one_smul]⟩
  · exact ⟨-1, Or.inr rfl, by rw [h, neg_one_smul]⟩

theorem neg_pow_ne {D : Matrix (Fin 2) (Fin 2) K'} {j : ℕ} (h : D ^ j ≠ 1 ∧ D ^ j ≠ -1) :
    (-D) ^ j ≠ 1 ∧ (-D) ^ j ≠ -1 := by
  rw [neg_pow]
  rcases neg_one_pow_eq_or (Matrix (Fin 2) (Fin 2) K') j with e | e <;> rw [e]
  · simpa using h
  · rw [neg_one_mul]
    exact ⟨fun h' => h.2 (neg_eq_iff_eq_neg.mp h'),
      fun h' => h.1 (neg_eq_iff_eq_neg.mp h' ▸ neg_neg _)⟩

section Frame

variable [Finite K'] {p : ℕ} [Fact p.Prime] [CharP K' p]

theorem false_of_relOrder_ten (hp2 : p ≠ 2) {G : Subgroup (GL V₄ K)}
    (hGS : G ≤ StatedSp 2 K) (hq : CFSG.IsQuasisimple G)
    (hZ : ∀ z ∈ Subgroup.center G, (z : GL V₄ K) = 1 ∨ (z : GL V₄ K) = -1)
    (hneg : (-1 : GL V₄ K) ∈ G) (hU0 : ∀ x ∈ G, IsSqZero x → x = 1) (φ : K →+* K')
    {k : GL V₄ K'} (hk : k ∈ StatedSp 2 K') {z : GL V₄ K} (hzG : z ∈ G)
    (hzt : frameMat φ k ⟪z⟫ * tStdMat = tStdMat * frameMat φ k ⟪z⟫) {eps : K'}
    (heps : eps = 1 ∨ eps = -1) (hzm : minusBlock (frameMat φ k ⟪z⟫) = eps • 1)
    (h5 : plusBlock (frameMat φ k ⟪z⟫) ^ 5 = (-eps) • 1)
    (hD : ∀ j, 1 ≤ j → j < 5 →
      plusBlock (frameMat φ k ⟪z⟫) ^ j ≠ 1 ∧ plusBlock (frameMat φ k ⟪z⟫) ^ j ≠ -1) : False := by
  have h2 : (2 : K') ≠ 0 := two_ne_zero_of_charP hp2
  have he2 : eps * eps = 1 := by rcases heps with rfl | rfl <;> norm_num
  have he5 : eps ^ 5 = eps := by rcases heps with rfl | rfl <;> norm_num
  obtain ⟨g₀, hg₀G, hg₀⟩ := exists_frame_tStd_of_relOrder_ten h2 hneg φ k hzG hzt he2 hzm
    (by rw [he5]; exact h5)
  refine false_of_frame_oneSided hp2 hGS hq hZ hneg hU0 φ hk hg₀G hg₀ hzG hzt he2 hzm
    fun j hj1 hj6 hjz => ?_
  by_cases hj : j < 5
  · rcases heps with rfl | rfl
    · exact (hD j hj1 hj).1 (by rw [hjz, one_pow, one_smul])
    · rcases neg_one_pow_eq_or K' j with h | h
      · exact (hD j hj1 hj).1 (by rw [hjz, h, one_smul])
      · exact (hD j hj1 hj).2 (by rw [hjz, h, neg_one_smul])
  · have hj5 : j = 5 := by omega
    subst hj5
    rw [h5, he5] at hjz
    have h0 := congrFun (congrFun hjz 0) 0
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h0
    have hz : eps = 0 := by
      have : (2 : K') * eps = 0 := by linear_combination -h0
      exact (mul_eq_zero.mp this).resolve_left h2
    rw [hz] at he2
    simp at he2

theorem minusBlock_eq_one_or_neg_of_plusBlock (hp5 : 5 ≤ p)
    {G : Subgroup (GL V₄ K)} (hGS : G ≤ StatedSp 2 K) (hq : CFSG.IsQuasisimple G)
    (hZ : ∀ z ∈ Subgroup.center G, (z : GL V₄ K) = 1 ∨ (z : GL V₄ K) = -1)
    (hneg : (-1 : GL V₄ K) ∈ G) (hU0 : ∀ x ∈ G, IsSqZero x → x = 1) (φ : K →+* K')
    {k : GL V₄ K'} (hk : k ∈ StatedSp 2 K')
    (hA5 : Nonempty (plusImage (two_ne_zero_of_charP (p := p) (by omega))
      (frameGroup φ (k * swapGL) G) ≃* alternatingGroup (Fin 5)))
    {c : GL V₄ K} (hcG : c ∈ G)
    (hct : frameMat φ k ⟪c⟫ * tStdMat = tStdMat * frameMat φ k ⟪c⟫)
    (hcp : plusBlock (frameMat φ k ⟪c⟫) = 1 ∨ plusBlock (frameMat φ k ⟪c⟫) = -1) :
    minusBlock (frameMat φ k ⟪c⟫) = 1 ∨ minusBlock (frameMat φ k ⟪c⟫) = -1 := by
  have hp2 : p ≠ 2 := by omega
  have h2 : (2 : K') ≠ 0 := two_ne_zero_of_charP hp2
  have hk' : k * swapGL ∈ StatedSp 2 K' := mul_mem hk swapGL_mem
  set X : Subgroup (GL V₄ K) := G ⊓ (stdCent K').comap (frameHom φ k) with hXd
  have hXG : ∀ g ∈ X, g ∈ G := fun g hg => (Subgroup.mem_inf.mp hg).1
  have hX : ∀ g ∈ X, frameHom φ k g ∈ stdCent K' := fun g hg => (Subgroup.mem_inf.mp hg).2
  have hX' : ∀ g ∈ X, frameHom φ (k * swapGL) g ∈ stdCent K' := fun g hg =>
    (frameHom_swap_mem_stdCent_iff φ hk hGS (hXG g hg)).mpr (hX g hg)
  have hcX : c ∈ X := Subgroup.mem_inf.mpr ⟨hcG, mem_stdCent.mpr
    ⟨frameHom_mem_statedSp φ hk (hGS hcG), by rw [coe_frameHom]; exact hct⟩⟩
  have hc' : ∀ g ∈ X, frameMat φ (k * swapGL) ⟪g⟫ * tStdMat =
      tStdMat * frameMat φ (k * swapGL) ⟪g⟫ := fun g hg => by
    have := (mem_stdCent.mp (hX' g hg)).2
    rwa [coe_frameHom] at this
  have hrange : (framePlusBar h2 φ (k * swapGL) X hX').range =
      plusImage h2 (frameGroup φ (k * swapGL) G) := by
    ext z
    constructor
    · rintro ⟨g, rfl⟩
      exact (plusBar h2 (mem_frameGroup φ (k * swapGL) (hXG g g.2)) (hX' g g.2)).2
    · intro hz
      obtain ⟨h, ⟨g, hgG, rfl⟩, hC, rfl⟩ := exists_mem_of_mem_plusImage h2 hz
      exact ⟨⟨g, Subgroup.mem_inf.mpr ⟨hgG,
        (frameHom_swap_mem_stdCent_iff φ hk hGS hgG).mp hC⟩⟩, rfl⟩
  obtain ⟨e⟩ := hA5
  rcases map_ker_eq_bot_or_orders (framePlusBar h2 φ k X hX) (framePlusBar h2 φ (k * swapGL) X hX')
    ((MulEquiv.subgroupCongr hrange).trans e) with hker | ⟨⟨a, haK, hao⟩, ⟨b, hbK, hbo⟩⟩
  ·
    have h1 := (framePlusBar_eq_one_iff h2 φ (k * swapGL) hX' ⟨c, hcX⟩).mp
      (hker ⟨c, hcX⟩ ((framePlusBar_eq_one_iff h2 φ k hX ⟨c, hcX⟩).mpr hcp))
    simpa only [plusBlock_frameMat_swap] using h1
  · exfalso
    have hDa5 := (framePlusBar_pow_eq_one_iff h2 φ (k * swapGL) hX' a 5).mp
      (by simpa [hao] using pow_orderOf_eq_one (framePlusBar h2 φ (k * swapGL) X hX' a))
    have hDaj : ∀ j, 1 ≤ j → j < 5 →
        plusBlock (frameMat φ (k * swapGL) ⟪(a : GL V₄ K)⟫) ^ j ≠ 1 ∧
          plusBlock (frameMat φ (k * swapGL) ⟪(a : GL V₄ K)⟫) ^ j ≠ -1 := fun j hj1 hj5 => by
      have := pow_ne_one_of_lt_orderOf (x := framePlusBar h2 φ (k * swapGL) X hX' a) (n := j)
        (by omega) (by rw [hao]; exact hj5)
      rw [Ne, framePlusBar_pow_eq_one_iff] at this
      exact not_or.mp this
    have hDb2 := (framePlusBar_pow_eq_one_iff h2 φ (k * swapGL) hX' b 2).mp
      (by simpa [hbo] using pow_orderOf_eq_one (framePlusBar h2 φ (k * swapGL) X hX' b))
    have hDb1 : plusBlock (frameMat φ (k * swapGL) ⟪(b : GL V₄ K)⟫) ≠ 1 ∧
        plusBlock (frameMat φ (k * swapGL) ⟪(b : GL V₄ K)⟫) ≠ -1 := by
      have := pow_ne_one_of_lt_orderOf (x := framePlusBar h2 φ (k * swapGL) X hX' b) (n := 1)
        (by omega) (by rw [hbo]; omega)
      rw [Ne, framePlusBar_pow_eq_one_iff, pow_one] at this
      exact not_or.mp this
    have hdet : (plusBlock (frameMat φ (k * swapGL) ⟪(b : GL V₄ K)⟫)).det = 1 := by
      have := det_plusBlock h2 (mem_stdCent.mp (hX' b b.2)).1 (mem_stdCent.mp (hX' b b.2)).2
      rwa [coe_frameHom] at this
    have hDb : plusBlock (frameMat φ (k * swapGL) ⟪(b : GL V₄ K)⟫) *
        plusBlock (frameMat φ (k * swapGL) ⟪(b : GL V₄ K)⟫) = -1 := by
      rw [← pow_two]
      rcases hDb2 with h | h
      · rcases eq_one_or_neg_of_mul_self h2 hdet (by rwa [pow_two] at h) with h' | h'
        · exact absurd h' hDb1.1
        · exact absurd h' hDb1.2
      · exact h
    obtain ⟨ea, hea, haA⟩ := exists_scalar_of_eq_one_or_neg
      ((framePlusBar_eq_one_iff h2 φ k hX a).mp (MonoidHom.mem_ker.mp haK))
    obtain ⟨eb, heb, hbA⟩ := exists_scalar_of_eq_one_or_neg
      ((framePlusBar_eq_one_iff h2 φ k hX b).mp (MonoidHom.mem_ker.mp hbK))
    obtain ⟨da, hda, haD⟩ := exists_scalar_of_eq_one_or_neg hDa5
    have heb2 : eb ^ 2 = 1 := by rcases heb with rfl | rfl <;> norm_num
    have key : ∀ z : GL V₄ K, z ∈ X → ∀ eps : K', (eps = 1 ∨ eps = -1) →
        plusBlock (frameMat φ k ⟪z⟫) = eps • 1 →
        plusBlock (frameMat φ (k * swapGL) ⟪z⟫) ^ 5 = (-eps) • 1 →
        (∀ j, 1 ≤ j → j < 5 → plusBlock (frameMat φ (k * swapGL) ⟪z⟫) ^ j ≠ 1 ∧
          plusBlock (frameMat φ (k * swapGL) ⟪z⟫) ^ j ≠ -1) → False := by
      intro z hz eps heps hA h5 hj
      exact false_of_relOrder_ten hp2 hGS hq hZ hneg hU0 φ hk' (hXG z hz) (hc' z hz) heps
        (by rw [minusBlock_frameMat_swap, hA]) h5 hj
    have hcase : da = -ea ∨ da = ea := by
      rcases hea with rfl | rfl <;> rcases hda with rfl | rfl <;> simp
    rcases hcase with h | h
    ·
      exact key a a.2 ea hea haA (by rw [haD, h]) hDaj
    ·
      have hz : (a : GL V₄ K) * (b : GL V₄ K) ^ 2 ∈ X := X.mul_mem a.2 (X.pow_mem b.2 2)
      have hDz : plusBlock (frameMat φ (k * swapGL) ⟪(a : GL V₄ K) * (b : GL V₄ K) ^ 2⟫) =
          -plusBlock (frameMat φ (k * swapGL) ⟪(a : GL V₄ K)⟫) := by
        rw [plusBlock_frameMat_mul_pow h2 φ _ (hX' a a.2) (hX' b b.2), pow_two, hDb, mul_neg_one]
      refine key _ hz ea hea ?_ ?_ ?_
      · rw [plusBlock_frameMat_mul_pow h2 φ k (hX a a.2) (hX b b.2), haA, hbA, smul_pow, one_pow,
          heb2, one_smul, mul_one]
      · rw [hDz, Odd.neg_pow (by decide), haD, h, neg_smul]
      · intro j hj1 hj5
        rw [hDz]
        exact neg_pow_ne (hDaj j hj1 hj5)

end Frame

end CFSG.RankThree.SubgroupLists
