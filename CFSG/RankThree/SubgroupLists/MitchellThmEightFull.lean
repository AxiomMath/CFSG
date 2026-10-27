module

public import CFSG.RankThree.SubgroupLists.MitchellThmEightSplit
public import CFSG.RankThree.SubgroupLists.SymplecticBaseChange
public import CFSG.RankThree.SubgroupLists.MitchellQOne
public import Certificates.Certificate113
public import Certificates.Certificate43

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank Module Polynomial

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {K : Type} [Field K]

theorem exists_isSquare_map [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p] (d : K) :
    ∃ (K' : Type) (_ : Field K') (_ : Finite K') (_ : CharP K' p) (φ : K →+* K'),
      IsSquare (φ d) := by
  classical
  by_cases hsq : IsSquare d
  · exact ⟨K, inferInstance, inferInstance, inferInstance, RingHom.id K, hsq⟩
  · set f : K[X] := X ^ 2 - C d
    have hfmon : f.Monic := by simp only [f]; monicity!
    have hfdeg : f.natDegree = 2 := by simp only [f]; compute_degree!
    have hfirr : Irreducible f := by
      apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
      · rw [hfdeg]
        decide
      · intro x hx
        apply hsq
        refine ⟨x, ?_⟩
        simp only [f, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
          Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hx
        rw [← hx, pow_two]
    haveI : Fact (Irreducible f) := ⟨hfirr⟩
    haveI : Module.Finite K (AdjoinRoot f) := (AdjoinRoot.powerBasis hfmon.ne_zero).finite
    haveI : Finite (AdjoinRoot f) := Module.finite_of_finite K
    haveI : CharP (AdjoinRoot f) p :=
      charP_of_injective_algebraMap (algebraMap K (AdjoinRoot f)).injective p
    refine ⟨AdjoinRoot f, inferInstance, inferInstance, inferInstance, AdjoinRoot.of f,
      AdjoinRoot.root f, ?_⟩
    have := AdjoinRoot.eval₂_root f
    simp only [f, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C,
      sub_eq_zero] at this
    rw [← this, pow_two]

variable {K' : Type} [Field K']

theorem plusBlock_map (φ : K →+* K') (M : Matrix V₄ V₄ K) :
    plusBlock (M.map φ) = (plusBlock M).map φ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [plusBlock]

theorem minusBlock_map (φ : K →+* K') (M : Matrix V₄ V₄ K) :
    minusBlock (M.map φ) = (minusBlock M).map φ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [minusBlock]

theorem tStdMat_map (φ : K →+* K') : (tStdMat : Matrix V₄ V₄ K).map φ = tStdMat := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [tStdMat, stdSign, Matrix.diagonal]

theorem isNCInv_map (φ : K →+* K') {w : GL V₄ K} (hw : IsNCInv w) : IsNCInv (mapGL φ w) := by
  obtain ⟨hS, h2, h1, hm⟩ := hw
  refine ⟨map_mem_statedSp φ hS, by rw [← map_mul, h2, map_one], fun h => h1 ?_, fun h => hm ?_⟩
  · apply mapGL_injective φ
    rw [h, map_one]
  · apply mapGL_injective φ
    rw [h, mapGL_neg_one]

theorem minusBlock_mul_self_of_smul (h2 : (2 : K) ≠ 0) {M : Matrix V₄ V₄ K}
    (hM : M * tStdMat = tStdMat * M) {c : K} (hc : minusBlock M = c • 1) :
    minusBlock (M * M) = (c * c) • 1 := by
  rw [minusBlock_mul h2 hM, hc, Matrix.smul_mul, Matrix.one_mul, smul_smul]

variable [Finite K]

theorem cliffB_tStd_of_thm_eight' (p : ℕ) [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    {G : Subgroup (GL V₄ K)} (hGS : G ≤ StatedSp 2 K) (hU0 : ∀ x ∈ G, IsSqZero x → x = 1)
    {z w : GL V₄ K} (hzG : z ∈ G) (hwG : w ∈ G) (hw : IsNCInv w)
    (hzt : (z : Matrix V₄ V₄ K) * tStdMat = tStdMat * (z : Matrix V₄ V₄ K))
    {eps : K} (heps : eps * eps = 1) (hzm : minusBlock (z : Matrix V₄ V₄ K) = eps • 1)
    (hord : ∀ k, 1 ≤ k → k < 6 → plusBlock (z : Matrix V₄ V₄ K) ^ k ≠ eps ^ k • 1) :
    cliffB tStdMat (w : Matrix V₄ V₄ K) = 0 ∨
      cliffB tStdMat (w : Matrix V₄ V₄ K) * cliffB tStdMat (w : Matrix V₄ V₄ K) = 1 := by
  classical
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP hp2
  set Z := plusBlock (z : Matrix V₄ V₄ K) with hZ
  have hdetZ : Z.det = 1 := det_plusBlock h2 (hGS hzG) hzt
  have hCH : Z * Z = Z.trace • Z - (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [fin_two_mul_self, hdetZ, one_smul]
  set τ := Z.trace with hτ
  by_cases hd : τ * τ - 4 = 0
  ·
    exfalso
    set c : K := τ / 2 with hc
    have hτc : τ = 2 * c := by rw [hc]; field_simp
    have hcc : c * c = 1 := by
      have : (2 * c) * (2 * c) - 4 = 0 := by rw [← hτc]; exact hd
      have h4 : (4 : K) * (c * c - 1) = 0 := by linear_combination this
      have h40 : (4 : K) ≠ 0 := by
        rw [show (4 : K) = 2 * 2 by norm_num]
        exact mul_ne_zero h2 h2
      linear_combination ((mul_eq_zero.mp h4).resolve_left h40)
    set N := Z - c • (1 : Matrix (Fin 2) (Fin 2) K) with hN
    have hNN : N * N = 0 := by
      have e : N * N = Z * Z - (2 * c) • Z + (c * c) • (1 : Matrix (Fin 2) (Fin 2) K) := by
        rw [hN]
        simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
          Matrix.one_mul, Matrix.mul_one, smul_smul]
        module
      rw [e, hCH, hτc, hcc]
      module
    have hZZ : Z * Z - 1 = (2 * c) • N := by
      rw [hCH, hτc, hN, smul_sub, smul_smul, mul_assoc, hcc, mul_one]
      module
    have hZZ2 : (Z * Z - 1) * (Z * Z - 1) = 0 := by
      rw [hZZ, Matrix.smul_mul, Matrix.mul_smul, hNN, smul_zero, smul_zero]
    have hz2t : ((z * z : GL V₄ K) : Matrix V₄ V₄ K) * tStdMat =
        tStdMat * ((z * z : GL V₄ K) : Matrix V₄ V₄ K) := by
      rw [Units.val_mul]
      exact mul_comm_tStd hzt hzt
    have hX : (((z * z : GL V₄ K) : Matrix V₄ V₄ K) - 1) * tStdMat =
        tStdMat * (((z * z : GL V₄ K) : Matrix V₄ V₄ K) - 1) := by
      rw [Matrix.sub_mul, Matrix.mul_sub, hz2t, Matrix.one_mul, Matrix.mul_one]
    have hsq : IsSqZero (z * z) := by
      unfold IsSqZero
      have hp : plusBlock ((((z * z : GL V₄ K) : Matrix V₄ V₄ K) - 1) *
          (((z * z : GL V₄ K) : Matrix V₄ V₄ K) - 1)) = (0 : K) • 1 := by
        rw [plusBlock_mul_of_left h2 hX, plusBlock_sub_one, Units.val_mul,
          plusBlock_mul_of_left h2 hzt, ← hZ, hZZ2, zero_smul]
      have hm : minusBlock ((((z * z : GL V₄ K) : Matrix V₄ V₄ K) - 1) *
          (((z * z : GL V₄ K) : Matrix V₄ V₄ K) - 1)) = (0 : K) • 1 := by
        rw [minusBlock_mul h2 hX, minusBlock_sub_one, Units.val_mul,
          minusBlock_mul_self_of_smul h2 hzt hzm, heps, one_smul, sub_self, Matrix.zero_mul,
          zero_smul]
      rw [eq_of_blocks h2 (mul_comm_tStd hX hX) hp hm]
      simp
    have hz1 := hU0 _ (G.mul_mem hzG hzG) hsq
    apply hord 2 (by norm_num) (by norm_num)
    have h1 : plusBlock (((z * z : GL V₄ K) : Matrix V₄ V₄ K)) = 1 := by
      rw [hz1, Units.val_one, plusBlock_one]
    rw [Units.val_mul, plusBlock_mul_of_left h2 hzt, ← hZ] at h1
    rw [pow_two, h1, pow_two, heps, one_smul]
  ·
    obtain ⟨K₁, iF, iFin, iCh, φ, s, hs⟩ := exists_isSquare_map (p := p) (τ * τ - 4)
    have h2' : (2 : K₁) ≠ 0 := two_ne_zero_of_charP hp2
    have hs' : φ τ * φ τ - 4 = s * s := by
      rw [← hs, map_sub, map_mul, map_ofNat]
    have hs0 : s ≠ 0 := by
      rintro rfl
      apply hd
      apply φ.injective
      rw [hs, mul_zero, map_zero]
    set Z' := Z.map φ with hZ'
    set lam : K₁ := (φ τ + s) / 2 with hlam
    set lam' : K₁ := (φ τ - s) / 2 with hlam'
    have hll : lam * lam' = 1 := by
      rw [hlam, hlam']
      field_simp
      linear_combination hs'
    have hne : lam ≠ lam' := by
      intro h
      apply hs0
      have : (2 : K₁) * s = 0 := by
        rw [hlam, hlam'] at h
        field_simp at h
        linear_combination h
      exact (mul_eq_zero.mp this).resolve_left h2'
    have htr : Z'.trace = φ τ := by
      rw [hZ', hτ, Matrix.trace_fin_two, Matrix.trace_fin_two]
      simp
    have hdet' : Z'.det = 1 := by
      rw [hZ', show Z.map φ = φ.mapMatrix Z from rfl, ← RingHom.map_det, hdetZ, map_one]
    have hroot : ∀ μ : K₁, μ * μ - φ τ * μ + 1 = 0 →
        ∃ v : Fin 2 → K₁, v ≠ 0 ∧ Z' *ᵥ v = μ • v := by
      intro μ hμ
      have hdet : (Z' - μ • 1).det = 0 := by
        rw [Matrix.trace_fin_two] at htr
        rw [Matrix.det_fin_two] at hdet'
        rw [Matrix.det_fin_two]
        simp [Matrix.one_apply]
        linear_combination hdet' - μ * htr + hμ
      obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
      refine ⟨v, hv0, ?_⟩
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hv
      exact hv
    have hlamroot : lam * lam - φ τ * lam + 1 = 0 := by
      rw [hlam]
      field_simp
      linear_combination -hs'
    have hlam'root : lam' * lam' - φ τ * lam' + 1 = 0 := by
      rw [hlam']
      field_simp
      linear_combination -hs'
    obtain ⟨v₁, hv₁0, hv₁⟩ := hroot lam hlamroot
    obtain ⟨v₂, hv₂0, hv₂⟩ := hroot lam' hlam'root
    set W : Matrix (Fin 2) (Fin 2) K₁ := Matrix.of fun i j => ![v₁, v₂] j i with hW
    have hWcol : ∀ x : Fin 2 → K₁, W *ᵥ x = x 0 • v₁ + x 1 • v₂ := by
      intro x
      ext i
      simp [hW, Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_comm]
    have hzW : Z' * W = W * !![lam, 0; 0, lam'] := by
      ext i j
      fin_cases j
      · have := congrFun hv₁ i
        simp [hW, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this ⊢
        linear_combination this
      · have := congrFun hv₂ i
        simp [hW, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this ⊢
        linear_combination this
    have hWdet : W.det ≠ 0 := by
      intro hdet0
      obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet0
      rw [hWcol] at hx
      have hZx : x 0 • (lam • v₁) + x 1 • (lam' • v₂) = 0 := by
        have := congrArg (fun y => Z' *ᵥ y) hx
        simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hv₁, hv₂, Matrix.mulVec_zero] at this
        exact this
      have h1 : (x 1 * (lam' - lam)) • v₂ = 0 := by
        have : x 0 • (lam • v₁) + x 1 • (lam' • v₂) - lam • (x 0 • v₁ + x 1 • v₂) = 0 := by
          rw [hZx, hx, smul_zero, sub_zero]
        rw [← this]
        module
      rcases smul_eq_zero.mp h1 with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · rw [h', zero_smul, add_zero] at hx
          rcases smul_eq_zero.mp hx with h'' | h''
          · exact hx0 (by ext i; fin_cases i <;> simp [h', h''])
          · exact hv₁0 h''
        · exact hne (sub_eq_zero.mp h').symm
      · exact hv₂0 h
    have hWu : IsUnit W.det := isUnit_iff_ne_zero.mpr hWdet
    set eps' : K₁ := φ eps with heps'
    have heps'2 : eps' * eps' = 1 := by rw [heps', ← map_mul, heps, map_one]
    have heps'0 : eps' ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at heps'2
      exact zero_ne_one heps'2
    have hpowW : ∀ n : ℕ, Z' ^ n * W = W * !![lam, 0; 0, lam'] ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ, Matrix.mul_assoc, hzW, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, ← pow_succ]
    have hord' : ∀ k, 1 ≤ k → k < 6 → (lam * eps'⁻¹) ^ k ≠ 1 := by
      intro k hk1 hk6 hk
      apply hord k hk1 hk6
      have hlk : lam ^ k = eps' ^ k := by
        rw [mul_pow, inv_pow] at hk
        field_simp at hk
        exact hk
      have hl'k : lam' ^ k = eps' ^ k := by
        have hl' : lam' = lam⁻¹ := (eq_inv_of_mul_eq_one_right hll)
        have he : eps' ^ k * eps' ^ k = 1 := by rw [← mul_pow, heps'2, one_pow]
        rw [hl', inv_pow, hlk]
        exact (eq_inv_of_mul_eq_one_left he).symm
      have hZk : Z' ^ k = eps' ^ k • 1 := by
        have h1 := hpowW k
        rw [diag_two_pow, hlk, hl'k] at h1
        have hdg : (!![eps' ^ k, 0; 0, eps' ^ k] : Matrix (Fin 2) (Fin 2) K₁) =
            eps' ^ k • 1 := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]
        rw [hdg, Matrix.mul_smul, Matrix.mul_one] at h1
        calc Z' ^ k = Z' ^ k * W * W⁻¹ := by
              rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hWu, Matrix.mul_one]
          _ = eps' ^ k • 1 := by
              rw [h1, Matrix.smul_mul, Matrix.mul_nonsing_inv _ hWu]
      ext i j
      have := congrFun (congrFun hZk i) j
      rw [hZ', ← Matrix.map_pow] at this
      simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, heps', smul_eq_mul,
        ← map_pow] at this
      apply φ.injective
      rw [this]
      simp [Matrix.smul_apply, Matrix.one_apply]
      split_ifs <;> simp
    set G' := G.map (mapGL φ)
    have hU0' : ∀ x ∈ G', IsSqZero x → x = 1 := by
      rintro _ ⟨x, hx, rfl⟩ hsq
      rw [hU0 x hx ((isSqZero_map_iff φ).mp hsq), map_one]
    have hzt' : ((mapGL φ z : GL V₄ K₁) : Matrix V₄ V₄ K₁) * tStdMat =
        tStdMat * ((mapGL φ z : GL V₄ K₁) : Matrix V₄ V₄ K₁) := by
      rw [coe_mapGL, ← tStdMat_map φ, ← Matrix.map_mul, hzt, Matrix.map_mul]
    have hzm' : minusBlock ((mapGL φ z : GL V₄ K₁) : Matrix V₄ V₄ K₁) = eps' • 1 := by
      rw [coe_mapGL, minusBlock_map, hzm, heps']
      ext i j
      simp [Matrix.one_apply]
      split_ifs <;> simp
    have hzW' : plusBlock ((mapGL φ z : GL V₄ K₁) : Matrix V₄ V₄ K₁) * W =
        W * !![lam, 0; 0, lam'] := by
      rw [coe_mapGL, plusBlock_map, ← hZ, ← hZ']
      exact hzW
    have hres := cliffB_tStd_of_thm_eight p hp2 hU0' (Subgroup.mem_map_of_mem _ hzG)
      (Subgroup.mem_map_of_mem _ hwG) (isNCInv_map φ hw) hzt' heps'0 hzm'
      (Matrix.nonsing_inv_mul _ hWu) (Matrix.mul_nonsing_inv _ hWu) hzW' hord'
    rw [coe_mapGL, ← tStdMat_map φ, cliffB_map] at hres
    rcases hres with h | h
    · left
      exact φ.injective (by rw [h, map_zero])
    · right
      exact φ.injective (by rw [map_mul, h, map_one])

end CFSG.RankThree.SubgroupLists
