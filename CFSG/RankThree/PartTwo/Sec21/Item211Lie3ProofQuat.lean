module

public import CFSG.RankThree.PartTwo.Sec21.Item211Lie3ProofOrth2
public import CFSG.RankThree.SubgroupLists.SymplecticRegulus
public import CFSG.RankThree.SubgroupLists.SymplecticInvolutions

public section

namespace CFSG.RankThree.PartTwo.Sec21

namespace Item211Lie3Proof

open Matrix CFSG.Assembly.LowTwoRank CFSG.RankThree.SubgroupLists

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {K : Type} [Field K]

abbrev sgnMat (K : Type) [Field K] : Matrix V₄ V₄ K :=
  fromBlocks 1 0 0 (-1)

theorem eq_zero_of_neg_eq (h2 : (2 : K) ≠ 0) {B : Matrix (Fin 2) (Fin 2) K} (hB : -B = B) :
    B = 0 := by
  have h : (2 : K) • B = 0 := by rw [two_smul]; nth_rw 1 [← hB]; exact neg_add_cancel B
  exact (smul_eq_zero.mp h).resolve_left h2

theorem eq_fromBlocks_of_commute_sgn (h2 : (2 : K) ≠ 0) {M : Matrix V₄ V₄ K}
    (hM : M * sgnMat K = sgnMat K * M) :
    M = fromBlocks M.toBlocks₁₁ 0 0 M.toBlocks₂₂ := by
  have e := hM
  rw [← fromBlocks_toBlocks M, fromBlocks_multiply, fromBlocks_multiply] at e
  simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_neg,
    Matrix.one_mul, Matrix.zero_mul, Matrix.neg_mul] at e
  obtain ⟨-, h12, h21, -⟩ := fromBlocks_inj.mp e
  conv_lhs => rw [← fromBlocks_toBlocks M]
  rw [eq_zero_of_neg_eq h2 h12, eq_zero_of_neg_eq h2 h21.symm]

theorem eq_fromBlocks_of_anticommute_sgn (h2 : (2 : K) ≠ 0) {M : Matrix V₄ V₄ K}
    (hM : M * sgnMat K = -(sgnMat K * M)) :
    M = fromBlocks 0 M.toBlocks₁₂ M.toBlocks₂₁ 0 := by
  have e := hM
  rw [← fromBlocks_toBlocks M, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_neg] at e
  simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_neg,
    Matrix.one_mul, Matrix.zero_mul, Matrix.neg_mul, neg_neg] at e
  obtain ⟨h11, -, -, h22⟩ := fromBlocks_inj.mp e
  conv_lhs => rw [← fromBlocks_toBlocks M]
  rw [eq_zero_of_neg_eq h2 h11.symm, eq_zero_of_neg_eq h2 h22]

theorem fromBlocks_diag_symp {A B : Matrix (Fin 2) (Fin 2) K}
    (h : (fromBlocks A 0 0 B)ᵀ * spGram 2 K * fromBlocks A 0 0 B = spGram 2 K) : Aᵀ * B = 1 := by
  rw [fromBlocks_transpose, spGram, fromBlocks_multiply, fromBlocks_multiply] at h
  simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_neg,
    Matrix.zero_mul, Matrix.transpose_zero, Matrix.neg_mul, neg_zero] at h
  exact (fromBlocks_inj.mp h).2.1

theorem eq_of_fromBlocks_diag_symp {A B B' : Matrix (Fin 2) (Fin 2) K}
    (h : Aᵀ * B = 1) (h' : Aᵀ * B' = 1) : fromBlocks A 0 0 B = fromBlocks A 0 0 B' := by
  have hBA : B * Aᵀ = 1 := mul_eq_one_comm.mp h
  have : B = B' := by
    calc B = B * (Aᵀ * B') := by rw [h', Matrix.mul_one]
      _ = (B * Aᵀ) * B' := (Matrix.mul_assoc _ _ _).symm
      _ = B' := by rw [hBA, Matrix.one_mul]
  rw [this]

theorem conj_eq_or_eq_inv_of_quat (h2 : (2 : K) ≠ 0) {a c : K} (hac : a ^ 2 + c ^ 2 = -1)
    {U V X H : GL V₄ K} (hU : U ∈ StatedSp 2 K) (hV : V ∈ StatedSp 2 K) (hX : X ∈ StatedSp 2 K)
    (hH : H ∈ StatedSp 2 K) (hU2 : U * U = -1) (hV2 : V * V = -1) (hUV : U * V = -(V * U))
    (hXU : X * U = U * X) (hXV : X * V = V * X) (hHU : H * U = U * H) (hHV : H * V = V * H)
    (hH3 : H ^ 3 = 1) : X * H * X⁻¹ = H ∨ X * H * X⁻¹ = H⁻¹ := by
  classical
  have hmat : ∀ {A B : GL V₄ K}, A * B = B * A →
      (A : Matrix V₄ V₄ K) * (B : Matrix V₄ V₄ K) = (B : Matrix V₄ V₄ K) * (A : Matrix V₄ V₄ K) :=
    fun h => by rw [← Units.val_mul, h, Units.val_mul]
  have hUU : (U : Matrix V₄ V₄ K) * U = -1 := by
    rw [← Units.val_mul, hU2, Units.val_neg, Units.val_one]
  have hVV : (V : Matrix V₄ V₄ K) * V = -1 := by
    rw [← Units.val_mul, hV2, Units.val_neg, Units.val_one]
  have hVU : (V : Matrix V₄ V₄ K) * U = -((U : Matrix V₄ V₄ K) * V) := by
    rw [← Units.val_mul, ← Units.val_mul, hUV, Units.val_neg, neg_neg]
  set Ψ : Matrix V₄ V₄ K := a • (U : Matrix V₄ V₄ K) + c • ((U : Matrix V₄ V₄ K) * V) with hΨ
  have r1 : (U : Matrix V₄ V₄ K) * ((U : Matrix V₄ V₄ K) * V) = -(V : Matrix V₄ V₄ K) := by
    rw [← Matrix.mul_assoc, hUU, Matrix.neg_mul, Matrix.one_mul]
  have r2 : (U : Matrix V₄ V₄ K) * ((V : Matrix V₄ V₄ K) * U) = V := by
    rw [hVU, Matrix.mul_neg, r1, neg_neg]
  have r4 : (U : Matrix V₄ V₄ K) * ((V : Matrix V₄ V₄ K) * V) = -(U : Matrix V₄ V₄ K) := by
    rw [hVV, Matrix.mul_neg, Matrix.mul_one]
  have r5 : (V : Matrix V₄ V₄ K) * ((U : Matrix V₄ V₄ K) * V) = U := by
    rw [← Matrix.mul_assoc, hVU, Matrix.neg_mul, Matrix.mul_assoc, r4, neg_neg]
  have r3 : (U : Matrix V₄ V₄ K) * ((V : Matrix V₄ V₄ K) * ((U : Matrix V₄ V₄ K) * V)) = -1 := by
    rw [r5, hUU]
  have hΨΨ : Ψ * Ψ = 1 := by
    have h1 : Ψ * Ψ = (-(a ^ 2 + c ^ 2)) • (1 : Matrix V₄ V₄ K) := by
      simp only [hΨ, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.mul_assoc, hUU, r1, r2, r3]
      module
    rw [h1, hac, neg_neg, one_smul]
  have hΨV : Ψ * V = -((V : Matrix V₄ V₄ K) * Ψ) := by
    simp only [hΨ, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.mul_assoc, r4, r5, hVU]
    module
  have hcommΨ : ∀ {Z : GL V₄ K}, Z * U = U * Z → Z * V = V * Z →
      (Z : Matrix V₄ V₄ K) * Ψ = Ψ * Z := by
    intro Z hZU hZV
    have h1 := hmat hZU
    have h3 := hmat hZV
    simp only [hΨ, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      ← Matrix.mul_assoc, h1]
    rw [Matrix.mul_assoc (U : Matrix V₄ V₄ K) (Z : Matrix V₄ V₄ K), h3, ← Matrix.mul_assoc]
  have hskew : ∀ {Z : GL V₄ K}, Z ∈ StatedSp 2 K → (Z : Matrix V₄ V₄ K) * Z = -1 →
      (Z : Matrix V₄ V₄ K)ᵀ * spGram 2 K = -(spGram 2 K * Z) := by
    intro Z hZ hZZ
    have hJ := transpose_mul_spGram_mul hZ
    calc (Z : Matrix V₄ V₄ K)ᵀ * spGram 2 K
        = (Z : Matrix V₄ V₄ K)ᵀ * spGram 2 K * (-((Z : Matrix V₄ V₄ K) * Z)) := by
          rw [hZZ, neg_neg, Matrix.mul_one]
      _ = -(((Z : Matrix V₄ V₄ K)ᵀ * spGram 2 K * Z) * Z) := by
          rw [Matrix.mul_neg, Matrix.mul_assoc _ (Z : Matrix V₄ V₄ K)]
      _ = -(spGram 2 K * Z) := by rw [hJ]
  have hUs := hskew hU hUU
  have hVs := hskew hV hVV
  have hΨs : Ψᵀ * spGram 2 K = -(spGram 2 K * Ψ) := by
    calc Ψᵀ * spGram 2 K = a • ((U : Matrix V₄ V₄ K)ᵀ * spGram 2 K) +
          c • ((V : Matrix V₄ V₄ K)ᵀ * ((U : Matrix V₄ V₄ K)ᵀ * spGram 2 K)) := by
          rw [hΨ, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul,
            Matrix.transpose_mul, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul,
            Matrix.mul_assoc]
      _ = -(spGram 2 K * Ψ) := by
          rw [hUs, Matrix.mul_neg, ← Matrix.mul_assoc, hVs, Matrix.neg_mul, neg_neg,
            Matrix.mul_assoc, hVU, hΨ, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul,
            Matrix.mul_neg]
          module
  set Ep := eigSp Ψ 1 with hEp
  set Em := eigSp Ψ (-1) with hEm
  have hsum : Module.finrank K Ep + Module.finrank K Em = 4 := finrank_eig_add_finrank_eig h2 hΨΨ
  have hVpm : ∀ x ∈ Ep, Matrix.toLin' (V : Matrix V₄ V₄ K) x ∈ Em := by
    intro x hx
    rw [mem_eigSp] at hx ⊢
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hΨV, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec,
      hx, one_smul, neg_one_smul]
  have hVmp : ∀ x ∈ Em, Matrix.toLin' (V : Matrix V₄ V₄ K) x ∈ Ep := by
    intro x hx
    rw [mem_eigSp] at hx ⊢
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hΨV, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec,
      hx, neg_one_smul, Matrix.mulVec_neg, neg_neg, one_smul]
  have hVinj : Function.Injective (Matrix.toLin' (V : Matrix V₄ V₄ K)) := by
    intro x y hxy
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply] at hxy
    have h1 := congrArg (fun w => (V : Matrix V₄ V₄ K) *ᵥ w) hxy
    simp only [Matrix.mulVec_mulVec, hVV, Matrix.neg_mulVec, Matrix.one_mulVec, neg_inj] at h1
    exact h1
  have hle1 : Module.finrank K Ep ≤ Module.finrank K Em :=
    LinearMap.finrank_le_finrank_of_injective
      (f := (Matrix.toLin' (V : Matrix V₄ V₄ K)).restrict hVpm)
      (fun x y hxy => Subtype.ext (hVinj (congrArg Subtype.val hxy)))
  have hle2 : Module.finrank K Em ≤ Module.finrank K Ep :=
    LinearMap.finrank_le_finrank_of_injective
      (f := (Matrix.toLin' (V : Matrix V₄ V₄ K)).restrict hVmp)
      (fun x y hxy => Subtype.ext (hVinj (congrArg Subtype.val hxy)))
  have hEp2 : Module.finrank K Ep = 2 := by omega
  have hEm2 : Module.finrank K Em = 2 := by omega
  have hskewform : ∀ x y : V₄ → K, spForm 2 K (Ψ *ᵥ x) y = -spForm 2 K x (Ψ *ᵥ y) := by
    intro x y
    rw [spForm_eq_dotProduct, spForm_eq_dotProduct, ← Matrix.vecMul_transpose,
      ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hΨs, Matrix.neg_mulVec,
      Matrix.mulVec_mulVec, dotProduct_neg]
  have hisoP : ∀ x ∈ Ep, ∀ y ∈ Ep, spForm 2 K x y = 0 := by
    intro x hx y hy
    have h1 := hskewform x y
    rw [mem_eigSp.mp hx, mem_eigSp.mp hy, one_smul, one_smul] at h1
    have : (2 : K) * spForm 2 K x y = 0 := by linear_combination h1
    exact (mul_eq_zero.mp this).resolve_left h2
  have hisoM : ∀ x ∈ Em, ∀ y ∈ Em, spForm 2 K x y = 0 := by
    intro x hx y hy
    have h1 := hskewform x y
    rw [mem_eigSp.mp hx, mem_eigSp.mp hy] at h1
    simp only [neg_one_smul, map_neg, LinearMap.neg_apply, neg_neg] at h1
    have : (2 : K) * spForm 2 K x y = 0 := by linear_combination -h1
    exact (mul_eq_zero.mp this).resolve_left h2
  obtain ⟨g, hgS, hgL, hgG⟩ :=
    exists_mem_statedSp_translate_eq hEp2 hEm2 hisoP hisoM (eig_inf_eig h2 Ψ)
  set gm : Matrix V₄ V₄ K := (g : Matrix V₄ V₄ K) with hgm
  set gim : Matrix V₄ V₄ K := ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) with hgim
  have hgg : gim * gm = 1 := by rw [hgim, hgm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hgg' : gm * gim = 1 := by rw [hgim, hgm, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hconj_mul : ∀ A B : Matrix V₄ V₄ K,
      (gim * A * gm) * (gim * B * gm) = gim * (A * B) * gm := fun A B => by
    calc (gim * A * gm) * (gim * B * gm) = gim * A * (gm * gim) * B * gm := by
          simp only [Matrix.mul_assoc]
      _ = gim * (A * B) * gm := by rw [hgg', Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have hconj_inj : ∀ A B : Matrix V₄ V₄ K, gim * A * gm = gim * B * gm → A = B := by
    intro A B h
    calc A = (gm * gim) * A * (gm * gim) := by rw [hgg', Matrix.one_mul, Matrix.mul_one]
      _ = gm * (gim * A * gm) * gim := by simp only [Matrix.mul_assoc]
      _ = gm * (gim * B * gm) * gim := by rw [h]
      _ = (gm * gim) * B * (gm * gim) := by simp only [Matrix.mul_assoc]
      _ = B := by rw [hgg', Matrix.one_mul, Matrix.mul_one]
  have hΨ' : gim * Ψ * gm = sgnMat K := by
    refine Matrix.ext_of_mulVec_single fun k => ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rcases k with i | i
    · have hmem : gm *ᵥ Pi.single (Sum.inl i) (1 : K) ∈ Ep := by
        rw [← hgL]
        refine mulVec_mem_translate (mem_lagInl.mpr fun j => ?_)
        simp
      rw [mem_eigSp.mp hmem, one_smul, hgim, hgm, gl_inv_mulVec_mulVec]
      ext j
      rcases j with j | j <;>
        simp [sgnMat, Matrix.mulVec, dotProduct, fromBlocks, Pi.single_apply, Matrix.one_apply]
    · have hmem : gm *ᵥ Pi.single (Sum.inr i) (1 : K) ∈ Em := by
        rw [← hgG]
        refine mulVec_mem_translate (mem_graphLag.mpr fun j => ?_)
        simp [Matrix.mulVec, dotProduct]
      rw [mem_eigSp.mp hmem, Matrix.mulVec_smul, hgim, hgm, gl_inv_mulVec_mulVec]
      ext j
      rcases j with j | j
      · simp [sgnMat, Matrix.mulVec, dotProduct, fromBlocks, Pi.single_apply]
      · by_cases hji : j = i
        · subst hji
          simp [sgnMat, Matrix.mulVec, dotProduct, fromBlocks, Pi.single_apply]
        · simp [sgnMat, Matrix.mulVec, dotProduct, fromBlocks, Pi.single_apply, hji]
  have hcomm_sgn : ∀ A : Matrix V₄ V₄ K, A * Ψ = Ψ * A →
      (gim * A * gm) * sgnMat K = sgnMat K * (gim * A * gm) := by
    intro A hA
    rw [← hΨ', hconj_mul, hconj_mul, hA]
  have hsymp : ∀ {Z : GL V₄ K}, Z ∈ StatedSp 2 K →
      (gim * (Z : Matrix V₄ V₄ K) * gm)ᵀ * spGram 2 K * (gim * (Z : Matrix V₄ V₄ K) * gm) =
        spGram 2 K := by
    intro Z hZ
    have := transpose_mul_spGram_mul (mul_mem (mul_mem (inv_mem hgS) hZ) hgS)
    simpa only [Units.val_mul] using this
  have hblk : ∀ {Z : GL V₄ K}, Z ∈ StatedSp 2 K → Z * U = U * Z → Z * V = V * Z →
      gim * (Z : Matrix V₄ V₄ K) * gm = fromBlocks (gim * (Z : Matrix V₄ V₄ K) * gm).toBlocks₁₁ 0 0
        (gim * (Z : Matrix V₄ V₄ K) * gm).toBlocks₂₂ ∧
      (gim * (Z : Matrix V₄ V₄ K) * gm).toBlocks₁₁ᵀ * (gim * (Z : Matrix V₄ V₄ K) * gm).toBlocks₂₂
        = 1 := by
    intro Z hZ hZU hZV
    have hb := eq_fromBlocks_of_commute_sgn h2 (hcomm_sgn _ (hcommΨ hZU hZV))
    refine ⟨hb, ?_⟩
    have := hsymp hZ
    rw [hb] at this
    exact fromBlocks_diag_symp this
  have hV'sgn : (gim * (V : Matrix V₄ V₄ K) * gm) * sgnMat K =
      -(sgnMat K * (gim * (V : Matrix V₄ V₄ K) * gm)) := by
    rw [← hΨ', hconj_mul, hconj_mul, show (V : Matrix V₄ V₄ K) * Ψ = -(Ψ * V) by
      rw [hΨV, neg_neg], Matrix.mul_neg, Matrix.neg_mul]
  have hV'b := eq_fromBlocks_of_anticommute_sgn h2 hV'sgn
  set P := (gim * (V : Matrix V₄ V₄ K) * gm).toBlocks₁₂ with hP
  set Q := (gim * (V : Matrix V₄ V₄ K) * gm).toBlocks₂₁ with hQ
  have hVsymp := hsymp hV
  rw [hV'b, fromBlocks_transpose, spGram, fromBlocks_multiply, fromBlocks_multiply] at hVsymp
  simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_neg,
    Matrix.zero_mul, Matrix.transpose_zero, Matrix.neg_mul, neg_zero] at hVsymp
  have hPtQ : Pᵀ * Q = -1 := (fromBlocks_inj.mp hVsymp).2.2.1
  have hVV' : (gim * (V : Matrix V₄ V₄ K) * gm) * (gim * (V : Matrix V₄ V₄ K) * gm) = -1 := by
    rw [hconj_mul, hVV, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_one, hgg]
  rw [hV'b, fromBlocks_multiply] at hVV'
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at hVV'
  have hPQ : P * Q = -1 := by
    rw [← fromBlocks_one, fromBlocks_neg, neg_zero] at hVV'
    exact (fromBlocks_inj.mp hVV').1
  have hQP : Q * P = -1 := by
    have h1 : P * (-Q) = 1 := by rw [Matrix.mul_neg, hPQ, neg_neg]
    have h3 := mul_eq_one_comm.mp h1
    rw [Matrix.neg_mul] at h3
    rw [← neg_neg (Q * P), h3]
  have hPs : Pᵀ = P := by
    have h3 : (Pᵀ - P) * Q * P = 0 := by
      rw [Matrix.sub_mul, hPtQ, hPQ, sub_self, Matrix.zero_mul]
    rw [Matrix.mul_assoc, hQP, Matrix.mul_neg, Matrix.mul_one, neg_eq_zero, sub_eq_zero] at h3
    exact h3
  have hPdet : P.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hPQ
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_neg, Matrix.det_one] at this
    simp at this
  have horth : ∀ {A B : Matrix (Fin 2) (Fin 2) K}, Aᵀ * B = 1 →
      fromBlocks A 0 0 B * fromBlocks 0 P Q 0 = fromBlocks 0 P Q 0 * fromBlocks A 0 0 B →
      A * P * Aᵀ = P := by
    intro A B hAB hcomm
    rw [fromBlocks_multiply, fromBlocks_multiply] at hcomm
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at hcomm
    have h1 : A * P = P * B := (fromBlocks_inj.mp hcomm).2.1
    have h3 : B * Aᵀ = 1 := mul_eq_one_comm.mp hAB
    rw [h1, Matrix.mul_assoc, h3, Matrix.mul_one]
  have hcV : ∀ {Z : GL V₄ K}, Z * V = V * Z →
      (gim * (Z : Matrix V₄ V₄ K) * gm) * (gim * (V : Matrix V₄ V₄ K) * gm) =
        (gim * (V : Matrix V₄ V₄ K) * gm) * (gim * (Z : Matrix V₄ V₄ K) * gm) := by
    intro Z hZV
    rw [hconj_mul, hconj_mul, hmat hZV]
  obtain ⟨hXb, hXs⟩ := hblk hX hXU hXV
  obtain ⟨hHb, hHs⟩ := hblk hH hHU hHV
  set Y := (gim * (X : Matrix V₄ V₄ K) * gm).toBlocks₁₁ with hY
  set Y₂ := (gim * (X : Matrix V₄ V₄ K) * gm).toBlocks₂₂ with hY₂
  set H₁ := (gim * (H : Matrix V₄ V₄ K) * gm).toBlocks₁₁ with hH₁
  set H₂ := (gim * (H : Matrix V₄ V₄ K) * gm).toBlocks₂₂ with hH₂
  have hYorth : Y * P * Yᵀ = P := by
    refine horth hXs ?_
    rw [← hXb, ← hV'b]
    exact hcV hXV
  have hHorth : H₁ * P * H₁ᵀ = P := by
    refine horth hHs ?_
    rw [← hHb, ← hV'b]
    exact hcV hHV
  have hH₁3 : H₁ * H₁ * H₁ = 1 := by
    have h1 : (gim * (H : Matrix V₄ V₄ K) * gm) * (gim * (H : Matrix V₄ V₄ K) * gm) *
        (gim * (H : Matrix V₄ V₄ K) * gm) = 1 := by
      rw [hconj_mul, hconj_mul, ← Units.val_mul, ← Units.val_mul, ← pow_three', hH3,
        Units.val_one, Matrix.mul_one, hgg]
    rw [hHb, fromBlocks_multiply, fromBlocks_multiply] at h1
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at h1
    exact (fromBlocks_inj.mp (h1.trans fromBlocks_one.symm)).1
  have hH₁det : H₁.det = 1 := by
    rcases det_eq_one_or_neg_one_of_orth hPdet hHorth with h1 | h1
    · exact h1
    · exfalso
      have := congrArg Matrix.det hH₁3
      rw [Matrix.det_mul, Matrix.det_mul, h1, Matrix.det_one] at this
      apply h2
      linear_combination -this
  have hXH : gim * ((X : Matrix V₄ V₄ K) * H) * gm = fromBlocks (Y * H₁) 0 0 (Y₂ * H₂) := by
    rw [← hconj_mul, hXb, hHb, fromBlocks_multiply]
    simp
  have hXHs : (Y * H₁)ᵀ * (Y₂ * H₂) = 1 := by
    rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Yᵀ, hXs, Matrix.one_mul, hHs]
  rcases orth_mul_comm_or_inv h2 hPs hPdet hYorth hHorth hH₁det with hc | hc
  · left
    have hHX : gim * ((H : Matrix V₄ V₄ K) * X) * gm = fromBlocks (H₁ * Y) 0 0 (H₂ * Y₂) := by
      rw [← hconj_mul, hXb, hHb, fromBlocks_multiply]
      simp
    have hHXs : (H₁ * Y)ᵀ * (H₂ * Y₂) = 1 := by
      rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc H₁ᵀ, hHs, Matrix.one_mul,
        hXs]
    have h1 : gim * ((X : Matrix V₄ V₄ K) * H) * gm = gim * ((H : Matrix V₄ V₄ K) * X) * gm := by
      rw [hXH, hHX, hc]
      rw [hc] at hXHs
      exact eq_of_fromBlocks_diag_symp hXHs hHXs
    have h3 := hconj_inj _ _ h1
    have h4 : X * H = H * X := Units.ext (by rw [Units.val_mul, Units.val_mul]; exact h3)
    rw [h4, mul_inv_cancel_right]
  · right
    obtain ⟨hHib, hHis⟩ := hblk (inv_mem hH) (show Commute H U from hHU).inv_left.eq
      (show Commute H V from hHV).inv_left.eq
    set Hi₁ := (gim * ((H⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * gm).toBlocks₁₁ with hHi₁
    set Hi₂ := (gim * ((H⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * gm).toBlocks₂₂ with hHi₂
    have hHiH : Hi₁ * H₁ = 1 := by
      have h1 : gim * (((H⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * H) * gm = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one, hgg]
      rw [← hconj_mul, hHib, hHb, fromBlocks_multiply] at h1
      simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at h1
      exact (fromBlocks_inj.mp (h1.trans fromBlocks_one.symm)).1
    have hHi : Hi₁ = adjugate H₁ := by
      have h1 : H₁ * adjugate H₁ = 1 := by rw [mul_adjugate, hH₁det, one_smul]
      calc Hi₁ = Hi₁ * (H₁ * adjugate H₁) := by rw [h1, Matrix.mul_one]
        _ = (Hi₁ * H₁) * adjugate H₁ := (Matrix.mul_assoc _ _ _).symm
        _ = adjugate H₁ := by rw [hHiH, Matrix.one_mul]
    have hHiX : gim * (((H⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * X) * gm =
        fromBlocks (Hi₁ * Y) 0 0 (Hi₂ * Y₂) := by
      rw [← hconj_mul, hXb, hHib, fromBlocks_multiply]
      simp
    have hHiXs : (Hi₁ * Y)ᵀ * (Hi₂ * Y₂) = 1 := by
      rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Hi₁ᵀ, hHis, Matrix.one_mul,
        hXs]
    have h1 : gim * ((X : Matrix V₄ V₄ K) * H) * gm =
        gim * (((H⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * X) * gm := by
      rw [hXH, hHiX, hc, ← hHi]
      rw [hc, ← hHi] at hXHs
      exact eq_of_fromBlocks_diag_symp hXHs hHiXs
    have h3 := hconj_inj _ _ h1
    have h4 : X * H = H⁻¹ * X := Units.ext (by rw [Units.val_mul, Units.val_mul]; exact h3)
    rw [h4, mul_inv_cancel_right]

end Item211Lie3Proof

end CFSG.RankThree.PartTwo.Sec21
