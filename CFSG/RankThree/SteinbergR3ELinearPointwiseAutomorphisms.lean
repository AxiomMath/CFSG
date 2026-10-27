module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration

public section

namespace CFSG.RankThree.LinearPointwise

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification

variable {n : ℕ} {k : Type*} [Field k]

theorem eq_of_proj_eq_of_pow_eq_one {p : ℕ} [Fact p.Prime] [CharP k p] (hn : 0 < n)
    (ψ : SpecialLinearGroup (Fin n) k →* SpecialLinearGroup (Fin n) k)
    {h : SpecialLinearGroup (Fin n) k} {a : ℕ} (ha : h ^ p ^ a = 1)
    (hψ : proj n k (ψ h) = proj n k h) : ψ h = h := by
  rw [proj_eq_proj_iff] at hψ
  obtain ⟨c, -, hc⟩ := mem_scalars.1 hψ
  set z := (ψ h)⁻¹ * h with hz
  have hzc : z ∈ Subgroup.center _ := scalars_le_center n k hψ
  have hh : h = ψ h * z := by rw [hz, mul_inv_cancel_left]
  have hzp : z ^ p ^ a = 1 := by
    have h1 : (ψ h * z) ^ p ^ a = ψ h ^ p ^ a * z ^ p ^ a :=
      (Commute.mul_pow (Subgroup.mem_center_iff.mp hzc (ψ h)) _)
    rw [← hh, ha, ← map_pow, ha, map_one, one_mul] at h1
    exact h1.symm
  have hcp : (c : k) ^ p ^ a = 1 := by
    have h3 := Matrix.SpecialLinearGroup.coe_pow z (p ^ a)
    rw [hzp, Matrix.SpecialLinearGroup.coe_one, hc, scalar_apply, diagonal_pow] at h3
    have h4 := congrArg (fun M : Matrix (Fin n) (Fin n) k => M ⟨0, hn⟩ ⟨0, hn⟩) h3
    simp only [one_apply_eq, diagonal_apply_eq, Pi.pow_apply] at h4
    exact h4.symm
  have hc1 : (c : k) = 1 := by
    have h3 : ((c : k) - 1) ^ p ^ a = 0 := by rw [sub_pow_char_pow, hcp, one_pow, sub_self]
    exact sub_eq_zero.mp (pow_eq_zero_iff (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) |>.mp h3)
  have hz1 : z = 1 := by
    ext a b
    rw [hc, hc1, map_one]
    rfl
  rw [hz1, mul_one] at hh
  exact hh.symm

theorem standard_eq_descendAut (A : GL (Fin n) k) (σ : k ≃+* k) (ε : ℕ) :
    conjAut n k A * fieldAut n k σ * dualAut n k ^ ε =
      descendAut n k (CatalogueBHigherLinearAction.slConjugation n k A *
        CatalogueBHigherLinearField.slFieldAut (Fin n) k σ *
          CatalogueBGraphForm.slGraphAut n k ^ ε) := by
  rw [map_mul, map_mul, map_pow]
  rfl

theorem slFieldAut_apply (σ : k ≃+* k) (g : SpecialLinearGroup (Fin n) k) :
    (CatalogueBHigherLinearField.slFieldAut (Fin n) k σ g : Matrix (Fin n) (Fin n) k) =
      (g : Matrix (Fin n) (Fin n) k).map σ := by
  ext a b
  rfl

theorem map_transvection (σ : k ≃+* k) (i j : Fin n) (c : k) :
    (transvection i j c).map σ = transvection i j (σ c) := by
  ext a b
  simp only [transvection, map_apply, Matrix.add_apply, one_apply, single_apply]
  split_ifs <;> simp_all

theorem mul_eq_mul_of_conj_one_add {M N X Y : Matrix (Fin n) (Fin n) k} (hMN : M * N = 1)
    (hNM : N * M = 1) (h : M * (1 + X) * N = 1 + Y) : M * X = Y * M := by
  have h1 : M * X * N = Y := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, hMN] at h
    exact add_left_cancel h
  calc M * X = M * X * (N * M) := by rw [hNM, Matrix.mul_one]
    _ = M * X * N * M := by rw [Matrix.mul_assoc (M * X)]
    _ = Y * M := by rw [h1]

theorem false_of_columns_supported_on_row {M N : Matrix (Fin n) (Fin n) k} (hNM : N * M = 1)
    {i j r : Fin n} (hjr : j ≠ r) (hj : ∀ a, a ≠ i → M a j = 0)
    (hr : ∀ a, a ≠ i → M a r = 0) : False := by
  have hinj : ∀ v : Fin n → k, M *ᵥ v = 0 → v = 0 := by
    intro v hv
    have := congrArg (N *ᵥ ·) hv
    simpa only [Matrix.mulVec_mulVec, hNM, Matrix.one_mulVec, Matrix.mulVec_zero] using this
  by_cases hij0 : M i j = 0
  · have hcol : M *ᵥ Pi.single j 1 = 0 := by
      ext a
      simp only [Matrix.mulVec, dotProduct_single, mul_one, Pi.zero_apply]
      by_cases ha : a = i
      · rw [ha]
        exact hij0
      · exact hj a ha
    have h1 := congrFun (hinj _ hcol) j
    simp at h1
  · set v : Fin n → k := Pi.single j (M i r) - Pi.single r (M i j) with hv
    have hMv : M *ᵥ v = 0 := by
      ext a
      simp only [hv, Matrix.mulVec, dotProduct_sub, dotProduct_single, Pi.zero_apply]
      by_cases ha : a = i
      · rw [ha]
        ring
      · rw [hj a ha, hr a ha]
        ring
    have h1 := congrFun (hinj _ hMv) r
    rw [hv, Pi.sub_apply, Pi.single_eq_of_ne' hjr, Pi.single_eq_same, zero_sub, Pi.zero_apply,
      neg_eq_zero] at h1
    exact hij0 h1

theorem linear_common_row_root_pointwise_automorphisms_are_linear {p f : ℕ} (hp : p.Prime)
    (_hf : 1 ≤ f) (hn : 3 ≤ n) [Finite k] [CharP k p] (_hk : Nat.card k = p ^ f)
    (H : Subgroup (SpecialLinearGroup (Fin n) k)) (hH : IsPGroup p H) {i j r : Fin n}
    (hij : i ≠ j) (hir : i ≠ r) (hjr : j ≠ r)
    (hroot : ∀ c : k, SpecialLinearGroup.transvection hij c ∈ H ∧
      SpecialLinearGroup.transvection hir c ∈ H) :
    {α : MulAut (projectiveSL n k) | ∀ h ∈ H, α (proj n k h) = proj n k h} =
      {α | ∃ A : GL (Fin n) k, (∀ h ∈ H, (A : Matrix (Fin n) (Fin n) k) *
        (h : Matrix (Fin n) (Fin n) k) = (h : Matrix (Fin n) (Fin n) k) *
          (A : Matrix (Fin n) (Fin n) k)) ∧ α = conjAut n k A} := by
  have : Fact p.Prime := ⟨hp⟩
  have hn0 : 0 < n := by omega
  ext α
  constructor
  · intro hα
    obtain ⟨A, σ, ε, hε, rfl⟩ := (automorphism_generation (K := k) hn).2 α
    set M : Matrix (Fin n) (Fin n) k := (A : Matrix (Fin n) (Fin n) k) with hM
    set N : Matrix (Fin n) (Fin n) k := ((A⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
      with hN
    have hMN : M * N = 1 := by rw [hM, hN, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hNM : N * M = 1 := by rw [hM, hN, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    set e := CatalogueBHigherLinearAction.slConjugation n k A *
      CatalogueBHigherLinearField.slFieldAut (Fin n) k σ *
        CatalogueBGraphForm.slGraphAut n k ^ ε with he
    have hfix : ∀ h ∈ H, e h = h := by
      intro h hh
      obtain ⟨a, ha⟩ := hH ⟨h, hh⟩
      have ha' : h ^ p ^ a = 1 := by
        have := congrArg Subtype.val ha
        simpa using this
      refine eq_of_proj_eq_of_pow_eq_one hn0 e.toMonoidHom ha' ?_
      have := hα h hh
      rwa [standard_eq_descendAut, descendAut_proj] at this
    rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
    ·
      have hroot0 : ∀ c : k, M * single i j (σ c) = single i j c * M := by
        intro c
        have h1 := congrArg (fun g : SpecialLinearGroup (Fin n) k => (g : Matrix (Fin n) (Fin n) k))
          (hfix _ (hroot c).1)
        simp only [he, pow_zero, mul_one, MulAut.mul_apply] at h1
        rw [CatalogueBHigherLinearAction.slConjugation_matrix, slFieldAut_apply,
          SpecialLinearGroup.transvection_coe] at h1
        have hmap : (1 + single i j c : Matrix (Fin n) (Fin n) k).map σ =
            1 + single i j (σ c) := map_transvection σ i j c
        rw [hmap] at h1
        exact mul_eq_mul_of_conj_one_add hMN hNM h1
      have hσ : ∀ c : k, σ c = c := by
        intro c
        have h1 := hroot0 c
        have h2 : M * single i j (σ c) = single i j (σ c) * M := by
          have h3 := hroot0 1
          rw [map_one] at h3
          calc M * single i j (σ c) = σ c • (M * single i j 1) := by
                rw [← Matrix.mul_smul, smul_single, smul_eq_mul, mul_one]
            _ = single i j (σ c) * M := by
                rw [h3, ← Matrix.smul_mul, smul_single, smul_eq_mul, mul_one]
        have h4 : single i j (σ c) * M * N = single i j c * M * N := by rw [← h2, h1]
        rw [Matrix.mul_assoc, Matrix.mul_assoc, hMN, Matrix.mul_one, Matrix.mul_one] at h4
        have := congrFun (congrFun h4 i) j
        simpa using this
      have hσ1 : σ = 1 := RingEquiv.ext hσ
      subst hσ1
      refine ⟨A, fun h hh => ?_, by rw [map_one, mul_one, pow_zero, mul_one]⟩
      have h1 := congrArg (fun g : SpecialLinearGroup (Fin n) k => (g : Matrix (Fin n) (Fin n) k))
        (hfix h hh)
      simp only [he, pow_zero, mul_one, map_one] at h1
      rw [CatalogueBHigherLinearAction.slConjugation_matrix] at h1
      have h1' : M * (h : Matrix (Fin n) (Fin n) k) * N = h := h1
      calc M * (h : Matrix (Fin n) (Fin n) k) = M * h * (N * M) := by rw [hNM, Matrix.mul_one]
        _ = M * h * N * M := by simp only [Matrix.mul_assoc]
        _ = h * M := by rw [h1']
    ·
      exfalso
      have hcol : ∀ {s : Fin n} (his : i ≠ s), SpecialLinearGroup.transvection his (1 : k) ∈ H →
          ∀ a, a ≠ i → M a s = 0 := by
        intro s his hs a ha
        have h1 := congrArg (fun g : SpecialLinearGroup (Fin n) k => (g : Matrix (Fin n) (Fin n) k))
          (hfix _ hs)
        simp only [he, pow_one, MulAut.mul_apply] at h1
        rw [CatalogueBHigherLinearAction.slConjugation_matrix, slFieldAut_apply] at h1
        have hgraph : ((CatalogueBGraphForm.slGraphAut n k
            (SpecialLinearGroup.transvection his (1 : k)) : SpecialLinearGroup (Fin n) k) :
              Matrix (Fin n) (Fin n) k) = 1 + single s i (-1) := by
          change (((SpecialLinearGroup.transvection his (1 : k))⁻¹ :
            SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k)ᵀ = _
          rw [SpecialLinearGroup.transvection_inv, SpecialLinearGroup.transvection_coe,
            Matrix.transpose_add, Matrix.transpose_one, transpose_single]
        have hmap : (1 + single s i (-1) : Matrix (Fin n) (Fin n) k).map σ =
            1 + single s i (-1) := by
          rw [show (1 + single s i (-1) : Matrix (Fin n) (Fin n) k) = transvection s i (-1) from
            rfl, map_transvection, map_neg, map_one]
        rw [hgraph, hmap, SpecialLinearGroup.transvection_coe] at h1
        have h2 := mul_eq_mul_of_conj_one_add hMN hNM h1
        have h3 := congrFun (congrFun h2 a) i
        rw [mul_single_apply_same, single_mul_apply_of_ne _ _ _ _ _ ha] at h3
        simpa using h3
      exact false_of_columns_supported_on_row hNM hjr (hcol hij (hroot 1).1)
        (hcol hir (hroot 1).2)
  · rintro ⟨A, hA, rfl⟩ h hh
    rw [conjAut_proj]
    congr 1
    apply Subtype.ext
    change (CatalogueBHigherLinearAction.slConjugation n k A h : Matrix (Fin n) (Fin n) k) = h
    rw [CatalogueBHigherLinearAction.slConjugation_matrix, hA h hh, Matrix.mul_assoc,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

end CFSG.RankThree.LinearPointwise
