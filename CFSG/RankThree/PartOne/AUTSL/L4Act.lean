module

public import CFSG.RankThree.PartOne.AUTSL.L4Push
public import CFSG.RankThree.PartOne.AUTSL.Interface
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt

public section

namespace CFSG.RankThree.PartOne.AUTSL.L4

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type} [Field K]

@[expose] def nilM (X : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 4) (Fin 4) K :=
  !![0, 0, X 0 0, X 0 1; 0, 0, X 1 0, X 1 1; 0, 0, 0, 0; 0, 0, 0, 0]

theorem cornerM_eq (X : Matrix (Fin 2) (Fin 2) K) : cornerM X = 1 + nilM X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cornerM, nilM]

theorem nilM_smul (c : K) (X : Matrix (Fin 2) (Fin 2) K) : nilM (c • X) = c • nilM X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nilM]

theorem nilM_injective : Function.Injective (nilM : Matrix (Fin 2) (Fin 2) K →
    Matrix (Fin 4) (Fin 4) K) := by
  intro X Y h
  ext i j
  have := congrFun₂ h (Fin.castAdd 2 i) (Fin.natAdd 2 j)
  fin_cases i <;> fin_cases j <;> simpa [nilM] using this

theorem cornerM_map (σ : K ≃+* K) (X : Matrix (Fin 2) (Fin 2) K) :
    (cornerM X).map σ = cornerM (X.map σ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cornerM]

theorem map_smul_σ {m n : Type*} (σ : K ≃+* K) (c : K) (X : Matrix m n K) :
    (c • X).map σ = σ c • X.map σ := by
  ext i j
  simp

theorem corner_injective : Function.Injective (corner : Matrix (Fin 2) (Fin 2) K →
    SpecialLinearGroup (Fin 4) K) := fun _ _ h =>
  Multiplicative.toAdd.injective (cornerHom_injective (K := K) h)

theorem coe_inv_eq_of_mul_eq_one (g : SpecialLinearGroup (Fin 4) K) (N : Matrix (Fin 4) (Fin 4) K)
    (h : (g : Matrix (Fin 4) (Fin 4) K) * N = 1) :
    ((g⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = N := by
  calc ((g⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
      = ((g⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          ((g : Matrix (Fin 4) (Fin 4) K) * N) := by rw [h, mul_one]
    _ = (((g⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          (g : Matrix (Fin 4) (Fin 4) K)) * N := by rw [mul_assoc]
    _ = N := by
        rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one,
          one_mul]

@[expose] noncomputable def actFun (t : MulAut (SpecialLinearGroup (Fin 4) K))
    (h : ∀ X : Matrix (Fin 2) (Fin 2) K, ∃ Y, t (corner X) = corner Y)
    (X : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 2) (Fin 2) K :=
  Classical.choose (h X)

theorem actFun_spec (t : MulAut (SpecialLinearGroup (Fin 4) K))
    (h : ∀ X : Matrix (Fin 2) (Fin 2) K, ∃ Y, t (corner X) = corner Y)
    (X : Matrix (Fin 2) (Fin 2) K) : t (corner X) = corner (actFun t h X) :=
  Classical.choose_spec (h X)

@[expose] noncomputable def act (t : MulAut (SpecialLinearGroup (Fin 4) K))
    (h : ∀ X : Matrix (Fin 2) (Fin 2) K, ∃ Y, t (corner X) = corner Y) :
    Matrix (Fin 2) (Fin 2) K →+ Matrix (Fin 2) (Fin 2) K where
  toFun := actFun t h
  map_zero' := by
    apply corner_injective
    rw [← actFun_spec, corner_zero, map_one]
  map_add' X Y := by
    apply corner_injective
    have h1 := actFun_spec t h (X + Y)
    have h2 := actFun_spec t h X
    have h3 := actFun_spec t h Y
    rw [← h1, ← corner_add, map_mul, h2, h3, corner_add]

theorem act_spec (t : MulAut (SpecialLinearGroup (Fin 4) K))
    (h : ∀ X : Matrix (Fin 2) (Fin 2) K, ∃ Y, t (corner X) = corner Y)
    (X : Matrix (Fin 2) (Fin 2) K) : t (corner X) = corner (act t h X) :=
  actFun_spec t h X

theorem semilinear_of_conj {σ : K ≃+* K} {M N : Matrix (Fin 4) (Fin 4) K}
    (W : Matrix (Fin 2) (Fin 2) K → Matrix (Fin 4) (Fin 4) K)
    (hW : ∀ (c : K) (X : Matrix (Fin 2) (Fin 2) K), W (c • X) = σ c • W X)
    (ψ : Matrix (Fin 2) (Fin 2) K →+ Matrix (Fin 2) (Fin 2) K)
    (hψ : ∀ X, nilM (ψ X) = M * W X * N) (c : K) (X : Matrix (Fin 2) (Fin 2) K) :
    ψ (c • X) = σ c • ψ X := by
  apply nilM_injective
  rw [hψ, hW, nilM_smul, hψ, Matrix.mul_smul, Matrix.smul_mul]

section Plain

variable {t : MulAut (SpecialLinearGroup (Fin 4) K)}

theorem action_plain (h : ∀ X : Matrix (Fin 2) (Fin 2) K, ∃ Y, t (corner X) = corner Y)
    {A : GL (Fin 4) K} {σ : K ≃+* K}
    (hA : ∀ g : SpecialLinearGroup (Fin 4) K, (t g : Matrix (Fin 4) (Fin 4) K) =
      (A : Matrix (Fin 4) (Fin 4) K) * (g : Matrix (Fin 4) (Fin 4) K).map σ *
        ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) :
    (∀ (c : K) (X : Matrix (Fin 2) (Fin 2) K), act t h (c • X) = σ c • act t h X) ∧
      ((∀ X, act t h X = X) → t ∈ (MulAut.conj : SpecialLinearGroup (Fin 4) K →*
        MulAut (SpecialLinearGroup (Fin 4) K)).range) := by
  set M : Matrix (Fin 4) (Fin 4) K := (A : Matrix (Fin 4) (Fin 4) K) with hM
  set N : Matrix (Fin 4) (Fin 4) K := ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hN
  have hMN : M * N = 1 := by rw [hM, hN, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hNM : N * M = 1 := by rw [hM, hN, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have key : ∀ X, nilM (act t h X) = M * nilM (X.map σ) * N := by
    intro X
    have e1 := hA (corner X)
    rw [act_spec t h X, coe_corner, coe_corner, cornerM_map, cornerM_eq, cornerM_eq] at e1
    have e2 : M * (1 + nilM (X.map σ)) * N = 1 + M * nilM (X.map σ) * N := by
      rw [Matrix.mul_add, Matrix.add_mul, mul_one, hMN]
    exact add_left_cancel (e1.trans e2)
  refine ⟨semilinear_of_conj (fun X => nilM (X.map σ))
    (fun c X => by rw [map_smul_σ, nilM_smul]) (act t h) key, fun hid => ?_⟩
  have key' : ∀ X : Matrix (Fin 2) (Fin 2) K, nilM X * M = M * nilM (X.map σ) := by
    intro X
    have := key X
    rw [show act t h X = X from hid X] at this
    calc nilM X * M = (M * nilM (X.map σ) * N) * M := by rw [← this]
      _ = M * nilM (X.map σ) := by rw [mul_assoc, hNM, mul_one]
  have hσ : ∀ c, σ c = c := by
    intro c
    have hP : nilM (1 : Matrix (Fin 2) (Fin 2) K) * M ≠ 0 := by
      intro h0
      have : nilM (1 : Matrix (Fin 2) (Fin 2) K) = 0 := by
        calc nilM (1 : Matrix (Fin 2) (Fin 2) K)
            = (nilM (1 : Matrix (Fin 2) (Fin 2) K) * M) * N := by rw [mul_assoc, hMN, mul_one]
          _ = 0 := by rw [h0, zero_mul]
      have h02 := congrFun₂ this 0 2
      simp [nilM] at h02
    have h1 := key' 1
    rw [Matrix.map_one σ (map_zero σ) (map_one σ)] at h1
    have h2 := key' (c • 1)
    rw [map_smul_σ, Matrix.map_one σ (map_zero σ) (map_one σ), nilM_smul, nilM_smul,
      Matrix.smul_mul, Matrix.mul_smul, ← h1] at h2
    have h3 : (c - σ c) • (nilM (1 : Matrix (Fin 2) (Fin 2) K) * M) = 0 := by
      rw [sub_smul, h2, sub_self]
    exact (sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_right hP)).symm
  have hmap : ∀ X : Matrix (Fin 2) (Fin 2) K, X.map σ = X := fun X => by
    ext i j
    simp [hσ]
  have key'' : ∀ X : Matrix (Fin 2) (Fin 2) K, nilM X * M = M * nilM X := fun X => by
    rw [key' X, hmap X]
  have ent : ∀ (X : Matrix (Fin 2) (Fin 2) K) (i j : Fin 4),
      (nilM X * M) i j = (M * nilM X) i j := fun X i j => by rw [key'' X]
  have f10 : M 1 0 = 0 := by
    have := ent !![1, 0; 0, 0] 1 2
    simpa [nilM, Matrix.mul_apply, Fin.sum_univ_four] using this.symm
  have f20 : M 2 0 = 0 := by
    have := ent !![1, 0; 0, 0] 0 0
    simpa [nilM, Matrix.mul_apply, Fin.sum_univ_four] using this
  have f30 : M 3 0 = 0 := by
    have := ent !![1, 0; 0, 0] 3 2
    simpa [nilM, Matrix.mul_apply, Fin.sum_univ_four] using this.symm
  have f01 : M 0 1 = 0 := by
    have := ent !![0, 0; 1, 0] 0 2
    simpa [nilM, Matrix.mul_apply, Fin.sum_univ_four] using this.symm
  have f21 : M 2 1 = 0 := by
    have := ent !![1, 0; 0, 0] 0 1
    simpa [nilM, Matrix.mul_apply, Fin.sum_univ_four] using this
  have f31 : M 3 1 = 0 := by
    have := ent !![0, 1; 0, 0] 0 1
    simpa [nilM, Matrix.mul_apply, Fin.sum_univ_four] using this
  have f23 : M 2 3 = 0 := by
    have := ent !![1, 0; 0, 0] 0 3
    simpa [nilM, Matrix.mul_apply, Fin.sum_univ_four] using this
  have f32 : M 3 2 = 0 := by
    have := ent !![0, 1; 0, 0] 0 2
    simpa [nilM, Matrix.mul_apply, Fin.sum_univ_four] using this
  have f22 : M 2 2 = M 0 0 := by
    have := ent !![1, 0; 0, 0] 0 2
    simpa [nilM, Matrix.mul_apply, Fin.sum_univ_four] using this
  have f33 : M 3 3 = M 0 0 := by
    have := ent !![0, 1; 0, 0] 0 3
    simpa [nilM, Matrix.mul_apply, Fin.sum_univ_four] using this
  have f11 : M 1 1 = M 2 2 := by
    have := ent !![0, 0; 1, 0] 1 2
    simpa [nilM, Matrix.mul_apply, Fin.sum_univ_four] using this.symm
  set B : Matrix (Fin 2) (Fin 2) K := !![M 0 2, M 0 3; M 1 2, M 1 3] with hB
  have hMeq : M = M 0 0 • 1 + nilM B := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [nilM, hB, f10, f20, f30, f01, f21, f31, f23, f32, f22,
      f33, f11]
  have hl0 : M 0 0 ≠ 0 := by
    intro h0
    have h33 := congrFun₂ hMN 3 3
    simp [Matrix.mul_apply, Fin.sum_univ_four, f30, f31, f32, f33, h0] at h33
  generalize M 0 0 = lam at hMeq hl0
  have hmap4 : ∀ Y : Matrix (Fin 4) (Fin 4) K, Y.map σ = Y := fun Y => by
    ext i j
    simp [hσ]
  set u : SpecialLinearGroup (Fin 4) K := corner (lam⁻¹ • B) with hu
  have hcu : (u : Matrix (Fin 4) (Fin 4) K) = lam⁻¹ • M := by
    rw [hu, coe_corner, cornerM_eq, nilM_smul]
    conv_rhs => rw [hMeq]
    rw [smul_add, smul_smul, inv_mul_cancel₀ hl0, one_smul]
  have hui : ((u⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = lam • N := by
    apply coe_inv_eq_of_mul_eq_one
    rw [hcu, Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hl0, one_smul, hMN]
  refine ⟨u, ?_⟩
  ext g : 1
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  have e1 := congrFun₂ (hA g) i j
  rw [hmap4] at e1
  show ((u * g * u⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i j =
    (t g : Matrix (Fin 4) (Fin 4) K) i j
  rw [e1, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hcu, hui]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hl0, one_smul]

end Plain

section Graph

variable {t : MulAut (SpecialLinearGroup (Fin 4) K)}

theorem corner_inv (X : Matrix (Fin 2) (Fin 2) K) : (corner X)⁻¹ = corner (-X) :=
  inv_eq_of_mul_eq_one_right (by rw [corner_add, add_neg_cancel, corner_zero])

theorem transpose_map_one_add (σ : K ≃+* K) (P : Matrix (Fin 4) (Fin 4) K) :
    (1 + P).transpose.map σ = 1 + P.transpose.map σ := by
  ext i j
  by_cases h : i = j <;> simp [h]

theorem action_graph (h : ∀ X : Matrix (Fin 2) (Fin 2) K, ∃ Y, t (corner X) = corner Y)
    {A : GL (Fin 4) K} {σ : K ≃+* K}
    (hA : ∀ g : SpecialLinearGroup (Fin 4) K, (t g : Matrix (Fin 4) (Fin 4) K) =
      (A : Matrix (Fin 4) (Fin 4) K) *
        ((g⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).transpose.map σ *
          ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) :
    (∀ (c : K) (X : Matrix (Fin 2) (Fin 2) K), act t h (c • X) = σ c • act t h X) ∧
      ¬ ∀ X, act t h X = X := by
  set M : Matrix (Fin 4) (Fin 4) K := (A : Matrix (Fin 4) (Fin 4) K) with hM
  set N : Matrix (Fin 4) (Fin 4) K := ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hN
  have hMN : M * N = 1 := by rw [hM, hN, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hNM : N * M = 1 := by rw [hM, hN, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have key : ∀ X, nilM (act t h X) = M * (nilM (-X)).transpose.map σ * N := by
    intro X
    have e1 := hA (corner X)
    rw [act_spec t h X, corner_inv, coe_corner, coe_corner, cornerM_eq, cornerM_eq,
      transpose_map_one_add] at e1
    have e2 : M * (1 + (nilM (-X)).transpose.map σ) * N =
        1 + M * (nilM (-X)).transpose.map σ * N := by
      rw [Matrix.mul_add, Matrix.add_mul, mul_one, hMN]
    exact add_left_cancel (e1.trans e2)
  refine ⟨semilinear_of_conj (fun X => (nilM (-X)).transpose.map σ)
    (fun c X => ?_) (act t h) key, fun hid => ?_⟩
  · rw [← smul_neg, nilM_smul, Matrix.transpose_smul, map_smul_σ]
  · have key' : ∀ X : Matrix (Fin 2) (Fin 2) K,
        nilM X * M = M * (nilM (-X)).transpose.map σ := by
      intro X
      have := key X
      rw [show act t h X = X from hid X] at this
      calc nilM X * M = (M * (nilM (-X)).transpose.map σ * N) * M := by rw [← this]
        _ = M * (nilM (-X)).transpose.map σ := by rw [mul_assoc, hNM, mul_one]
    have c02 : M 0 2 = 0 := by
      have := congrFun₂ (key' !![0, 0; 1, 0]) 0 1
      simpa [nilM, Matrix.mul_apply, Fin.sum_univ_four] using this
    have c12 : M 1 2 = 0 := by
      have := congrFun₂ (key' !![1, 0; 0, 0]) 1 0
      simpa [nilM, Matrix.mul_apply, Fin.sum_univ_four] using this
    have c22 : M 2 2 = 0 := by
      have := congrFun₂ (key' !![1, 0; 0, 0]) 2 0
      simpa [nilM, Matrix.mul_apply, Fin.sum_univ_four] using this
    have c32 : M 3 2 = 0 := by
      have := congrFun₂ (key' !![1, 0; 0, 0]) 3 0
      simpa [nilM, Matrix.mul_apply, Fin.sum_univ_four] using this
    have h22 := congrFun₂ hNM 2 2
    simp [Matrix.mul_apply, Fin.sum_univ_four, c02, c12, c22, c32] at h22

end Graph

section Main

variable [Finite K]

theorem outer_action (t : MulAut (SpecialLinearGroup (Fin 4) K))
    (h : ∀ X : Matrix (Fin 2) (Fin 2) K, ∃ Y, t (corner X) = corner Y) :
    ∃ σ : K ≃+* K,
      (∀ (c : K) (X : Matrix (Fin 2) (Fin 2) K), act t h (c • X) = σ c • act t h X) ∧
        ((∀ X, act t h X = X) → t ∈ (MulAut.conj : SpecialLinearGroup (Fin 4) K →*
          MulAut (SpecialLinearGroup (Fin 4) K)).range) := by
  obtain ⟨A, σ, hA | hA⟩ := AUTSL.exists_matrix_form_of_mulAut_sl (n := 4) (by norm_num) t
  · exact ⟨σ, action_plain h hA⟩
  · obtain ⟨hs, hne⟩ := action_graph h hA
    exact ⟨σ, hs, fun hid => absurd hid hne⟩

theorem card_fix_le (t : MulAut (SpecialLinearGroup (Fin 4) K))
    (h : ∀ X : Matrix (Fin 2) (Fin 2) K, ∃ Y, t (corner X) = corner Y)
    (hnot : t ∉ (MulAut.conj : SpecialLinearGroup (Fin 4) K →*
      MulAut (SpecialLinearGroup (Fin 4) K)).range) :
    Nat.card {X : Matrix (Fin 2) (Fin 2) K // act t h X = X} * Nat.card K ≤ Nat.card K ^ 4 := by
  obtain ⟨σ, hσ, hid⟩ := outer_action t h
  have hne : ∃ X, act t h X ≠ X := by
    by_contra hcon
    push Not at hcon
    exact hnot (hid hcon)
  have hfin : Module.finrank K (Matrix (Fin 2) (Fin 2) K) = 4 := by
    rw [Module.finrank_matrix]
    simp
  have := card_fix_mul_le (by norm_num : 2 ≤ 4) hfin σ (act t h) hσ hne
  have hcard : Nat.card (Matrix (Fin 2) (Fin 2) K) = Nat.card K ^ 4 := by
    change Nat.card (Fin 2 → Fin 2 → K) = _
    rw [Nat.card_fun, Nat.card_fun]
    simp [← pow_mul]
  rwa [hcard] at this

end Main

end CFSG.RankThree.PartOne.AUTSL.L4
