module

public import CFSG.Quasithin.Background.Harris.L3.RankDescent
public import CFSG.GroupTheory.ABGLocalTools.SL2FieldAutSemilinear
public import CFSG.Quasithin.Background.Harris.L3.RankElem

public section

namespace CFSG.Quasithin.G11.Harris.L3

open scoped MatrixGroups
open Matrix CFSG.ComponentClassification.CatalogueBHigherLinearAction
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Conj

variable {F : Type*} [Field F]

theorem map_slConjugation (σ : F ≃+* F) (A : GL (Fin 3) F) (g : SL(3, F)) :
    SpecialLinearGroup.map σ.toRingHom (slConjugation 3 F A g) =
      slConjugation 3 F (GeneralLinearGroup.map σ.toRingHom A)
        (SpecialLinearGroup.map σ.toRingHom g) := by
  apply Subtype.ext
  rw [SpecialLinearGroup.map_apply_coe, slConjugation_matrix, slConjugation_matrix,
    SpecialLinearGroup.map_apply_coe]
  rw [map_mul, map_mul, ← map_inv (GeneralLinearGroup.map σ.toRingHom)]
  rfl

theorem slConjugation_scalar (c : Fˣ) (g : SL(3, F)) :
    slConjugation 3 F (GeneralLinearGroup.scalar (Fin 3) c) g = g := by
  apply Subtype.ext
  rw [slConjugation_matrix]
  have h1 : ((GeneralLinearGroup.scalar (Fin 3) c)⁻¹ : GL (Fin 3) F).val =
      Matrix.scalar (Fin 3) ((c⁻¹ : Fˣ) : F) := by
    rw [← map_inv, GeneralLinearGroup.coe_scalar]
  rw [h1, GeneralLinearGroup.coe_scalar]
  have h2 : Matrix.scalar (Fin 3) (c : F) * (g : Matrix (Fin 3) (Fin 3) F) =
      (g : Matrix (Fin 3) (Fin 3) F) * Matrix.scalar (Fin 3) (c : F) :=
    (Matrix.scalar_commute _ (fun r => Commute.all _ _) _).eq
  rw [h2, mul_assoc, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one, mul_one]

theorem map_mapMatrix_map {σ : F ≃+* F} (hσσ : ∀ x, σ (σ x) = x) (N : Matrix (Fin 3) (Fin 3) F) :
    (N.map σ).map σ = N := by
  ext i j
  simp [hσσ]

theorem frob_scalar_eq {σ : F ≃+* F} (hσσ : ∀ x, σ (σ x) = x) (M : GL (Fin 3) F) (c : Fˣ)
    (hM : M * GeneralLinearGroup.map σ.toRingHom M = GeneralLinearGroup.scalar (Fin 3) c) :
    σ c = c := by
  have h1 : M.val * M.val.map σ = Matrix.scalar (Fin 3) (c : F) := by
    have := congrArg Units.val hM
    rwa [Units.val_mul, GeneralLinearGroup.coe_scalar] at this
  have h2 : M.val.map σ * M.val = Matrix.scalar (Fin 3) (σ c : F) := by
    have := congrArg (fun X : Matrix (Fin 3) (Fin 3) F => X.map σ) h1
    simp only [Matrix.map_mul] at this
    rw [map_mapMatrix_map hσσ] at this
    rw [this]
    ext i j
    simp only [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.map_apply]
    split_ifs <;> simp
  have h3 : (c : F) • M.val = (σ c : F) • M.val := by
    calc (c : F) • M.val = Matrix.scalar (Fin 3) (c : F) * M.val := by
          rw [Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]
      _ = M.val * (M.val.map σ * M.val) := by rw [← h1, Matrix.mul_assoc]
      _ = (σ c : F) • M.val := by
          rw [h2, Matrix.scalar_apply, ← Matrix.smul_eq_mul_diagonal]
  have h4 : (c : F) • (M.val * (M⁻¹ : GL (Fin 3) F).val) =
      (σ c : F) • (M.val * (M⁻¹ : GL (Fin 3) F).val) := by
    rw [← smul_mul_assoc, ← smul_mul_assoc, h3]
  rw [Units.mul_inv] at h4
  have h5 := congrFun (congrFun h4 0) 0
  simpa using h5.symm

end Conj

section Hilbert

variable {F : Type} [Field F] [Finite F] {k : ℕ}

theorem exists_twist_conjugator (hk : 1 ≤ k) (hF : Nat.card F = 2 ^ (2 * k)) {σ : F ≃+* F}
    (hσ : ∀ x, σ x = x ^ 2 ^ k) (M : GL (Fin 3) F) (c : Fˣ)
    (hM : M * GeneralLinearGroup.map σ.toRingHom M = GeneralLinearGroup.scalar (Fin 3) c) :
    ∃ (Y : GL (Fin 3) F) (d : Fˣ),
      M * GeneralLinearGroup.map σ.toRingHom Y = GeneralLinearGroup.scalar (Fin 3) d * Y := by
  have hσσ := frob_frob_eq hF hσ
  have hc := frob_scalar_eq hσσ M c hM
  obtain ⟨d, hd⟩ := CFSG.ABGLocalTools.exists_prod_pow_eq σ hc
  rw [orderOf_frob hk hF hσ] at hd
  simp only [Finset.prod_range_succ, Finset.range_zero, Finset.prod_empty, one_mul, pow_zero,
    pow_one, RingAut.one_apply] at hd
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hd
    exact c.ne_zero hd.symm
  set N := M.val with hN
  have hA : (d⁻¹ • N) * (d⁻¹ • N).map σ = 1 := by
    have h1 : N * N.map σ = Matrix.scalar (Fin 3) (c : F) := by
      have := congrArg Units.val hM
      rwa [Units.val_mul, GeneralLinearGroup.coe_scalar] at this
    have h2 : (d⁻¹ • N).map σ = σ d⁻¹ • N.map σ := by
      ext i j
      simp
    rw [h2, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h1, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, smul_smul, map_inv₀]
    have hσd : σ d ≠ 0 := by simpa using hd0
    have : d⁻¹ * (σ d)⁻¹ * (c : F) = 1 := by
      rw [← hd]
      field_simp
    rw [this, one_smul]
  obtain ⟨B, hB, hAB⟩ := exists_fixed_matrix hk hF hσ _ hA
  have hNB : N * B.map σ = d • B := by
    rw [Matrix.smul_mul] at hAB
    have h := congrArg (fun X => d • X) hAB
    simp only [smul_inv_smul₀ hd0] at h
    exact h
  refine ⟨GeneralLinearGroup.mk'' B hB, Units.mk0 d hd0, ?_⟩
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar, Units.val_mk0,
    Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
  exact hNB

omit [Finite F] in
theorem map_conj_twist_fixed {σ : F ≃+* F} {M Y : GL (Fin 3) F} {d : Fˣ}
    (hY : M * GeneralLinearGroup.map σ.toRingHom Y = GeneralLinearGroup.scalar (Fin 3) d * Y)
    {s : SL(3, F)} (hs : slConjugation 3 F M (SpecialLinearGroup.map σ.toRingHom s) = s) :
    SpecialLinearGroup.map σ.toRingHom (slConjugation 3 F Y⁻¹ s) = slConjugation 3 F Y⁻¹ s := by
  have e : GeneralLinearGroup.map σ.toRingHom Y⁻¹ =
      Y⁻¹ * (GeneralLinearGroup.scalar (Fin 3) d)⁻¹ * M := by
    rw [map_inv, eq_inv_mul_of_mul_eq hY]
    group
  rw [map_slConjugation, e, map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, ← map_inv,
    slConjugation_scalar, hs]

end Hilbert

section Fixed

variable {F : Type} [Field F]

theorem mem_range_map_of_fixed (σ : F ≃+* F) (t : SL(3, F))
    (ht : SpecialLinearGroup.map σ.toRingHom t = t) :
    t ∈ (SpecialLinearGroup.map
      (RingHom.eqLocusField σ.toRingHom (RingHom.id F)).subtype).range := by
  have hent : ∀ i j, σ ((t : Matrix (Fin 3) (Fin 3) F) i j) = (t : Matrix (Fin 3) (Fin 3) F) i j := by
    intro i j
    have := congrArg (fun g : SL(3, F) => (g : Matrix (Fin 3) (Fin 3) F) i j) ht
    simpa using this
  let F₀ := RingHom.eqLocusField σ.toRingHom (RingHom.id F)
  let M0 : Matrix (Fin 3) (Fin 3) F₀ :=
    Matrix.of fun i j => ⟨(t : Matrix (Fin 3) (Fin 3) F) i j, hent i j⟩
  have hM0 : F₀.subtype.mapMatrix M0 = (t : Matrix (Fin 3) (Fin 3) F) := by
    ext i j
    rfl
  have hdet : M0.det = 1 := by
    apply F₀.subtype.injective
    rw [RingHom.map_det, hM0, t.2, map_one]
  refine ⟨(⟨M0, hdet⟩ : SL(3, F₀)), ?_⟩
  apply Subtype.ext
  exact hM0

end Fixed

section Main

variable {F : Type} [Field F] [Finite F] [CharP F 2] {k : ℕ}

theorem card_le_of_twisted_fixed (hk : 1 ≤ k) (hF : Nat.card F = 2 ^ (2 * k)) {σ : F ≃+* F}
    (hσ : ∀ x, σ x = x ^ 2 ^ k) (M : GL (Fin 3) F) (c : Fˣ)
    (hM : M * GeneralLinearGroup.map σ.toRingHom M = GeneralLinearGroup.scalar (Fin 3) c)
    (S : Subgroup SL(3, F)) (hS2 : ∀ s ∈ S, s * s = 1) (hSc : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s)
    (hfix : ∀ s ∈ S, slConjugation 3 F M (SpecialLinearGroup.map σ.toRingHom s) = s) :
    Nat.card S ≤ 2 ^ (2 * k) := by
  obtain ⟨Y, d, hY⟩ := exists_twist_conjugator hk hF hσ M c hM
  let φ : SL(3, F) →* SL(3, F) := (slConjugation 3 F Y⁻¹).toMonoidHom
  let F₀ := RingHom.eqLocusField σ.toRingHom (RingHom.id F)
  let ψ : SL(3, F₀) →* SL(3, F) := SpecialLinearGroup.map F₀.subtype
  have hψ : Function.Injective ψ := by
    intro a b h
    apply Subtype.ext
    ext i j
    have := congrArg (fun g : SL(3, F) => (g : Matrix (Fin 3) (Fin 3) F) i j) h
    simpa [ψ] using this
  have hφ : Function.Injective φ := (slConjugation 3 F Y⁻¹).injective
  have hT : Nat.card (S.map φ) = Nat.card S := Subgroup.card_map_of_injective hφ
  have hTfix : S.map φ ≤ ψ.range := by
    rintro _ ⟨s, hs, rfl⟩
    exact mem_range_map_of_fixed σ _ (map_conj_twist_fixed hY (hfix s hs))
  have hmap : ((S.map φ).comap ψ).map ψ = S.map φ := by
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.mpr hTfix
  have hT₀ : Nat.card ((S.map φ).comap ψ) = Nat.card S := by
    rw [← hT, ← hmap, Subgroup.card_map_of_injective hψ, hmap]
  have hmem : ∀ a ∈ (S.map φ).comap ψ, ∃ s ∈ S, φ s = ψ a := fun a ha => ha
  have h2 : ∀ a ∈ (S.map φ).comap ψ, a * a = 1 := by
    intro a ha
    obtain ⟨s, hs, hsa⟩ := hmem a ha
    apply hψ
    rw [map_mul, ← hsa, ← map_mul, hS2 s hs, map_one, map_one]
  have hc : ∀ a ∈ (S.map φ).comap ψ, ∀ b ∈ (S.map φ).comap ψ, a * b = b * a := by
    intro a ha b hb
    obtain ⟨s, hs, hsa⟩ := hmem a ha
    obtain ⟨t, ht, htb⟩ := hmem b hb
    apply hψ
    rw [map_mul, map_mul, ← hsa, ← htb, ← map_mul, ← map_mul, hSc s hs t ht]
  have hF₀ : Nat.card F₀ ≤ 2 ^ k := by
    calc Nat.card F₀ = Nat.card {x : F // σ x = x} :=
          Nat.card_congr (Equiv.subtypeEquivRight fun x => by
            simp [F₀, RingHom.mem_eqLocusField])
      _ ≤ 2 ^ k := card_fixed_le hk hσ
  calc Nat.card S = Nat.card ((S.map φ).comap ψ) := hT₀.symm
    _ ≤ Nat.card F₀ ^ 2 := card_le_of_involutions _ h2 hc
    _ ≤ (2 ^ k) ^ 2 := Nat.pow_le_pow_left hF₀ 2
    _ = 2 ^ (2 * k) := by rw [← pow_mul, mul_comm]

end Main

end CFSG.Quasithin.G11.Harris.L3
