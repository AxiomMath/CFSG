module

public import CFSG.RankThree.PartOne.K133.ProjUnip4
public import CFSG.LieType.BorelTits.UnitaryForm
public import CFSG.RankThree.PartOne.K133.InnerRed

public section

namespace CFSG.RankThree.PartOne.K133

open CFSG CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank Module Matrix Polynomial

theorem unitary_unip_scalar_fixed {K ι : Type} [Field K] [Fintype ι] [DecidableEq ι] (φ : K →+* K)
    (N : Matrix ι ι K) (c : K) (h1 : ((1 + N).map φ)ᵀ * (1 + N) = 1)
    (h2 : ((1 + c • N).map φ)ᵀ * (1 + c • N) = 1) (hsq : N * N = 0) (hN : N ≠ 0) : φ c = c := by
  classical
  set N' : Matrix ι ι K := (N.map φ)ᵀ with hN'
  have hadd : ∀ X Y : Matrix ι ι K, ((X + Y).map φ)ᵀ = (X.map φ)ᵀ + (Y.map φ)ᵀ := fun X Y => by
    ext i j; simp
  have hsmul : ∀ (a : K) (X : Matrix ι ι K), ((a • X).map φ)ᵀ = φ a • (X.map φ)ᵀ := fun a X => by
    ext i j; simp
  have hone : ((1 : Matrix ι ι K).map φ)ᵀ = 1 := by
    ext i j
    by_cases hij : j = i
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  rw [hadd, hone] at h1 h2
  rw [hsmul] at h2
  have E1 : N + N' + N' * N = 0 := by
    have e : (1 + N') * (1 + N) = 1 + (N + N' + N' * N) := by noncomm_ring
    rw [e] at h1
    have := congrArg (fun X => X - 1) h1
    simpa using this
  have E2 : c • N + φ c • N' + (φ c * c) • (N' * N) = 0 := by
    have e : (1 + φ c • N') * (1 + c • N) =
        1 + (c • N + φ c • N' + (φ c * c) • (N' * N)) := by
      simp only [add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      module
    rw [e] at h2
    have := congrArg (fun X => X - 1) h2
    simpa using this
  by_cases hc0 : c = 0
  · rw [hc0, map_zero]
  by_cases hc1 : c = 1
  · rw [hc1, map_one]
  have hφ0 : φ c ≠ 0 := fun h => hc0 (φ.injective (by rw [h, map_zero]))
  have hc1' : c - 1 ≠ 0 := sub_ne_zero.2 hc1
  have E3 : (c * (φ c - 1)) • N + (φ c * (c - 1)) • N' = 0 := by
    have : (φ c * c) • (N + N' + N' * N) - (c • N + φ c • N' + (φ c * c) • (N' * N)) = 0 := by
      rw [E1, E2]; simp
    rw [← this]
    module
  have hα : φ c * (c - 1) ≠ 0 := mul_ne_zero hφ0 hc1'
  have hP : N' * N = 0 := by
    have h' : (φ c * (c - 1)) • N' = -((c * (φ c - 1)) • N) := eq_neg_of_add_eq_zero_right E3
    have h : (φ c * (c - 1)) • (N' * N) = 0 := by
      rw [← Matrix.smul_mul, h', Matrix.neg_mul, Matrix.smul_mul, hsq, smul_zero, neg_zero]
    exact (smul_eq_zero.1 h).resolve_left hα
  have hN'eq : N' = -N := by
    have : N + N' = 0 := by simpa [hP] using E1
    exact eq_neg_of_add_eq_zero_right this
  rw [hN'eq] at E3
  have h3 : (c * (φ c - 1) - φ c * (c - 1)) • N = 0 := by
    rw [← E3]
    module
  have h0 := (smul_eq_zero.1 h3).resolve_right hN
  linear_combination h0

theorem exists_natCast_of_pow_char_eq_self {K : Type} [Field K] [Finite K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    {c : K} (hc : c ^ ℓ = c) : ∃ k : ℕ, (k : K) = c := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  let ψ : ZMod ℓ →+* K := ZMod.castHom (dvd_refl ℓ) K
  have hψinj : Function.Injective ψ := ψ.injective
  let T : Finset K := Finset.univ.image ψ
  have hTcard : T.card = ℓ := by
    rw [Finset.card_image_of_injective _ hψinj, Finset.card_univ, ZMod.card]
  let P : K[X] := X ^ ℓ - X
  have hPdeg : P.natDegree = ℓ :=
    FiniteField.X_pow_card_sub_X_natDegree_eq K (Fact.out : ℓ.Prime).one_lt
  have hP0 : P ≠ 0 := Polynomial.ne_zero_of_natDegree_gt (n := 0) (by
    rw [hPdeg]; exact (Fact.out : ℓ.Prime).pos)
  let S : Finset K := P.roots.toFinset
  have hScard : S.card ≤ ℓ :=
    (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' P).trans hPdeg.le)
  have hTS : T ⊆ S := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP0]
    simp [P, Polynomial.IsRoot, ← map_pow, ZMod.pow_card]
  have hcS : c ∈ S := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP0]
    simp [P, Polynomial.IsRoot, hc]
  have hTeq : T = S := Finset.eq_of_subset_of_card_le hTS (by rw [hTcard]; exact hScard)
  rw [← hTeq] at hcS
  obtain ⟨y, -, hy⟩ := Finset.mem_image.1 hcS
  refine ⟨y.val, ?_⟩
  rw [← hy]
  calc ((y.val : ℕ) : K) = ψ ((y.val : ℕ) : ZMod ℓ) := (map_natCast ψ _).symm
    _ = ψ y := by rw [ZMod.natCast_zmod_val]

theorem statedSU_scalar_criterion {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (hf : f = 1) (a₁ a₂ : StatedSU 4 (ℓ ^ f) K) (c₁ c₂ μ₁ μ₂ : Kˣ)
    (h₁ : (a₁ : GL (Fin 4) K) ^ ℓ = Matrix.GeneralLinearGroup.scalar (Fin 4) c₁)
    (h₂ : (a₂ : GL (Fin 4) K) ^ ℓ = Matrix.GeneralLinearGroup.scalar (Fin 4) c₂)
    (hμ₁ : (μ₁ : K) ^ ℓ = (c₁ : K)) (hμ₂ : (μ₂ : K) ^ ℓ = (c₂ : K))
    (hsq : unipPart μ₁ (a₁ : GL (Fin 4) K) * unipPart μ₁ (a₁ : GL (Fin 4) K) = 0)
    (hN : unipPart μ₁ (a₁ : GL (Fin 4) K) ≠ 0) (c : K)
    (hc : unipPart μ₂ (a₂ : GL (Fin 4) K) = c • unipPart μ₁ (a₁ : GL (Fin 4) K)) :
    ∃ k : ℕ, (k : K) = c := by
  classical
  let φ : K →+* K := (unitaryInvolution K ℓ f).toRingHom
  have hφ : ∀ x : K, φ x = x ^ ℓ := fun x => by
    show unitaryInvolution K ℓ f x = x ^ ℓ
    rw [unitaryInvolution_apply, hf, pow_one]
  have hu : ∀ a : StatedSU 4 (ℓ ^ f) K,
      (((a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map φ)ᵀ * ((a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
        = 1 := fun a =>
    (unitaryForm_preserves_iff hK _).1 (fun u v => statedSU_preserves hK a.2 u v)
  have hsmul : ∀ (r : K) (X : Matrix (Fin 4) (Fin 4) K), ((r • X).map φ)ᵀ = φ r • (X.map φ)ᵀ :=
    fun r X => by ext i j; simp
  have hμ : ∀ (a : StatedSU 4 (ℓ ^ f) K) (c μ : Kˣ),
      (a : GL (Fin 4) K) ^ ℓ = Matrix.GeneralLinearGroup.scalar (Fin 4) c → (μ : K) ^ ℓ = (c : K) →
      (μ : K) ^ (ℓ + 1) = 1 := by
    intro a c μ ha hμc
    have hpow : ((a ^ ℓ : StatedSU 4 (ℓ ^ f) K) : GL (Fin 4) K) = Matrix.GeneralLinearGroup.scalar (Fin 4) c := by
      rw [← ha]; rfl
    have h1 := hu (a ^ ℓ)
    rw [hpow, Matrix.GeneralLinearGroup.coe_scalar] at h1
    have h2 := congrFun (congrFun h1 0) 0
    simp [Matrix.scalar_apply, Matrix.diagonal_apply_eq, hφ] at h2
    have h3 : (c : K) ^ (ℓ + 1) = 1 := by rw [pow_succ]; exact h2
    refine eq_one_of_pow_char_pow_eq_one ℓ (e := 1) ?_
    rw [pow_one, ← pow_mul, mul_comm, pow_mul, hμc, h3]
  have hμ₁' := hμ a₁ c₁ μ₁ h₁ hμ₁
  have hμ₂' := hμ a₂ c₂ μ₂ h₂ hμ₂
  have hus : ∀ (a : StatedSU 4 (ℓ ^ f) K) (μ : Kˣ), (μ : K) ^ (ℓ + 1) = 1 →
      (((1 + unipPart μ (a : GL (Fin 4) K)).map φ)ᵀ) * (1 + unipPart μ (a : GL (Fin 4) K)) = 1 := by
    intro a μ hμ1
    have e : 1 + unipPart μ (a : GL (Fin 4) K) =
        ((μ⁻¹ : Kˣ) : K) • ((a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
      simp [unipPart]
    rw [e, hsmul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hu a]
    have : φ ((μ⁻¹ : Kˣ) : K) * ((μ⁻¹ : Kˣ) : K) = 1 := by
      rw [hφ, ← pow_succ, Units.val_inv_eq_inv_val, inv_pow, hμ1, inv_one]
    rw [this, one_smul]
  have hfix : φ c = c := by
    refine unitary_unip_scalar_fixed φ (unipPart μ₁ (a₁ : GL (Fin 4) K)) c (hus a₁ μ₁ hμ₁') ?_ hsq hN
    rw [← hc]
    exact hus a₂ μ₂ hμ₂'
  rw [hφ] at hfix
  exact exists_natCast_of_pow_char_eq_self hfix

theorem goodRes_statedProj_su_four_char {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (hf : f = 1) (h5 : 5 ≤ ℓ)
    [IsSimpleGroup (StatedProj (StatedSU 4 (ℓ ^ f) K))]
    (hne : ∃ a b : StatedProj (StatedSU 4 (ℓ ^ f) K), a * b ≠ b * a)
    (hOut : ∀ E : Subgroup (MulAut (StatedProj (StatedSU 4 (ℓ ^ f) K))), IsElementaryAbelian ℓ E →
      E ≤ ComponentClassification.OuterAutomorphisms.inner (StatedProj (StatedSU 4 (ℓ ^ f) K))) :
    GoodRes ℓ (StatedProj (StatedSU 4 (ℓ ^ f) K)) := by
  have hZ : Subgroup.center (StatedProj (StatedSU 4 (ℓ ^ f) K)) = ⊥ :=
    center_eq_bot_of_simple_nonabelian hne
  refine goodRes_of_inner_noConfig_el (Fact.out : ℓ.Prime) hZ hOut ?_
  intro C hC hCc Kb hKs hKn hpKb hall
  exact statedProj_four_no_config' h5 (ι := Fin 4) (by simp) (StatedSU 4 (ℓ ^ f) K)
    (fun a₁ a₂ c₁ c₂ μ₁ μ₂ h₁ h₂ hμ₁ hμ₂ hsq hN c hc =>
      statedSU_scalar_criterion hK hf a₁ a₂ c₁ c₂ μ₁ μ₂ h₁ h₂ hμ₁ hμ₂ hsq hN c hc)
    C hC hCc Kb hKn hall

end CFSG.RankThree.PartOne.K133
