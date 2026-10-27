module

public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableBTypeAMono
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeABstar

public section

namespace CFSG.StandardType.TypeA

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {d p : ℕ} {K : Type} [Field K]

theorem coe_conj_toGL (A : GL (Fin d) K) (g : SpecialLinearGroup (Fin d) K) :
    ((A * SpecialLinearGroup.toGL g * A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      conjMat A g := by
  rw [Units.val_mul, Units.val_mul]
  rfl

theorem coe_map_GL (f : K →+* K) (M : GL (Fin d) K) :
    ((GeneralLinearGroup.map f M : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      (M : Matrix (Fin d) (Fin d) K).map f := by
  ext i j
  rw [GeneralLinearGroup.map_apply, Matrix.map_apply]

theorem rootT_pow {ζ : K} (hζ : ζ ^ p = 1) (i j : Fin d) (k : Fin d) : rootT ζ i j k ^ p = 1 := by
  unfold rootT
  split_ifs
  · exact hζ
  · rw [inv_pow, hζ, inv_one]
  · exact one_pow p

theorem prod_rootT {ζ : K} (hζ0 : ζ ≠ 0) {i j : Fin d} (hij : i ≠ j) : ∏ k, rootT ζ i j k = 1 := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), rootT_left,
    ← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩),
    rootT_right ζ hij]
  rw [Finset.prod_eq_one, mul_one, mul_inv_cancel₀ hζ0]
  intro k hk
  rw [Finset.mem_erase, Finset.mem_erase] at hk
  exact rootT_other ζ hk.2.1 hk.1

theorem ne_inv_of_sq_ne_one {x : K} (hx0 : x ≠ 0) (hx : x ^ 2 ≠ 1) : x ≠ x⁻¹ := by
  intro h
  apply hx
  rw [pow_two]
  nth_rewrite 2 [h]
  exact mul_inv_cancel₀ hx0

theorem ne_inv_of_isPrimitiveRoot {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hp : p.Prime)
    (hp2 : p ≠ 2) : ζ ≠ ζ⁻¹ := by
  refine ne_inv_of_sq_ne_one (hζ.ne_zero hp.ne_zero) ?_
  intro h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp ((hζ.pow_eq_one_iff_dvd 2).mp h))

section NormalForm

variable [Finite K] (hd : 0 < d) (hpd : Nat.Coprime p d)
  {X : Subgroup (MulAut (projectiveSL d K))} (hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x)

include hXc in
theorem exists_mem_slLift_of_mem (hXp : ∀ x ∈ X, x ^ p = 1)
    (hXI : ∀ x ∈ X, ∃ A : GL (Fin d) K, conjAut d K A = x) {x : MulAut (projectiveSL d K)}
    (hx : x ∈ X) :
    ∃ g ∈ slLift hd hpd X hXc, conjAut d K (SpecialLinearGroup.toGL g) = x := by
  obtain ⟨A, rfl⟩ := hXI x hx
  obtain ⟨g, hgp, hgA⟩ := exists_slLift hd hpd (hXp _ hx)
  exact ⟨g, ⟨hgp, hgA ▸ hx⟩, hgA⟩

omit [Finite K] in
theorem conjAut_conj (A₀ M : GL (Fin d) K) :
    conjAut d K (A₀ * M * A₀⁻¹) = conjAut d K A₀ * conjAut d K M * (conjAut d K A₀)⁻¹ := by
  rw [map_mul, map_mul, map_inv]

omit [Finite K] in
theorem conjAut_semilinear_conj (A : GL (Fin d) K) (σ : K ≃+* K) (B : GL (Fin d) K) :
    conjAut d K A * fieldAut d K σ * conjAut d K B * (conjAut d K A * fieldAut d K σ)⁻¹ =
      conjAut d K (A * GeneralLinearGroup.map (σ : K →+* K) B * A⁻¹) := by
  have htrans := standard_automorphism_transport (K := K) (n := d)
  calc conjAut d K A * fieldAut d K σ * conjAut d K B * (conjAut d K A * fieldAut d K σ)⁻¹ =
        conjAut d K A * (fieldAut d K σ * conjAut d K B * (fieldAut d K σ)⁻¹) *
          (conjAut d K A)⁻¹ := by group
    _ = _ := by rw [htrans.2.2.1 σ B, ← map_inv, ← map_mul, ← map_mul]

theorem exists_scalar_mul_diag {A₀ : GL (Fin d) K}
    (hdiag : ∀ g ∈ slLift hd hpd X hXc, ∀ i j, i ≠ j → conjMat A₀ g i j = 0)
    (A : GL (Fin d) K) (σ : K ≃+* K) {g g' : SpecialLinearGroup (Fin d) K}
    (hg : g ∈ slLift hd hpd X hXc) (hg' : g' ∈ slLift hd hpd X hXc)
    (hgg' : conjAut d K (SpecialLinearGroup.toGL g') =
      conjAut d K A * fieldAut d K σ * conjAut d K (SpecialLinearGroup.toGL g) *
        (conjAut d K A * fieldAut d K σ)⁻¹) :
    ∃ c : K, ((A₀ * A * GeneralLinearGroup.map (σ : K →+* K) A₀⁻¹ : GL (Fin d) K) :
        Matrix (Fin d) (Fin d) K) * diagonal (fun k => σ (conjMat A₀ g k k)) =
      diagonal (fun k => conjMat A₀ g' k k * c) *
        ((A₀ * A * GeneralLinearGroup.map (σ : K →+* K) A₀⁻¹ : GL (Fin d) K) :
          Matrix (Fin d) (Fin d) K) := by
  obtain ⟨P, hP⟩ : ∃ P : GL (Fin d) K,
      P = A₀ * A * GeneralLinearGroup.map (σ : K →+* K) A₀⁻¹ := ⟨_, rfl⟩
  rw [← hP]
  obtain ⟨D₁, hD₁⟩ : ∃ D₁ : GL (Fin d) K, D₁ = A₀ * SpecialLinearGroup.toGL g' * A₀⁻¹ :=
    ⟨_, rfl⟩
  obtain ⟨Dσ, hDσ⟩ : ∃ Dσ : GL (Fin d) K,
      Dσ = GeneralLinearGroup.map (σ : K →+* K) (A₀ * SpecialLinearGroup.toGL g * A₀⁻¹) :=
    ⟨_, rfl⟩
  have e1 : P * Dσ * P⁻¹ = A₀ * (A * GeneralLinearGroup.map (σ : K →+* K)
      (SpecialLinearGroup.toGL g) * A⁻¹) * A₀⁻¹ := by
    rw [hP, hDσ]
    simp only [map_mul, map_inv]
    group
  have hD : conjAut d K D₁ = conjAut d K (P * Dσ * P⁻¹) := by
    rw [e1, conjAut_conj, ← conjAut_semilinear_conj, ← hgg', hD₁, conjAut_conj]
  obtain ⟨c, hc⟩ := exists_scalar_of_conjAut_eq_one (A := D₁⁻¹ * (P * Dσ * P⁻¹))
    (by rw [map_mul, map_inv, hD, inv_mul_cancel])
  have hmD₁ : (D₁ : Matrix (Fin d) (Fin d) K) = diagonal (fun k => conjMat A₀ g' k k) := by
    rw [hD₁, coe_conj_toGL]
    exact (conjMat_diag hg'.1 (hdiag g' hg')).1
  have hmDσ : (Dσ : Matrix (Fin d) (Fin d) K) = diagonal (fun k => σ (conjMat A₀ g k k)) := by
    have e := (conjMat_diag hg.1 (hdiag g hg)).1
    rw [hDσ, coe_map_GL, coe_conj_toGL]
    conv_lhs => rw [e]
    rw [diagonal_map (map_zero _)]
    rfl
  refine ⟨c, ?_⟩
  have h1 : ((P * Dσ * P⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      (D₁ : Matrix (Fin d) (Fin d) K) * scalar (Fin d) c := by
    rw [← hc, ← Units.val_mul, mul_inv_cancel_left]
  have h2 : (P : Matrix (Fin d) (Fin d) K) * (Dσ : Matrix (Fin d) (Fin d) K) =
      (D₁ : Matrix (Fin d) (Fin d) K) * scalar (Fin d) c * (P : Matrix (Fin d) (Fin d) K) := by
    rw [← h1, ← Units.val_mul, ← Units.val_mul, inv_mul_cancel_right]
  rw [hmDσ, hmD₁, scalar_apply, diagonal_mul_diagonal] at h2
  exact h2

theorem semilinear_normal_form (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1)
    (hXp : ∀ x ∈ X, x ^ p = 1) (hXI : ∀ x ∈ X, ∃ A : GL (Fin d) K, conjAut d K A = x)
    {A₀ : GL (Fin d) K}
    (hdiag : ∀ g ∈ slLift hd hpd X hXc, ∀ i j, i ≠ j → conjMat A₀ g i j = 0)
    (hfull : ∀ t : Fin d → K, (∀ i, t i ^ p = 1) → ∏ i, t i = 1 →
      ∃ g ∈ slLift hd hpd X hXc, conjMat A₀ g = diagonal t)
    (A : GL (Fin d) K) (σ : K ≃+* K)
    (hN : ∀ x ∈ X, conjAut d K A * fieldAut d K σ * x * (conjAut d K A * fieldAut d K σ)⁻¹ ∈ X) :
    ∃ π : Equiv.Perm (Fin d),
      (∀ u : Fin d → K, ((A₀ * A * GeneralLinearGroup.map (σ : K →+* K) A₀⁻¹ : GL (Fin d) K) :
          Matrix (Fin d) (Fin d) K) * diagonal u =
        diagonal (u ∘ π) * ((A₀ * A * GeneralLinearGroup.map (σ : K →+* K) A₀⁻¹ :
          GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) ∧
      ∀ g ∈ slLift hd hpd X hXc, ∀ g' ∈ slLift hd hpd X hXc,
        conjAut d K (SpecialLinearGroup.toGL g') =
          conjAut d K A * fieldAut d K σ * conjAut d K (SpecialLinearGroup.toGL g) *
            (conjAut d K A * fieldAut d K σ)⁻¹ →
        ∀ k, conjMat A₀ g' k k = σ (conjMat A₀ g (π k) (π k)) := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot hp hpK
  have hζ' : σ ζ ≠ (σ ζ)⁻¹ := ne_inv_of_isPrimitiveRoot (hζ.map_of_injective σ.injective) hp hp2
  obtain ⟨P, hP⟩ : ∃ P : GL (Fin d) K,
      P = A₀ * A * GeneralLinearGroup.map (σ : K →+* K) A₀⁻¹ := ⟨_, rfl⟩
  rw [← hP]
  have hmono : ∀ i j : Fin d, i ≠ j → ∃ D : Fin d → K,
      (P : Matrix (Fin d) (Fin d) K) * diagonal (rootT (σ ζ) i j) =
        diagonal D * (P : Matrix (Fin d) (Fin d) K) := by
    intro i j hij
    obtain ⟨g, hg, hgt⟩ := hfull (rootT ζ i j) (rootT_pow hζ.pow_eq_one i j)
      (prod_rootT (hζ.ne_zero hp.ne_zero) hij)
    obtain ⟨g', hg', hgg'⟩ := exists_mem_slLift_of_mem hd hpd hXc hXp hXI (hN _ hg.2)
    obtain ⟨c, hc⟩ := exists_scalar_mul_diag hd hpd hXc hdiag A σ hg hg' hgg'
    rw [← hP] at hc
    have e : (fun k => σ (conjMat A₀ g k k)) = rootT (σ ζ) i j := by
      funext k
      rw [hgt, diagonal_apply_eq]
      unfold rootT
      split_ifs <;> simp [map_inv₀]
    rw [e] at hc
    exact ⟨_, hc⟩
  obtain ⟨π, hπ⟩ := exists_perm_mul_diagonal hζ' P hmono
  refine ⟨π, hπ, fun g hg g' hg' hgg' k => ?_⟩
  obtain ⟨c, hc⟩ := exists_scalar_mul_diag hd hpd hXc hdiag A σ hg hg' hgg'
  rw [← hP, hπ] at hc
  have hc' := congrArg (· * ((P⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) hc
  simp only [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.mul_one] at hc'
  have hent : ∀ k, σ (conjMat A₀ g (π k) (π k)) = conjMat A₀ g' k k * c := by
    intro k
    have := congrFun (congrFun hc' k) k
    simpa [diagonal_apply_eq] using this
  have hTg := conjMat_diag hg.1 (hdiag g hg)
  have hTg' := conjMat_diag hg'.1 (hdiag g' hg')
  have hcd : c ^ d = 1 := by
    have h1 : ∏ k, σ (conjMat A₀ g (π k) (π k)) = 1 := by
      rw [← map_prod, Equiv.prod_comp π (fun i => conjMat A₀ g i i), hTg.2.2, map_one]
    rw [Finset.prod_congr rfl fun k _ => hent k, Finset.prod_mul_distrib, hTg'.2.2, one_mul,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
    exact h1
  have hcp : c ^ p = 1 := by
    set k₀ : Fin d := ⟨0, hd⟩
    have h1 := hent k₀
    have h2 : (conjMat A₀ g' k₀ k₀ * c) ^ p = 1 := by
      rw [← h1, ← map_pow, hTg.2.1, map_one]
    rwa [mul_pow, hTg'.2.1, one_mul] at h2
  have hc1 : c = 1 := by
    have h := pow_gcd_eq_one.mpr ⟨hcp, hcd⟩
    rwa [Nat.Coprime.gcd_eq_one hpd, pow_one] at h
  rw [hent k, hc1, mul_one]

end NormalForm

end CFSG.StandardType.TypeA
