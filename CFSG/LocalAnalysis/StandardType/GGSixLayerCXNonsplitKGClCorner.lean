module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGClLift

public section

namespace CFSG.StandardType

namespace ClNonsplit

open Matrix

section Corner

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem mul_single_mul_apply (M N : Matrix ι ι F) (k l i j : ι) :
    (M * Matrix.single k l (1 : F) * N : Matrix ι ι F) i j = M i k * N l j := by
  classical
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and]

theorem exists_eq_smul_of_commute_corner {P z : Matrix ι ι F} (hP : P ≠ 0)
    (hPz : P * z = z) (hzP : z * P = z)
    (hc : ∀ M : Matrix ι ι F, z * (P * M * P) = P * M * P * z) :
    ∃ c : F, z = c • P := by
  classical
  have key : ∀ i k l j, z i k * P l j = P i k * z l j := by
    intro i k l j
    have h := congrFun (congrFun (hc (Matrix.single k l (1 : F))) i) j
    have e1 : (z * (P * Matrix.single k l (1 : F) * P) : Matrix ι ι F) i j =
        z i k * P l j := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hzP, mul_single_mul_apply]
    have e2 : (P * Matrix.single k l (1 : F) * P * z : Matrix ι ι F) i j =
        P i k * z l j := by
      rw [Matrix.mul_assoc _ P z, hPz, mul_single_mul_apply]
    rw [← e1, ← e2, h]
  obtain ⟨l, j, hlj⟩ : ∃ l j, P l j ≠ 0 := by
    by_contra h
    push Not at h
    exact hP (Matrix.ext h)
  refine ⟨z l j / P l j, Matrix.ext fun i k => ?_⟩
  rw [Matrix.smul_apply, smul_eq_mul]
  field_simp
  linear_combination key i k l j

variable {r : ℕ} {D : Fin r → Type*} {d : Fin r → ℕ} [∀ i, Field (D i)] [∀ i, Algebra F (D i)]

theorem algebraMap_surjective_of_corner
    (Φ : (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) →ₐ[F] Matrix ι ι F)
    (hΦinj : Function.Injective Φ) {A : Matrix ι ι F}
    (hrange : ∀ X : Matrix ι ι F, X * A = A * X → X ∈ Set.range Φ)
    {b : Fin r} (hd : NeZero (d b))
    (h1 : Φ (Pi.single b 1) * A = Φ (Pi.single b 1))
    (h2 : A * Φ (Pi.single b 1) = Φ (Pi.single b 1)) :
    Function.Surjective (algebraMap F (D b)) := by
  classical
  set e : Π i, Matrix (Fin (d i)) (Fin (d i)) (D i) := Pi.single b 1 with he
  set P := Φ e with hP
  intro t
  set c : Π i, Matrix (Fin (d i)) (Fin (d i)) (D i) := Pi.single b (t • 1) with hcdef
  have hcen : ∀ w, c * w = w * c := by
    intro w
    funext i
    by_cases hi : i = b
    · subst hi
      simp [hcdef]
    · simp [hcdef, hi]
  have hec : e * c = c := by
    funext i
    by_cases hi : i = b
    · subst hi
      simp [he, hcdef]
    · simp [he, hcdef, hi]
  have hce : c * e = c := by
    funext i
    by_cases hi : i = b
    · subst hi
      simp [he, hcdef]
    · simp [he, hcdef, hi]
  have hPne : P ≠ 0 := by
    intro h
    have h0 : e = 0 := hΦinj (by rw [← hP, h, map_zero])
    have h00 := congrFun h0 b
    simp [he] at h00
  obtain ⟨c₀, hc₀⟩ := exists_eq_smul_of_commute_corner hPne (z := Φ c)
    (by rw [hP, ← map_mul, hec]) (by rw [hP, ← map_mul, hce]) fun M => by
      obtain ⟨w, hw⟩ := hrange (P * M * P) (by
        rw [Matrix.mul_assoc (P * M) P A, h1, ← Matrix.mul_assoc A (P * M) P,
          ← Matrix.mul_assoc A P M, h2])
      rw [← hw, ← map_mul, ← map_mul, hcen]
  refine ⟨c₀, ?_⟩
  have h3 : c = c₀ • e := hΦinj (by rw [hc₀, map_smul])
  have h4 := congrFun h3 b
  simp only [hcdef, he, Pi.single_eq_same, Pi.smul_apply] at h4
  have i₀ : Fin (d b) := ⟨0, Nat.pos_of_ne_zero hd.ne⟩
  have h5 := congrFun (congrFun h4 i₀) i₀
  simp [Algebra.smul_def] at h5
  exact h5.symm

theorem card_eq_of_corner
    (Φ : (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) →ₐ[F] Matrix ι ι F)
    (hΦinj : Function.Injective Φ) {A : Matrix ι ι F}
    (hrange : ∀ X : Matrix ι ι F, X * A = A * X → X ∈ Set.range Φ)
    {b : Fin r} (hd : NeZero (d b))
    (h1 : Φ (Pi.single b 1) * A = Φ (Pi.single b 1))
    (h2 : A * Φ (Pi.single b 1) = Φ (Pi.single b 1)) :
    Nat.card (D b) = Nat.card F :=
  (Nat.card_congr (Equiv.ofBijective _ ⟨(algebraMap F (D b)).injective,
    algebraMap_surjective_of_corner Φ hΦinj hrange hd h1 h2⟩)).symm

end Corner

open LayerCores

section Block

variable {K : Type} [Field K] {r : ℕ} {D : Fin r → Type} [∀ i, Field (D i)]
  [∀ i, Algebra K (D i)] {d : Fin r → ℕ} [∀ i, NeZero (d i)] {τ : PiMat D d → PiMat D d}
  {π : Fin r → Fin r}

omit [∀ i, NeZero (d i)] in
theorem tauFix_scalar_of_smul (hπ : ∀ i, τ (piE D d i) = piE D d (π i))
    {b : Fin r} (hb : π b = b) (hτK : ∀ (c : K) (y : PiMat D d), τ (c • y) = c • τ y)
    (hsurj : Function.Surjective (algebraMap K (D b))) (c : D b) :
    tauFix τ b (Matrix.scalar (Fin (d b)) c) = Matrix.scalar (Fin (d b)) c := by
  classical
  obtain ⟨c₀, rfl⟩ := hsurj c
  have hsc : Matrix.scalar (Fin (d b)) (algebraMap K (D b) c₀) =
      c₀ • (1 : Matrix (Fin (d b)) (Fin (d b)) (D b)) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Algebra.smul_def]
    · simp [hij, Matrix.one_apply_ne hij]
  have h1 : (Pi.single b (Matrix.scalar (Fin (d b)) (algebraMap K (D b) c₀)) : PiMat D d) =
      c₀ • piE D d b := by
    funext i
    by_cases hi : i = b
    · subst hi
      simp [piE, hsc]
    · simp [piE, hi]
  show τ (Pi.single b _) b = _
  rw [h1, hτK, hπ, hb, hsc]
  simp [piE]

theorem conj_eq_conj_of_mem_orbitGroup (hτ : IsInvol τ) (hπ : ∀ i, τ (piE D d i) = piE D d (π i))
    {b : Fin r} {a γ ã : (PiMat D d)ˣ} (ha : a ∈ unitaryOf hτ) (hγ : γ ∈ orbitGroup π hτ b)
    (hã : ã ∈ orbitGroup π hτ b) (hãa : coordHom D d b ã = coordHom D d b a) :
    a⁻¹ * γ * a = ã⁻¹ * γ * ã := by
  have h1 : a⁻¹ * γ * a ∈ orbitGroup π hτ b := by
    have h := conj_mem_orbitGroup hτ (Subgroup.inv_mem _ ha) hγ
    rwa [inv_inv] at h
  have h2 : ã⁻¹ * γ * ã ∈ orbitGroup π hτ b := by
    have h := conj_mem_orbitGroup hτ (Subgroup.inv_mem _ hã.1) hγ
    rwa [inv_inv] at h
  refine coordHom_injOn hτ hπ h1 h2 ?_
  simp only [map_mul, map_inv, hãa]

end Block

end ClNonsplit

end CFSG.StandardType
