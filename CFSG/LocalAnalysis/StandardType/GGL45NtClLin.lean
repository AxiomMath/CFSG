module

public import CFSG.LocalAnalysis.StandardType.GGL45NtClTransfer
public import CFSG.LocalAnalysis.StandardType.GGL45NtClRecipes
public import CFSG.LocalAnalysis.StandardType.GGL45NtClLinBlocks
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldLinear
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
public import CFSG.Monster.B.TwoA.Unitary.Semilinear

public section

namespace CFSG.HardMathSupport.C14Cl

open CFSG CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

@[expose] noncomputable def linSigmaGL {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (σ₀ : K ≃+* K) : GL ι K →* GL ι K :=
  Units.map (σ₀.mapMatrix : Matrix ι ι K ≃+* Matrix ι ι K).toRingHom.toMonoidHom

theorem matrix_core_lin {K : Type} [Field K] [Fintype K] [CharP K 2] {ι : Type} [Fintype ι]
    [DecidableEq ι] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (σ₀ : K ≃+* K) (hσ₀ : orderOf σ₀ = p)
    (E₀ : Subgroup (GL ι K)) (hE : IsElemAbelian p E₀)
    (hEfix : ∀ e ∈ E₀, (e : Matrix ι ι K).map σ₀ = e)
    (hSat : ∀ y : GL ι K, (∀ e ∈ E₀, y * e = e * y) → y ^ p = 1 →
      (y : Matrix ι ι K).map σ₀ = y → (y : Matrix ι ι K) ∈ spanE K E₀)
    (hcard : p ^ 2 ≤ Nat.card E₀) :
    ClCoreConcl p E₀ (linSigmaGL σ₀) := by
  unfold ClCoreConcl
  haveI := Fact.mk hp
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  obtain ⟨a, ha⟩ := exists_pow_two_of_ringEquiv σ₀
  have hσp : σ₀ ^ p = 1 := hσ₀ ▸ pow_orderOf_eq_one σ₀
  have hiter : ∀ k (c : K), (σ₀ ^ k) c = c ^ 2 ^ (a * k) := by
    intro k
    induction k with
    | zero => intro c; simp
    | succ k ih =>
      intro c
      rw [pow_succ']
      change σ₀ ((σ₀ ^ k) c) = _
      rw [ih, map_pow, ha, ← pow_mul, ← pow_add, Nat.mul_succ, add_comm]
  have hfix : ∀ c : K, c ^ 2 ^ (a * p) = c := fun c => by rw [← hiter, hσp]; rfl
  have hap : (n : ℕ) ∣ a * p := dvd_of_forall_pow_two_pow_eq hn hfix
  have hna : ¬ (n : ℕ) ∣ a := by
    rintro ⟨j, hj⟩
    have h1 : σ₀ = 1 := RingEquiv.ext fun c => by
      show σ₀ c = c
      rw [ha, hj, pow_mul, ← hn]; exact FiniteField.pow_card_pow j c
    have h2 := hσ₀
    rw [h1, orderOf_one] at h2
    exact hp.one_lt.ne h2
  set d := orderOf (((2 ^ (n : ℕ) : ℕ)) : ZMod p) with hd
  set s := padicValNat p ((2 ^ (n : ℕ)) ^ d - 1) with hs
  obtain ⟨hs2, k, hk, hN⟩ := power_class hp hp2 hap hna hd hs
  have hA : ∀ x, CentPAbs p E₀ x → (x : Matrix ι ι K) ∈ spanE K E₀ := by
    intro x hx
    rw [CentPAbs.eq_def] at hx
    exact pElt_mem_A_lin hp hp2 σ₀ hσ₀ E₀ hE hEfix hSat hx.1 hx.2
  have hd0 : d ≠ 0 := by
    have h2 : ¬ p ∣ 2 ^ (n : ℕ) := fun h => hp2
      ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
    have : ((2 ^ (n : ℕ) : ℕ) : ZMod p) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; exact h2
    exact (orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨p - 1, by have := hp.two_le; omega,
      ZMod.pow_card_sub_one_eq_one this⟩)).ne'
  have hQ : ∀ M ∈ spanE K E₀, M ^ 2 ^ ((n : ℕ) * d) = M := by
    refine pow_eq_self_of_mem_spanE E₀ hE.1 hE.2 (fun c => ?_) ?_
    · rw [pow_mul, ← hn]; exact FiniteField.pow_card_pow d c
    · rw [← ZMod.natCast_eq_natCast_iff, pow_mul, Nat.cast_pow (2 ^ (n : ℕ)), hd]
      push_cast
      rw [← Nat.cast_ofNat, ← Nat.cast_pow, pow_orderOf_eq_one]
  have hexp : ∀ x, CentPAbs p E₀ x → x ^ p ^ s = 1 := by
    intro x hx
    have hx' := hx
    rw [CentPAbs.eq_def] at hx'
    obtain ⟨j, hj⟩ := hx'.2
    have hxQ : x ^ (2 ^ ((n : ℕ) * d) - 1) = 1 := by
      have h1 : x ^ (2 ^ ((n : ℕ) * d) - 1) * x = x := by
        rw [← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow]
        exact Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hQ _ (hA x hx))
      simpa using h1
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hj)
    have hne : 2 ^ ((n : ℕ) * d) - 1 ≠ 0 := by
      have : 1 < 2 ^ ((n : ℕ) * d) := Nat.one_lt_two_pow (mul_ne_zero n.ne_zero hd0)
      omega
    have hpi : p ^ i ∣ 2 ^ ((n : ℕ) * d) - 1 := hi ▸ orderOf_dvd_of_pow_eq_one hxQ
    rw [padicValNat_dvd_iff_le hne, pow_mul] at hpi
    exact orderOf_dvd_iff_pow_eq_one.1 (hi ▸ pow_dvd_pow p hpi)
  refine ⟨s, hs2, k, hk, fun x y hx hy => Units.ext ?_, fun x hx => ⟨hexp x hx, ?_⟩,
    fun x hx w hw => Units.ext ?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul]; exact spanE_commute E₀ hE.1 (hA x hx) (hA y hy)
  · have hmod : 2 ^ (a * p) ≡ 2 ^ a [MOD p] := by
      rw [← ZMod.natCast_eq_natCast_iff, pow_mul, Nat.cast_pow, ZMod.pow_card]
    have hA2 := semilinear_pow_eq E₀ hE.1 hE.2 σ₀.mapMatrix σ₀
      (fun c M => by ext i j; simp [RingEquiv.mapMatrix_apply, Matrix.map_apply])
      (fun e he => hEfix e he) ha hfix hmod (x : Matrix ι ι K) (hA x hx)
    have hA2' : (linSigmaGL σ₀ x) ^ 2 ^ (a * p) = x ^ 2 ^ a := Units.ext (by
      rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]; exact hA2)
    have hcop : Nat.Coprime (2 ^ (a * p)) (p ^ s) := Nat.Coprime.pow _ _
      ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
    have hps : 1 < p ^ s := Nat.one_lt_pow (by omega) hp.one_lt
    obtain ⟨M, -, hM⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hps
    have hM' : 2 ^ (a * p) * M ≡ 1 [MOD p ^ s] := by
      rw [Nat.ModEq, hM, Nat.mod_eq_of_lt hps]
    have hNmod : 2 ^ a * M * 2 ^ (a * p) ≡ 2 ^ a [MOD p ^ s] := by
      have := Nat.ModEq.mul_left (2 ^ a) hM'
      rw [mul_one] at this
      rwa [mul_assoc, mul_comm M]
    have hσx : (linSigmaGL σ₀ x) ^ p ^ s = 1 := by rw [← map_pow, hexp x hx, map_one]
    have hpow : linSigmaGL σ₀ x = x ^ (1 + p ^ (s - 1) * k) := by
      calc linSigmaGL σ₀ x = (linSigmaGL σ₀ x) ^ 1 := (pow_one _).symm
        _ = (linSigmaGL σ₀ x) ^ (2 ^ (a * p) * M) := pow_eq_pow_of_modEq' hσx hM'.symm
        _ = x ^ (2 ^ a * M) := by rw [pow_mul, hA2', ← pow_mul]
        _ = x ^ (1 + p ^ (s - 1) * k) := pow_eq_pow_of_modEq' (hexp x hx) (hN _ hNmod)
    rw [hpow]; exact_mod_cast (zpow_natCast x (1 + p ^ (s - 1) * k)).symm
  · rw [Units.val_mul, Units.val_mul]
    exact commute_of_mem_spanE E₀ (fun e he => by
      have := congrArg (fun g : GL ι K => (g : Matrix ι ι K)) (hw e he); simpa using this) (hA x hx)
  · obtain ⟨e₁, he₁, e₂, he₂, hind⟩ := exists_indep hp E₀ hE.2 hcard
    have hroot : ∀ e ∈ E₀, ∃ c : GL ι K, CentPAbs p E₀ c ∧ c ^ p ^ (s - 1) = e := by
      intro e he
      obtain ⟨c, hcA, hce, hcs⟩ := exists_pow_eq_of_pow_eq_one (q := 2 ^ (n : ℕ)) hp hp2 hn hd hs
        E₀ hE.1 hE.2 e (Submodule.subset_span ⟨⟨e, he⟩, rfl⟩) (hE.2 e he)
      have hcomm : ∀ e' ∈ E₀, c * e' = e' * c := by
        intro e' he'
        exact Units.ext (by
          rw [Units.val_mul, Units.val_mul]
          exact spanE_commute E₀ hE.1 hcA (Submodule.subset_span ⟨⟨e', he'⟩, rfl⟩))
      refine ⟨c, ?_, hce⟩
      rw [CentPAbs.eq_def]
      exact ⟨hcomm, ⟨s, hcs⟩⟩
    obtain ⟨a₁, ha₁, h₁⟩ := hroot e₁ he₁
    obtain ⟨a₂, ha₂, h₂⟩ := hroot e₂ he₂
    exact ⟨a₁, a₂, ha₁, ha₂, by rw [h₁]; exact he₁, by rw [h₂]; exact he₂,
      fun i j h => hind i j (by rw [← h₁, ← h₂]; exact h)⟩

private lemma cL2_linSigmaGL_coe {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (σ : K ≃+* K) (g : GL ι K) :
    ((linSigmaGL σ g : GL ι K) : Matrix ι ι K) =
      σ.toRingHom.mapMatrix (g : Matrix ι ι K) :=
  rfl

private lemma cL2_slMap_comp {K : Type} [Field K] {d : ℕ} (σ : K ≃+* K)
    (s : SpecialLinearGroup (Fin d) K) :
    SpecialLinearGroup.map σ.toRingHom (SpecialLinearGroup.map (σ⁻¹).toRingHom s) = s := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_map]
  have h : (⇑σ.toRingHom ∘ ⇑(σ⁻¹).toRingHom : K → K) = id := by
    funext x
    simpa using σ.apply_symm_apply x
  rw [h, Matrix.map_id]

private lemma cL2_slConjugation_map {K : Type} [Field K] {d : ℕ} (σ : K ≃+* K)
    (A : GL (Fin d) K) (B : SpecialLinearGroup (Fin d) K) :
    SpecialLinearGroup.map σ.toRingHom
        (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d K A B) =
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d K
        (linSigmaGL σ A) (SpecialLinearGroup.map σ.toRingHom B) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe, coe_slConjugation, map_mul, map_mul]
  rw [coe_slConjugation, Matrix.SpecialLinearGroup.map_apply_coe]
  rw [← map_inv (linSigmaGL σ) A, cL2_linSigmaGL_coe, cL2_linSigmaGL_coe]

theorem conjAut_linSigmaGL {K : Type} [Field K] {d : ℕ} (σ₀ : K ≃+* K) (g : GL (Fin d) K) :
    conjAut d K (linSigmaGL σ₀ g) = fieldAut d K σ₀ * conjAut d K g * (fieldAut d K σ₀)⁻¹ := by
  apply MulEquiv.ext
  intro x
  obtain ⟨s, rfl⟩ := proj_surjective d K x
  rw [conjAut_proj, ← map_inv (fieldAut d K) σ₀]
  simp only [MulAut.mul_apply]
  rw [fieldAut_proj, conjAut_proj, fieldAut_proj]
  rw [cL2_slConjugation_map, cL2_slMap_comp]

theorem lin_commute_of_conjAut_commute {K : Type} [Field K] [Fintype K] [CharP K 2] {d p : ℕ}
    (hd : 3 ≤ d) (hp : p.Prime) (hpd : ¬ p ∣ d ∨ ¬ p ∣ Fintype.card K - 1)
    (E₀ : Subgroup (GL (Fin d) K)) (hE : ∀ e ∈ E₀, e ^ p = 1) (h : GL (Fin d) K)
    (hh : ∀ e ∈ E₀, conjAut d K h * conjAut d K e = conjAut d K e * conjAut d K h) :
    ∀ e ∈ E₀, h * e = e * h := by
  intro e he
  have hconj : conjAut d K (h * e * h⁻¹ * e⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hh e he]
    group
  obtain ⟨κ, hκ⟩ :=
    (ProjectivePlane.conjAut_eq_one_iff hd (h * e * h⁻¹ * e⁻¹)).mp hconj
  have hstep : h * e * h⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin d) κ * e := by
    rw [← hκ]
    group
  have hmat : ((h * e * h⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      (κ : K) • (e : Matrix (Fin d) (Fin d) K) := by
    rw [hstep, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.smul_eq_diagonal_mul]
  have hκ1 : κ = 1 := lin_kappa hp (by omega) hpd h e κ hmat (hE e he)
  have heq : h * e * h⁻¹ = e := by
    rw [hstep, hκ1]
    simp
  exact (mul_inv_eq_iff_eq_mul).mp heq

private theorem cL4_linSigmaGL_coe {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (σ₀ : K ≃+* K) (g : GL ι K) :
    ((linSigmaGL σ₀ g : GL ι K) : Matrix ι ι K) = (g : Matrix ι ι K).map σ₀ := by
  rw [linSigmaGL, Units.coe_map]
  exact RingEquiv.mapMatrix_apply σ₀ (g : Matrix ι ι K)

private theorem cL4_scalar_eq_one {K : Type} [Field K] [Fintype K] {d p : ℕ} (hp : p.Prime)
    (hpd : ¬ p ∣ d ∨ ¬ p ∣ Fintype.card K - 1) (κ : Kˣ)
    (hκd : (κ : K) ^ d = 1) (hκp : (κ : K) ^ p = 1) : κ = 1 := by
  classical
  rcases hpd with h | h
  · have hcop : Nat.Coprime d p := ((Nat.Prime.coprime_iff_not_dvd hp).2 h).symm
    have hu1 : κ ^ d = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hκd, Units.val_one])
    have hu2 : κ ^ p = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hκp, Units.val_one])
    have h3 : orderOf κ ∣ 1 := by
      have h4 : orderOf κ ∣ Nat.gcd d p :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hu1) (orderOf_dvd_of_pow_eq_one hu2)
      rwa [hcop] at h4
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  · have hu : κ ^ p = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hκp, Units.val_one])
    have hcard : Fintype.card Kˣ = Fintype.card K - 1 := Fintype.card_units K
    have hcop' : Nat.Coprime p (Fintype.card K - 1) := (hp.coprime_iff_not_dvd).mpr h
    have hcop : Nat.Coprime (Fintype.card Kˣ) p := by
      rw [hcard]; exact Nat.coprime_comm.mp hcop'
    have h3 : orderOf κ ∣ 1 := by
      have h4 : orderOf κ ∣ Nat.gcd (Fintype.card Kˣ) p :=
        Nat.dvd_gcd (orderOf_dvd_card (x := κ)) (orderOf_dvd_of_pow_eq_one hu)
      rwa [hcop] at h4
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

private theorem cL4_conjAut_eq_one_iff {K : Type} [Field K] [Fintype K] {d : ℕ} (hd : 3 ≤ d)
    (A : GL (Fin d) K) :
    conjAut d K A = 1 ↔ ∃ c : Kˣ, GeneralLinearGroup.scalar (Fin d) c = A := by
  constructor
  · intro h
    exact (eq_one_of_conjAut_mul_fieldAut_eq_one hd A 1 (by rw [map_one, mul_one, h])).2
  · rintro ⟨c, rfl⟩
    exact conjAut_scalar c

private theorem cL4_lift_exists {K : Type} [Field K] [Fintype K] [CharP K 2] {d p : ℕ}
    (hd : 3 ≤ d) (hp : p.Prime) (hpd : ¬ p ∣ d ∨ ¬ p ∣ Fintype.card K - 1)
    (σ₀ : K ≃+* K) (Ebar : Subgroup (MulAut (projectiveSL d K)))
    (hEab : IsElemAbelian p Ebar) (hEI : ∀ e ∈ Ebar, e ∈ Set.range (conjAut d K))
    (hcomm : ∀ e ∈ Ebar, e * fieldAut d K σ₀ = fieldAut d K σ₀ * e)
    (ē : MulAut (projectiveSL d K)) (hē : ē ∈ Ebar) :
    ∃ y : GL (Fin d) K, conjAut d K y = ē ∧ y ^ p = 1 ∧
      (y : Matrix (Fin d) (Fin d) K).map σ₀ = y ∧
      (y : Matrix (Fin d) (Fin d) K).det = 1 := by
  classical
  obtain ⟨g, hg⟩ := hEI ē hē
  have hfē : fieldAut d K σ₀ * ē * (fieldAut d K σ₀)⁻¹ = ē := by
    rw [← hcomm ē hē]; group
  have hconj1 : conjAut d K (linSigmaGL σ₀ g) = conjAut d K g := by
    rw [conjAut_linSigmaGL, hg, hfē]
  have hker : conjAut d K (linSigmaGL σ₀ g * g⁻¹) = 1 := by
    rw [map_mul, map_inv, hconj1, mul_inv_cancel]
  obtain ⟨lam, hlam⟩ := (cL4_conjAut_eq_one_iff hd _).mp hker
  have hlamg : GeneralLinearGroup.scalar (Fin d) lam * g = linSigmaGL σ₀ g := by
    rw [hlam, mul_assoc, inv_mul_cancel, mul_one]
  have hx : (g : Matrix (Fin d) (Fin d) K).map σ₀ =
      (lam : K) • (g : Matrix (Fin d) (Fin d) K) := by
    have h4 := congrArg (fun u : GL (Fin d) K => (u : Matrix (Fin d) (Fin d) K)) hlamg
    rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_eq_diagonal_mul, cL4_linSigmaGL_coe] at h4
    exact h4.symm
  obtain ⟨μ₁, hμ₁⟩ := lin_descent σ₀ g lam hx
  set g₁ : GL (Fin d) K := GeneralLinearGroup.scalar (Fin d) μ₁ * g with hg₁
  have hg₁mat : (g₁ : Matrix (Fin d) (Fin d) K) =
      (μ₁ : K) • (g : Matrix (Fin d) (Fin d) K) := by
    rw [hg₁, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_eq_diagonal_mul]
  have hg₁fix : (g₁ : Matrix (Fin d) (Fin d) K).map σ₀ = g₁ := by
    rw [hg₁mat]; exact hμ₁
  have hg₁conj : conjAut d K g₁ = ē := by
    rw [hg₁, map_mul, conjAut_scalar, one_mul, hg]
  have hg₁p_conj : conjAut d K (g₁ ^ p) = 1 := by
    rw [map_pow, hg₁conj, hEab.2 ē hē]
  obtain ⟨ν, hν⟩ := (cL4_conjAut_eq_one_iff hd _).mp hg₁p_conj
  have hν' : ((g₁ ^ p : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = (ν : K) • 1 := by
    have h4 := congrArg (fun u : GL (Fin d) K => (u : Matrix (Fin d) (Fin d) K)) hν
    rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h4
    rw [← h4, Matrix.smul_eq_diagonal_mul, Matrix.mul_one]
  obtain ⟨μ₂, hσμ₂, hμ₂p⟩ := lin_order_p hp hpd σ₀ g₁ hg₁fix ν hν'
  set x : GL (Fin d) K := GeneralLinearGroup.scalar (Fin d) μ₂ * g₁ with hx_def
  have hxmat : (x : Matrix (Fin d) (Fin d) K) =
      (μ₂ : K) • (g₁ : Matrix (Fin d) (Fin d) K) := by
    rw [hx_def, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_eq_diagonal_mul]
  have hsm : ∀ (c : K) (M : Matrix (Fin d) (Fin d) K),
      (c • M).map σ₀ = σ₀ c • M.map σ₀ := fun c M => by ext i j; simp [Matrix.map_apply]
  have hσμ₂' : σ₀ (μ₂ : K) = (μ₂ : K) := hσμ₂
  have hxfix : (x : Matrix (Fin d) (Fin d) K).map σ₀ = x := by
    rw [hxmat, hsm, hσμ₂', hg₁fix]
  have hxp : x ^ p = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hxmat]
    exact hμ₂p
  have hxconj : conjAut d K x = ē := by
    rw [hx_def, map_mul, conjAut_scalar, one_mul, hg₁conj]
  obtain ⟨μ₃, hσμ₃, hμ₃p, hμ₃det⟩ := lin_sl_adjust hp hpd σ₀ x hxfix hxp
  set y : GL (Fin d) K := GeneralLinearGroup.scalar (Fin d) μ₃ * x with hy_def
  have hymat : (y : Matrix (Fin d) (Fin d) K) =
      (μ₃ : K) • (x : Matrix (Fin d) (Fin d) K) := by
    rw [hy_def, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_eq_diagonal_mul]
  have hσμ₃' : σ₀ (μ₃ : K) = (μ₃ : K) := hσμ₃
  have hμ₃p' : (μ₃ : K) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, hμ₃p, Units.val_one]
  refine ⟨y, ?_, ?_, ?_, ?_⟩
  · rw [hy_def, map_mul, conjAut_scalar, one_mul, hxconj]
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, hymat, smul_pow]
    have hxp' : (x : Matrix (Fin d) (Fin d) K) ^ p = 1 := by
      rw [← Units.val_pow_eq_pow_val, hxp, Units.val_one]
    rw [hμ₃p', hxp', one_smul, Units.val_one]
  · rw [hymat, hsm, hσμ₃', hxfix]
  · rw [hymat]; exact hμ₃det

private theorem cL4_lift_commute {K : Type} [Field K] [Fintype K] [CharP K 2] {d p : ℕ}
    (hd : 3 ≤ d) (hp : p.Prime) (hpd : ¬ p ∣ d ∨ ¬ p ∣ Fintype.card K - 1)
    (Ebar : Subgroup (MulAut (projectiveSL d K))) (hEab : IsElemAbelian p Ebar)
    {x y : GL (Fin d) K} (hx : conjAut d K x ∈ Ebar) (hy : conjAut d K y ∈ Ebar)
    (hyp : y ^ p = 1) (hxp : x ^ p = 1) : x * y = y * x := by
  refine lin_commute_of_conjAut_commute hd hp hpd (Subgroup.zpowers y) ?_ x ?_ y
    (Subgroup.mem_zpowers y)
  · rw [Subgroup.forall_mem_zpowers]
    intro m
    have hypz : y ^ (p : ℤ) = 1 := by rw [zpow_natCast, hyp]
    calc (y ^ m) ^ p = (y ^ m) ^ (p : ℤ) := by rw [zpow_natCast]
      _ = y ^ (m * (p : ℤ)) := by rw [_root_.zpow_mul]
      _ = y ^ ((p : ℤ) * m) := by rw [mul_comm]
      _ = (y ^ (p : ℤ)) ^ m := by rw [_root_.zpow_mul]
      _ = 1 := by rw [hypz, _root_.one_zpow]
  · rw [Subgroup.forall_mem_zpowers]
    intro m
    have hc : Commute (conjAut d K x) (conjAut d K y) := IsElemAbelian.comm hEab hx hy
    have h := (hc.zpow_right m).eq
    rwa [map_zpow]

theorem lin_E0_lift {K : Type} [Field K] [Fintype K] [CharP K 2] {d p : ℕ} (hd : 3 ≤ d)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpd : ¬ p ∣ d ∨ ¬ p ∣ Fintype.card K - 1) (σ₀ : K ≃+* K)
    (hσ₀ : orderOf σ₀ = p) (Ebar : Subgroup (MulAut (projectiveSL d K)))
    (hEab : IsElemAbelian p Ebar) (hEI : ∀ e ∈ Ebar, e ∈ Set.range (conjAut d K))
    (hcomm : ∀ e ∈ Ebar, e * fieldAut d K σ₀ = fieldAut d K σ₀ * e) :
    ∃ E₀ : Subgroup (GL (Fin d) K), IsElemAbelian p E₀ ∧
      (∀ e ∈ E₀, (e : Matrix (Fin d) (Fin d) K).map σ₀ = e) ∧
      (∀ x ∈ E₀, ∀ y ∈ E₀, conjAut d K x = conjAut d K y → x = y) ∧
      ∀ e, e ∈ Ebar ↔ ∃ x ∈ E₀, conjAut d K x = e := by
  classical
  let lift : Ebar → GL (Fin d) K := fun ē =>
    Classical.choose (cL4_lift_exists hd hp hpd σ₀ Ebar hEab hEI hcomm ē.1 ē.2)
  have hspec : ∀ ē : Ebar, conjAut d K (lift ē) = (ē : MulAut (projectiveSL d K)) ∧
      (lift ē) ^ p = 1 ∧
      ((lift ē : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map σ₀ = lift ē ∧
      (((lift ē : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)).det = 1 :=
    fun ē => Classical.choose_spec (cL4_lift_exists hd hp hpd σ₀ Ebar hEab hEI hcomm ē.1 ē.2)
  let s : Set (GL (Fin d) K) := Set.range lift
  have hEab₀ : IsElemAbelian p (Subgroup.closure s) := by
    refine IsElemAbelian.closure_of_commute ?_ ?_
    · rintro a ⟨ē₁, rfl⟩ b ⟨ē₂, rfl⟩
      exact cL4_lift_commute hd hp hpd Ebar hEab
        (by rw [(hspec ē₁).1]; exact ē₁.2) (by rw [(hspec ē₂).1]; exact ē₂.2)
        (hspec ē₂).2.1 (hspec ē₁).2.1
    · rintro a ⟨ē, rfl⟩
      exact (hspec ē).2.1
  have hfix_ls : ∀ e ∈ Subgroup.closure s, linSigmaGL σ₀ e = e := by
    intro e he
    induction he using Subgroup.closure_induction with
    | mem a ha =>
        obtain ⟨ē, rfl⟩ := ha
        exact Units.ext ((cL4_linSigmaGL_coe σ₀ (lift ē)).trans (hspec ē).2.2.1)
    | one => exact map_one _
    | mul a b ha hb iha ihb => rw [map_mul, iha, ihb]
    | inv a ha iha => rw [map_inv, iha]
  have hEfix : ∀ e ∈ Subgroup.closure s, (e : Matrix (Fin d) (Fin d) K).map σ₀ = e := by
    intro e he
    rw [← cL4_linSigmaGL_coe σ₀ e, hfix_ls e he]
  have hconj_mem : ∀ e ∈ Subgroup.closure s, conjAut d K e ∈ Ebar := by
    intro e he
    induction he using Subgroup.closure_induction with
    | mem a ha =>
        obtain ⟨ē, rfl⟩ := ha
        rw [(hspec ē).1]
        exact ē.2
    | one => rw [map_one]; exact Ebar.one_mem
    | mul a b ha hb iha ihb => rw [map_mul]; exact Ebar.mul_mem iha ihb
    | inv a ha iha => rw [map_inv]; exact Ebar.inv_mem iha
  have hdetu : ∀ y : GL (Fin d) K, (y : Matrix (Fin d) (Fin d) K).det *
      ((y⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).det = 1 := fun y => by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have hdet : ∀ e ∈ Subgroup.closure s, (e : Matrix (Fin d) (Fin d) K).det = 1 := by
    intro e he
    induction he using Subgroup.closure_induction with
    | mem a ha => obtain ⟨ē, rfl⟩ := ha; exact (hspec ē).2.2.2
    | one => rw [Units.val_one, Matrix.det_one]
    | mul a b ha hb iha ihb => rw [Units.val_mul, Matrix.det_mul, iha, ihb, one_mul]
    | inv a ha iha =>
        have h := hdetu a
        rw [iha, one_mul] at h
        exact h
  have hinj : ∀ x ∈ Subgroup.closure s, ∀ y ∈ Subgroup.closure s,
      conjAut d K x = conjAut d K y → x = y := by
    intro x hx y hy hxy
    have h1 : conjAut d K (x * y⁻¹) = 1 := by rw [map_mul, map_inv, hxy, mul_inv_cancel]
    obtain ⟨c, hc⟩ := (cL4_conjAut_eq_one_iff hd (x * y⁻¹)).mp h1
    have hxy' : x = GeneralLinearGroup.scalar (Fin d) c * y := by
      rw [hc, mul_assoc, inv_mul_cancel, mul_one]
    have hmat : (x : Matrix (Fin d) (Fin d) K) = (c : K) • (y : Matrix (Fin d) (Fin d) K) := by
      have h4 := congrArg (fun u : GL (Fin d) K => (u : Matrix (Fin d) (Fin d) K)) hxy'
      rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        ← Matrix.smul_eq_diagonal_mul] at h4
      exact h4
    have hcd : (c : K) ^ d = 1 := by
      have h := congrArg Matrix.det hmat
      rw [Matrix.det_smul, Fintype.card_fin, hdet x hx, hdet y hy, mul_one] at h
      exact h.symm
    have hcp : (c : K) ^ p = 1 := by
      have hcomm_sc : Commute (GeneralLinearGroup.scalar (Fin d) c) y :=
        GeneralLinearGroup.scalar_commute c y
      have h2 : (GeneralLinearGroup.scalar (Fin d) c * y) ^ p =
          (GeneralLinearGroup.scalar (Fin d) c) ^ p * y ^ p := hcomm_sc.mul_pow p
      have hxyp : x ^ p = 1 := hEab₀.2 x hx
      have hyp : y ^ p = 1 := hEab₀.2 y hy
      rw [hxy'] at hxyp
      rw [h2, hyp, mul_one] at hxyp
      have hscalar : GeneralLinearGroup.scalar (Fin d) (c ^ p) = 1 := by
        rw [map_pow]; exact hxyp
      have h00 := congrArg (fun u : GL (Fin d) K =>
        ((u : Matrix (Fin d) (Fin d) K) ⟨0, by omega⟩ ⟨0, by omega⟩)) hscalar
      simpa only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
        Units.val_one, Units.val_pow_eq_pow_val, Matrix.one_apply_eq] using h00
    have hc1 : c = 1 := cL4_scalar_eq_one hp hpd c hcd hcp
    have h1' : GeneralLinearGroup.scalar (Fin d) (1 : Kˣ) = 1 := map_one _
    rw [hc1, h1', one_mul] at hxy'
    exact hxy'
  refine ⟨Subgroup.closure s, hEab₀, hEfix, hinj, ?_⟩
  intro e
  constructor
  · intro he
    refine ⟨lift ⟨e, he⟩, Subgroup.subset_closure ⟨⟨e, he⟩, rfl⟩, ?_⟩
    exact (hspec ⟨e, he⟩).1
  · rintro ⟨x, hx, rfl⟩
    exact hconj_mem x hx

private lemma cL5_map_smul {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n]
    (σ₀ : K ≃+* K) (c : K) (M : Matrix n n K) :
    (c • M).map σ₀ = σ₀ c • M.map σ₀ := by
  ext i j
  simp [Matrix.map_apply, Matrix.smul_apply]

theorem lin_sat_translate {K : Type} [Field K] [Fintype K] [CharP K 2] {d p : ℕ} (hd : 3 ≤ d)
    (hp : p.Prime) (hpd : ¬ p ∣ d ∨ ¬ p ∣ Fintype.card K - 1) (σ₀ : K ≃+* K)
    (E₀ : Subgroup (GL (Fin d) K)) (Ebar : Subgroup (MulAut (projectiveSL d K)))
    (hE₀ : ∀ e, e ∈ Ebar ↔ ∃ x ∈ E₀, conjAut d K x = e)
    (hSatR : ∀ r : projectiveSL d K, r ^ p = 1 → (∀ e ∈ Ebar, e r = r) →
      fieldAut d K σ₀ r = r → MulAut.conj r ∈ Ebar) :
    ∀ y : GL (Fin d) K, (∀ e ∈ E₀, y * e = e * y) → y ^ p = 1 →
      (y : Matrix (Fin d) (Fin d) K).map σ₀ = y → (y : Matrix (Fin d) (Fin d) K) ∈ spanE K E₀ := by
  intro y hycomm hyp hyfix
  obtain ⟨μ, hσμ, hμp, hdet⟩ := lin_sl_adjust hp hpd σ₀ y hyfix hyp
  have hσμ' : σ₀ (μ : K) = (μ : K) := hσμ
  set z : GL (Fin d) K := GeneralLinearGroup.scalar (Fin d) μ * y with hzdef
  have hzmat : (z : Matrix (Fin d) (Fin d) K) =
      (μ : K) • (y : Matrix (Fin d) (Fin d) K) := by
    rw [hzdef, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.smul_eq_diagonal_mul]
  have hdetz : (z : Matrix (Fin d) (Fin d) K).det = 1 := by
    rw [hzmat]; exact hdet
  have hzfix : (z : Matrix (Fin d) (Fin d) K).map σ₀ = (z : Matrix (Fin d) (Fin d) K) := by
    calc (z : Matrix (Fin d) (Fin d) K).map σ₀
        = ((μ : K) • (y : Matrix (Fin d) (Fin d) K)).map σ₀ := by rw [hzmat]
      _ = σ₀ (μ : K) • (y : Matrix (Fin d) (Fin d) K).map σ₀ :=
            cL5_map_smul σ₀ (μ : K) _
      _ = (μ : K) • (y : Matrix (Fin d) (Fin d) K).map σ₀ := by rw [hσμ']
      _ = (μ : K) • (y : Matrix (Fin d) (Fin d) K) := by rw [hyfix]
      _ = (z : Matrix (Fin d) (Fin d) K) := hzmat.symm
  have hμp' : (μ : K) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val μ p, hμp, Units.val_one]
  have hzpow : z ^ p = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hzmat, smul_pow, ← Units.val_pow_eq_pow_val y p, hyp, hμp',
      one_smul]
  obtain ⟨s, hs⟩ : ∃ s : SpecialLinearGroup (Fin d) K, SpecialLinearGroup.toGL s = z := by
    have hzrange : z ∈ (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin d) K →*
        GL (Fin d) K).range := by
      rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.mem_ker]
      exact Units.ext hdetz
    exact MonoidHom.mem_range.mp hzrange
  have hsm : (s : Matrix (Fin d) (Fin d) K) = (z : Matrix (Fin d) (Fin d) K) := by
    have h := congrArg (fun g : GL (Fin d) K => (g : Matrix (Fin d) (Fin d) K)) hs
    simpa using h
  have hsp : s ^ p = 1 := by
    apply SpecialLinearGroup.toGL_injective
    rw [map_pow, hs, hzpow, map_one]
  have hrpow : (proj d K s) ^ p = 1 := by
    rw [← map_pow, hsp, map_one]
  have hfixs : SpecialLinearGroup.map σ₀.toRingHom s = s := by
    apply Subtype.ext
    rw [SpecialLinearGroup.map_apply_coe, hsm]
    simpa using hzfix
  have hfield : fieldAut d K σ₀ (proj d K s) = proj d K s := by
    rw [fieldAut_proj, hfixs]
  have hfixE : ∀ e ∈ Ebar, e (proj d K s) = proj d K s := by
    intro e he
    obtain ⟨x, hxE, hxeq⟩ := (hE₀ e).mp he
    have hxcomm : x * z = z * x := by
      rw [hzdef]
      calc x * (GeneralLinearGroup.scalar (Fin d) μ * y)
          = (x * GeneralLinearGroup.scalar (Fin d) μ) * y := by rw [mul_assoc]
        _ = (GeneralLinearGroup.scalar (Fin d) μ * x) * y := by
              rw [(GeneralLinearGroup.scalar_commute μ x).symm]
        _ = GeneralLinearGroup.scalar (Fin d) μ * (x * y) := by rw [mul_assoc]
        _ = GeneralLinearGroup.scalar (Fin d) μ * (y * x) := by rw [hycomm x hxE]
        _ = (GeneralLinearGroup.scalar (Fin d) μ * y) * x := by rw [← mul_assoc]
    have hm : (x : Matrix (Fin d) (Fin d) K) * (s : Matrix (Fin d) (Fin d) K) =
        (s : Matrix (Fin d) (Fin d) K) * (x : Matrix (Fin d) (Fin d) K) := by
      have h := congrArg (fun g : GL (Fin d) K => (g : Matrix (Fin d) (Fin d) K)) hxcomm
      simpa [Units.val_mul, ← hs] using h
    have hxinv : (x : Matrix (Fin d) (Fin d) K) *
        ((x⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [← hxeq, conjAut_proj]
    refine congrArg (proj d K) ?_
    apply Subtype.ext
    rw [coe_slConjugation]
    calc (x : Matrix (Fin d) (Fin d) K) * (s : Matrix (Fin d) (Fin d) K) *
            ((x⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
        = (s : Matrix (Fin d) (Fin d) K) * (x : Matrix (Fin d) (Fin d) K) *
            ((x⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by rw [hm]
      _ = (s : Matrix (Fin d) (Fin d) K) *
            ((x : Matrix (Fin d) (Fin d) K) *
              ((x⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) := by rw [mul_assoc]
      _ = (s : Matrix (Fin d) (Fin d) K) := by rw [hxinv, mul_one]
  have hrSat : MulAut.conj (proj d K s) ∈ Ebar :=
    hSatR (proj d K s) hrpow hfixE hfield
  obtain ⟨x, hxE, hxeq⟩ := (hE₀ (MulAut.conj (proj d K s))).mp hrSat
  have hzx : conjAut d K z = conjAut d K x := by
    have h1 : conjAut d K z = MulAut.conj (proj d K s) := by
      rw [← hs]; exact conjAut_toGL s
    rw [h1, hxeq]
  have hker : conjAut d K (z * x⁻¹) = 1 := by
    rw [map_mul, map_inv, hzx]
    group
  obtain ⟨c, hc⟩ := (ProjectivePlane.conjAut_eq_one_iff hd (z * x⁻¹)).mp hker
  have hzc : z = GeneralLinearGroup.scalar (Fin d) c * x := by
    rw [← hc]; group
  have hy_eq : y = GeneralLinearGroup.scalar (Fin d) (μ⁻¹ * c) * x := by
    calc y = (GeneralLinearGroup.scalar (Fin d) μ)⁻¹ * z := by rw [hzdef]; group
      _ = (GeneralLinearGroup.scalar (Fin d) μ)⁻¹ *
            (GeneralLinearGroup.scalar (Fin d) c * x) := by rw [hzc]
      _ = GeneralLinearGroup.scalar (Fin d) (μ⁻¹ * c) * x := by
            rw [← map_inv (GeneralLinearGroup.scalar (Fin d)) μ, ← mul_assoc, ← map_mul]
  have hyval : (y : Matrix (Fin d) (Fin d) K) =
      ((μ⁻¹ * c : Kˣ) : K) • (x : Matrix (Fin d) (Fin d) K) := by
    rw [hy_eq, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_eq_diagonal_mul (x : Matrix (Fin d) (Fin d) K) ((μ⁻¹ * c : Kˣ) : K)]
  have hxmem : (x : Matrix (Fin d) (Fin d) K) ∈ spanE K E₀ :=
    Submodule.subset_span ⟨⟨x, hxE⟩, rfl⟩
  rw [hyval]
  exact Submodule.smul_mem (spanE K E₀) ((μ⁻¹ * c : Kˣ) : K) hxmem

private theorem cL6_fieldAut_injective {K : Type} [Field K] [Fintype K] {d : ℕ} (hd : 3 ≤ d) :
    Function.Injective (fieldAut d K) := by
  intro σ τ hστ
  have h1 : fieldAut d K (σ * τ⁻¹) = 1 := by
    rw [map_mul, map_inv, hστ, mul_inv_cancel]
  have h2 : σ * τ⁻¹ = 1 :=
    (eq_one_of_conjAut_mul_fieldAut_eq_one hd (1 : GL (Fin d) K) (σ * τ⁻¹)
      (by rw [map_one, one_mul, h1])).1
  exact mul_inv_eq_one.mp h2

private theorem cL6_card_E0 {K : Type} [Field K] [Fintype K] {d : ℕ} (E₀ : Subgroup (GL (Fin d) K))
    (Ebar : Subgroup (MulAut (projectiveSL d K)))
    (hinj : ∀ x ∈ E₀, ∀ y ∈ E₀, conjAut d K x = conjAut d K y → x = y)
    (hE₀ : ∀ e, e ∈ Ebar ↔ ∃ x ∈ E₀, conjAut d K x = e) :
    Nat.card E₀ = Nat.card Ebar := by
  have hmap : E₀.map (conjAut d K) = Ebar := by
    ext e
    rw [Subgroup.mem_map]
    exact (hE₀ e).symm
  rw [← hmap]
  let φ : E₀ → E₀.map (conjAut d K) :=
    fun x => ⟨conjAut d K x, Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩⟩
  have hφ : Function.Bijective φ := by
    constructor
    · intro x y hxy
      exact Subtype.ext (hinj x x.2 y y.2 (Subtype.ext_iff.mp hxy))
    · rintro ⟨y, hy⟩
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  exact Finite.card_eq.mpr ⟨Equiv.ofBijective φ hφ⟩

theorem ntCore_lin_model {K : Type} [Field K] [Fintype K] [CharP K 2] {d p : ℕ} (hd : 3 ≤ d)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpd : ¬ p ∣ d ∨ ¬ p ∣ Fintype.card K - 1) :
    GGL45NtCore p (projectiveSL d K) (Set.range (conjAut d K)) (Set.range (fieldAut d K)) := by
  refine ntCore_of_conj p (Set.range (conjAut d K)) (Set.range (fieldAut d K)) ?_ ?_ ?_
  · rintro x ⟨a, rfl⟩ y ⟨b, rfl⟩
    exact ⟨a * b⁻¹, by rw [map_mul, map_inv]⟩
  · exact ⟨1, map_one _⟩
  · intro _ _ Ebar f hEab hcard hEI hfF hfp hfcomm hSat
    obtain ⟨σ₀, hσ₀eq⟩ := hfF
    have hσ₀ : orderOf σ₀ = p := by
      rw [← orderOf_injective (fieldAut d K) (cL6_fieldAut_injective hd) σ₀, hσ₀eq, hfp]
    have hcommF : ∀ e ∈ Ebar, e * fieldAut d K σ₀ = fieldAut d K σ₀ * e := by
      intro e he
      rw [hσ₀eq]
      exact hfcomm e he
    have hSatR : ∀ r : projectiveSL d K, r ^ p = 1 → (∀ e ∈ Ebar, e r = r) →
        fieldAut d K σ₀ r = r → MulAut.conj r ∈ Ebar := by
      intro r hr hcr hfr
      exact hSat r hr hcr (by rw [← hσ₀eq]; exact hfr)
    obtain ⟨E₀, hEab₀, hEfix₀, hinj₀, hE₀⟩ :=
      lin_E0_lift hd hp hp2 hpd σ₀ hσ₀ Ebar hEab hEI hcommF
    have hSatGL := lin_sat_translate hd hp hpd σ₀ E₀ Ebar hE₀ hSatR
    have hcard₀ : p ^ 2 ≤ Nat.card E₀ :=
      (cL6_card_E0 E₀ Ebar hinj₀ hE₀).symm ▸ hcard
    have hcore : ClCoreConcl p E₀ (linSigmaGL σ₀) :=
      matrix_core_lin hp hp2 σ₀ hσ₀ E₀ hEab₀ hEfix₀ hSatGL hcard₀
    have hα : ∀ g : GL (Fin d) K,
        conjAut d K (linSigmaGL σ₀ g) = f * conjAut d K g * f⁻¹ := by
      intro g
      rw [conjAut_linSigmaGL, hσ₀eq]
    have hI' : ∀ w ∈ Set.range (conjAut d K), ∃ h : GL (Fin d) K, conjAut d K h = w :=
      fun w hw => hw
    have hIp : ∀ h : GL (Fin d) K, (∃ k : ℕ, h ^ p ^ k = 1) →
        conjAut d K h ∈ Set.range (conjAut d K) := fun h _ => ⟨h, rfl⟩
    have hcomm' : ∀ h : GL (Fin d) K,
        (∀ e ∈ E₀, conjAut d K h * conjAut d K e = conjAut d K e * conjAut d K h) →
        ∀ e ∈ E₀, h * e = e * h :=
      fun h hh => lin_commute_of_conjAut_commute hd hp hpd E₀ hEab₀.2 h hh
    exact coreConcl_transfer hp (Set.range (conjAut d K)) Ebar f
      (conjAut d K) (linSigmaGL σ₀) hα E₀ hinj₀ hE₀ hI' hIp hcomm' hcore

end CFSG.HardMathSupport.C14Cl
