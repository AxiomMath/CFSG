module

public import CFSG.RankThree.PartOne.S15K.PSylowSub
public import CFSG.RankThree.PartOne.S15K.CommonEigen

public section

namespace CFSG.RankThree.PartOne.S15K

open Matrix
open scoped commutatorElement

section Transvection

variable {E : Type*} [Field E] {m : ℕ}

@[expose] def tvMat (v φ : Fin m → E) (x : E) : Matrix (Fin m) (Fin m) E := 1 + x • vecMulVec v φ

theorem tvMat_zero (v φ : Fin m → E) : tvMat v φ 0 = 1 := by simp [tvMat]

theorem tvMat_mul {v φ : Fin m → E} (hφv : φ ⬝ᵥ v = 0) (x y : E) :
    tvMat v φ x * tvMat v φ y = tvMat v φ (x + y) := by
  have h : vecMulVec v φ * vecMulVec v φ = 0 := by
    rw [vecMulVec_mul_vecMulVec, hφv, zero_smul, vecMulVec_zero]
  unfold tvMat
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, h, smul_zero,
    add_zero, add_smul]
  abel

theorem det_tvMat [CharP E 2] {v φ : Fin m → E} (hφv : φ ⬝ᵥ v = 0) (x : E) :
    (tvMat v φ x).det = 1 := by
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  have hsq : (tvMat v φ x).det ^ 2 = 1 := by
    rw [sq, ← det_mul, tvMat_mul hφv, ← two_mul, h2, zero_mul, tvMat_zero, det_one]
  have h3 : ((tvMat v φ x).det - 1) ^ 2 = 0 := by
    linear_combination hsq + (1 - (tvMat v φ x).det) * h2
  exact sub_eq_zero.1 ((pow_eq_zero_iff (by norm_num)).1 h3)

@[expose] def tvHomSL [CharP E 2] (v φ : Fin m → E) (hφv : φ ⬝ᵥ v = 0) :
    Multiplicative E →* SpecialLinearGroup (Fin m) E where
  toFun x := ⟨tvMat v φ (Multiplicative.toAdd x), det_tvMat hφv _⟩
  map_one' := Subtype.ext (by simp [tvMat_zero])
  map_mul' x y := Subtype.ext (by
    simp only [toAdd_mul]
    exact (tvMat_mul hφv _ _).symm)

theorem coe_tvHomSL [CharP E 2] (v φ : Fin m → E) (hφv : φ ⬝ᵥ v = 0) (x : E) :
    ((tvHomSL v φ hφv (Multiplicative.ofAdd x) : SpecialLinearGroup (Fin m) E) :
      Matrix (Fin m) (Fin m) E) = tvMat v φ x := rfl

theorem tvHomSL_ne_one [CharP E 2] {v φ : Fin m → E} (hφv : φ ⬝ᵥ v = 0) (hv : v ≠ 0) (hφ : φ ≠ 0) :
    tvHomSL v φ hφv (Multiplicative.ofAdd 1) ≠ 1 := by
  intro h
  have h1 := congrArg (fun g : SpecialLinearGroup (Fin m) E => (g : Matrix (Fin m) (Fin m) E)) h
  simp only [coe_tvHomSL, Matrix.SpecialLinearGroup.coe_one, tvMat, one_smul] at h1
  have h2 : vecMulVec v φ = 0 := by simpa using h1
  exact (vecMulVec_ne_zero hv hφ) h2

theorem mul_tvMat {v φ : Fin m → E} {h : Matrix (Fin m) (Fin m) E} {lam mu : E} (hmu : mu ≠ 0)
    (hv : h *ᵥ v = lam • v) (hφ : φ ᵥ* h = mu • φ) (x : E) :
    h * tvMat v φ x = tvMat v φ (lam / mu * x) * h := by
  unfold tvMat
  rw [mul_add, mul_one, add_mul, one_mul, Matrix.mul_smul, mul_vecMulVec, hv, Matrix.smul_mul,
    vecMulVec_mul, hφ, smul_vecMulVec, vecMulVec_smul, smul_smul, smul_smul]
  congr 2
  field_simp

end Transvection

section Annihilator

variable {E : Type*} [Field E] {m : ℕ}

theorem exists_ann_ne_zero (U : Submodule E (Fin m → E)) (hU : U ≠ ⊤) :
    ∃ φ : Fin m → E, φ ≠ 0 ∧ ∀ u ∈ U, φ ⬝ᵥ u = 0 := by
  obtain ⟨f, hf0, hUf⟩ := Submodule.exists_le_ker_of_lt_top U (lt_top_iff_ne_top.2 hU)
  have hfu : ∀ u : Fin m → E, f u = (fun j => f (Pi.single j 1)) ⬝ᵥ u := by
    intro u
    conv_lhs => rw [pi_eq_sum_univ u]
    simp only [map_sum, map_smul, dotProduct, smul_eq_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
    congr 2
    funext i
    simp [Pi.single_apply, eq_comm]
  refine ⟨fun j => f (Pi.single j 1), ?_, fun u hu => ?_⟩
  · intro h
    apply hf0
    refine LinearMap.ext fun u => ?_
    rw [hfu, h]
    simp
  · rw [← hfu]
    exact hUf hu

end Annihilator

section Main

variable {E : Type*} [Field E] [CharP E 2] {p : ℕ}

theorem psylowSub_specialLinear (hp : p.Prime) {ζ : E} (hζ : IsPrimitiveRoot ζ p) {m : ℕ}
    (hpm : ¬ p ∣ m) : PSylowSub p (⊤ : Subgroup (SpecialLinearGroup (Fin m) E)) := by
  classical
  intro P _ hcomm hpow hP1
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
    have : (ζ - 1) ^ 2 = 0 := by linear_combination hζ.pow_eq_one + (1 - ζ) * h2
    exact hζ.ne_one hp.one_lt (sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 this))
  have hpE : (p : E) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff E 2] at h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h).symm
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hpm (dvd_zero p)
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).2 hpm
  obtain ⟨⟨g₀, hg₀P⟩, hg₀1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hP1
  have hg₀1 : g₀ ≠ 1 := fun h => hg₀1' (Subtype.ext h)
  set g₀' : ↥P := ⟨g₀, hg₀P⟩ with hg₀'
  let T : ↥P → Module.End E (Fin m → E) := fun h =>
    Matrix.toLinAlgEquiv' ((h : SpecialLinearGroup (Fin m) E) : Matrix (Fin m) (Fin m) E)
  let D : ↥P → Module.End E (Fin m → E) := fun h =>
    Matrix.toLinAlgEquiv' ((h : SpecialLinearGroup (Fin m) E) : Matrix (Fin m) (Fin m) E)ᵀ
  have hTapp : ∀ (h : ↥P) (w : Fin m → E),
      T h w = ((h : SpecialLinearGroup (Fin m) E) : Matrix (Fin m) (Fin m) E) *ᵥ w := fun h w => by
    simp [T, Matrix.toLinAlgEquiv'_apply]
  have hDapp : ∀ (h : ↥P) (w : Fin m → E),
      D h w = w ᵥ* ((h : SpecialLinearGroup (Fin m) E) : Matrix (Fin m) (Fin m) E) := fun h w => by
    simp [D, Matrix.toLinAlgEquiv'_apply, Matrix.mulVec_transpose]
  have hmatpow : ∀ h : ↥P, ((h : SpecialLinearGroup (Fin m) E) : Matrix (Fin m) (Fin m) E) ^ p = 1 := by
    intro h
    rw [← Matrix.SpecialLinearGroup.coe_pow]
    have := hpow (h : SpecialLinearGroup (Fin m) E) h.2
    rw [this, Matrix.SpecialLinearGroup.coe_one]
  have hTpow : ∀ h, T h ^ p = 1 := fun h => by
    simp only [T]
    rw [← map_pow, hmatpow h, map_one]
  have hDpow : ∀ h, D h ^ p = 1 := fun h => by
    simp only [D]
    rw [← map_pow, ← Matrix.transpose_pow, hmatpow h, Matrix.transpose_one, map_one]
  have hcommSL : ∀ h h' : ↥P, ((h : SpecialLinearGroup (Fin m) E) : Matrix (Fin m) (Fin m) E) *
      ((h' : SpecialLinearGroup (Fin m) E) : Matrix (Fin m) (Fin m) E) =
      ((h' : SpecialLinearGroup (Fin m) E) : Matrix (Fin m) (Fin m) E) *
      ((h : SpecialLinearGroup (Fin m) E) : Matrix (Fin m) (Fin m) E) := fun h h' => by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul,
      hcomm _ h.2 _ h'.2]
  have hTcomm : ∀ h h', T h * T h' = T h' * T h := fun h h' => by
    simp only [T]
    rw [← map_mul, ← map_mul, hcommSL h h']
  have hDcomm : ∀ h h', D h * D h' = D h' * D h := fun h h' => by
    simp only [D]
    rw [← map_mul, ← map_mul, ← Matrix.transpose_mul, ← Matrix.transpose_mul, hcommSL h h']
  have hWne : (⊤ : Submodule E (Fin m → E)) ≠ ⊥ := by
    intro h
    have hmem : (Pi.single ⟨0, Nat.pos_of_ne_zero hm0⟩ (1 : E) : Fin m → E) ∈
        (⊤ : Submodule E (Fin m → E)) := Submodule.mem_top
    rw [h, Submodule.mem_bot] at hmem
    have := congrFun hmem ⟨0, Nat.pos_of_ne_zero hm0⟩
    simp at this
  obtain ⟨ξ, v₀, -, hv₀0, hv₀⟩ := exists_eigen_on_stable hp.pos hζ (hTpow g₀') hWne
    (fun w _ => Submodule.mem_top)
  have hξp : ξ ^ p = 1 := eigenvalue_pow_eq_one (hTpow g₀') hv₀0 hv₀
  let A : Module.End E (Fin m → E) := T g₀' - ξ • 1
  let U : Submodule E (Fin m → E) := LinearMap.ker A
  have hUmem : ∀ w, w ∈ U ↔ T g₀' w = ξ • w := fun w => by
    rw [LinearMap.mem_ker]
    show (T g₀' - ξ • 1) w = 0 ↔ _
    rw [LinearMap.sub_apply, sub_eq_zero]
    rfl
  have hUne : U ≠ ⊥ := fun h => hv₀0 ((Submodule.mem_bot E).1 (h ▸ (hUmem v₀).2 hv₀))
  have hUtop : U ≠ ⊤ := by
    intro htop
    have hscal : ((g₀ : SpecialLinearGroup (Fin m) E) : Matrix (Fin m) (Fin m) E) =
        ξ • (1 : Matrix (Fin m) (Fin m) E) := by
      refine Matrix.toLin'.injective (LinearMap.ext fun w => ?_)
      have hw : w ∈ U := htop ▸ Submodule.mem_top
      have := (hUmem w).1 hw
      rw [hTapp] at this
      simpa [Matrix.toLin'_apply] using this
    have hdet : ξ ^ m = 1 := by
      have h1 := g₀.2
      rw [hscal, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one] at h1
      exact h1
    have hξ1 : ξ = 1 := by
      have := pow_gcd_eq_one.2 ⟨hξp, hdet⟩
      rwa [hcop.gcd_eq_one, pow_one] at this
    apply hg₀1
    apply Subtype.ext
    rw [hscal, hξ1, one_smul]
    rfl
  have hUstab : ∀ h : ↥P, ∀ w ∈ U, T h w ∈ U := by
    intro h w hw
    rw [hUmem] at hw ⊢
    have hc : T g₀' (T h w) = T h (T g₀' w) := by
      have := congrArg (fun f => f w) (hTcomm g₀' h)
      simpa using this
    rw [hc, hw, map_smul]
  obtain ⟨v, hvU, hv0, hvc⟩ := exists_common_eigenvector hp.pos hζ T hTcomm hTpow hUne hUstab
  choose lam hlam using hvc
  obtain ⟨φ₀, hφ₀0, hφ₀U⟩ := exists_ann_ne_zero U hUtop
  let N' : Submodule E (Fin m → E) :=
    { carrier := {φ | ∀ u ∈ U, φ ⬝ᵥ u = 0}
      add_mem' := fun {a b} ha hb u hu => by rw [add_dotProduct, ha u hu, hb u hu, add_zero]
      zero_mem' := fun u _ => by simp
      smul_mem' := fun c a ha u hu => by rw [smul_dotProduct, ha u hu, smul_zero] }
  have hN'ne : N' ≠ ⊥ := fun h => hφ₀0 ((Submodule.mem_bot E).1 (h ▸ hφ₀U))
  have hN'stab : ∀ h : ↥P, ∀ φ ∈ N', D h φ ∈ N' := by
    intro h φ hφ u hu
    show (D h φ) ⬝ᵥ u = 0
    rw [hDapp, ← Matrix.dotProduct_mulVec, ← hTapp]
    exact hφ _ (hUstab h u hu)
  obtain ⟨φ, hφN, hφ0, hφc⟩ := exists_common_eigenvector hp.pos hζ D hDcomm hDpow hN'ne hN'stab
  choose mu hmu using hφc
  have hlam' : ∀ h : ↥P, ((h : SpecialLinearGroup (Fin m) E) : Matrix (Fin m) (Fin m) E) *ᵥ v =
      lam h • v := fun h => by rw [← hTapp]; exact hlam h
  have hmu' : ∀ h : ↥P, φ ᵥ* ((h : SpecialLinearGroup (Fin m) E) : Matrix (Fin m) (Fin m) E) =
      mu h • φ := fun h => by rw [← hDapp]; exact hmu h
  have hφv : φ ⬝ᵥ v = 0 := hφN v hvU
  have hinv1 : ∀ h : ↥P, ((h : SpecialLinearGroup (Fin m) E) : Matrix (Fin m) (Fin m) E) *
      (((h : SpecialLinearGroup (Fin m) E)⁻¹ : SpecialLinearGroup (Fin m) E) :
        Matrix (Fin m) (Fin m) E) = 1 := fun h => by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hinv2 : ∀ h : ↥P, (((h : SpecialLinearGroup (Fin m) E)⁻¹ : SpecialLinearGroup (Fin m) E) :
        Matrix (Fin m) (Fin m) E) * ((h : SpecialLinearGroup (Fin m) E) : Matrix (Fin m) (Fin m) E) =
      1 := fun h => by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hmu0 : ∀ h : ↥P, mu h ≠ 0 := by
    intro h h0
    apply hφ0
    have h1 : φ ᵥ* ((h : SpecialLinearGroup (Fin m) E) : Matrix (Fin m) (Fin m) E) = 0 := by
      rw [hmu', h0, zero_smul]
    calc φ = φ ᵥ* (((h : SpecialLinearGroup (Fin m) E) : Matrix (Fin m) (Fin m) E) *
          (((h : SpecialLinearGroup (Fin m) E)⁻¹ : SpecialLinearGroup (Fin m) E) :
            Matrix (Fin m) (Fin m) E)) := by rw [hinv1, Matrix.vecMul_one]
      _ = 0 := by rw [← Matrix.vecMul_vecMul, h1, Matrix.zero_vecMul]
  have hlam0 : ∀ h : ↥P, lam h ≠ 0 := by
    intro h h0
    apply hv0
    have h1 : ((h : SpecialLinearGroup (Fin m) E) : Matrix (Fin m) (Fin m) E) *ᵥ v = 0 := by
      rw [hlam', h0, zero_smul]
    calc v = (((((h : SpecialLinearGroup (Fin m) E)⁻¹ : SpecialLinearGroup (Fin m) E) :
          Matrix (Fin m) (Fin m) E)) * ((h : SpecialLinearGroup (Fin m) E) :
            Matrix (Fin m) (Fin m) E)) *ᵥ v := by rw [hinv2, Matrix.one_mulVec]
      _ = 0 := by rw [← Matrix.mulVec_mulVec, h1, Matrix.mulVec_zero]
  have hlam_g : lam g₀' = ξ := by
    have h1 : ξ • v = lam g₀' • v := ((hUmem v).1 hvU).symm.trans (hlam g₀')
    exact (smul_left_injective E hv0 h1).symm
  have hmu_ne : mu g₀' ≠ ξ := by
    intro hmuξ
    apply hφ0
    have hall : ∀ w : Fin m → E, φ ⬝ᵥ w = 0 := by
      intro w
      obtain ⟨u, z, hw, hAu⟩ := exists_decomp hpE (T g₀') (hTpow g₀') hξp w
      have hu : u ∈ U := LinearMap.mem_ker.2 hAu
      rw [hw, dotProduct_add, hφN u hu, zero_add]
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, dotProduct_sub,
        dotProduct_smul, hTapp, smul_eq_mul]
      rw [Matrix.dotProduct_mulVec, hmu', hmuξ, smul_dotProduct, smul_eq_mul, sub_self]
    funext j
    have := hall (Pi.single j 1)
    simpa using this
  have hrel : ∀ (h : ↥P) (x : E), (h : SpecialLinearGroup (Fin m) E) *
      tvHomSL v φ hφv (Multiplicative.ofAdd x) =
      tvHomSL v φ hφv (Multiplicative.ofAdd (lam h / mu h * x)) * (h : SpecialLinearGroup (Fin m) E) :=
    fun h x => Subtype.ext (by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_tvHomSL,
        coe_tvHomSL]
      exact mul_tvMat (hmu0 h) (hlam' h) (hmu' h) x)
  obtain ⟨S, -, hS1, hS2, hS3, hS4⟩ := exists_good_of_scaling (tvHomSL v φ hφv) (P := P)
    (tvHomSL_ne_one hφv hv0 hφ0)
    (fun h hh => ⟨lam ⟨h, hh⟩ / mu ⟨h, hh⟩, div_ne_zero (hlam0 _) (hmu0 _), fun x =>
      hrel ⟨h, hh⟩ x⟩)
    ⟨g₀, hg₀P, ξ / mu g₀', fun h1 => hmu_ne ((div_eq_one_iff_eq (hmu0 g₀')).1 h1).symm, fun x => by
      have := hrel g₀' x
      rw [hlam_g] at this
      exact this⟩
  exact ⟨S, le_top, hS1, hS2, hS3, hS4⟩

end Main

end CFSG.RankThree.PartOne.S15K
