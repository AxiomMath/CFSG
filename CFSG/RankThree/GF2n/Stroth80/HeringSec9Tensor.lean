module

public import CFSG.RankThree.GF2n.Stroth80.Sec41iii
public import CFSG.RankThree.GF2n.Stroth80.ClassicalQuasisimple
public import CFSG.ClassicalGroups.SpecialLinear.Transitive

public section

namespace CFSG.RankThree.GF2n.Stroth80.HS9

open CFSG CFSG.Open CFSG.Open.StatedAPI CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.SpecialLinear
open CFSG.Quasithin.G11.P3Ortho.Om4 CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
open Matrix

section Algebra

variable {K : Type} [Field K]

theorem exists_vecMulVec_of_det_eq_zero
    {u : Matrix (Fin 2) (Fin 2) K} (hdet : u.det = 0) (hu : u ≠ 0) :
    ∃ a b : Fin 2 → K, a ≠ 0 ∧ b ≠ 0 ∧ u = Matrix.vecMulVec a b := by
  obtain ⟨p, q, r, s, rfl⟩ : ∃ p q r s : K, u = !![p, q; r, s] :=
    ⟨u 0 0, u 0 1, u 1 0, u 1 1, Matrix.eta_fin_two u⟩
  rw [Matrix.det_fin_two_of] at hdet
  by_cases hrow : p = 0 ∧ q = 0
  ·
    obtain ⟨rfl, rfl⟩ := hrow
    have hrs : r ≠ 0 ∨ s ≠ 0 := by
      by_cases hr : r = 0
      · by_cases hs : s = 0
        · exact (hu (by ext i j; fin_cases i <;> fin_cases j <;> simp [hr, hs])).elim
        · exact Or.inr hs
      · exact Or.inl hr
    refine ⟨![0, 1], ![r, s], ?_, ?_, ?_⟩
    · intro h
      have h1 := congrFun h 1
      simp at h1
    · intro h
      rcases hrs with hr | hs
      · exact hr (by simpa using congrFun h 0)
      · exact hs (by simpa using congrFun h 1)
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.vecMulVec_apply]
  · by_cases hp : p = 0
    ·
      have hq : q ≠ 0 := fun hq => hrow ⟨hp, hq⟩
      subst hp
      have hr : r = 0 := by
        have h' : q * r = 0 := by simpa using hdet
        exact (mul_eq_zero.mp h').resolve_left hq
      subst hr
      have hdq : s / q * q = s := div_mul_cancel₀ s hq
      refine ⟨![1, s / q], ![0, q], ?_, ?_, ?_⟩
      · intro h
        have h0 := congrFun h 0
        simp at h0
      · intro h
        exact hq (by simpa using congrFun h 1)
      · ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.vecMulVec_apply, hq, hdq]
    ·
      have hsp : s * p = r * q := by
        rw [mul_comm s p, mul_comm r q]
        exact sub_eq_zero.mp hdet
      have hs : s = r / p * q := by
        rw [div_mul_eq_mul_div, eq_div_iff hp]
        exact hsp
      have hdp : r / p * p = r := div_mul_cancel₀ r hp
      refine ⟨![1, r / p], ![p, q], ?_, ?_, ?_⟩
      · intro h
        have h0 := congrFun h 0
        simp at h0
      · intro h
        exact hp (by simpa using congrFun h 0)
      · ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.vecMulVec_apply, hp, hs, hdp]

theorem eq_smul_of_fixed_by_stabilizer {w₀ w : Fin 2 → K} (hw₀ : w₀ ≠ 0)
    (h : ∀ g : Matrix.SpecialLinearGroup (Fin 2) K,
      (g : Matrix (Fin 2) (Fin 2) K) *ᵥ w₀ = w₀ → (g : Matrix (Fin 2) (Fin 2) K) *ᵥ w = w) :
    ∃ c : K, w = c • w₀ := by
  let f : Module.Dual K (Fin 2 → K) :=
    { toFun := fun z => z 0 * w₀ 1 - z 1 * w₀ 0
      map_add' := fun x y => by simp only [Pi.add_apply]; ring
      map_smul' := fun c x => by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  have hf : ∀ z, f z = z 0 * w₀ 1 - z 1 * w₀ 0 := fun z => rfl
  have hfw₀ : f w₀ = 0 := by rw [hf]; ring
  obtain ⟨A, hA, hAz⟩ := exists_statedSL_mulVec_eq_transvection f hfw₀
  have hdet : (A : Matrix (Fin 2) (Fin 2) K).det = 1 :=
    CFSG.Open.StatedAPI.det_of_mem_statedSL hA
  have hAw₀ : (A : Matrix (Fin 2) (Fin 2) K) *ᵥ w₀ = w₀ := by
    rw [hAz, hfw₀, zero_smul, add_zero]
  have hAw : (A : Matrix (Fin 2) (Fin 2) K) *ᵥ w = w :=
    h ⟨(A : Matrix (Fin 2) (Fin 2) K), hdet⟩ hAw₀
  have hfw : f w • w₀ = 0 := by
    have h2 : w + f w • w₀ = w + 0 := by rw [add_zero, ← hAz w, hAw]
    exact add_left_cancel h2
  have hfw' : f w = 0 := (smul_eq_zero.mp hfw).resolve_right hw₀
  rw [hf] at hfw'
  by_cases h0 : w₀ 0 = 0
  · have h1 : w₀ 1 ≠ 0 := by
      intro h1
      apply hw₀
      funext i
      fin_cases i
      · exact h0
      · exact h1
    have hw0 : w 0 = 0 := by
      rw [h0, mul_zero, sub_zero] at hfw'
      exact (mul_eq_zero.mp hfw').resolve_right h1
    refine ⟨w 1 / w₀ 1, ?_⟩
    have e0 : w 0 = w 1 / w₀ 1 * w₀ 0 := by rw [h0, mul_zero]; exact hw0
    have e1 : w 1 = w 1 / w₀ 1 * w₀ 1 := (div_mul_cancel₀ (w 1) h1).symm
    funext i
    fin_cases i
    · exact e0
    · exact e1
  · refine ⟨w 0 / w₀ 0, ?_⟩
    have e0 : w 0 = w 0 / w₀ 0 * w₀ 0 := (div_mul_cancel₀ (w 0) h0).symm
    have e1 : w 1 = w 0 / w₀ 0 * w₀ 1 := by
      rw [div_mul_eq_mul_div, eq_div_iff h0]
      linear_combination -hfw'
    funext i
    fin_cases i
    · exact e0
    · exact e1

@[expose] def outerR (a : Fin 2 → K) : (Fin 2 → K) →ₗ[K] Matrix (Fin 2) (Fin 2) K where
  toFun w := Matrix.vecMulVec a w
  map_add' w w' := by
    ext i j
    simp [Matrix.vecMulVec_apply, mul_add]
  map_smul' c w := by
    ext i j
    simp [Matrix.vecMulVec_apply, mul_left_comm]

@[expose] def outerL (b : Fin 2 → K) : (Fin 2 → K) →ₗ[K] Matrix (Fin 2) (Fin 2) K where
  toFun w := Matrix.vecMulVec w b
  map_add' w w' := by
    ext i j
    simp [Matrix.vecMulVec_apply, add_mul]
  map_smul' c w := by
    ext i j
    simp [Matrix.vecMulVec_apply, mul_assoc]

theorem outerR_injective {a : Fin 2 → K} (ha : a ≠ 0) : Function.Injective (outerR a) := by
  intro w w' h
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact ha (funext hcon)
  funext j
  have := congrFun (congrFun h i) j
  simp only [outerR, LinearMap.coe_mk, AddHom.coe_mk, Matrix.vecMulVec_apply] at this
  exact mul_left_cancel₀ hi this

theorem outerL_injective {b : Fin 2 → K} (hb : b ≠ 0) : Function.Injective (outerL b) := by
  intro w w' h
  obtain ⟨j, hj⟩ : ∃ j, b j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hb (funext hcon)
  funext i
  have := congrFun (congrFun h i) j
  simp only [outerL, LinearMap.coe_mk, AddHom.coe_mk, Matrix.vecMulVec_apply] at this
  exact mul_right_cancel₀ hj this

theorem exists_sl2_mulVec_eq {x y : Fin 2 → K} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) K, (g : Matrix (Fin 2) (Fin 2) K) *ᵥ x = y := by
  obtain ⟨A, hA, hAxy⟩ := exists_statedSL_mulVec_eq (m := 2) le_rfl hx hy
  exact ⟨⟨(A : Matrix (Fin 2) (Fin 2) K), det_of_mem_statedSL hA⟩, hAxy⟩

structure ActsNat (H : Subgroup (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K))
    (Φ : (Fin 2 → K) →ₗ[K] Matrix (Fin 2) (Fin 2) K) : Prop where
  inj : Function.Injective Φ
  act : ∀ h ∈ H, ∃ g : Matrix.SpecialLinearGroup (Fin 2) K,
    ∀ w, h (Φ w) = Φ ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ w)
  lift : ∀ g : Matrix.SpecialLinearGroup (Fin 2) K, ∃ h ∈ H,
    ∀ w, h (Φ w) = Φ ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ w)

theorem ActsNat.irred {H : Subgroup (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K)}
    {Φ : (Fin 2 → K) →ₗ[K] Matrix (Fin 2) (Fin 2) K} (hA : ActsNat H Φ)
    (T : Set (Matrix (Fin 2) (Fin 2) K)) (hT1 : ∀ x ∈ T, ∃ w, x = Φ w)
    (hT2 : ∀ h ∈ H, ∀ x ∈ T, h x ∈ T) : (∀ x ∈ T, x = 0) ∨ ∀ w, w ≠ 0 → Φ w ∈ T := by
  by_cases hbot : ∀ x ∈ T, x = 0
  · exact Or.inl hbot
  right
  push Not at hbot
  obtain ⟨x, hxT, hx0⟩ := hbot
  obtain ⟨w₁, rfl⟩ := hT1 x hxT
  have hw₁ : w₁ ≠ 0 := by
    rintro rfl
    exact hx0 (map_zero Φ)
  intro w hw
  obtain ⟨g, hg⟩ := exists_sl2_mulVec_eq hw₁ hw
  obtain ⟨h, hH, hh⟩ := hA.lift g
  have := hT2 h hH _ hxT
  rwa [hh, hg] at this

theorem ActsNat.fixed {H : Subgroup (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K)}
    {Φ : (Fin 2 → K) →ₗ[K] Matrix (Fin 2) (Fin 2) K} (hA : ActsNat H Φ) {w₀ : Fin 2 → K}
    (hw₀ : w₀ ≠ 0) {w : Fin 2 → K} (hfix : ∀ h ∈ H, h (Φ w₀) = Φ w₀ → h (Φ w) = Φ w) :
    ∃ c : K, w = c • w₀ := by
  refine eq_smul_of_fixed_by_stabilizer hw₀ fun g hg => ?_
  obtain ⟨h, hH, hh⟩ := hA.lift g
  have h1 : h (Φ w₀) = Φ w₀ := by rw [hh, hg]
  have h2 := hfix h hH h1
  rw [hh] at h2
  exact hA.inj h2

end Algebra

section Factors

variable {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] noncomputable def leftF (K : Type) [Field K] :
    Subgroup (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) :=
  ((rho' K).comp (MonoidHom.inl _ _)).range

@[expose] noncomputable def rightF (K : Type) [Field K] :
    Subgroup (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) :=
  ((rho' K).comp (MonoidHom.inr _ _)).range

theorem isSimpleGroup_sl2 (h4 : 4 ≤ Nat.card K) :
    IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) K) := by
  haveI := isSimpleGroup_statedSL_two (statedSL_quasisimple_of_card 2 K le_rfl h4)
  exact (MulEquiv.isSimpleGroup_congr (specialLinearGroupEquivStatedSL 2 K)).mpr this

theorem exists_not_comm_sl2 (h4 : 4 ≤ Nat.card K) :
    ∃ a b : Matrix.SpecialLinearGroup (Fin 2) K, a * b ≠ b * a := by
  by_contra h
  push Not at h
  haveI := isSimpleGroup_statedSL_two (statedSL_quasisimple_of_card 2 K le_rfl h4)
  have hq := statedSL_quasisimple_of_card 2 K le_rfl h4
  exact not_isSolvable_of_isQuasisimple hq (isSolvable_of_comm fun a b => by
    have := h ((specialLinearGroupEquivStatedSL 2 K).symm a)
      ((specialLinearGroupEquivStatedSL 2 K).symm b)
    simpa [← map_mul] using congrArg (specialLinearGroupEquivStatedSL 2 K) this)

theorem leftF_le_range : leftF K ≤ (rho' K).range := by
  rintro _ ⟨A, rfl⟩
  exact ⟨(A, 1), rfl⟩

theorem rho'_inl_apply (A : Matrix.SpecialLinearGroup (Fin 2) K) (X : Matrix (Fin 2) (Fin 2) K) :
    rho' K (A, 1) X = (A : Matrix (Fin 2) (Fin 2) K) * X := by
  have h1 : rho' K (A, 1) X = (specialRho (A, 1)).val X := rfl
  rw [h1, specialRho_apply]
  simp

theorem rho'_inr_apply (B : Matrix.SpecialLinearGroup (Fin 2) K) (X : Matrix (Fin 2) (Fin 2) K) :
    rho' K (1, B) X =
      X * ((B⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
  have h1 : rho' K (1, B) X = (specialRho (1, B)).val X := rfl
  rw [h1, specialRho_apply]
  simp

theorem natural_module_data
    {H : Subgroup (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K)}
    (hH : H = leftF K ∨ H = rightF K) {u₀ : Matrix (Fin 2) (Fin 2) K} (hdet : u₀.det = 0)
    (hu : u₀ ≠ 0) :
    ∃ (Φ : (Fin 2 → K) →ₗ[K] Matrix (Fin 2) (Fin 2) K) (w₀ : Fin 2 → K),
      ActsNat H Φ ∧ w₀ ≠ 0 ∧ u₀ = Φ w₀ := by
  obtain ⟨a, b, ha, hb, rfl⟩ := exists_vecMulVec_of_det_eq_zero hdet hu
  rcases hH with rfl | rfl
  · refine ⟨outerL b, a, ⟨outerL_injective hb, ?_, ?_⟩, ha, rfl⟩
    · rintro _ ⟨A, rfl⟩
      refine ⟨A, fun w => ?_⟩
      show rho' K (A, 1) (Matrix.vecMulVec w b) = Matrix.vecMulVec _ b
      rw [rho'_inl_apply, Matrix.mul_vecMulVec]
    · intro g
      refine ⟨rho' K (g, 1), ⟨g, rfl⟩, fun w => ?_⟩
      show rho' K (g, 1) (Matrix.vecMulVec w b) = Matrix.vecMulVec _ b
      rw [rho'_inl_apply, Matrix.mul_vecMulVec]
  · refine ⟨outerR a, b, ⟨outerR_injective ha, ?_, ?_⟩, hb, rfl⟩
    · rintro _ ⟨B, rfl⟩
      refine ⟨(B⁻¹).transpose, fun w => ?_⟩
      show rho' K (1, B) (Matrix.vecMulVec a w) = Matrix.vecMulVec a _
      rw [rho'_inr_apply, Matrix.vecMulVec_mul, Matrix.SpecialLinearGroup.coe_transpose,
        Matrix.mulVec_transpose]
    · intro g
      refine ⟨rho' K (1, (g.transpose)⁻¹), ⟨_, rfl⟩, fun w => ?_⟩
      show rho' K (1, (g.transpose)⁻¹) (Matrix.vecMulVec a w) = Matrix.vecMulVec a _
      have e : (((g.transpose)⁻¹)⁻¹).transpose = g := by
        rw [inv_inv]
        exact Subtype.ext (Matrix.transpose_transpose _)
      rw [rho'_inr_apply, Matrix.vecMulVec_mul, ← Matrix.mulVec_transpose,
        ← Matrix.SpecialLinearGroup.coe_transpose, e]

theorem eq_leftF_or_rightF (h4 : 4 ≤ Nat.card K)
    {H₁ H₂ : Subgroup (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K)}
    (hn₁ : ∀ g ∈ (rho' K).range, ∀ h ∈ H₁, g * h * g⁻¹ ∈ H₁)
    (hn₂ : ∀ g ∈ (rho' K).range, ∀ h ∈ H₂, g * h * g⁻¹ ∈ H₂)
    (hle₁ : H₁ ≤ (rho' K).range) (hle₂ : H₂ ≤ (rho' K).range) (h1 : H₁ ≠ ⊥) (h2 : H₂ ≠ ⊥)
    (hc : ∀ x ∈ H₁, ∀ y ∈ H₂, x * y = y * x) :
    (H₁ = leftF K ∧ H₂ = rightF K) ∨ (H₁ = rightF K ∧ H₂ = leftF K) := by
  haveI := isSimpleGroup_sl2 (K := K) h4
  have hρ := rho'_injective (K := K)
  haveI hN₁ : (H₁.comap (rho' K)).Normal := ⟨fun n hn g => by
    have := hn₁ (rho' K g) ⟨g, rfl⟩ (rho' K n) hn
    simpa [← map_mul, ← map_inv] using this⟩
  haveI hN₂ : (H₂.comap (rho' K)).Normal := ⟨fun n hn g => by
    have := hn₂ (rho' K g) ⟨g, rfl⟩ (rho' K n) hn
    simpa [← map_mul, ← map_inv] using this⟩
  have hbot : ∀ H : Subgroup (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K),
      H ≤ (rho' K).range → H ≠ ⊥ → H.comap (rho' K) ≠ ⊥ := by
    intro H hle hne hcomap
    apply hne
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨z, rfl⟩ := hle hx
    have : z ∈ H.comap (rho' K) := hx
    rw [hcomap, Subgroup.mem_bot] at this
    rw [this, map_one]
    exact Subgroup.one_mem _
  have hcomm : ∀ x ∈ H₁.comap (rho' K), ∀ y ∈ H₂.comap (rho' K), x * y = y * x := by
    intro x hx y hy
    apply hρ
    rw [map_mul, map_mul]
    exact hc _ hx _ hy
  have hmap : ∀ H : Subgroup (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K),
      H ≤ (rho' K).range → (H.comap (rho' K)).map (rho' K) = H := fun H hle =>
    Subgroup.map_comap_eq_self hle
  have hL : ((⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)).prod ⊥).map (rho' K) =
      leftF K := by
    ext x
    constructor
    · rintro ⟨⟨a, b⟩, hab, rfl⟩
      obtain ⟨-, hb⟩ := Subgroup.mem_prod.mp hab
      rw [Subgroup.mem_bot] at hb
      subst hb
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨(a, 1), Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, Subgroup.one_mem _⟩, rfl⟩
  have hR : ((⊥ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)).prod ⊤).map (rho' K) =
      rightF K := by
    ext x
    constructor
    · rintro ⟨⟨a, b⟩, hab, rfl⟩
      obtain ⟨ha, -⟩ := Subgroup.mem_prod.mp hab
      rw [Subgroup.mem_bot] at ha
      subst ha
      exact ⟨b, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨(1, b), Subgroup.mem_prod.mpr ⟨Subgroup.one_mem _, Subgroup.mem_top _⟩, rfl⟩
  have hA := exists_not_comm_sl2 (K := K) h4
  rcases commuting_normal_ne_bot_prod hA hA (hbot H₁ hle₁ h1) (hbot H₂ hle₂ h2) hcomm with
    ⟨e1, e2⟩ | ⟨e1, e2⟩
  · left
    rw [← hmap H₁ hle₁, ← hmap H₂ hle₂, e1, e2, hL, hR]
    exact ⟨rfl, rfl⟩
  · right
    rw [← hmap H₁ hle₁, ← hmap H₂ hle₂, e1, e2, hL, hR]
    exact ⟨rfl, rfl⟩

end Factors

end CFSG.RankThree.GF2n.Stroth80.HS9
