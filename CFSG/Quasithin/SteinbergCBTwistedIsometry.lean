module

public import CFSG.Quasithin.SteinbergCBTwistedForm

public section

namespace CFSG.Quasithin.SteinbergCB

open Matrix

@[expose] def isometryGroup {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (Q : QuadraticForm R V) : Subgroup (V ≃ₗ[R] V) where
  carrier := {h | ∀ x, Q (h x) = Q x}
  one_mem' _ := rfl
  mul_mem' {h k} hh hk x := by
    rw [LinearEquiv.mul_apply, hh, hk]
  inv_mem' {h} hh x := by
    have := hh (h⁻¹ x)
    rw [← this, ← LinearEquiv.mul_apply, mul_inv_cancel]
    rfl

theorem mem_isometryGroup {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    {Q : QuadraticForm R V} {h : V ≃ₗ[R] V} : h ∈ isometryGroup Q ↔ ∀ x, Q (h x) = Q x :=
  Iff.rfl

theorem polar_isometry {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    {Q : QuadraticForm R V} {h : V ≃ₗ[R] V} (hh : h ∈ isometryGroup Q) (x y : V) :
    QuadraticMap.polar Q (h x) (h y) = QuadraticMap.polar Q x y := by
  rw [QuadraticMap.polar, QuadraticMap.polar, ← map_add, hh, hh, hh]

variable {F : Type*} [Field F] {σ : F →+* F}

theorem linearMap_ext_twMk (hinv : ∀ x, σ (σ x) = x) {ω : F} (hω : σ ω ≠ ω)
    {k₁ k₂ : twistedForm σ →ₗ[frobFixed σ] twistedForm σ}
    (he : k₁ (twMk hinv 1 0 0) = k₂ (twMk hinv 1 0 0))
    (hf : k₁ (twMk hinv 0 0 1) = k₂ (twMk hinv 0 0 1))
    (h1 : k₁ (twMk hinv 0 1 0) = k₂ (twMk hinv 0 1 0))
    (h2 : k₁ (twMk hinv 0 ω 0) = k₂ (twMk hinv 0 ω 0)) : k₁ = k₂ := by
  apply LinearMap.ext
  intro X
  obtain ⟨α, β, hα, hβ, hX⟩ := exists_frob_decomp hinv hω ((X : Matrix (Fin 2) (Fin 2) F) 0 1)
  have hdec : X = (⟨(X : Matrix (Fin 2) (Fin 2) F) 0 0, twistedForm_diag_mem X.2 0⟩ :
      frobFixed σ) • twMk hinv 1 0 0 +
      (⟨(X : Matrix (Fin 2) (Fin 2) F) 1 1, twistedForm_diag_mem X.2 1⟩ : frobFixed σ) •
        twMk hinv 0 0 1 +
      (⟨α, mem_frobFixed.2 hα⟩ : frobFixed σ) • twMk hinv 0 1 0 +
      (⟨β, mem_frobFixed.2 hβ⟩ : frobFixed σ) • twMk hinv 0 ω 0 := by
    apply Subtype.ext
    simp only [Submodule.coe_add, Submodule.coe_smul, twMk_coe, Subfield.smul_def]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hX, hα, hβ, ← twistedForm_entry X.2 0 1]
  rw [hdec]
  simp only [map_add, map_smul, he, hf, h1, h2]

variable (hinv : ∀ x, σ (σ x) = x)

theorem polar_twMk_e (X : twistedForm σ) :
    ((QuadraticMap.polar (twistedDet σ) X (twMk hinv 1 0 0) : frobFixed σ) : F) =
      (X : Matrix (Fin 2) (Fin 2) F) 1 1 := by
  rw [twistedDet_polar_twMk]
  simp

theorem polar_twMk_f (X : twistedForm σ) :
    ((QuadraticMap.polar (twistedDet σ) X (twMk hinv 0 0 1) : frobFixed σ) : F) =
      (X : Matrix (Fin 2) (Fin 2) F) 0 0 := by
  rw [twistedDet_polar_twMk]
  simp

theorem isometry_mem_ker_twistDiag {h : twistedForm σ ≃ₗ[frobFixed σ] twistedForm σ}
    (hh : h ∈ isometryGroup (twistedDet σ)) (he : h (twMk hinv 1 0 0) = twMk hinv 1 0 0)
    (hf : h (twMk hinv 0 0 1) = twMk hinv 0 0 1) {X : twistedForm σ}
    (hX : X ∈ LinearMap.ker (twistDiag σ)) : h X ∈ LinearMap.ker (twistDiag σ) := by
  obtain ⟨h00, h11⟩ := mem_ker_twistDiag.1 hX
  rw [mem_ker_twistDiag]
  constructor
  · rw [← polar_twMk_f hinv, ← hf, polar_isometry hh, polar_twMk_f hinv, h00]
  · rw [← polar_twMk_e hinv, ← he, polar_isometry hh, polar_twMk_e hinv, h11]

theorem eq_twMk_of_mem_ker {X : twistedForm σ} (hX : X ∈ LinearMap.ker (twistDiag σ)) :
    X = twMk hinv 0 ((X : Matrix (Fin 2) (Fin 2) F) 0 1) 0 := by
  obtain ⟨h00, h11⟩ := mem_ker_twistDiag.1 hX
  apply Subtype.ext
  rw [twMk_coe, twistedForm_eq X, h00, h11]
  simp

theorem twMk_mem_ker (b : F) : twMk hinv 0 b 0 ∈ LinearMap.ker (twistDiag σ) := by
  rw [mem_ker_twistDiag, twMk_coe]
  simp

theorem twistedDet_twMk_zero (b : F) :
    ((twistedDet σ (twMk hinv 0 b 0) : frobFixed σ) : F) = -(b * σ b) := by
  rw [twistedDet_apply, twMk_coe, det_fin_two_of]
  simp

theorem polar_twMk_zero (b b' : F) :
    ((QuadraticMap.polar (twistedDet σ) (twMk hinv 0 b 0) (twMk hinv 0 b' 0) : frobFixed σ) :
      F) = -(b * σ b' + b' * σ b) := by
  rw [twistedDet_polar_twMk, twMk_coe]
  simp
  ring

theorem isometry_norm_one {h : twistedForm σ ≃ₗ[frobFixed σ] twistedForm σ}
    (hh : h ∈ isometryGroup (twistedDet σ)) (he : h (twMk hinv 1 0 0) = twMk hinv 1 0 0)
    (hf : h (twMk hinv 0 0 1) = twMk hinv 0 0 1) :
    ((h (twMk hinv 0 1 0) : twistedForm σ) : Matrix (Fin 2) (Fin 2) F) 0 1 *
      σ (((h (twMk hinv 0 1 0) : twistedForm σ) : Matrix (Fin 2) (Fin 2) F) 0 1) = 1 := by
  have hmem := isometry_mem_ker_twistDiag hinv hh he hf (twMk_mem_ker hinv 1)
  have hQ : ((twistedDet σ (h (twMk hinv 0 1 0)) : frobFixed σ) : F) =
      ((twistedDet σ (twMk hinv 0 1 0) : frobFixed σ) : F) := congrArg Subtype.val (hh _)
  rw [eq_twMk_of_mem_ker hinv hmem, twistedDet_twMk_zero, twistedDet_twMk_zero] at hQ
  simpa using hQ

theorem isometry_omega_cases (ω : F) {h : twistedForm σ ≃ₗ[frobFixed σ] twistedForm σ}
    (hh : h ∈ isometryGroup (twistedDet σ)) (he : h (twMk hinv 1 0 0) = twMk hinv 1 0 0)
    (hf : h (twMk hinv 0 0 1) = twMk hinv 0 0 1) :
    ((h (twMk hinv 0 ω 0) : twistedForm σ) : Matrix (Fin 2) (Fin 2) F) 0 1 =
        ((h (twMk hinv 0 1 0) : twistedForm σ) : Matrix (Fin 2) (Fin 2) F) 0 1 * ω ∨
      ((h (twMk hinv 0 ω 0) : twistedForm σ) : Matrix (Fin 2) (Fin 2) F) 0 1 =
        ((h (twMk hinv 0 1 0) : twistedForm σ) : Matrix (Fin 2) (Fin 2) F) 0 1 * σ ω := by
  set c := ((h (twMk hinv 0 1 0) : twistedForm σ) : Matrix (Fin 2) (Fin 2) F) 0 1 with hc
  set μ := ((h (twMk hinv 0 ω 0) : twistedForm σ) : Matrix (Fin 2) (Fin 2) F) 0 1 with hμ
  have hN : c * σ c = 1 := isometry_norm_one hinv hh he hf
  have hmem1 := isometry_mem_ker_twistDiag hinv hh he hf (twMk_mem_ker hinv 1)
  have hmemω := isometry_mem_ker_twistDiag hinv hh he hf (twMk_mem_ker hinv ω)
  have hQ : ((twistedDet σ (h (twMk hinv 0 ω 0)) : frobFixed σ) : F) =
      ((twistedDet σ (twMk hinv 0 ω 0) : frobFixed σ) : F) := congrArg Subtype.val (hh _)
  rw [eq_twMk_of_mem_ker hinv hmemω, twistedDet_twMk_zero, twistedDet_twMk_zero] at hQ
  have hNμ : μ * σ μ = ω * σ ω := by linear_combination -hQ
  have hP : ((QuadraticMap.polar (twistedDet σ) (h (twMk hinv 0 1 0)) (h (twMk hinv 0 ω 0)) :
      frobFixed σ) : F) = ((QuadraticMap.polar (twistedDet σ) (twMk hinv 0 1 0)
        (twMk hinv 0 ω 0) : frobFixed σ) : F) :=
    congrArg Subtype.val (polar_isometry hh (twMk hinv 0 1 0) (twMk hinv 0 ω 0))
  rw [eq_twMk_of_mem_ker hinv hmem1, eq_twMk_of_mem_ker hinv hmemω, polar_twMk_zero,
    polar_twMk_zero, map_one, one_mul, mul_one] at hP
  have hT : c * σ μ + μ * σ c = σ ω + ω := by linear_combination -hP
  have key : (μ * σ c - ω) * (μ * σ c - σ ω) = 0 := by
    linear_combination (μ * σ c) * hT - (μ * σ μ) * hN - hNμ
  have hμc : μ = μ * σ c * c := by linear_combination -μ * hN
  rcases mul_eq_zero.1 key with h0 | h0
  · left
    rw [hμc, sub_eq_zero.1 h0, mul_comm]
  · right
    rw [hμc, sub_eq_zero.1 h0, mul_comm]

omit hinv in
theorem twistedDet_coe (X : twistedForm σ) :
    ((twistedDet σ X : frobFixed σ) : F) =
      (X : Matrix (Fin 2) (Fin 2) F) 0 0 * (X : Matrix (Fin 2) (Fin 2) F) 1 1 -
        (X : Matrix (Fin 2) (Fin 2) F) 0 1 * σ ((X : Matrix (Fin 2) (Fin 2) F) 0 1) := by
  rw [twistedDet_apply, det_fin_two, ← twistedForm_entry X.2 0 1]

omit hinv in
theorem twistedForm_ext {X Y : twistedForm σ}
    (h00 : (X : Matrix (Fin 2) (Fin 2) F) 0 0 = (Y : Matrix (Fin 2) (Fin 2) F) 0 0)
    (h01 : (X : Matrix (Fin 2) (Fin 2) F) 0 1 = (Y : Matrix (Fin 2) (Fin 2) F) 0 1)
    (h11 : (X : Matrix (Fin 2) (Fin 2) F) 1 1 = (Y : Matrix (Fin 2) (Fin 2) F) 1 1) : X = Y := by
  apply Subtype.ext
  rw [twistedForm_eq X, twistedForm_eq Y, h00, h01, h11]

open MulAction in
theorem card_stabilizer_stabilizer_le [Finite F] {ω : F} (hω : σ ω ≠ ω) :
    Nat.card (stabilizer (stabilizer (isometryGroup (twistedDet σ)) (twMk hinv 1 0 0))
      (twMk hinv 0 0 1)) ≤ 2 * Nat.card {c : F // c * σ c = 1} := by
  classical
  set O := isometryGroup (twistedDet σ)
  let L : stabilizer (stabilizer O (twMk hinv 1 0 0)) (twMk hinv 0 0 1) →
      (twistedForm σ ≃ₗ[frobFixed σ] twistedForm σ) :=
    fun k => ((k : stabilizer O (twMk hinv 1 0 0)) : O)
  have hO : ∀ k, L k ∈ O := fun k => ((k : stabilizer O (twMk hinv 1 0 0)) : O).2
  have he : ∀ k, L k (twMk hinv 1 0 0) = twMk hinv 1 0 0 := fun k => by
    have := mem_stabilizer_iff.1 (k : stabilizer O (twMk hinv 1 0 0)).2
    rwa [Subgroup.smul_def, LinearEquiv.smul_def] at this
  have hf : ∀ k, L k (twMk hinv 0 0 1) = twMk hinv 0 0 1 := fun k => by
    have := mem_stabilizer_iff.1 k.2
    rwa [Subgroup.smul_def, Subgroup.smul_def, LinearEquiv.smul_def] at this
  let Φ : stabilizer (stabilizer O (twMk hinv 1 0 0)) (twMk hinv 0 0 1) →
      {c : F // c * σ c = 1} × Bool := fun k =>
    (⟨((L k (twMk hinv 0 1 0) : twistedForm σ) : Matrix (Fin 2) (Fin 2) F) 0 1,
      isometry_norm_one hinv (hO k) (he k) (hf k)⟩,
      decide (((L k (twMk hinv 0 ω 0) : twistedForm σ) : Matrix (Fin 2) (Fin 2) F) 0 1 =
        ((L k (twMk hinv 0 1 0) : twistedForm σ) : Matrix (Fin 2) (Fin 2) F) 0 1 * ω))
  have hinj : Function.Injective Φ := by
    intro k₁ k₂ hk
    have hc : ((L k₁ (twMk hinv 0 1 0) : twistedForm σ) : Matrix (Fin 2) (Fin 2) F) 0 1 =
        ((L k₂ (twMk hinv 0 1 0) : twistedForm σ) : Matrix (Fin 2) (Fin 2) F) 0 1 :=
      congrArg (fun p => (p.1 : F)) hk
    have hd := congrArg Prod.snd hk
    simp only [Φ, decide_eq_decide] at hd
    have hmem : ∀ k b, L k (twMk hinv 0 b 0) = twMk hinv 0
        (((L k (twMk hinv 0 b 0) : twistedForm σ) : Matrix (Fin 2) (Fin 2) F) 0 1) 0 :=
      fun k b => eq_twMk_of_mem_ker hinv
        (isometry_mem_ker_twistDiag hinv (hO k) (he k) (hf k) (twMk_mem_ker hinv b))
    have hL : L k₁ = L k₂ := by
      apply LinearEquiv.toLinearMap_injective
      apply linearMap_ext_twMk hinv hω
      · simp only [LinearEquiv.coe_coe, he]
      · simp only [LinearEquiv.coe_coe, hf]
      · simp only [LinearEquiv.coe_coe]
        rw [hmem k₁ 1, hmem k₂ 1, hc]
      · simp only [LinearEquiv.coe_coe]
        have h₁ := isometry_omega_cases hinv ω (hO k₁) (he k₁) (hf k₁)
        have h₂ := isometry_omega_cases hinv ω (hO k₂) (he k₂) (hf k₂)
        rw [hc] at h₁ hd
        rw [hmem k₁ ω, hmem k₂ ω]
        congr 1
        by_cases hx : ((L k₁ (twMk hinv 0 ω 0) : twistedForm σ) :
            Matrix (Fin 2) (Fin 2) F) 0 1 =
              ((L k₂ (twMk hinv 0 1 0) : twistedForm σ) : Matrix (Fin 2) (Fin 2) F) 0 1 * ω
        · rw [hx, hd.1 hx]
        · rw [h₁.resolve_left hx, h₂.resolve_left (fun h => hx (hd.2 h))]
    exact Subtype.ext (Subtype.ext (Subtype.ext hL))
  calc Nat.card (stabilizer (stabilizer O (twMk hinv 1 0 0)) (twMk hinv 0 0 1))
      ≤ Nat.card ({c : F // c * σ c = 1} × Bool) := Nat.card_le_card_of_injective Φ hinj
    _ = 2 * Nat.card {c : F // c * σ c = 1} := by
      rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool, mul_comm]

open MulAction in
theorem ncard_orbit_f_le [Finite F] :
    (orbit (stabilizer (isometryGroup (twistedDet σ)) (twMk hinv 1 0 0))
      (twMk hinv 0 0 1)).ncard ≤ Nat.card F := by
  set T : Set (twistedForm σ) :=
    {y | (y : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 ∧ twistedDet σ y = 0} with hT
  have hsub : orbit (stabilizer (isometryGroup (twistedDet σ)) (twMk hinv 1 0 0))
      (twMk hinv 0 0 1) ⊆ T := by
    rintro y ⟨⟨⟨g, hk⟩, hge⟩, rfl⟩
    change g (twMk hinv 0 0 1) ∈ T
    have he : g (twMk hinv 1 0 0) = twMk hinv 1 0 0 := hge
    refine ⟨?_, ?_⟩
    · rw [← polar_twMk_e hinv, ← he, polar_isometry hk, polar_twMk_e hinv, twMk_coe]
      simp
    · rw [hk]
      apply Subtype.ext
      rw [twistedDet_apply, twMk_coe, det_fin_two_of]
      simp
  have hTle : T.ncard ≤ Nat.card F := by
    rw [← Nat.card_coe_set_eq]
    refine Nat.card_le_card_of_injective
      (fun y => ((y : twistedForm σ) : Matrix (Fin 2) (Fin 2) F) 0 1) ?_
    intro y₁ y₂ hy
    obtain ⟨h₁, hQ₁⟩ := y₁.2
    obtain ⟨h₂, hQ₂⟩ := y₂.2
    have e₁ := congrArg Subtype.val hQ₁
    have e₂ := congrArg Subtype.val hQ₂
    change ((twistedDet σ y₁ : frobFixed σ) : F) = 0 at e₁
    change ((twistedDet σ y₂ : frobFixed σ) : F) = 0 at e₂
    rw [twistedDet_coe, h₁] at e₁
    rw [twistedDet_coe, h₂] at e₂
    simp only at hy
    apply Subtype.ext
    apply twistedForm_ext
    · rw [hy] at e₁
      linear_combination e₁ - e₂
    · exact hy
    · rw [h₁, h₂]
  exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans hTle

open MulAction in
theorem ncard_orbit_e_le [Finite F] :
    (orbit (isometryGroup (twistedDet σ)) (twMk hinv 1 0 0)).ncard ≤
      (Nat.card (frobFixed σ) - 1) * Nat.card F + (Nat.card (frobFixed σ) - 1) := by
  set S₁ : Set (twistedForm σ) :=
    {y | (y : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 ∧ twistedDet σ y = 0} with hS₁
  set S₂ : Set (twistedForm σ) :=
    {y | y ≠ 0 ∧ (y : Matrix (Fin 2) (Fin 2) F) 0 0 = 0 ∧ twistedDet σ y = 0} with hS₂
  have hsub : orbit (isometryGroup (twistedDet σ)) (twMk hinv 1 0 0) ⊆ S₁ ∪ S₂ := by
    rintro y ⟨h, rfl⟩
    change h • twMk hinv 1 0 0 ∈ S₁ ∪ S₂
    rw [Subgroup.smul_def, LinearEquiv.smul_def]
    have hQ : twistedDet σ ((h : twistedForm σ ≃ₗ[frobFixed σ] twistedForm σ)
        (twMk hinv 1 0 0)) = 0 := by
      rw [h.2]
      apply Subtype.ext
      rw [twistedDet_apply, twMk_coe, det_fin_two_of]
      simp
    have hne : (h : twistedForm σ ≃ₗ[frobFixed σ] twistedForm σ) (twMk hinv 1 0 0) ≠ 0 := by
      rw [Ne, LinearEquiv.map_eq_zero_iff]
      intro h0
      have := congrArg (fun X : twistedForm σ => (X : Matrix (Fin 2) (Fin 2) F) 0 0) h0
      simp [twMk_coe] at this
    by_cases h0 : (((h : twistedForm σ ≃ₗ[frobFixed σ] twistedForm σ) (twMk hinv 1 0 0) :
        twistedForm σ) : Matrix (Fin 2) (Fin 2) F) 0 0 = 0
    · exact Or.inr ⟨hne, h0, hQ⟩
    · exact Or.inl ⟨h0, hQ⟩
  have hentry : ∀ {y : twistedForm σ}, twistedDet σ y = 0 →
      (y : Matrix (Fin 2) (Fin 2) F) 0 0 * (y : Matrix (Fin 2) (Fin 2) F) 1 1 =
        (y : Matrix (Fin 2) (Fin 2) F) 0 1 * σ ((y : Matrix (Fin 2) (Fin 2) F) 0 1) :=
    fun {y} hy => by
      have := congrArg Subtype.val hy
      change ((twistedDet σ y : frobFixed σ) : F) = 0 at this
      rw [twistedDet_coe] at this
      linear_combination this
  have h₁ : S₁.ncard ≤ (Nat.card (frobFixed σ) - 1) * Nat.card F := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_units (frobFixed σ), ← Nat.card_prod]
    refine Nat.card_le_card_of_injective (fun y => (Units.mk0
      (⟨((y : twistedForm σ) : Matrix (Fin 2) (Fin 2) F) 0 0, twistedForm_diag_mem y.1.2 0⟩ :
        frobFixed σ) (fun h => y.2.1 (congrArg Subtype.val h)),
      ((y : twistedForm σ) : Matrix (Fin 2) (Fin 2) F) 0 1)) ?_
    intro y₁ y₂ hy
    have ha : ((y₁ : twistedForm σ) : Matrix (Fin 2) (Fin 2) F) 0 0 =
        ((y₂ : twistedForm σ) : Matrix (Fin 2) (Fin 2) F) 0 0 :=
      congrArg (fun p => ((p.1 : frobFixed σ) : F)) hy
    have hb : ((y₁ : twistedForm σ) : Matrix (Fin 2) (Fin 2) F) 0 1 =
        ((y₂ : twistedForm σ) : Matrix (Fin 2) (Fin 2) F) 0 1 := congrArg Prod.snd hy
    have e₁ := hentry y₁.2.2
    have e₂ := hentry y₂.2.2
    apply Subtype.ext
    apply twistedForm_ext ha hb
    rw [hb, ← e₂, ha] at e₁
    exact mul_left_cancel₀ (ha ▸ y₁.2.1) e₁
  have h₂ : S₂.ncard ≤ Nat.card (frobFixed σ) - 1 := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_units (frobFixed σ)]
    have hb : ∀ y : S₂, ((y : twistedForm σ) : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := fun y => by
      have e := hentry y.2.2.2
      rw [y.2.2.1, zero_mul] at e
      exact frob_norm_eq_zero e.symm
    have hd : ∀ y : S₂, ((y : twistedForm σ) : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := fun y h => by
      apply y.2.1
      apply Subtype.ext
      rw [twistedForm_eq, y.2.2.1, hb y, h]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    refine Nat.card_le_card_of_injective (fun y => Units.mk0
      (⟨((y : twistedForm σ) : Matrix (Fin 2) (Fin 2) F) 1 1, twistedForm_diag_mem y.1.2 1⟩ :
        frobFixed σ) (fun h => hd y (congrArg Subtype.val h))) ?_
    intro y₁ y₂ hy
    have hdd : ((y₁ : twistedForm σ) : Matrix (Fin 2) (Fin 2) F) 1 1 =
        ((y₂ : twistedForm σ) : Matrix (Fin 2) (Fin 2) F) 1 1 :=
      congrArg (fun u : (frobFixed σ)ˣ => ((u : frobFixed σ) : F)) hy
    apply Subtype.ext
    apply twistedForm_ext _ _ hdd
    · rw [y₁.2.2.1, y₂.2.2.1]
    · rw [hb y₁, hb y₂]
  calc (orbit (isometryGroup (twistedDet σ)) (twMk hinv 1 0 0)).ncard ≤ (S₁ ∪ S₂).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ S₁.ncard + S₂.ncard := Set.ncard_union_le _ _
    _ ≤ _ := add_le_add h₁ h₂

include hinv in
open MulAction in
theorem card_isometryGroup_le [Finite F] {ω : F} (hω : σ ω ≠ ω) :
    Nat.card (isometryGroup (twistedDet σ)) ≤
      ((Nat.card (frobFixed σ) - 1) * Nat.card F + (Nat.card (frobFixed σ) - 1)) *
        (Nat.card F * (2 * Nat.card {c : F // c * σ c = 1})) := by
  have hO := Subgroup.card_mul_index (stabilizer (isometryGroup (twistedDet σ)) (twMk hinv 1 0 0))
  rw [index_stabilizer] at hO
  have hO' := Subgroup.card_mul_index (stabilizer (stabilizer (isometryGroup (twistedDet σ))
    (twMk hinv 1 0 0)) (twMk hinv 0 0 1))
  rw [index_stabilizer] at hO'
  rw [← hO, ← hO', mul_comm, mul_comm (Nat.card _)]
  exact Nat.mul_le_mul (ncard_orbit_e_le hinv) (Nat.mul_le_mul (ncard_orbit_f_le hinv)
    (card_stabilizer_stabilizer_le hinv hω))

end CFSG.Quasithin.SteinbergCB
