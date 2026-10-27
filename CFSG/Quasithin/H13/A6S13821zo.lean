module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.Quasithin.Background.F918C2

public section

namespace CFSG.Quasithin.H13.A6.A6Semi

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type} [Field K]

def u01 : SpecialLinearGroup (Fin 3) K :=
  ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

def u12 : SpecialLinearGroup (Fin 3) K :=
  ⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

theorem u01_mem : (u01 : SpecialLinearGroup (Fin 3) K) ∈ unitriangular 3 K := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp_all [u01]
  · fin_cases i <;> simp [u01]

theorem u12_mem : (u12 : SpecialLinearGroup (Fin 3) K) ∈ unitriangular 3 K := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp_all [u12]
  · fin_cases i <;> simp [u12]

theorem fixed_iff (v : Fin 3 → K) :
    (∀ u ∈ unitriangular 3 K, (u : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v) ↔ v 1 = 0 ∧ v 2 = 0 := by
  constructor
  · intro h
    have h1 := congrFun (h _ u01_mem) 0
    have h2 := congrFun (h _ u12_mem) 1
    simp [u01, u12, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩ u hu
    obtain ⟨hl, hd⟩ := hu
    funext i
    have h10 := hl 1 0 (by decide)
    have h20 := hl 2 0 (by decide)
    have h00 := hd 0
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h1, h2, h10, h20, h00]

theorem plane_iff (v : Fin 3 → K) :
    (∀ u ∈ unitriangular 3 K, ((u : Matrix (Fin 3) (Fin 3) K) *ᵥ v - v) 1 = 0 ∧
      ((u : Matrix (Fin 3) (Fin 3) K) *ᵥ v - v) 2 = 0) ↔ v 2 = 0 := by
  constructor
  · intro h
    have h2 := (h _ u12_mem).1
    simpa [u12, Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h2
  · intro h2 u hu
    obtain ⟨hl, hd⟩ := hu
    have h10 := hl 1 0 (by decide)
    have h20 := hl 2 0 (by decide)
    have h21 := hl 2 1 (by decide)
    have h11 := hd 1
    have h22 := hd 2
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h2, h10, h20, h21, h11, h22]

theorem mulVec_conj (γ u : SpecialLinearGroup (Fin 3) K) (v : Fin 3 → K) :
    (u : Matrix (Fin 3) (Fin 3) K) *ᵥ ((γ : Matrix (Fin 3) (Fin 3) K) *ᵥ v) =
      (γ : Matrix (Fin 3) (Fin 3) K) *ᵥ
        (((γ⁻¹ * u * γ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have h : u * γ = γ * (γ⁻¹ * u * γ) := by group
  have h2 : ((u * γ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((γ * (γ⁻¹ * u * γ) : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [h]
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul (A := γ)] at h2
  rw [h2]

theorem upper_of_mem_normalizer {γ : SpecialLinearGroup (Fin 3) K}
    (hγ : γ ∈ Subgroup.normalizer ((unitriangular 3 K : Subgroup _) : Set _)) :
    (γ : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 ∧ (γ : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 ∧
      (γ : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 := by
  have hconj : ∀ u ∈ unitriangular 3 K, γ⁻¹ * u * γ ∈ unitriangular 3 K := by
    intro u hu
    apply (Subgroup.mem_normalizer_iff.mp hγ (γ⁻¹ * u * γ)).mpr
    simpa [mul_assoc] using hu
  have hL : ∀ w : Fin 3 → K, w 1 = 0 ∧ w 2 = 0 →
      ((γ : Matrix (Fin 3) (Fin 3) K) *ᵥ w) 1 = 0 ∧
        ((γ : Matrix (Fin 3) (Fin 3) K) *ᵥ w) 2 = 0 := by
    intro w hw
    apply (fixed_iff _).mp
    intro u hu
    rw [mulVec_conj, (fixed_iff w).mpr hw _ (hconj u hu)]
  have hP : ∀ v : Fin 3 → K, v 2 = 0 → ((γ : Matrix (Fin 3) (Fin 3) K) *ᵥ v) 2 = 0 := by
    intro v hv
    apply (plane_iff _).mp
    intro u hu
    have h := (plane_iff v).mpr hv _ (hconj u hu)
    rw [mulVec_conj, ← Matrix.mulVec_sub]
    exact hL _ h
  have h0 := hL (Pi.single 0 1) ⟨by simp, by simp⟩
  have h1 := hP (Pi.single 1 1) (by simp)
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h0 h1
  exact ⟨h0.1, h0.2, h1⟩


theorem det_diag {γ : SpecialLinearGroup (Fin 3) K} (h10 : (γ : Matrix (Fin 3) (Fin 3) K) 1 0 = 0)
    (h20 : (γ : Matrix (Fin 3) (Fin 3) K) 2 0 = 0) (h21 : (γ : Matrix (Fin 3) (Fin 3) K) 2 1 = 0) :
    (γ : Matrix (Fin 3) (Fin 3) K) 0 0 * (γ : Matrix (Fin 3) (Fin 3) K) 1 1 *
      (γ : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
  have h := γ.prop
  rw [Matrix.det_fin_three, h10, h20, h21] at h
  simpa using h

theorem diag_twist [Finite K] (φ : (Fin 3 → K) ≃+ (Fin 3 → K)) {e : ℕ}
    (hφ : ∀ (x : K) (v : Fin 3 → K), φ (x • v) = x ^ e • φ v)
    (α : SpecialLinearGroup (Fin 3) K →* SpecialLinearGroup (Fin 3) K)
    (hint : ∀ (γ : SpecialLinearGroup (Fin 3) K) (v : Fin 3 → K),
      φ ((γ : Matrix (Fin 3) (Fin 3) K) *ᵥ v) = (α γ : Matrix (Fin 3) (Fin 3) K) *ᵥ φ v)
    (hUs : ∀ u ∈ unitriangular 3 K, ∃ u' ∈ unitriangular 3 K, α u' = u)
    {γ : SpecialLinearGroup (Fin 3) K}
    (hγ : γ ∈ Subgroup.normalizer ((unitriangular 3 K : Subgroup _) : Set _))
    (hαγ : α γ ∈ Subgroup.normalizer ((unitriangular 3 K : Subgroup _) : Set _)) :
    ∀ i, (α γ : Matrix (Fin 3) (Fin 3) K) i i = (γ : Matrix (Fin 3) (Fin 3) K) i i ^ e := by
  classical
  have hφL : ∀ w : Fin 3 → K, w 1 = 0 ∧ w 2 = 0 → (φ w) 1 = 0 ∧ (φ w) 2 = 0 := by
    intro w hw
    apply (fixed_iff _).mp
    intro u hu
    obtain ⟨u', hu', rfl⟩ := hUs u hu
    rw [← hint, (fixed_iff w).mpr hw _ hu']
  have hφP : ∀ v : Fin 3 → K, v 2 = 0 → (φ v) 2 = 0 := by
    intro v hv
    apply (plane_iff _).mp
    intro u hu
    obtain ⟨u', hu', rfl⟩ := hUs u hu
    rw [← hint, ← map_sub]
    exact hφL _ ((plane_iff v).mpr hv _ hu')
  have hφLs : ∀ w : Fin 3 → K, (φ w) 1 = 0 ∧ (φ w) 2 = 0 → w 1 = 0 ∧ w 2 = 0 := by
    intro w hw
    let f : {x : Fin 3 → K // x 1 = 0 ∧ x 2 = 0} → {x : Fin 3 → K // x 1 = 0 ∧ x 2 = 0} :=
      fun x => ⟨φ x, hφL x x.2⟩
    have hf : Function.Injective f := fun x y h =>
      Subtype.ext (φ.injective (congrArg Subtype.val h))
    obtain ⟨x, hx⟩ := (Finite.injective_iff_surjective.mp hf) ⟨φ w, hw⟩
    have : (x : Fin 3 → K) = w := φ.injective (congrArg Subtype.val hx)
    rw [← this]
    exact x.2
  obtain ⟨g10, g20, g21⟩ := upper_of_mem_normalizer hγ
  obtain ⟨a10, a20, a21⟩ := upper_of_mem_normalizer hαγ
  set f0 := φ (Pi.single 0 1) with hf0
  set f1 := φ (Pi.single 1 1) with hf1
  have hf0L : f0 1 = 0 ∧ f0 2 = 0 := hφL (Pi.single 0 1) ⟨by simp, by simp⟩
  have hf1P : f1 2 = 0 := hφP (Pi.single 1 1) (by simp)
  have hf00 : f0 0 ≠ 0 := by
    intro h0
    have : f0 = 0 := by
      funext i
      fin_cases i
      · exact h0
      · exact hf0L.1
      · exact hf0L.2
    have h := φ.injective (this.trans (map_zero φ).symm)
    have := congrFun h 0
    simp at this
  have hf11 : f1 1 ≠ 0 := by
    intro h1
    have := hφLs (Pi.single 1 1) ⟨h1, hf1P⟩
    simp at this
  have hγe0 : (γ : Matrix (Fin 3) (Fin 3) K) *ᵥ (Pi.single 0 1) =
      (γ : Matrix (Fin 3) (Fin 3) K) 0 0 • (Pi.single 0 1 : Fin 3 → K) := by
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, g10, g20]
  have hγe1 : (γ : Matrix (Fin 3) (Fin 3) K) *ᵥ (Pi.single 1 1) =
      (γ : Matrix (Fin 3) (Fin 3) K) 0 1 • (Pi.single 0 1 : Fin 3 → K) +
        (γ : Matrix (Fin 3) (Fin 3) K) 1 1 • (Pi.single 1 1 : Fin 3 → K) := by
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, g21]
  have h0 : (α γ : Matrix (Fin 3) (Fin 3) K) 0 0 = (γ : Matrix (Fin 3) (Fin 3) K) 0 0 ^ e := by
    have h := hint γ (Pi.single 0 1)
    rw [hγe0, hφ, ← hf0] at h
    have h' := congrFun h 0
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hf0L.1, hf0L.2] at h'
    exact (h'.resolve_right hf00).symm
  have h1 : (α γ : Matrix (Fin 3) (Fin 3) K) 1 1 = (γ : Matrix (Fin 3) (Fin 3) K) 1 1 ^ e := by
    have h := hint γ (Pi.single 1 1)
    rw [hγe1, map_add, hφ, hφ, ← hf0, ← hf1] at h
    have h' := congrFun h 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hf0L.1, hf1P, a10] at h'
    exact (h'.resolve_right hf11).symm
  have hd := det_diag g10 g20 g21
  have hd' := det_diag a10 a20 a21
  rw [h0, h1] at hd'
  have h2 : (α γ : Matrix (Fin 3) (Fin 3) K) 2 2 = (γ : Matrix (Fin 3) (Fin 3) K) 2 2 ^ e := by
    have hpow := congrArg (· ^ e) hd
    simp only [mul_pow, one_pow] at hpow
    have hne : (γ : Matrix (Fin 3) (Fin 3) K) 0 0 ^ e * (γ : Matrix (Fin 3) (Fin 3) K) 1 1 ^ e ≠
        0 := by
      intro h
      rw [h, zero_mul] at hd'
      exact zero_ne_one hd'
    exact mul_left_cancel₀ hne (hd'.trans hpow.symm)
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2


theorem isUpperTriangular_of_mem_normalizer {γ : SpecialLinearGroup (Fin 3) K}
    (hγ : γ ∈ Subgroup.normalizer ((unitriangular 3 K : Subgroup _) : Set _)) :
    (γ : Matrix (Fin 3) (Fin 3) K).IsUpperTriangular := by
  obtain ⟨h10, h20, h21⟩ := upper_of_mem_normalizer hγ
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

theorem pow_three_eq_one [Finite K] (hK : Nat.card K = 4) {x : K} (hx : x ≠ 0) : x ^ 3 = 1 := by
  have := Fintype.ofFinite K
  have h := FiniteField.pow_card_sub_one_eq_one x hx
  rwa [← Nat.card_eq_fintype_card, hK] at h

theorem mem_unitriangular_of_diag [Finite K] (hK : Nat.card K = 4)
    {γ δ : SpecialLinearGroup (Fin 3) K} (hγ : (γ : Matrix (Fin 3) (Fin 3) K).IsUpperTriangular)
    (hδ : (δ : Matrix (Fin 3) (Fin 3) K).IsUpperTriangular) {e : ℕ}
    (hd : ∀ i, (δ : Matrix (Fin 3) (Fin 3) K) i i = (γ : Matrix (Fin 3) (Fin 3) K) i i ^ e) :
    (e = 1 → δ * γ⁻¹ ∈ unitriangular 3 K) ∧ (e = 2 → δ * γ ∈ unitriangular 3 K) := by
  have hγB : γ ∈ upperTriangular 3 K := mem_upperTriangular_iff_isUpperTriangular.mpr hγ
  have hδB : δ ∈ upperTriangular 3 K := mem_upperTriangular_iff_isUpperTriangular.mpr hδ
  have hγi := coe_inv_isUpperTriangular hγ
  have hne : ∀ i, (γ : Matrix (Fin 3) (Fin 3) K) i i ≠ 0 := by
    intro i h0
    have h := coe_inv_apply_self_of_isUpperTriangular hγ i
    rw [h0, zero_mul] at h
    exact zero_ne_one h
  refine ⟨fun he => ⟨fun i j hij => ?_, fun i => ?_⟩, fun he => ⟨fun i j hij => ?_, fun i => ?_⟩⟩
  · exact (upperTriangular 3 K).mul_mem hδB ((upperTriangular 3 K).inv_mem hγB) i j hij
  · rw [Matrix.SpecialLinearGroup.coe_mul, mul_apply_self_of_isUpperTriangular hδ hγi, hd, he,
      pow_one]
    exact coe_inv_apply_self_of_isUpperTriangular hγ i
  · exact (upperTriangular 3 K).mul_mem hδB hγB i j hij
  · rw [Matrix.SpecialLinearGroup.coe_mul, mul_apply_self_of_isUpperTriangular hδ hγ, hd, he,
      ← pow_succ]
    exact pow_three_eq_one hK (hne i)


theorem eq_zero_or_pow [Finite K] (hK : Nat.card K = 4) {ω : K} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (x : K) : x = 0 ∨ x = 1 ∨ x = ω ∨ x = ω ^ 2 := by
  by_cases hx : x = 0
  · exact Or.inl hx
  right
  have hx3 := pow_three_eq_one hK hx
  have hs : 1 + ω + ω ^ 2 = 0 := by
    have h : (ω - 1) * (1 + ω + ω ^ 2) = 0 := by
      have : (ω - 1) * (1 + ω + ω ^ 2) = ω ^ 3 - 1 := by ring
      rw [this, hω, sub_self]
    rcases mul_eq_zero.mp h with h | h
    · exact absurd (sub_eq_zero.mp h) hω1
    · exact h
  have key : (x - 1) * (x - ω) * (x - ω ^ 2) = 0 := by
    have : (x - 1) * (x - ω) * (x - ω ^ 2) =
        x ^ 3 - (1 + ω + ω ^ 2) * x ^ 2 + (ω + ω ^ 2 + ω ^ 3) * x - ω ^ 3 := by ring
    rw [this, hs, hx3, hω]
    have : ω + ω ^ 2 + 1 = 0 := by rw [← hs]; ring
    rw [this]
    ring
  rcases mul_eq_zero.mp key with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (Or.inl (sub_eq_zero.mp h))
  · exact Or.inr (Or.inr (sub_eq_zero.mp h))

theorem exists_semilinear [Finite K] (hK : Nat.card K = 4) (φ : (Fin 3 → K) ≃+ (Fin 3 → K))
    (α : SpecialLinearGroup (Fin 3) K →* SpecialLinearGroup (Fin 3) K)
    (hint : ∀ (γ : SpecialLinearGroup (Fin 3) K) (v : Fin 3 → K),
      φ ((γ : Matrix (Fin 3) (Fin 3) K) *ᵥ v) = (α γ : Matrix (Fin 3) (Fin 3) K) *ᵥ φ v)
    (hinj : Function.Injective α) :
    ∃ e : ℕ, (e = 1 ∨ e = 2) ∧ ∀ (x : K) (v : Fin 3 → K), φ (x • v) = x ^ e • φ v := by
  classical
  have hsurj : Function.Surjective α := Finite.injective_iff_surjective.mp hinj
  obtain ⟨ω, hω, hω1⟩ : ∃ ω : K, ω ^ 3 = 1 ∧ ω ≠ 1 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have := Fintype.ofFinite K
    have hu : 3 ∣ Nat.card Kˣ := by
      rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 3 hu
    refine ⟨g, ?_, ?_⟩
    · have := pow_orderOf_eq_one g
      rw [hg] at this
      simpa using congrArg Units.val this
    · intro h1
      have : g = 1 := Units.ext h1
      rw [this, orderOf_one] at hg
      exact absurd hg (by norm_num)
  let z : SpecialLinearGroup (Fin 3) K :=
    ⟨Matrix.scalar (Fin 3) ω, by simp [hω]⟩
  have hz : z ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K) :=
    Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨ω, by simpa using hω, rfl⟩
  have hαz : α z ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := hsurj y
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz x)]
  obtain ⟨r, hr3, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hαz
  simp only [Fintype.card_fin] at hr3
  have hr1 : r ≠ 1 := by
    rintro rfl
    have h1 : α z = α 1 := by
      rw [map_one]
      ext i j
      rw [← hr]
      simp
    have := congrArg (fun A : SpecialLinearGroup (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 0)
      (hinj h1)
    simp [z] at this
    exact hω1 this
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hr3
  have hφω : ∀ v : Fin 3 → K, φ (ω • v) = r • φ v := by
    intro v
    have h := hint z v
    have hz' : (z : Matrix (Fin 3) (Fin 3) K) *ᵥ v = ω • v := by
      simp [z, Matrix.scalar_apply]
    rw [hz'] at h
    rw [h, ← hr]
    simp [Matrix.scalar_apply]
  have hrω : r = ω ∨ r = ω ^ 2 := by
    rcases eq_zero_or_pow hK hω hω1 r with h | h | h | h
    · exact absurd h hr0
    · exact absurd h hr1
    · exact Or.inl h
    · exact Or.inr h
  rcases hrω with hrω | hrω
  · refine ⟨1, Or.inl rfl, fun x v => ?_⟩
    rcases eq_zero_or_pow hK hω hω1 x with rfl | rfl | rfl | rfl
    · simp
    · simp
    · rw [hφω, hrω, pow_one]
    · rw [pow_two, mul_smul, hφω, hφω, hrω, pow_one, mul_smul]
  · refine ⟨2, Or.inr rfl, fun x v => ?_⟩
    rcases eq_zero_or_pow hK hω hω1 x with rfl | rfl | rfl | rfl
    · simp
    · simp
    · rw [hφω, hrω]
    · rw [pow_two ω, mul_smul, hφω, hφω, hrω, ← mul_smul, ← pow_add]
      congr 1
      ring


theorem mulVec_mulVec_SL (A B : SpecialLinearGroup (Fin 3) K) (v : Fin 3 → K) :
    (A : Matrix (Fin 3) (Fin 3) K) *ᵥ ((B : Matrix (Fin 3) (Fin 3) K) *ᵥ v) =
      ((A * B : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v := by
  rw [Matrix.mulVec_mulVec, Matrix.SpecialLinearGroup.coe_mul]

abbrev SL3 (K : Type) [Field K] : Type := SpecialLinearGroup (Fin 3) K

theorem model [Finite K] (hK : Nat.card K = 4) (φ : (Fin 3 → K) ≃+ (Fin 3 → K))
    (α : SL3 K →* SL3 K)
    (hint : ∀ (γ : SL3 K) (v : Fin 3 → K),
      φ ((γ : Matrix (Fin 3) (Fin 3) K) *ᵥ v) = (α γ : Matrix (Fin 3) (Fin 3) K) *ᵥ φ v)
    (S : Sylow 2 (SL3 K)) (hSα : ∀ s ∈ (S : Subgroup (SL3 K)), α s ∈ (S : Subgroup (SL3 K))) :
    (∀ γ ∈ Subgroup.normalizer ((S : Subgroup (SL3 K)) : Set (SL3 K)),
      α γ * γ⁻¹ ∈ (S : Subgroup (SL3 K))) ∨
    ∀ γ ∈ Subgroup.normalizer ((S : Subgroup (SL3 K)) : Set (SL3 K)),
      α γ * γ ∈ (S : Subgroup (SL3 K)) := by
  classical
  have hinj : Function.Injective α := by
    rw [injective_iff_map_eq_one]
    intro γ hγ
    have h : ∀ v, (γ : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v := by
      intro v
      apply φ.injective
      rw [hint, hγ, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
    ext i j
    have := congrFun (h (Pi.single j 1)) i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply] at this
    rw [this]
    simp [Matrix.one_apply]
  obtain ⟨e, he, hφ⟩ := exists_semilinear hK φ α hint hinj
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := 2) (by
    rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  obtain ⟨P₀, hP₀⟩ := exists_sylow_unitriangular (K := K) 2 (n := 3) (by norm_num)
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (SL3 K) P₀ S
  have hmemS : ∀ x : SL3 K, x ∈ (S : Subgroup (SL3 K)) ↔ h⁻¹ * x * h ∈ unitriangular 3 K := by
    intro x
    rw [← hh, Sylow.coe_subgroup_smul, ← hP₀, Subgroup.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have e1 : h⁻¹ * ((MulAut.conj h) • y) * h = y := by
        rw [MulAut.smul_def, MulAut.conj_apply]; group
      rw [e1]; exact hy
    · intro hx
      refine ⟨h⁻¹ * x * h, hx, ?_⟩
      rw [MulAut.smul_def, MulAut.conj_apply]; group
  let φ' : (Fin 3 → K) ≃+ (Fin 3 → K) :=
    (Matrix.SpecialLinearGroup.toLin' h).toAddEquiv.trans
      (φ.trans (Matrix.SpecialLinearGroup.toLin' h⁻¹).toAddEquiv)
  have hφ'_apply : ∀ v, φ' v = ((h⁻¹ : SL3 K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      φ ((h : Matrix (Fin 3) (Fin 3) K) *ᵥ v) := fun v => by
    show (Matrix.SpecialLinearGroup.toLin' h⁻¹) (φ ((Matrix.SpecialLinearGroup.toLin' h) v)) = _
    simp only [Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply]
  let α' : SL3 K →* SL3 K :=
    (MulAut.conj h⁻¹).toMonoidHom.comp (α.comp (MulAut.conj h).toMonoidHom)
  have hα'_apply : ∀ γ, α' γ = h⁻¹ * α (h * γ * h⁻¹) * h := fun γ => by
    simp [α', MulAut.conj_apply]
  have hint' : ∀ (γ : SL3 K) (v : Fin 3 → K),
      φ' ((γ : Matrix (Fin 3) (Fin 3) K) *ᵥ v) = (α' γ : Matrix (Fin 3) (Fin 3) K) *ᵥ φ' v := by
    intro γ v
    have e1 : (h : Matrix (Fin 3) (Fin 3) K) *ᵥ ((γ : Matrix (Fin 3) (Fin 3) K) *ᵥ v) =
        ((h * γ * h⁻¹ : SL3 K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
          ((h : Matrix (Fin 3) (Fin 3) K) *ᵥ v) := by
      rw [mulVec_mulVec_SL, mulVec_mulVec_SL, show h * γ * h⁻¹ * h = h * γ by group]
    rw [hφ'_apply, hφ'_apply, e1, hint, hα'_apply, mulVec_mulVec_SL, mulVec_mulVec_SL,
      show h⁻¹ * α (h * γ * h⁻¹) * h * h⁻¹ = h⁻¹ * α (h * γ * h⁻¹) by group]
  have hφ' : ∀ (x : K) (v : Fin 3 → K), φ' (x • v) = x ^ e • φ' v := by
    intro x v
    rw [hφ'_apply, hφ'_apply, Matrix.mulVec_smul, hφ, Matrix.mulVec_smul]
  have hinj' : Function.Injective α' := by
    intro a b hab
    rw [hα'_apply, hα'_apply] at hab
    have h1 : α (h * a * h⁻¹) = α (h * b * h⁻¹) := by
      have := congrArg (fun x => h * x * h⁻¹) hab
      simpa [mul_assoc] using this
    have h2 := hinj h1
    have := congrArg (fun x => h⁻¹ * x * h) h2
    simpa [mul_assoc] using this
  have hU' : ∀ u ∈ unitriangular 3 K, α' u ∈ unitriangular 3 K := by
    intro u hu
    rw [hα'_apply]
    have h1 : h * u * h⁻¹ ∈ (S : Subgroup (SL3 K)) := by
      rw [hmemS, show h⁻¹ * (h * u * h⁻¹) * h = u by group]; exact hu
    have h2 := (hmemS _).mp (hSα _ h1)
    exact h2
  have hUs' : ∀ u ∈ unitriangular 3 K, ∃ u' ∈ unitriangular 3 K, α' u' = u := by
    let f : ↥(unitriangular 3 K) → ↥(unitriangular 3 K) := fun x => ⟨α' x, hU' x x.2⟩
    have hf : Function.Injective f := fun x y hxy =>
      Subtype.ext (hinj' (congrArg Subtype.val hxy))
    intro u hu
    obtain ⟨x, hx⟩ := (Finite.injective_iff_surjective.mp hf) ⟨u, hu⟩
    exact ⟨x, x.2, congrArg Subtype.val hx⟩
  have hSs : ∀ s ∈ (S : Subgroup (SL3 K)), ∃ s' ∈ (S : Subgroup (SL3 K)), α s' = s := by
    let f : ↥(S : Subgroup (SL3 K)) → ↥(S : Subgroup (SL3 K)) := fun x => ⟨α x, hSα x x.2⟩
    have hf : Function.Injective f := fun x y hxy =>
      Subtype.ext (hinj (congrArg Subtype.val hxy))
    intro s hs
    obtain ⟨x, hx⟩ := (Finite.injective_iff_surjective.mp hf) ⟨s, hs⟩
    exact ⟨x, x.2, congrArg Subtype.val hx⟩
  have hnorm : ∀ γ ∈ Subgroup.normalizer ((S : Subgroup (SL3 K)) : Set (SL3 K)),
      h⁻¹ * γ * h ∈ Subgroup.normalizer ((unitriangular 3 K : Subgroup (SL3 K)) : Set (SL3 K)) := by
    intro γ hγ
    rw [Subgroup.mem_normalizer_iff]
    intro u
    have e1 : u ∈ unitriangular 3 K ↔ h * u * h⁻¹ ∈ (S : Subgroup (SL3 K)) := by
      rw [hmemS, show h⁻¹ * (h * u * h⁻¹) * h = u by group]
    have e2 : h⁻¹ * γ * h * u * (h⁻¹ * γ * h)⁻¹ ∈ unitriangular 3 K ↔
        γ * (h * u * h⁻¹) * γ⁻¹ ∈ (S : Subgroup (SL3 K)) := by
      rw [hmemS, show h⁻¹ * (γ * (h * u * h⁻¹) * γ⁻¹) * h = h⁻¹ * γ * h * u * (h⁻¹ * γ * h)⁻¹ by
        group]
    rw [e1, e2]
    exact Subgroup.mem_normalizer_iff.mp hγ _
  have hαnorm : ∀ γ ∈ Subgroup.normalizer ((S : Subgroup (SL3 K)) : Set (SL3 K)),
      α γ ∈ Subgroup.normalizer ((S : Subgroup (SL3 K)) : Set (SL3 K)) := by
    intro γ hγ
    rw [Subgroup.mem_normalizer_iff]
    intro s
    constructor
    · intro hs
      obtain ⟨s', hs', rfl⟩ := hSs s hs
      rw [← map_inv, ← map_mul, ← map_mul]
      exact hSα _ ((Subgroup.mem_normalizer_iff.mp hγ s').mp hs')
    · intro hs
      obtain ⟨t, ht, hts⟩ := hSs _ hs
      have hs' : s = α (γ⁻¹ * t * γ) := by
        rw [map_mul, map_mul, map_inv, hts]
        group
      rw [hs']
      apply hSα
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hγ) t).mp ht
      simpa using this
  have key : ∀ γ ∈ Subgroup.normalizer ((S : Subgroup (SL3 K)) : Set (SL3 K)),
      (e = 1 → α γ * γ⁻¹ ∈ (S : Subgroup (SL3 K))) ∧
        (e = 2 → α γ * γ ∈ (S : Subgroup (SL3 K))) := by
    intro γ hγ
    have h1 := hnorm γ hγ
    have h2 : α' (h⁻¹ * γ * h) ∈
        Subgroup.normalizer ((unitriangular 3 K : Subgroup (SL3 K)) : Set (SL3 K)) := by
      rw [hα'_apply, show h * (h⁻¹ * γ * h) * h⁻¹ = γ by group]
      exact hnorm _ (hαnorm γ hγ)
    have hd := diag_twist φ' hφ' α' hint' hUs' h1 h2
    obtain ⟨k1, k2⟩ := mem_unitriangular_of_diag hK (isUpperTriangular_of_mem_normalizer h1)
      (isUpperTriangular_of_mem_normalizer h2) hd
    rw [hα'_apply, show h * (h⁻¹ * γ * h) * h⁻¹ = γ by group] at k1 k2
    refine ⟨fun he1 => (hmemS _).mpr ?_, fun he2 => (hmemS _).mpr ?_⟩
    · have := k1 he1
      rwa [show h⁻¹ * α γ * h * (h⁻¹ * γ * h)⁻¹ = h⁻¹ * (α γ * γ⁻¹) * h by group] at this
    · have := k2 he2
      rwa [show h⁻¹ * α γ * h * (h⁻¹ * γ * h) = h⁻¹ * (α γ * γ) * h by group] at this
  rcases he with he | he
  · exact Or.inl fun γ hγ => (key γ hγ).1 he
  · exact Or.inr fun γ hγ => (key γ hγ).2 he


open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique in
theorem semi_of_binaryNaturalSL {W : Type} [CommGroup W] [Finite W]
    {Q : Subgroup (MulAut W)} {V Z : Subgroup W} (hnat : BinaryNaturalSL Q V Z 3 2)
    {U : Subgroup (MulAut W)} (hU : IsSylowTwoOf U Q) {g : MulAut W}
    (hgQ : ∀ x ∈ Q, g * x * g⁻¹ ∈ Q) (hgU : ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hgV : ∀ v ∈ V, g v ∈ V) (hgZ : ∀ z ∈ Z, g z ∈ Z) :
    (∀ b ∈ Q ⊓ Subgroup.normalizer (U : Set (MulAut W)), g * b * g⁻¹ * b⁻¹ ∈ U) ∨
      ∀ b ∈ Q ⊓ Subgroup.normalizer (U : Set (MulAut W)), g * b * g⁻¹ * b ∈ U := by
  classical
  obtain ⟨K, hKf, hKfin, hK, π, hπ⟩ := hnat
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  obtain ⟨ε, hε⟩ := exists_sec_equiv_nat (StatedSL 3 K) hπ
  obtain ⟨hπs, hZV, -, hQV, hQZ, -, -, -⟩ := hπ
  have hπi : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro γ hγ
    have h1 : ((π γ : ↥Q) : MulAut W) = 1 := by rw [hγ]; rfl
    apply natAct_injective (StatedSL 3 K)
    intro a
    obtain ⟨s, rfl⟩ := ε.surjective a
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective s
    have hu : ((π γ : ↥Q) : MulAut W) (u : W) ∈ V := hQV (π γ) u u.2
    rw [← hε γ u hu]
    have : (QuotientGroup.mk ⟨((π γ : ↥Q) : MulAut W) (u : W), hu⟩ : ↥V ⧸ Z.subgroupOf V) =
        QuotientGroup.mk u := by
      congr 1
      apply Subtype.ext
      show ((π γ : ↥Q) : MulAut W) (u : W) = u
      rw [h1]
      rfl
    refine (congrArg ε this).trans ?_
    show _ = Multiplicative.ofAdd (((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      Multiplicative.toAdd (ε (QuotientGroup.mk u)))
    simp
  have hgZ' : ∀ x : W, g x ∈ Z → x ∈ Z := by
    intro x hx
    let f : ↥Z → ↥Z := fun z => ⟨g z, hgZ z z.2⟩
    have hf : Function.Injective f := fun a b h =>
      Subtype.ext (g.injective (congrArg Subtype.val h))
    obtain ⟨z, hz⟩ := (Finite.injective_iff_surjective.mp hf) ⟨g x, hx⟩
    have : (z : W) = x := g.injective (congrArg Subtype.val hz)
    rw [← this]; exact z.2
  let gV : ↥V →* ↥V :=
    { toFun := fun x => ⟨g x, hgV x x.2⟩
      map_one' := Subtype.ext (map_one g)
      map_mul' := fun x y => Subtype.ext (map_mul g (x : W) (y : W)) }
  let F : (↥V ⧸ Z.subgroupOf V) →* (↥V ⧸ Z.subgroupOf V) :=
    QuotientGroup.map (Z.subgroupOf V) (Z.subgroupOf V) gV (fun x hx => by
      rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
      exact hgZ x (Subgroup.mem_subgroupOf.mp hx))
  have hFmk : ∀ u : ↥V, F (QuotientGroup.mk u) = QuotientGroup.mk (gV u) := fun u => rfl
  have hFi : Function.Injective F := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
    rw [hFmk, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hx
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hgZ' _ hx
  let Fe : (↥V ⧸ Z.subgroupOf V) ≃* (↥V ⧸ Z.subgroupOf V) :=
    MulEquiv.ofBijective F ⟨hFi, Finite.injective_iff_surjective.mp hFi⟩
  let φ₀ : Multiplicative (Fin 3 → K) ≃* Multiplicative (Fin 3 → K) := ε.symm.trans (Fe.trans ε)
  let φ : (Fin 3 → K) ≃+ (Fin 3 → K) := AddEquiv.toMultiplicative.symm φ₀
  have hφ : ∀ v, φ v = Multiplicative.toAdd (φ₀ (Multiplicative.ofAdd v)) := fun v => rfl
  let πe : ↥(StatedSL 3 K) ≃* ↥Q := MulEquiv.ofBijective π ⟨hπi, hπs⟩
  let Ψ : SL3 K ≃* ↥Q := (specialLinearGroupEquivStatedSL 3 K).trans πe
  let cg : ↥Q →* ↥Q :=
    { toFun := fun x => ⟨g * x * g⁻¹, hgQ x x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  let α : SL3 K →* SL3 K := Ψ.symm.toMonoidHom.comp (cg.comp Ψ.toMonoidHom)
  have hαΨ : ∀ γ, ((Ψ (α γ) : ↥Q) : MulAut W) = g * (Ψ γ : MulAut W) * g⁻¹ := fun γ => by
    simp [α, cg]
  have hΨ : ∀ γ : SL3 K, Ψ γ = π (specialLinearGroupEquivStatedSL 3 K γ) := fun γ => rfl
  have hnat' : ∀ (γ : SL3 K) (a : Multiplicative (Fin 3 → K)),
      natAct (StatedSL 3 K) (specialLinearGroupEquivStatedSL 3 K γ) a =
        Multiplicative.ofAdd ((γ : Matrix (Fin 3) (Fin 3) K) *ᵥ Multiplicative.toAdd a) :=
    fun γ a => rfl
  have hφ₀ : ∀ x : ↥V, φ₀ (ε (QuotientGroup.mk x)) = ε (QuotientGroup.mk (gV x)) := by
    intro x
    show ε (Fe (ε.symm (ε (QuotientGroup.mk x)))) = _
    rw [MulEquiv.symm_apply_apply]
    rfl
  have hint : ∀ (γ : SL3 K) (v : Fin 3 → K),
      φ ((γ : Matrix (Fin 3) (Fin 3) K) *ᵥ v) = (α γ : Matrix (Fin 3) (Fin 3) K) *ᵥ φ v := by
    intro γ v
    obtain ⟨s, hs⟩ := ε.surjective (Multiplicative.ofAdd v)
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective s
    let E := specialLinearGroupEquivStatedSL 3 K
    have hu : ((π (E γ) : ↥Q) : MulAut W) (u : W) ∈ V := hQV _ u u.2
    have hgu : g (u : W) ∈ V := hgV u u.2
    have hgu' : ((π (E (α γ)) : ↥Q) : MulAut W) (g (u : W)) ∈ V := hQV _ _ hgu
    have e1 : Multiplicative.ofAdd ((γ : Matrix (Fin 3) (Fin 3) K) *ᵥ v) =
        ε (QuotientGroup.mk ⟨((π (E γ) : ↥Q) : MulAut W) (u : W), hu⟩) :=
      ((hε (E γ) u hu).trans (by rw [hs]; rfl)).symm
    have e3 : gV ⟨((π (E γ) : ↥Q) : MulAut W) (u : W), hu⟩ =
        ⟨((π (E (α γ)) : ↥Q) : MulAut W) (g (u : W)), hgu'⟩ := by
      apply Subtype.ext
      show g (((π (E γ) : ↥Q) : MulAut W) (u : W)) = ((π (E (α γ)) : ↥Q) : MulAut W) (g (u : W))
      have h := hαΨ γ
      change ((π (E (α γ)) : ↥Q) : MulAut W) = g * ((π (E γ) : ↥Q) : MulAut W) * g⁻¹ at h
      rw [h]
      simp [MulAut.mul_apply]
    calc φ ((γ : Matrix (Fin 3) (Fin 3) K) *ᵥ v)
        = Multiplicative.toAdd (φ₀ (Multiplicative.ofAdd ((γ : Matrix (Fin 3) (Fin 3) K) *ᵥ v))) :=
          rfl
      _ = Multiplicative.toAdd (φ₀ (ε (QuotientGroup.mk
            ⟨((π (E γ) : ↥Q) : MulAut W) (u : W), hu⟩))) := by rw [e1]
      _ = Multiplicative.toAdd (ε (QuotientGroup.mk
            (gV ⟨((π (E γ) : ↥Q) : MulAut W) (u : W), hu⟩))) := by rw [hφ₀]
      _ = Multiplicative.toAdd (ε (QuotientGroup.mk
            ⟨((π (E (α γ)) : ↥Q) : MulAut W) (g (u : W)), hgu'⟩)) := by rw [e3]
      _ = Multiplicative.toAdd (natAct (StatedSL 3 K) (E (α γ))
            (ε (QuotientGroup.mk ⟨g (u : W), hgu⟩))) :=
          congrArg _ (hε (E (α γ)) ⟨g (u : W), hgu⟩ hgu')
      _ = (α γ : Matrix (Fin 3) (Fin 3) K) *ᵥ
            Multiplicative.toAdd (ε (QuotientGroup.mk (gV u))) := rfl
      _ = (α γ : Matrix (Fin 3) (Fin 3) K) *ᵥ
            Multiplicative.toAdd (φ₀ (ε (QuotientGroup.mk u))) := by rw [hφ₀]
      _ = (α γ : Matrix (Fin 3) (Fin 3) K) *ᵥ φ v := by rw [hs]; rfl
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Ut : Subgroup (SL3 K) := (U.subgroupOf Q).comap Ψ.toMonoidHom
  have hUt : ∀ s : SL3 K, s ∈ Ut ↔ ((Ψ s : ↥Q) : MulAut W) ∈ U := fun s => by
    simp [Ut, Subgroup.mem_subgroupOf]
  have hUtp : IsPGroup 2 Ut := by
    intro s
    obtain ⟨k, hk⟩ := hU.2.1 ⟨Ψ s, (hUt s).mp s.2⟩
    refine ⟨k, Subtype.ext (Ψ.injective (Subtype.ext ?_))⟩
    have := congrArg Subtype.val hk
    simpa using this
  have hUti : Ut.index = (U.subgroupOf Q).index :=
    Subgroup.index_comap_of_surjective _ Ψ.surjective
  let S : Sylow 2 (SL3 K) := hUtp.toSylow (by rw [hUti]; exact hU.2.2)
  have hSα : ∀ s ∈ (S : Subgroup (SL3 K)), α s ∈ (S : Subgroup (SL3 K)) := by
    intro s hs
    show α s ∈ Ut
    rw [hUt, hαΨ]
    exact hgU _ ((hUt s).mp hs)
  have hmod := model hK4 φ α hint S hSα
  have hγ : ∀ b (hb : b ∈ Q ⊓ Subgroup.normalizer (U : Set (MulAut W))),
      ((Ψ (Ψ.symm ⟨b, hb.1⟩) : ↥Q) : MulAut W) = b := fun b hb => by simp
  have hN : ∀ b (hb : b ∈ Q ⊓ Subgroup.normalizer (U : Set (MulAut W))),
      Ψ.symm ⟨b, hb.1⟩ ∈ Subgroup.normalizer ((S : Subgroup (SL3 K)) : Set (SL3 K)) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro s
    show s ∈ Ut ↔ _ ∈ Ut
    rw [hUt, hUt, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, hγ b hb]
    exact Subgroup.mem_normalizer_iff.mp hb.2 _
  rcases hmod with h | h
  · left
    intro b hb
    have := (hUt _).mp (h _ (hN b hb))
    rwa [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hαΨ, hγ b hb] at this
  · right
    intro b hb
    have := (hUt _).mp (h _ (hN b hb))
    rwa [map_mul, Subgroup.coe_mul, hαΨ, hγ b hb] at this


end CFSG.Quasithin.H13.A6.A6Semi
