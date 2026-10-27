module

public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.RankThree.PartOne

open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open scoped MatrixGroups

namespace PSL2EvenBorel

open Matrix

variable {F : Type} [Field F]

def uni (a : F) : SL(2, F) :=
  ⟨!![1, a; 0, 1], by simp [det_fin_two_of]⟩

def dia (t : Fˣ) : SL(2, F) :=
  ⟨!![(t : F), 0; 0, ((t⁻¹ : Fˣ) : F)], by simp [det_fin_two_of]⟩

theorem uni_zero : uni (0 : F) = 1 := by
  apply Subtype.ext
  show !![1, (0 : F); 0, 1] = 1
  rw [one_fin_two]

theorem uni_mul (a b : F) : uni a * uni b = uni (a + b) := by
  apply Subtype.ext
  show !![1, a; 0, 1] * !![1, b; 0, 1] = !![1, a + b; 0, 1]
  rw [mul_fin_two]
  simp [add_comm]

theorem dia_one : dia (1 : Fˣ) = (1 : SL(2, F)) := by
  apply Subtype.ext
  show !![((1 : Fˣ) : F), 0; 0, (((1 : Fˣ)⁻¹ : Fˣ) : F)] = 1
  rw [one_fin_two]
  simp

theorem dia_mul (s t : Fˣ) : dia s * dia t = (dia (s * t) : SL(2, F)) := by
  apply Subtype.ext
  show !![(s : F), 0; 0, ((s⁻¹ : Fˣ) : F)] * !![(t : F), 0; 0, ((t⁻¹ : Fˣ) : F)] =
    !![((s * t : Fˣ) : F), 0; 0, (((s * t)⁻¹ : Fˣ) : F)]
  rw [mul_fin_two]
  simp [mul_comm]

theorem dia_mul_uni (t : Fˣ) (a : F) : dia t * uni a = uni ((t : F) ^ 2 * a) * dia t := by
  apply Subtype.ext
  show !![(t : F), 0; 0, ((t⁻¹ : Fˣ) : F)] * !![1, a; 0, 1] =
    !![1, (t : F) ^ 2 * a; 0, 1] * !![(t : F), 0; 0, ((t⁻¹ : Fˣ) : F)]
  rw [mul_fin_two, mul_fin_two]
  have ht : (t : F) ≠ 0 := t.ne_zero
  simp
  field_simp

def uniHom : Multiplicative F →* SL(2, F) where
  toFun a := uni (Multiplicative.toAdd a)
  map_one' := uni_zero
  map_mul' _ _ := (uni_mul _ _).symm

def diaHom : Fˣ →* SL(2, F) where
  toFun := dia
  map_one' := dia_one
  map_mul' s t := (dia_mul s t).symm

theorem diaHom_conj_uni (t : Fˣ) (a : F) :
    diaHom t * uni a * (diaHom t)⁻¹ = uni ((t : F) ^ 2 * a) := by
  rw [mul_inv_eq_iff_eq_mul]
  exact dia_mul_uni t a

theorem uni_mul_self (h2 : (2 : F) = 0) (a : F) : uni a * uni a = 1 := by
  rw [uni_mul, ← two_mul, h2, zero_mul, uni_zero]

theorem sq_eq_one_of_dia_mem_center {t : Fˣ} (h : dia t ∈ Subgroup.center SL(2, F)) :
    t ^ 2 = 1 := by
  obtain ⟨c, -, hc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h
  have h0 := congrFun (congrFun hc 0) 0
  have h1 := congrFun (congrFun hc 1) 1
  simp [dia, scalar_apply] at h0 h1
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one, pow_two]
  have h3 : (t : F) = (t : F)⁻¹ := h0.symm.trans h1
  calc (t : F) * t = t * (t : F)⁻¹ := by rw [← h3]
    _ = 1 := mul_inv_cancel₀ t.ne_zero

theorem uni_not_mem_center {a : F} (ha : a ≠ 0) : uni a ∉ Subgroup.center SL(2, F) := by
  intro h
  obtain ⟨c, -, hc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h
  have h0 := congrFun (congrFun hc 0) 1
  simp [uni, scalar_apply] at h0
  exact ha h0.symm

theorem conj_map {K : Type} [Group K] (φ : SL(2, F) →* K) (s : Fˣ) (a : F) :
    φ (diaHom s) * φ (uni a) * (φ (diaHom s))⁻¹ = φ (uni ((s : F) ^ 2 * a)) := by
  rw [← map_inv, ← map_mul, ← map_mul, diaHom_conj_uni]

theorem exists_two_subgroup_of_hom {K : Type} [Group K] [Finite F] (h2 : (2 : F) = 0)
    (φ : SL(2, F) →* K) (hφ : ∀ g, φ g = 1 → g ∈ Subgroup.center SL(2, F)) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hrF : r ∣ Nat.card F - 1) :
    ∃ U : Subgroup K, U ≠ ⊥ ∧ IsPGroup 2 U ∧
      ∃ x ∈ Subgroup.normalizer (U : Set K), orderOf x = r ∧ ∃ u ∈ U, x * u * x⁻¹ ≠ u := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) r (by rw [Nat.card_units]; exact hrF)
  let v : Multiplicative F →* K := φ.comp uniHom
  have hrange : ∀ g, g ∈ v.range ↔ ∃ a : F, φ (uni a) = g := by
    intro g
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨Multiplicative.toAdd a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨Multiplicative.ofAdd a, rfl⟩
  refine ⟨v.range, ?_, ?_, φ (diaHom t), ?_, ?_⟩
  · intro hbot
    have hmem : φ (uni 1) ∈ v.range := (hrange _).mpr ⟨1, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact uni_not_mem_center one_ne_zero (hφ _ hmem)
  · rintro ⟨g, hg⟩
    obtain ⟨a, rfl⟩ := (hrange g).mp hg
    refine ⟨1, Subtype.ext ?_⟩
    change (φ (uni a)) ^ 2 ^ 1 = 1
    rw [pow_one, pow_two, ← map_mul, uni_mul_self h2, map_one]
  · rw [Subgroup.mem_normalizer_iff]
    intro g
    rw [hrange, hrange]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨(t : F) ^ 2 * a, (conj_map φ t a).symm⟩
    · rintro ⟨b, hb⟩
      refine ⟨((t⁻¹ : Fˣ) : F) ^ 2 * b, ?_⟩
      have hx : φ (diaHom t⁻¹) = (φ (diaHom t))⁻¹ := by rw [map_inv, map_inv]
      rw [← conj_map φ t⁻¹ b, hb, hx]
      group
  · have hpow : φ (diaHom t) ^ r = 1 := by
      rw [← map_pow, ← map_pow, ← ht, pow_orderOf_eq_one, map_one, map_one]
    have hsq : t ^ 2 = 1 → False := fun hsq => by
      have h22 : r ∣ 2 := ht ▸ orderOf_dvd_of_pow_eq_one hsq
      exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h22)
    refine ⟨orderOf_eq_prime hpow fun hone => ?_, ?_⟩
    · exact hsq (sq_eq_one_of_dia_mem_center (hφ _ hone))
    · refine ⟨φ (uni 1), (hrange _).mpr ⟨1, rfl⟩, fun hc => ?_⟩
      rw [conj_map φ t 1, mul_one] at hc
      have hmem : uni ((t : F) ^ 2 + 1) ∈ Subgroup.center SL(2, F) := by
        apply hφ
        calc φ (uni ((t : F) ^ 2 + 1)) = φ (uni ((t : F) ^ 2) * uni 1) := by rw [uni_mul]
          _ = φ (uni ((t : F) ^ 2)) * φ (uni 1) := map_mul φ _ _
          _ = φ (uni 1) * φ (uni 1) := by rw [hc]
          _ = 1 := by rw [← map_mul, uni_mul_self h2, map_one]
      have hne : (t : F) ^ 2 + 1 = 0 := by
        by_contra hne
        exact uni_not_mem_center hne hmem
      apply hsq
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      linear_combination hne - h2

end PSL2EvenBorel

theorem exists_two_subgroup_normalized_by_odd_prime {K : Type} [Group K] {f : ℕ}
    (hK : StatedClassicalModel K .PSL 2 2 f) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrf : r ∣ 2 ^ f - 1) :
    ∃ U : Subgroup K, U ≠ ⊥ ∧ IsPGroup 2 U ∧
      ∃ x ∈ Subgroup.normalizer (U : Set K), orderOf x = r ∧ ∃ u ∈ U, x * u * x⁻¹ ≠ u := by
  obtain ⟨⟨-, hf, -⟩, F, _, _, hcard, ⟨e⟩⟩ := hK
  have h2 : (2 : F) = 0 := by
    have := Fintype.ofFinite F
    have h := FiniteField.cast_card_eq_zero F
    rw [← Nat.card_eq_fintype_card, hcard, Nat.cast_pow, Nat.cast_ofNat] at h
    exact (pow_eq_zero_iff (by omega)).mp h
  let ε : PSL(2, F) ≃* K :=
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).trans e.symm
  let φ : SL(2, F) →* K := ε.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center SL(2, F)))
  have hφ : ∀ g, φ g = 1 → g ∈ Subgroup.center SL(2, F) := fun g hg =>
    (QuotientGroup.eq_one_iff g).mp (ε.injective (hg.trans (map_one ε).symm))
  exact PSL2EvenBorel.exists_two_subgroup_of_hom h2 φ hφ hr hr2 (by rw [hcard]; exact hrf)

end CFSG.RankThree.PartOne
