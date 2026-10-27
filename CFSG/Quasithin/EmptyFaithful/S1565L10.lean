module

public import CFSG.Quasithin.EmptyFaithful.S1565L5
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSylow

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial Matrix
open CFSG.ClassicalGroups.UnitaryFlag

variable {V : Type} [CommGroup V] {F : Type} [Field F]

section SU3

private theorem su3_torus_conditions {a : ℕ} (h : UnitaryFieldData 2 a F) (ω : Fˣ) :
    ∃ d : Fˣ, h.norm (d : F) = 1 ∧ (ω : F) / h.bar ω * d = 1 ∧ (d : F) = h.bar ω / ω := by
  have hb : h.bar (ω : F) ≠ 0 := by
    intro h0
    have := (map_eq_zero h.bar).mp h0
    exact ω.ne_zero this
  refine ⟨Units.mk0 (h.bar ω / ω) (div_ne_zero hb ω.ne_zero), ?_, ?_, rfl⟩
  · simp only [UnitaryFieldData.norm, Units.val_mk0, map_div₀, h.bar_bar]
    field_simp
  · simp only [Units.val_mk0]
    field_simp

theorem natural_su3_borel_element [Finite F] {a : ℕ} (ha : 1 ≤ a) (hK : Nat.card F = (2 ^ a) ^ 2)
    (ω : Fˣ) (hω1 : ω ≠ 1) (hωb : (ω : F) ^ 2 ^ a ≠ ω) (r : ℕ) (hr : ω ^ r = 1)
    {H : Subgroup (MulAut V)} {U Z : Subgroup V} {π : ↥(StatedSU 3 (2 ^ a) F) →* ↥H}
    (hR : (FFModel.nat (StatedSU 3 (2 ^ a) F)).RealizesVia H U Z π) (S : Sylow 2 H) :
    ∃ b ∈ Subgroup.normalizer ((S : Subgroup ↥H) : Set ↥H), b ^ r = 1 ∧
      ∀ u ∈ U, ((b : MulAut V) u) * u⁻¹ ∈ Z → u ∈ Z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : UnitaryFieldData 2 a F := ⟨Nat.prime_two, ha, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨R, hRt⟩ := exists_isHypTransport h (r := 1) (ε := 1)
  obtain ⟨-, ⟨P, hP⟩, -⟩ := unitary_order_and_Sylow h (r := 1) (ε := 1) le_rfl le_rfl
  obtain ⟨d, hdn, hdp, hdval⟩ := su3_torus_conditions h ω
  let a' : Fin 1 → Fˣ := fun _ => ω
  let d' : Fin 1 → Fˣ := fun _ => d
  have hd : ∀ k, h.norm (d' k : F) = 1 := fun _ => hdn
  have hp : torusRatio h a' d' = 1 := by simpa [torusRatio, a', d'] using hdp
  obtain ⟨g, hgT, hg⟩ := torusMat_mem_hypSU h a' hd hp
  have hgN : g ∈ Subgroup.normalizer ((P : Subgroup (hypSU h 1 1)) : Set (hypSU h 1 1)) := by
    rw [hP, UnitaryHigher.normalizer_hypUnitriangular h le_rfl le_rfl]
    exact hypTorus_le_hypBorel h hgT
  obtain ⟨Q1, hQ1⟩ := exists_sylow_normalizer_of_mulEquiv (hypTransport h hRt) P g hgN
  set g₀ := hypTransport h hRt g with hg₀
  have hbar0 : h.bar (ω : F) ≠ 1 := by
    intro h1
    apply hω1
    apply Units.ext
    have := h.bar.injective (h1.trans h.bar.map_one.symm)
    simpa using this
  have hd1 : (d : F) ≠ 1 := by
    rw [hdval]
    intro h1
    apply hωb
    have h2 := (div_eq_one_iff_eq ω.ne_zero).mp h1
    rw [h.bar_apply] at h2
    exact h2
  have hω0 : (ω : F) ≠ 1 := fun h1 => hω1 (Units.ext h1)
  have hfix : ∀ m : Fin 3 → F,
      ((g₀ : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec m = m →
        m = 0 := by
    intro m hm
    have hc : ((g₀ : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        R * (((g : hypSU h 1 1) : GL (HypIndex 1 1) F) : Matrix (HypIndex 1 1) (HypIndex 1 1) F) *
          transportInv h R := rfl
    rw [hc, hg] at hm
    have hx : (diagonal (torusEntries h a' d')).mulVec ((transportInv h R).mulVec m) =
        (transportInv h R).mulVec m := by
      have h1 := congrArg (fun y => (transportInv h R).mulVec y) hm
      simp only [Matrix.mulVec_mulVec] at h1
      have e : transportInv h R * (R * diagonal (torusEntries h a' d') * transportInv h R) =
          diagonal (torusEntries h a' d') * transportInv h R := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, transportInv_mul hRt, Matrix.one_mul]
      rw [e] at h1
      rw [Matrix.mulVec_mulVec]
      exact h1
    have hx0 : (transportInv h R).mulVec m = 0 := by
      funext i
      have hi := congrFun hx i
      rw [Matrix.mulVec_diagonal] at hi
      rcases i with i | i | i
      · simp [torusEntries, a'] at hi
        by_contra hne
        exact hω0 (mul_right_cancel₀ hne (hi.trans (one_mul _).symm))
      · simp [torusEntries, d'] at hi
        by_contra hne
        exact hd1 (mul_right_cancel₀ hne (hi.trans (one_mul _).symm))
      · simp [torusEntries, a'] at hi
        by_contra hne
        apply hbar0
        have := mul_right_cancel₀ hne (hi.trans (one_mul _).symm)
        simpa using this
    have : m = R.mulVec ((transportInv h R).mulVec m) := by
      rw [Matrix.mulVec_mulVec, mul_transportInv hRt, Matrix.one_mulVec]
    rw [this, hx0, Matrix.mulVec_zero]
  obtain ⟨b, hbN, hbo, hb⟩ := natural_borel_element (StatedSU 3 (2 ^ a) F) Q1 g₀ hQ1 hfix hR S
  refine ⟨b, hbN, ?_, hb⟩
  have hωr : (ω : F) ^ r = 1 := by rw [← Units.val_pow_eq_pow_val, hr, Units.val_one]
  have hbarr : (h.bar (ω : F)) ^ r = 1 := by rw [← map_pow, hωr, map_one]
  have hdr : (d : F) ^ r = 1 := by rw [hdval, div_pow, hbarr, hωr, div_one]
  have hgr : g ^ r = 1 := by
    have hm : (((g ^ r : hypSU h 1 1) : GL (HypIndex 1 1) F) :
        Matrix (HypIndex 1 1) (HypIndex 1 1) F) = 1 := by
      rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hg, Matrix.diagonal_pow,
        ← Matrix.diagonal_one]
      congr 1
      funext x
      rcases x with i | k | i
      · simp [torusEntries, a', hωr]
      · simp [torusEntries, d', hdr]
      · simp [torusEntries, a', hbarr]
    exact Subtype.ext (Units.ext (by simpa using hm))
  have hg₀r : g₀ ^ r = 1 := by
    rw [hg₀, ← map_pow, hgr, map_one]
  exact orderOf_dvd_iff_pow_eq_one.mp (hbo.trans (orderOf_dvd_of_pow_eq_one hg₀r))

end SU3

end CFSG.Quasithin
