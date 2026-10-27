module

public import CFSG.Quasithin.EmptyFaithful.S1565L5
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherSylow

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial Matrix

variable {V : Type} [CommGroup V] {F : Type} [Field F]

section SL3

private noncomputable def diagSL3 (ω : Fˣ) : SpecialLinearGroup (Fin 3) F :=
  ⟨Matrix.diagonal ![(ω : F), (ω : F), ((ω⁻¹ * ω⁻¹ : Fˣ) : F)], by
    have h : (ω : F) ≠ 0 := ω.ne_zero
    simp [Matrix.det_diagonal, Fin.prod_univ_three]
    field_simp⟩

private theorem coe_diagSL3 (ω : Fˣ) :
    (diagSL3 ω : Matrix (Fin 3) (Fin 3) F) =
      Matrix.diagonal ![(ω : F), (ω : F), ((ω⁻¹ * ω⁻¹ : Fˣ) : F)] := rfl

private theorem diagSL3_mem_upperTriangular (ω : Fˣ) :
    diagSL3 ω ∈ LinearFlag.upperTriangular 3 F := by
  rw [LinearFlag.mem_upperTriangular]
  intro i j hji
  rw [coe_diagSL3, Matrix.diagonal_apply_ne _ (ne_of_gt hji)]

private theorem diagSL3_pow (ω : Fˣ) (r : ℕ) (hω : ω ^ r = 1) : (diagSL3 ω) ^ r = 1 := by
  have h3 : ((ω : F)) ^ r = 1 := by
    rw [← Units.val_pow_eq_pow_val, hω, Units.val_one]
  have h4 : (((ω⁻¹ * ω⁻¹ : Fˣ) : F)) ^ r = 1 := by
    rw [← Units.val_pow_eq_pow_val, mul_pow, inv_pow, hω, inv_one, mul_one, Units.val_one]
  have key : ((diagSL3 ω ^ r : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((1 : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    rw [Matrix.SpecialLinearGroup.coe_pow, coe_diagSL3, Matrix.diagonal_pow,
      Matrix.SpecialLinearGroup.coe_one, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i
    · simp [h3]
    · simp [h3]
    · simpa using h4
  exact Subtype.ext key

theorem natural_sl3_borel_element [Finite F] [CharP F 2] (ω : Fˣ) (hω1 : ω ≠ 1) (hω2 : ω ^ 2 ≠ 1)
    (r : ℕ) (hr : ω ^ r = 1) {H : Subgroup (MulAut V)} {U Z : Subgroup V}
    {π : ↥(StatedSL 3 F) →* ↥H} (hR : (FFModel.nat (StatedSL 3 F)).RealizesVia H U Z π)
    (S : Sylow 2 H) :
    ∃ b ∈ Subgroup.normalizer ((S : Subgroup ↥H) : Set ↥H), b ^ r = 1 ∧
      ∀ u ∈ U, ((b : MulAut V) u) * u⁻¹ ∈ Z → u ∈ Z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q0, hQ0⟩ := LinearFlag.exists_sylow_unitriangular (K := F) 2 (n := 3) (by norm_num)
  have hN : diagSL3 ω ∈ Subgroup.normalizer ((Q0 : Subgroup (SpecialLinearGroup (Fin 3) F)) :
      Set (SpecialLinearGroup (Fin 3) F)) := by
    rw [hQ0, LinearFlag.normalizer_unitriangular]
    exact diagSL3_mem_upperTriangular ω
  obtain ⟨Q1, hQ1⟩ := exists_sylow_normalizer_of_mulEquiv (specialLinearGroupEquivStatedSL 3 F) Q0 _ hN
  set g₀ : ↥(StatedSL 3 F) := specialLinearGroupEquivStatedSL 3 F (diagSL3 ω) with hg₀
  have hω0 : (ω : F) ≠ 1 := fun h => hω1 (Units.ext h)
  have hω20 : ((ω⁻¹ * ω⁻¹ : Fˣ) : F) ≠ 1 := by
    intro h
    apply hω2
    have h' : ω⁻¹ * ω⁻¹ = 1 := Units.ext h
    have : (ω * ω)⁻¹ = 1 := by rw [_root_.mul_inv_rev]; exact h'
    rw [inv_eq_one] at this
    rw [pow_two]; exact this
  have hfix : ∀ m : Fin 3 → F,
      ((g₀ : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec m = m →
        m = 0 := by
    intro m hm
    have hc : ((g₀ : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        Matrix.diagonal ![(ω : F), (ω : F), ((ω⁻¹ * ω⁻¹ : Fˣ) : F)] := rfl
    rw [hc] at hm
    have h0 := congrFun hm 0
    have h1 := congrFun hm 1
    have h2 := congrFun hm 2
    simp only [Matrix.mulVec_diagonal] at h0 h1 h2
    funext i
    fin_cases i
    · by_contra hne
      exact hω0 (mul_right_cancel₀ hne (h0.trans (one_mul _).symm))
    · by_contra hne
      exact hω0 (mul_right_cancel₀ hne (h1.trans (one_mul _).symm))
    · by_contra hne
      exact hω20 (mul_right_cancel₀ hne (h2.trans (one_mul _).symm))
  obtain ⟨b, hbN, hbo, hb⟩ := natural_borel_element (StatedSL 3 F) Q1 g₀ hQ1 hfix hR S
  refine ⟨b, hbN, ?_, hb⟩
  have hg₀r : g₀ ^ r = 1 := by
    rw [hg₀, ← map_pow, diagSL3_pow ω r hr, map_one]
  exact orderOf_dvd_iff_pow_eq_one.mp (hbo.trans (orderOf_dvd_of_pow_eq_one hg₀r))

end SL3

section Sp4

private theorem torusHom_pow_r (ω : Fˣ) (r : ℕ) (hω : ω ^ r = 1) :
    (SymplecticTorusWeyl.torusHom (r := 2) (k := F) ![ω, ω]) ^ r = 1 := by
  rw [← map_pow]
  have : (![ω, ω] : Fin 2 → Fˣ) ^ r = 1 := by
    funext i
    fin_cases i <;> simp [hω]
  rw [this, map_one]

theorem natural_sp4_borel_element [Finite F] [CharP F 2] (ω : Fˣ) (hω1 : ω ≠ 1) (r : ℕ)
    (hr : ω ^ r = 1) {H : Subgroup (MulAut V)} {U Z : Subgroup V}
    {π : ↥(StatedSp 2 F) →* ↥H} (hR : (FFModel.nat (StatedSp 2 F)).RealizesVia H U Z π)
    (S : Sylow 2 H) :
    ∃ b ∈ Subgroup.normalizer ((S : Subgroup ↥H) : Set ↥H), b ^ r = 1 ∧
      ∀ u ∈ U, ((b : MulAut V) u) * u⁻¹ ∈ Z → u ∈ Z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q0, hQ0⟩ := SymplecticFlag.exists_sylow_unipotent (K := F) 2 2
  set g₀ : ↥(StatedSp 2 F) := SymplecticTorusWeyl.torusHom ![ω, ω] with hg₀
  have hN : g₀ ∈ Subgroup.normalizer ((Q0 : Subgroup ↥(StatedSp 2 F)) :
      Set ↥(StatedSp 2 F)) := by
    rw [hQ0, SymplecticHigher.normalizer_unipotent]
    exact SymplecticFlag.torus_le_borelSubgroup (SymplecticTorusWeyl.torusHom_mem_torus _)
  have hω0 : (ω : F) ≠ 1 := fun h => hω1 (Units.ext h)
  have hωi : ((ω⁻¹ : Fˣ) : F) ≠ 1 := by
    intro h
    apply hω1
    have : ω⁻¹ = 1 := Units.ext h
    simpa using this
  have hfix : ∀ m : Fin 2 ⊕ Fin 2 → F,
      ((g₀ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).mulVec m = m → m = 0 := by
    intro m hm
    have hv : ∀ i : Fin 2, (![ω, ω] : Fin 2 → Fˣ) i = ω := fun i => by fin_cases i <;> rfl
    rw [hg₀, SymplecticTorusWeyl.coe_torusHom] at hm
    funext i
    have hi := congrFun hm i
    rw [Matrix.mulVec_diagonal] at hi
    rcases i with i | i
    · simp [hv] at hi
      by_contra hne
      exact hω0 (mul_right_cancel₀ hne (hi.trans (one_mul _).symm))
    · simp [hv] at hi
      by_contra hne
      apply hωi
      have := mul_right_cancel₀ hne (hi.trans (one_mul _).symm)
      simpa using this
  obtain ⟨b, hbN, hbo, hb⟩ := natural_borel_element (StatedSp 2 F) Q0 g₀ hN hfix hR S
  refine ⟨b, hbN, ?_, hb⟩
  exact orderOf_dvd_iff_pow_eq_one.mp (hbo.trans (orderOf_dvd_of_pow_eq_one
    (torusHom_pow_r ω r hr)))

end Sp4

end CFSG.Quasithin
