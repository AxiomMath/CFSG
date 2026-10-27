module

public import CFSG.RankThree.PartTwo.Sec6.BThreeCensusL2

public section

namespace CFSG.RankThree.PartTwo.Sec6.BThreeCensus

open Matrix

theorem map_eq_one_of_isPerfect {Y A : Type*} [Group Y] [Group A] [IsMulCommutative A]
    (hY : Group.IsPerfect Y) (f : Y →* A) (y : Y) : f y = 1 := by
  have h := Abelianization.commutator_subset_ker f
  rw [hY.commutator_eq_top] at h
  exact h (Subgroup.mem_top y)

variable {K : Type} [Field K] [Finite K]

theorem eq_bot_of_isPerfect_of_glTwo
    (H : Subgroup (GL (Fin 2) K)) (hp : Group.IsPerfect H) (h3 : ¬ 3 ∣ Nat.card H) : H = ⊥ := by
  have hdet : ∀ h : H, ((h : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    intro h
    have h1 := map_eq_one_of_isPerfect hp (Matrix.GeneralLinearGroup.det.comp H.subtype) h
    have h2 := congrArg Units.val h1
    simpa using h2
  let φ : H →* SpecialLinearGroup (Fin 2) K :=
    { toFun := fun h => ⟨((h : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K), hdet h⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl }
  have hφ : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    apply Units.ext
    have := congrArg (fun s : SpecialLinearGroup (Fin 2) K => (s : Matrix (Fin 2) (Fin 2) K)) hab
    exact this
  let ψ : H →* ProjectiveSpecialLinearGroup (Fin 2) K :=
    (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 2) K))).comp φ
  have hker : ∀ a ∈ ψ.ker, φ a ∈ Subgroup.center (SpecialLinearGroup (Fin 2) K) := by
    intro a ha
    rw [MonoidHom.mem_ker] at ha
    exact (QuotientGroup.eq_one_iff (φ a)).mp ha
  have hkerc : Group.IsSolvable ψ.ker := Group.isSolvable_of_comm fun a b => by
    apply Subtype.ext
    apply hφ
    rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact Subgroup.mem_center_iff.mp (hker b b.2) (φ a)
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨p, -, f, hp', hK⟩ := FiniteField.card' K
  have : Fact p.Prime := ⟨hp'⟩
  have hs : Group.IsSolvable ψ.range :=
    isSolvable_of_not_three_dvd_psl2 (f := f) (by rw [Nat.card_eq_fintype_card, hK]) ψ.range
      (fun h3' => h3 (h3'.trans (Subgroup.card_range_dvd _)))
  have : Group.IsSolvable H :=
    Group.isSolvable_of_ker_le_range ψ.ker.subtype ψ.rangeRestrict
      (by rw [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype])
  exact eq_bot_of_isPerfect_of_isSolvable hp this

theorem eq_one_of_finrank_le_two {E : Type*}
    [AddCommGroup E] [Module K E] [FiniteDimensional K E] (hE : Module.finrank K E ≤ 2)
    {Y : Type*} [Group Y] [Finite Y] (hYp : Group.IsPerfect Y) (hY3 : ¬ 3 ∣ Nat.card Y)
    (ρ : Y →* (Module.End K E)ˣ) (y : Y) : ρ y = 1 := by
  rcases (by omega : Module.finrank K E = 0 ∨ Module.finrank K E = 1 ∨ Module.finrank K E = 2)
    with h | h | h
  · have : Subsingleton E := Module.finrank_zero_iff.mp h
    apply Units.ext
    ext v
    exact Subsingleton.elim _ _
  · let b := Module.finBasisOfFinrankEq K E h
    let e : (Module.End K E)ˣ ≃* GL (Fin 1) K :=
      Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv
    have h1 := map_eq_one_of_isPerfect hYp
      (Matrix.GeneralLinearGroup.det.comp (e.toMonoidHom.comp ρ)) y
    apply e.injective
    rw [map_one]
    apply Units.ext
    have h2 := congrArg Units.val h1
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      Matrix.GeneralLinearGroup.val_det_apply, Units.val_one, Matrix.det_fin_one] at h2
    ext i j
    fin_cases i
    fin_cases j
    simpa using h2
  · let b := Module.finBasisOfFinrankEq K E h
    let e : (Module.End K E)ˣ ≃* GL (Fin 2) K :=
      Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv
    have hH := eq_bot_of_isPerfect_of_glTwo (e.toMonoidHom.comp ρ).range
      (Group.IsPerfect.range _) (fun h3 => hY3 (h3.trans (Subgroup.card_range_dvd _)))
    have hmem : e (ρ y) ∈ (e.toMonoidHom.comp ρ).range := ⟨y, rfl⟩
    rw [hH, Subgroup.mem_bot] at hmem
    apply e.injective
    rw [hmem, map_one]

section Eigen

variable {n : Type} [Fintype n] [DecidableEq n]

@[expose] def eigenProj (g : Matrix n n K) (c : K) : Matrix n n K :=
  1 + c • g + c ^ 2 • g ^ 2

omit [Finite K] in
theorem mul_eigenProj {g : Matrix n n K} (hg : g ^ 3 = 1) {c : K} (hc : c ^ 3 = 1) :
    g * eigenProj g c = c ^ 2 • eigenProj g c := by
  have hg' : g * g ^ 2 = 1 := by rw [← pow_succ', hg]
  have hc' : c ^ 2 * c ^ 2 = c := by
    calc c ^ 2 * c ^ 2 = c ^ 3 * c := by ring
      _ = c := by rw [hc, one_mul]
  have hc'' : c ^ 2 * c = 1 := by rw [← hc]; ring
  simp only [eigenProj, mul_add, mul_one, Matrix.mul_smul, smul_add, smul_smul, hc', hc'',
    one_smul, hg']
  rw [show g * g = g ^ 2 by rw [sq]]
  abel

omit [Finite K] in
theorem commute_eigenProj {g y : Matrix n n K} (h : y * g = g * y) (c : K) :
    y * eigenProj g c = eigenProj g c * y := by
  have h2 : y * g ^ 2 = g ^ 2 * y := by
    rw [sq, ← mul_assoc, h, mul_assoc, h, mul_assoc]
  simp only [eigenProj, mul_add, add_mul, mul_one, one_mul, Matrix.mul_smul, Matrix.smul_mul, h,
    h2]

omit [Finite K] in
theorem eigenProj_add_add {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (g : Matrix n n K) :
    eigenProj g 1 + eigenProj g ω + eigenProj g (ω ^ 2) = (3 : K) • 1 := by
  have hω4 : (ω ^ 2) ^ 2 = ω := by linear_combination (ω ^ 2 - ω) * hω
  simp only [eigenProj, one_pow, one_smul, hω4]
  have e1 : (1 : Matrix n n K) + g + g ^ 2 + (1 + ω • g + ω ^ 2 • g ^ 2) +
      (1 + ω ^ 2 • g + ω • g ^ 2) =
      (3 : K) • (1 : Matrix n n K) + (ω ^ 2 + ω + 1) • g + (ω ^ 2 + ω + 1) • g ^ 2 := by
    simp only [add_smul, one_smul, ofNat_smul_eq_nsmul (R := K) (n := 3) (1 : Matrix n n K)]
    abel
  rw [e1, hω, zero_smul, zero_smul, add_zero, add_zero]

omit [Finite K] in
theorem mulVec_eq_of_mem_range_eigenProj {g : Matrix n n K} (hg : g ^ 3 = 1) {c : K}
    (hc : c ^ 3 = 1) {u : n → K} (hu : u ∈ LinearMap.range (Matrix.toLin' (eigenProj g c))) :
    g *ᵥ u = c ^ 2 • u := by
  obtain ⟨w, rfl⟩ := hu
  rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, mul_eigenProj hg hc, Matrix.smul_mulVec]

omit [Finite K] in
theorem finrank_range_eigenProj_le_two_of_ne_smul_one {g : Matrix (Fin 3) (Fin 3) K}
    (hg : g ^ 3 = 1) (hns : ∀ a : K, g ≠ a • 1) {c : K} (hc : c ^ 3 = 1) :
    Module.finrank K (LinearMap.range (Matrix.toLin' (eigenProj g c))) ≤ 2 := by
  by_contra h
  push Not at h
  have hle := Submodule.finrank_le (LinearMap.range (Matrix.toLin' (eigenProj g c)))
  rw [Module.finrank_fin_fun] at hle
  have h3 : Module.finrank K (LinearMap.range (Matrix.toLin' (eigenProj g c))) =
      Module.finrank K (Fin 3 → K) := by
    rw [Module.finrank_fin_fun]
    omega
  have htop := Submodule.eq_top_of_finrank_eq h3
  apply hns (c ^ 2)
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  have hv : v ∈ LinearMap.range (Matrix.toLin' (eigenProj g c)) := by
    rw [htop]
    exact Submodule.mem_top
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.smul_mulVec, Matrix.one_mulVec]
  exact mulVec_eq_of_mem_range_eigenProj hg hc hv

theorem eq_bot_of_commute_of_finrank_le_two (h3 : (3 : K) ≠ 0)
    {ω : K} (hω : ω ^ 2 + ω + 1 = 0) {g : Matrix n n K}
    (hdim : ∀ c : K, c ^ 3 = 1 →
      Module.finrank K (LinearMap.range (Matrix.toLin' (eigenProj g c))) ≤ 2)
    (Y : Subgroup (GL n K)) (hYg : ∀ y ∈ Y, (y : Matrix n n K) * g = g * y)
    (hYp : Group.IsPerfect Y) (hY3 : ¬ 3 ∣ Nat.card Y) : Y = ⊥ := by
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hfix : ∀ c : K, c ^ 3 = 1 → ∀ y ∈ Y, ∀ v : n → K,
      (y : Matrix n n K) *ᵥ (eigenProj g c *ᵥ v) = eigenProj g c *ᵥ v := by
    intro c hc
    set E := LinearMap.range (Matrix.toLin' (eigenProj g c)) with hE
    have hinv : ∀ y ∈ Y, ∀ v ∈ E, Matrix.toLin' (y : Matrix n n K) v ∈ E := by
      rintro y hy _ ⟨w, rfl⟩
      refine ⟨(y : Matrix n n K) *ᵥ w, ?_⟩
      simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, commute_eigenProj (hYg y hy)]
    let base : Y →* Module.End K E :=
      { toFun := fun y => (Matrix.toLin' ((y : GL n K) : Matrix n n K)).restrict (hinv y y.2)
        map_one' := by
          ext v
          simp
        map_mul' := fun a b => by
          ext v
          simp [Matrix.mulVec_mulVec] }
    intro y hy v
    have h1 := eq_one_of_finrank_le_two (hdim c hc) hYp hY3 base.toHomUnits ⟨y, hy⟩
    have h2 := congrArg (fun u : (Module.End K E)ˣ =>
      ((u : Module.End K E) ⟨eigenProj g c *ᵥ v, v, rfl⟩ : n → K)) h1
    simpa [base] using h2
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  apply Units.ext
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  have hv : v = (3 : K)⁻¹ • (eigenProj g 1 *ᵥ v + eigenProj g ω *ᵥ v +
      eigenProj g (ω ^ 2) *ᵥ v) := by
    rw [← Matrix.add_mulVec, ← Matrix.add_mulVec, eigenProj_add_add hω, Matrix.smul_mulVec,
      Matrix.one_mulVec, smul_smul, inv_mul_cancel₀ h3, one_smul]
  have hω6 : (ω ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hω3, one_pow]
  rw [Matrix.toLin'_apply, Units.val_one, Matrix.toLin'_one, LinearMap.id_apply, hv,
    Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_add, hfix 1 (one_pow 3) y hy,
    hfix ω hω3 y hy, hfix (ω ^ 2) hω6 y hy]

end Eigen

section BaseChange

variable {n : Type} [Fintype n] [DecidableEq n]

omit [Finite K] in
theorem map_gl_injective {F : Type} [Field F] (φ : F →+* K) :
    Function.Injective (Matrix.GeneralLinearGroup.map (n := n) φ) := by
  intro x y h
  apply Units.ext
  have := congrArg (fun z : GL n K => (z : Matrix n n K)) h
  ext i j
  exact φ.injective (congrFun (congrFun this i) j)

theorem eq_bot_of_commute_of_map (h3 : (3 : K) ≠ 0) {F : Type}
    [Field F] (φ : F →+* K) {ω : K} (hω : ω ^ 2 + ω + 1 = 0) {g : GL n F}
    (hdim : ∀ c : K, c ^ 3 = 1 → Module.finrank K (LinearMap.range (Matrix.toLin'
      (eigenProj ((g : Matrix n n F).map φ) c))) ≤ 2)
    (Y : Subgroup (GL n F)) (hYg : ∀ y ∈ Y, y * g = g * y) (hYp : Group.IsPerfect Y)
    (hY3 : ¬ 3 ∣ Nat.card Y) : Y = ⊥ := by
  set m := Matrix.GeneralLinearGroup.map (n := n) φ with hm
  have hinj : Function.Injective m := map_gl_injective φ
  have hY' : Y.map m = ⊥ := by
    refine eq_bot_of_commute_of_finrank_le_two h3 hω (g := ((m g : GL n K) : Matrix n n K)) hdim
      (Y.map m) ?_ ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      have h := congrArg (fun z : GL n F => ((m z : GL n K) : Matrix n n K)) (hYg y hy)
      simpa only [map_mul, Units.val_mul] using h
    · have := hYp
      exact Group.IsPerfect.map m
    · rwa [Subgroup.card_map_of_injective hinj]
  exact (Subgroup.map_eq_bot_iff_of_injective Y hinj).mp hY'

end BaseChange

theorem exists_splittingField_cubeRoot (F : Type) [Field F] [Finite F] :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : F →+* K) (ω : K), ω ^ 2 + ω + 1 = 0 := by
  set f : Polynomial F := Polynomial.X ^ 2 + Polynomial.X + 1 with hf
  have : Finite f.SplittingField := Module.finite_of_finite F
  have hdeg : (Polynomial.map (algebraMap F f.SplittingField) f).degree ≠ 0 := by
    have h2 : (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial F).degree = 2 := by
      compute_degree!
    rw [Polynomial.degree_map, hf, h2]
    exact two_ne_zero
  obtain ⟨a, ha⟩ := (Polynomial.SplittingField.splits f).exists_eval_eq_zero hdeg
  refine ⟨f.SplittingField, inferInstance, inferInstance, algebraMap F f.SplittingField, a, ?_⟩
  simpa [hf] using ha

omit [Finite K] in
theorem three_ne_zero_map {F : Type} [Field F] (φ : F →+* K) (h3 : (3 : F) ≠ 0) :
    (3 : K) ≠ 0 := by
  intro h
  apply h3
  apply φ.injective
  rw [map_zero, map_ofNat]
  exact h

omit [Finite K] in
theorem three_ne_zero_of_charTwo [CharP K 2] : (3 : K) ≠ 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h31 : (3 : K) = 1 := by linear_combination h2
  rw [h31]
  exact one_ne_zero

omit [Finite K] in
theorem eq_smul_one_of_map_eq_smul_one {F : Type} [Field F] (φ : F →+* K)
    {A : Matrix (Fin 3) (Fin 3) F} {a : K} (ha : A.map φ = a • 1) : A = A 0 0 • 1 := by
  have h0 := congrFun (congrFun ha 0) 0
  simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
    mul_one] at h0
  ext i j
  have h1 := congrFun (congrFun ha i) j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at h1
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq, mul_one] at h1
    rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    exact φ.injective (h1.trans h0.symm)
  · rw [Matrix.one_apply_ne hij, mul_zero, ← map_zero φ] at h1
    rw [Matrix.smul_apply, Matrix.one_apply_ne hij, smul_eq_mul, mul_zero]
    exact φ.injective h1

end CFSG.RankThree.PartTwo.Sec6.BThreeCensus
