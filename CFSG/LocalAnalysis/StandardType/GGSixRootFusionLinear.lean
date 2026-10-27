module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitness

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Generic

theorem eq_one_of_pow_two_pow_eq_one_of_forall {U : Type*} [Group U] {K : Subgroup U}
    (hK : ∀ z ∈ K, z ^ 2 = 1 → z = 1) : ∀ (k : ℕ) (z : U), z ∈ K → z ^ 2 ^ k = 1 → z = 1
  | 0, z, _, hz => by simpa using hz
  | k + 1, z, hzK, hz => by
    have h1 : z ^ 2 ^ k = 1 :=
      hK _ (K.pow_mem hzK _) (by rw [← pow_mul, ← pow_succ]; exact hz)
    exact eq_one_of_pow_two_pow_eq_one_of_forall hK k z hzK h1

theorem exists_orderOf_eq_two_of_mem_range {U G : Type*} [Group U] [Group G] [Finite U]
    (ψ : U →* G) (hker : ∀ z ∈ ψ.ker, z ^ 2 = 1 → z = 1) {s : G} (hs : s ∈ ψ.range)
    (hs2 : orderOf s = 2) : ∃ u : U, ψ u = s ∧ orderOf u = 2 := by
  obtain ⟨u₀, rfl⟩ := hs
  obtain ⟨a, m, hm, ho⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos u₀).ne'
  have hsq : (ψ u₀) ^ 2 = 1 := by
    rw [← hs2]
    exact pow_orderOf_eq_one _
  have hψm : ψ (u₀ ^ m) = ψ u₀ := by
    obtain ⟨j, rfl⟩ := hm
    rw [map_pow, pow_succ, pow_mul, hsq, one_pow, one_mul]
  refine ⟨u₀ ^ m, hψm, ?_⟩
  have hker2 : (u₀ ^ m) ^ 2 ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_pow, hψm, hsq]
  have hpow : ((u₀ ^ m) ^ 2) ^ 2 ^ a = 1 := by
    rw [← pow_mul, ← pow_mul, show m * (2 * 2 ^ a) = 2 ^ a * m * 2 by ring, pow_mul, ← ho,
      pow_orderOf_eq_one, one_pow]
  have h2 : (u₀ ^ m) ^ 2 = 1 := eq_one_of_pow_two_pow_eq_one_of_forall hker a _ hker2 hpow
  have hne : u₀ ^ m ≠ 1 := by
    intro h
    have h1 : ψ u₀ = 1 := by rw [← hψm, h, map_one]
    rw [h1, orderOf_one] at hs2
    exact absurd hs2 (by norm_num)
  exact orderOf_eq_prime h2 hne

variable {G : Type} [Group G]

theorem conj_mem_ggCentOTwoPrime {G₀ : Subgroup G} {s m y : G}
    (hm : m ∈ Subgroup.normalizer (G₀ : Set G)) (hy : y ∈ ggCentOTwoPrime G₀ s) :
    m⁻¹ * y * m ∈ ggCentOTwoPrime G₀ (m⁻¹ * s * m) := by
  have hm' : m⁻¹ ∈ Subgroup.normalizer (G₀ : Set G) := Subgroup.inv_mem _ hm
  have hcl : ggCentOTwoPrime G₀ s ≤
      (ggCentOTwoPrime G₀ (m⁻¹ * s * m)).comap (MulAut.conj m⁻¹).toMonoidHom := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro z ⟨hzG, hzs, k, hzk⟩
    refine Subgroup.mem_comap.mpr (Subgroup.subset_closure ⟨?_, ?_, k, ?_⟩)
    · have := (Subgroup.mem_normalizer_iff.mp hm' z).mp hzG
      simpa [MulAut.conj_apply] using this
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      calc m⁻¹ * z * m * (m⁻¹ * s * m) = m⁻¹ * (z * s) * m := by group
        _ = m⁻¹ * (s * z) * m := by rw [hzs]
        _ = m⁻¹ * s * m * (m⁻¹ * z * m) := by group
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      rw [show m⁻¹ * z * m = m⁻¹ * z * (m⁻¹)⁻¹ by rw [inv_inv], conj_pow, hzk, mul_one,
        mul_inv_cancel]
  simpa [MulAut.conj_apply] using hcl hy

theorem GGRootFusionWitnessAlt.of_conj {p : ℕ} {Bs D E G₀ : Subgroup G} {t : StatedLieTag}
    {f : ℕ} {r s m : G} (hm : m ∈ Subgroup.normalizer (G₀ : Set G))
    (h : GGRootFusionWitnessAlt p Bs D E G₀ (Subgroup.normalizer (G₀ : Set G)) t f r
      (m * s * m⁻¹)) :
    GGRootFusionWitnessAlt p Bs D E G₀ (Subgroup.normalizer (G₀ : Set G)) t f r s := by
  rcases h with ⟨m', hm', heq⟩ | ⟨y, hys, m', hm', hw⟩ | hα
  · refine Or.inl ⟨m' * m, Subgroup.mul_mem _ hm' hm, ?_⟩
    calc s = m⁻¹ * (m * s * m⁻¹) * m := by group
      _ = (m' * m)⁻¹ * r * (m' * m) := by rw [heq]; group
  · refine Or.inr (Or.inl ⟨m⁻¹ * y * m, ?_, m' * m, Subgroup.mul_mem _ hm' hm, ?_⟩)
    · calc m⁻¹ * y * m * s = m⁻¹ * (y * (m * s * m⁻¹)) * m := by group
        _ = m⁻¹ * ((m * s * m⁻¹) * y) * m := by rw [hys]
        _ = s * (m⁻¹ * y * m) := by group
    · have he : m' * m * (m⁻¹ * y * m) * (m' * m)⁻¹ = m' * y * m'⁻¹ := by group
      rwa [he]
  · refine Or.inr (Or.inr ?_)
    rintro ⟨φ, hφ⟩
    have hs : m⁻¹ * (m * s * m⁻¹) * m = s := by group
    have hmem : ∀ y ∈ ggCentOTwoPrime G₀ (m * s * m⁻¹), m⁻¹ * y * m ∈ ggCentOTwoPrime G₀ s := by
      intro y hy
      have := conj_mem_ggCentOTwoPrime hm hy
      rwa [hs] at this
    let c : ↥(ggCentOTwoPrime G₀ (m * s * m⁻¹)) →* ↥(ggCentOTwoPrime G₀ s) :=
      { toFun := fun y => ⟨m⁻¹ * y * m, hmem y y.2⟩
        map_one' := by ext; simp
        map_mul' := fun a b => by ext; simp [mul_assoc] }
    have hc : Function.Injective c := by
      intro a b hab
      have h := congrArg Subtype.val hab
      simp only [c, MonoidHom.coe_mk, OneHom.coe_mk, mul_left_inj, mul_right_inj] at h
      exact Subtype.ext h
    exact hα ⟨φ.comp c, hφ.comp hc⟩

theorem ggRootFusionWitnessAlt_of_lift_conj {U : Type*} [Group U] (ψ : U →* G) {p : ℕ}
    {Bs D E G₀ M : Subgroup G} {t : StatedLieTag} {f : ℕ} (hle : ψ.range ≤ M) {u w a : U}
    (hconj : u = a * w * a⁻¹) :
    GGRootFusionWitnessAlt p Bs D E G₀ M t f (ψ w) (ψ u) :=
  Or.inl ⟨ψ a⁻¹, hle ⟨a⁻¹, rfl⟩, by rw [hconj]; simp [map_mul, map_inv, mul_assoc]⟩

end Generic

section SL

open Matrix

@[expose] def ggInvNil (n l : ℕ) (F : Type*) [Field F] : Matrix (Fin n) (Fin n) F :=
  Matrix.of fun a b => if (b : ℕ) < l ∧ (a : ℕ) = b + (n - l) ∧ (b : ℕ) < a then 1 else 0

@[expose] def ggInvMatrix (n l : ℕ) (F : Type*) [Field F] : Matrix (Fin n) (Fin n) F :=
  1 + ggInvNil n l F

variable {F : Type*} [Field F]

theorem ggInvNil_apply (n l : ℕ) (a b : Fin n) :
    ggInvNil n l F a b = if (b : ℕ) < l ∧ (a : ℕ) = b + (n - l) ∧ (b : ℕ) < a then 1 else 0 :=
  rfl

theorem ggInvNil_mul_self {n l : ℕ} (h : 2 * l ≤ n) : ggInvNil n l F * ggInvNil n l F = 0 := by
  ext a c
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [ggInvNil_apply, ggInvNil_apply]
  by_cases h1 : (b : ℕ) < l ∧ (a : ℕ) = b + (n - l) ∧ (b : ℕ) < a
  · by_cases h2 : (c : ℕ) < l ∧ (b : ℕ) = c + (n - l) ∧ (c : ℕ) < b
    · exfalso
      omega
    · rw [ite_eq_right h2, mul_zero]
  · rw [ite_eq_right h1, zero_mul]

theorem det_ggInvMatrix (n l : ℕ) : (ggInvMatrix n l F).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular]
  · refine Finset.prod_eq_one fun a _ => ?_
    simp [ggInvMatrix, ggInvNil_apply]
  · intro a b hab
    have hab' : a < b := by simpa using hab
    have : (a : ℕ) < b := hab'
    simp only [ggInvMatrix, Matrix.add_apply, Matrix.one_apply_ne hab'.ne, ggInvNil_apply,
      zero_add]
    split_ifs with h1
    · omega
    · rfl

@[expose] def ggInvSL (n l : ℕ) (F : Type*) [Field F] : SpecialLinearGroup (Fin n) F :=
  ⟨ggInvMatrix n l F, det_ggInvMatrix n l⟩

theorem coe_ggInvSL (n l : ℕ) : ((ggInvSL n l F : SpecialLinearGroup (Fin n) F) :
    Matrix (Fin n) (Fin n) F) = ggInvMatrix n l F :=
  rfl

theorem ggInvSL_mul_self [CharP F 2] {n l : ℕ} (h : 2 * l ≤ n) :
    ggInvSL n l F * ggInvSL n l F = 1 := by
  refine Subtype.ext ?_
  change ggInvMatrix n l F * ggInvMatrix n l F = 1
  have hN : ggInvNil n l F + ggInvNil n l F = 0 := by
    ext a b
    simp [CharTwo.add_self_eq_zero]
  rw [ggInvMatrix, add_mul, mul_add, mul_add, ggInvNil_mul_self h, Matrix.one_mul,
    Matrix.mul_one, Matrix.one_mul, add_zero, add_assoc, hN, add_zero]

theorem ggInvMatrix_one (m : ℕ) (hm : 1 ≤ m) :
    ggInvMatrix (m + 1) 1 F = 1 + Matrix.single (Fin.last m) 0 1 := by
  ext a b
  simp only [ggInvMatrix, Matrix.add_apply, ggInvNil_apply, Matrix.single_apply, Fin.ext_iff,
    Fin.val_last, Fin.val_zero]
  congr 1
  split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; omega)

theorem eq_one_of_mem_center_of_sq_eq_one [CharP F 2] {n : ℕ}
    {z : SpecialLinearGroup (Fin n) F} (hz : z ∈ Subgroup.center (SpecialLinearGroup (Fin n) F))
    (hz2 : z ^ 2 = 1) : z = 1 := by
  obtain ⟨c, -, hc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Subsingleton.elim _ _
  have hc2 : c * c = 1 := by
    have h := congrArg (fun A : SpecialLinearGroup (Fin n) F =>
      (A : Matrix (Fin n) (Fin n) F) ⟨0, hn⟩ ⟨0, hn⟩) hz2
    simp only [pow_two, Matrix.SpecialLinearGroup.coe_mul, ← hc, Matrix.SpecialLinearGroup.coe_one,
      Matrix.one_apply_eq] at h
    simpa [Matrix.scalar_apply] using h
  have hc1 : c = 1 := by
    have h0 : (c + 1) * (c + 1) = 0 := by
      have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
      linear_combination hc2 + (c + 1) * h2
    have := mul_self_eq_zero.mp h0
    rw [← CharTwo.sub_eq_add] at this
    exact sub_eq_zero.mp this
  refine Subtype.ext ?_
  rw [← hc, hc1, map_one]
  rfl

end SL

section RootConj

open Matrix

variable {F : Type*} [Field F] [CharP F 2] {n : ℕ}

theorem det_permMatrix_charTwo (σ : Equiv.Perm (Fin n)) : (σ.permMatrix F).det = 1 := by
  rw [Matrix.det_permutation]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h]
  · simp
  · simp [CharTwo.neg_eq]

@[expose] def ggPermSL (σ : Equiv.Perm (Fin n)) : SpecialLinearGroup (Fin n) F :=
  ⟨σ.permMatrix F, det_permMatrix_charTwo σ⟩

theorem ggPermSL_mul_inv (σ : Equiv.Perm (Fin n)) :
    ggPermSL (F := F) σ * ggPermSL σ⁻¹ = 1 := by
  refine Subtype.ext ?_
  change σ.permMatrix F * (σ⁻¹).permMatrix F = 1
  rw [← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one]

theorem ggPermSL_inv (σ : Equiv.Perm (Fin n)) : (ggPermSL (F := F) σ)⁻¹ = ggPermSL σ⁻¹ :=
  (eq_inv_of_mul_eq_one_right (ggPermSL_mul_inv σ)).symm

theorem coe_ggPermSL_conj (σ : Equiv.Perm (Fin n)) (A : SpecialLinearGroup (Fin n) F) :
    ((ggPermSL σ * A * (ggPermSL σ)⁻¹ : SpecialLinearGroup (Fin n) F) :
      Matrix (Fin n) (Fin n) F) = (A : Matrix (Fin n) (Fin n) F).submatrix σ σ := by
  rw [ggPermSL_inv]
  change σ.permMatrix F * (A : Matrix (Fin n) (Fin n) F) * (σ⁻¹).permMatrix F = _
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul, Equiv.Perm.permMatrix,
    PEquiv.mul_toMatrix_toPEquiv]
  ext a b
  simp [Matrix.submatrix_apply, Equiv.Perm.inv_def]

omit [CharP F 2] in
theorem submatrix_transvection (σ : Equiv.Perm (Fin n)) (i j : Fin n) (c : F) :
    (Matrix.transvection i j c).submatrix σ σ = Matrix.transvection (σ⁻¹ i) (σ⁻¹ j) c := by
  ext a b
  simp only [Matrix.transvection, Matrix.submatrix_apply, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply, EmbeddingLike.apply_eq_iff_eq, Equiv.Perm.inv_eq_iff_eq]

@[expose] def ggDiagSL (d : Fin n → F) (hd : ∏ x, d x = 1) : SpecialLinearGroup (Fin n) F :=
  ⟨Matrix.diagonal d, by rw [Matrix.det_diagonal, hd]⟩

omit [CharP F 2] in
theorem coe_ggDiagSL_conj (d : Fin n → F) (hd : ∏ x, d x = 1) (hd0 : ∀ x, d x ≠ 0)
    (A : SpecialLinearGroup (Fin n) F) (a b : Fin n) :
    ((ggDiagSL d hd * A * (ggDiagSL d hd)⁻¹ : SpecialLinearGroup (Fin n) F) :
      Matrix (Fin n) (Fin n) F) a b = d a * (A : Matrix (Fin n) (Fin n) F) a b * (d b)⁻¹ := by
  have hd' : ∏ x, (d x)⁻¹ = 1 := by rw [Finset.prod_inv_distrib, hd, inv_one]
  have hmul : ggDiagSL d hd * ggDiagSL (fun x => (d x)⁻¹) hd' = 1 := by
    refine Subtype.ext ?_
    change Matrix.diagonal d * Matrix.diagonal (fun x => (d x)⁻¹) = 1
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext x
    exact mul_inv_cancel₀ (hd0 x)
  have hinv : (ggDiagSL d hd)⁻¹ = ggDiagSL (fun x => (d x)⁻¹) hd' :=
    (eq_inv_of_mul_eq_one_right hmul).symm
  rw [hinv]
  change (Matrix.diagonal d * (A : Matrix (Fin n) (Fin n) F) *
    Matrix.diagonal (fun x => (d x)⁻¹)) a b = _
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem exists_conj_transvection_eq [Finite F] {m : ℕ} (hm : 1 ≤ m) {i j : Fin (m + 1)}
    (hij : i ≠ j) {c : F} (hc : c ≠ 0) :
    ∃ g : SpecialLinearGroup (Fin (m + 1)) F,
      g * SpecialLinearGroup.transvection hij c * g⁻¹ = ggInvSL (m + 1) 1 F := by
  set i₀ : Fin (m + 1) := Fin.last m
  set j₀ : Fin (m + 1) := 0
  have h₀ : i₀ ≠ j₀ := by
    simp only [i₀, j₀, ne_eq, Fin.ext_iff, Fin.val_last, Fin.val_zero]
    omega
  set τ₁ := Equiv.swap j₀ j
  set τ₂ := Equiv.swap i₀ (τ₁ i)
  set σ : Equiv.Perm (Fin (m + 1)) := τ₁ * τ₂
  have hj₀ : j₀ ≠ τ₁ i := by
    intro h
    apply hij
    have := congrArg τ₁ h
    simp only [τ₁, Equiv.swap_apply_self, Equiv.swap_apply_left] at this
    exact this.symm
  have hσi : σ⁻¹ i = i₀ := by
    rw [Equiv.Perm.inv_eq_iff_eq]
    simp [σ, τ₂, τ₁, Equiv.Perm.mul_apply]
  have hσj : σ⁻¹ j = j₀ := by
    rw [Equiv.Perm.inv_eq_iff_eq]
    simp only [σ, Equiv.Perm.mul_apply, τ₂]
    rw [Equiv.swap_apply_of_ne_of_ne h₀.symm hj₀]
    simp [τ₁]
  obtain ⟨b, hb⟩ := isSquare_of_charTwo' (c⁻¹)
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hb
    exact inv_ne_zero hc hb
  set d : Fin (m + 1) → F := Pi.mulSingle i₀ b * Pi.mulSingle j₀ b⁻¹
  have hd : ∏ x, d x = 1 := by
    simp only [d, Pi.mul_apply, Finset.prod_mul_distrib, Finset.prod_pi_mulSingle',
      Finset.mem_univ, ite_true]
    exact mul_inv_cancel₀ hb0
  have hd0 : ∀ x, d x ≠ 0 := by
    intro x
    simp only [d, Pi.mul_apply]
    refine mul_ne_zero ?_ ?_
    · by_cases hx : x = i₀
      · rw [hx, Pi.mulSingle_eq_same]; exact hb0
      · rw [Pi.mulSingle_eq_of_ne hx]; exact one_ne_zero
    · by_cases hx : x = j₀
      · rw [hx, Pi.mulSingle_eq_same]; exact inv_ne_zero hb0
      · rw [Pi.mulSingle_eq_of_ne hx]; exact one_ne_zero
  refine ⟨ggDiagSL d hd * ggPermSL σ, Subtype.ext ?_⟩
  have hP : ((ggPermSL σ * SpecialLinearGroup.transvection hij c * (ggPermSL σ)⁻¹ :
      SpecialLinearGroup (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      Matrix.transvection i₀ j₀ c := by
    rw [coe_ggPermSL_conj, SpecialLinearGroup.transvection_coe, ← Matrix.transvection,
      submatrix_transvection, hσi, hσj]
  rw [_root_.mul_inv_rev, show ggDiagSL d hd * ggPermSL σ * SpecialLinearGroup.transvection hij c *
      ((ggPermSL σ)⁻¹ * (ggDiagSL d hd)⁻¹) = ggDiagSL d hd * (ggPermSL σ *
        SpecialLinearGroup.transvection hij c * (ggPermSL σ)⁻¹) * (ggDiagSL d hd)⁻¹ by group]
  ext a b'
  rw [coe_ggDiagSL_conj d hd hd0, hP, coe_ggInvSL, ggInvMatrix_one m hm]
  simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  by_cases hab : i₀ = a ∧ j₀ = b'
  · obtain ⟨rfl, rfl⟩ := hab
    rw [ite_eq_right h₀, ite_eq_left ⟨rfl, rfl⟩, ite_eq_left ⟨rfl, rfl⟩]
    simp only [d, Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne h₀,
      Pi.mulSingle_eq_of_ne h₀.symm, mul_one, one_mul, inv_inv, zero_add]
    rw [mul_comm b c, mul_assoc, ← hb, mul_inv_cancel₀ hc]
  · rw [ite_eq_right hab, ite_eq_right hab]
    by_cases hab' : a = b'
    · subst hab'
      simp only [ite_true, add_zero, mul_one]
      exact mul_inv_cancel₀ (hd0 a)
    · simp only [hab', ite_false, add_zero, mul_zero, zero_mul]


theorem exists_transvection_of_mem_rootGroup {m : ℕ} {F : Type} [Field F] {γ : Fin m → ℤ}
    {z : SpecialLinearGroup (Fin (m + 1)) F} (hz : z ∈ SpecialLinear.rootGroup m F γ)
    (hz1 : z ≠ 1) :
    ∃ (i j : Fin (m + 1)) (hij : i ≠ j) (c : F), c ≠ 0 ∧
      z = SpecialLinearGroup.transvection hij c := by
  by_cases h : ∃ (i j : Fin (m + 1)) (_ : i ≠ j),
      SpecialLinear.toStd m γ = Pi.single i 1 - Pi.single j 1
  · obtain ⟨i, j, hij, hγ⟩ := h
    rw [SpecialLinear.rootGroup_eq m F hij hγ, SpecialLinear.mem_rootSubgroup] at hz
    obtain ⟨c, rfl⟩ := hz
    refine ⟨i, j, hij, c, ?_, rfl⟩
    rintro rfl
    exact hz1 (SpecialLinearGroup.transvection_coeff_zero hij)
  · exfalso
    have hbot : SpecialLinear.rootGroup m F γ = ⊥ := by
      refine iSup_eq_bot.mpr fun i => iSup_eq_bot.mpr fun j => iSup_eq_bot.mpr fun hij =>
        iSup_eq_bot.mpr fun hγ => ?_
      exact absurd ⟨i, j, hij, hγ⟩ h
    rw [hbot, Subgroup.mem_bot] at hz
    exact hz1 hz

end RootConj

@[expose] def GGSLInvolutionClassInput : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (n : ℕ)
    (u : Matrix.SpecialLinearGroup (Fin n) F), orderOf u = 2 →
      ∃ l : ℕ, 1 ≤ l ∧ 2 * l ≤ n ∧ ∃ a : Matrix.SpecialLinearGroup (Fin n) F,
        u = a * ggInvSL n l F * a⁻¹

theorem ggRootFusionWitnessAlt_of_specialLinear (hAS : GGSLInvolutionClassInput) {G : Type}
    [Group G] {m f : ℕ} (hm1 : 1 ≤ m)
    (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f) →* G) {p : ℕ}
    {Bs D E G₀ : Subgroup G} {t : StatedLieTag} {r : G} (hrange : ψ.range = G₀)
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)))
    (hr2 : orderOf r = 2)
    (hr : ∃ (γ : Fin m → ℤ) (v z : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)),
      z ∈ SpecialLinear.rootGroup m (GaloisField 2 f) γ ∧ r = ψ (v * z * v⁻¹))
    (hrep : ∀ l : ℕ, 2 ≤ l → 2 * l ≤ m + 1 →
      GGRootFusionWitnessAlt p Bs D E G₀ (Subgroup.normalizer (G₀ : Set G)) t f r
        (ψ (ggInvSL (m + 1) l (GaloisField 2 f))))
    {s : G} (hs : s ∈ G₀) (hs2 : orderOf s = 2) :
    GGRootFusionWitnessAlt p Bs D E G₀ (Subgroup.normalizer (G₀ : Set G)) t f r s := by
  have hle : ψ.range ≤ Subgroup.normalizer (G₀ : Set G) :=
    fun y hy => Subgroup.le_normalizer (hrange ▸ hy)
  have hkerinv : ∀ z ∈ ψ.ker, z ^ 2 = 1 → z = 1 := fun z hz hz2 =>
    eq_one_of_mem_center_of_sq_eq_one (F := GaloisField 2 f) (hker hz) hz2
  obtain ⟨u, hu, hu2⟩ := exists_orderOf_eq_two_of_mem_range ψ hkerinv (hrange ▸ hs) hs2
  obtain ⟨l, hl1, hl2, a, rfl⟩ := hAS (GaloisField 2 f) (m + 1) u hu2
  have hmN : (ψ a)⁻¹ ∈ Subgroup.normalizer (G₀ : Set G) := Subgroup.inv_mem _ (hle ⟨a, rfl⟩)
  refine GGRootFusionWitnessAlt.of_conj hmN ?_
  have hconj : (ψ a)⁻¹ * s * (ψ a)⁻¹⁻¹ = ψ (ggInvSL (m + 1) l (GaloisField 2 f)) := by
    rw [← hu, map_mul, map_mul, map_inv, inv_inv]
    group
  rw [hconj]
  rcases Nat.lt_or_ge l 2 with hl | hl
  · obtain rfl : l = 1 := by omega
    obtain ⟨γ, v, z, hz, rfl⟩ := hr
    have hz1 : z ≠ 1 := by
      rintro rfl
      rw [mul_one, mul_inv_cancel, map_one, orderOf_one] at hr2
      exact absurd hr2 (by norm_num)
    obtain ⟨i, j, hij, c, hc, rfl⟩ := exists_transvection_of_mem_rootGroup hz hz1
    obtain ⟨g, hg⟩ := exists_conj_transvection_eq hm1 hij hc
    refine ggRootFusionWitnessAlt_of_lift_conj ψ hle (a := g * v⁻¹) ?_
    rw [← hg]
    group
  · exact hrep l hl hl2

section Inputs

@[expose] def GGSixRootFusionSLRepInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (m f : ℕ) (ψ : (ggU .PSL (m + 1) f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU .PSL (m + 1) f).D .PSL (m + 1) f ψ →
      GGSixStepOne p B Bs x L D J → GGSixStepTwo p B Bs x L D J → ∀ (E : Subgroup G) (r : G),
      GGStepThreeChoice p Bs (ggM p B x L D J) (ggU .PSL (m + 1) f).D .PSL ψ E r →
        Subgroup.centralizer {r} ≤ ggM p B x L D J →
        Odd ((ggG0 p B x L D J).relIndex (ggM p B x L D J)) →
          ∀ l : ℕ, 2 ≤ l → 2 * l ≤ m + 1 →
            GGRootFusionWitnessAlt p Bs D E (ggG0 p B x L D J) (ggM p B x L D J) .PSL f r
              (ψ (ggInvSL (m + 1) l (GaloisField 2 f)))

theorem ggSixRootFusionWitnessInputFor_PSL (hAS : GGSLInvolutionClassInput)
    (hrep : GGSixRootFusionSLRepInput) : GGSixRootFusionWitnessInputFor (· = .PSL) := by
  intro G _ _ p B Bs x L D J t n f ψ ht hctx s1 s2 E r hch hC hodd s hs hs2
  subst ht
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hctx.2.2.2.1.1.2.2.1; omega⟩
  have hm1 : 1 ≤ m := by have := hctx.2.2.2.1.1.2.2.1; omega
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hr : ∃ (γ : Fin m → ℤ) (v z : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)),
      z ∈ SpecialLinear.rootGroup m (GaloisField 2 f) γ ∧ r = ψ (v * z * v⁻¹) := by
    obtain ⟨-, -, -, -, -, γ, -, v, -, hrv⟩ := hch
    obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hrv
    exact ⟨γ, v, z, hz, rfl⟩
  exact ggRootFusionWitnessAlt_of_specialLinear hAS hm1 ψ hrange hker hch.2.2.2.2.1 hr
    (hrep G p B Bs x L D J m f ψ hctx s1 s2 E r hch hC hodd) hs hs2

end Inputs

end CFSG.StandardType
