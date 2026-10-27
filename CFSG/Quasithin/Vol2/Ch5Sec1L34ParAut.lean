module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34ModelL34
public import CFSG.RankThree.PartTwo.KFacts.L34Aut
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.H13.KGL34P

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {k : Type} [Field k] (hk : Nat.card k = 4)
include hk

omit hk in
@[expose] noncomputable def chiB : upperTriangular 3 k →* kˣ where
  toFun A := diagUnit A 0 * (diagUnit A 2)⁻¹
  map_one' := by
    ext
    simp [val_diagUnit]
  map_mul' A B := by
    have hA := mem_upperTriangular_iff_isUpperTriangular.mp A.2
    have hB := mem_upperTriangular_iff_isUpperTriangular.mp B.2
    have h0 : diagUnit (A * B) 0 = diagUnit A 0 * diagUnit B 0 :=
      Units.ext (mul_apply_self_of_isUpperTriangular hA hB 0)
    have h2 : diagUnit (A * B) 2 = diagUnit A 2 * diagUnit B 2 :=
      Units.ext (mul_apply_self_of_isUpperTriangular hA hB 2)
    show diagUnit (A * B) 0 * (diagUnit (A * B) 2)⁻¹ =
      diagUnit A 0 * (diagUnit A 2)⁻¹ * (diagUnit B 0 * (diagUnit B 2)⁻¹)
    rw [h0, h2, mul_inv]
    exact mul_mul_mul_comm _ _ _ _

omit hk in
theorem val_chiB (A : upperTriangular 3 k) :
    (chiB A : k) = ((A : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) 0 0 *
      (((A : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) 2 2)⁻¹ := by
  show ((diagUnit A 0 * (diagUnit A 2)⁻¹ : kˣ) : k) = _
  rw [Units.val_mul, Units.val_inv_eq_inv_val, val_diagUnit, val_diagUnit]

omit hk in
@[expose] noncomputable def projB : upperTriangular 3 k →* projUpperTriangular 3 k :=
  ((proj 3 k).comp (upperTriangular 3 k).subtype).codRestrict _ (fun g => ⟨g, g.2, rfl⟩)

omit hk in
theorem coe_projB (g : upperTriangular 3 k) :
    ((projB g : projUpperTriangular 3 k) : projectiveSL 3 k) = proj 3 k g := rfl

omit hk in
theorem projB_surjective : Function.Surjective (projB (k := k)) := by
  rintro ⟨x, g, hg, rfl⟩
  exact ⟨⟨g, hg⟩, rfl⟩

omit hk in
theorem ker_projB_le : (projB (k := k)).ker ≤ (chiB (k := k)).ker := by
  intro g hg
  rw [MonoidHom.mem_ker] at hg ⊢
  have h1 : proj 3 k (g : SpecialLinearGroup (Fin 3) k) = 1 := congrArg Subtype.val hg
  rw [proj_eq_one_iff, mem_scalars] at h1
  obtain ⟨c, -, hgc⟩ := h1
  apply Units.ext
  rw [val_chiB, hgc]
  simp

omit hk in
@[expose] noncomputable def chiP : projUpperTriangular 3 k →* kˣ :=
  projB.liftOfRightInverse (Function.surjInv projB_surjective)
    (Function.rightInverse_surjInv projB_surjective) ⟨chiB, ker_projB_le⟩

omit hk in
theorem chiP_projB (g : upperTriangular 3 k) : chiP (projB g) = chiB g :=
  projB.liftOfRightInverse_comp_apply _ _ ⟨chiB, ker_projB_le⟩ g

theorem unit_pow_three (u : kˣ) : u ^ 3 = 1 := LinearThreeFourOuter.units_pow_three hk u

theorem chiP_eq_one_iff (x : projUpperTriangular 3 k) :
    chiP x = 1 ↔ (x : projectiveSL 3 k) ∈ projUnitriangular 3 k := by
  obtain ⟨g, rfl⟩ := projB_surjective x
  rw [chiP_projB, coe_projB]
  have hU := mem_upperTriangular_iff_isUpperTriangular.mp g.2
  set A : Matrix (Fin 3) (Fin 3) k := ((g : SpecialLinearGroup (Fin 3) k) :
    Matrix (Fin 3) (Fin 3) k) with hA
  constructor
  · intro h
    have h02 : A 0 0 = A 2 2 := by
      have := congrArg Units.val h
      rw [val_chiB, Units.val_one] at this
      have h2 : A 2 2 ≠ 0 := by
        have := (diagUnit g 2).ne_zero
        rwa [val_diagUnit] at this
      exact (mul_inv_eq_one₀ h2).mp this
    set c := diagUnit g 0 with hc
    have hdet := (g : SpecialLinearGroup (Fin 3) k).2
    rw [Matrix.det_of_isUpperTriangular hU, Fin.prod_univ_three] at hdet
    have hc3 : (c : k) ^ 3 = 1 := by simpa using congrArg Units.val (unit_pow_three hk c)
    have h11 : A 1 1 = c := by
      have hc0 : (c : k) ≠ 0 := c.ne_zero
      have e1 : (c : k) * A 1 1 * c = 1 := by
        rw [← h02] at hdet
        exact hdet
      calc A 1 1 = A 1 1 * (c : k) ^ 3 := by rw [hc3, mul_one]
        _ = ((c : k) * A 1 1 * c) * c := by ring
        _ = c := by rw [e1, one_mul]
    have hc0 : (c : k) ≠ 0 := c.ne_zero
    have hc3' : (c⁻¹) ^ 3 = 1 := by rw [inv_pow, unit_pow_three hk, inv_one]
    set μ := scalarElement c⁻¹ hc3' with hμ
    refine ⟨μ * g, ?_, ?_⟩
    · show μ * (g : SpecialLinearGroup (Fin 3) k) ∈ unitriangular 3 k
      rw [mem_unitriangular]
      refine ⟨fun i j hij => ?_, fun i => ?_⟩
      · show ((μ : Matrix (Fin 3) (Fin 3) k) * A) i j = 0
        rw [hμ, coe_scalarElement, scalar_apply, diagonal_mul, hU hij, mul_zero]
      · show ((μ : Matrix (Fin 3) (Fin 3) k) * A) i i = 1
        rw [hμ, coe_scalarElement, scalar_apply, diagonal_mul]
        fin_cases i
        · show (c⁻¹ : kˣ) * A 0 0 = 1
          rw [Units.val_inv_eq_inv_val]
          exact inv_mul_cancel₀ hc0
        · show (c⁻¹ : kˣ) * A 1 1 = 1
          rw [h11, Units.val_inv_eq_inv_val]
          exact inv_mul_cancel₀ hc0
        · show (c⁻¹ : kˣ) * A 2 2 = 1
          rw [← h02, Units.val_inv_eq_inv_val]
          exact inv_mul_cancel₀ hc0
    · rw [map_mul, proj_eq_one_iff.mpr (scalarElement_mem_scalars _ _), one_mul]
  · rintro ⟨u, hu, hug⟩
    rw [proj_eq_proj_iff, mem_scalars] at hug
    obtain ⟨c, -, hc⟩ := hug
    have hg : A = (u : Matrix (Fin 3) (Fin 3) k) * scalar (Fin 3) (c : k) := by
      have e1 : (u : Matrix (Fin 3) (Fin 3) k) *
          ((u⁻¹ * (g : SpecialLinearGroup (Fin 3) k) : SpecialLinearGroup (Fin 3) k) :
            Matrix (Fin 3) (Fin 3) k) = A :=
        congrArg Subtype.val (mul_inv_cancel_left u (g : SpecialLinearGroup (Fin 3) k))
      rw [hc] at e1
      exact e1.symm
    have hu' := (mem_unitriangular.mp hu).2
    apply Units.ext
    rw [val_chiB, Units.val_one, ← hA, hg]
    simp only [scalar_apply, mul_diagonal, hu' 0, hu' 2, one_mul]
    exact mul_inv_cancel₀ c.ne_zero

abbrev OutL34 (k : Type) [Field k] : Type :=
  kˣ ⋊[LinearThreeFourOuter.inversionAction kˣ] (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))

omit hk in
theorem inversionAction_eq (w : Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) (x : kˣ) :
    LinearThreeFourOuter.inversionAction kˣ w x =
      if Multiplicative.toAdd w.1 + Multiplicative.toAdd w.2 = 0 then x else x⁻¹ := by
  obtain ⟨a, b⟩ := w
  rw [← ofAdd_toAdd a, ← ofAdd_toAdd b, LinearThreeFourOuter.inversionAction_apply]
  rfl

omit hk in
theorem inversionAction_pow_left (w : Multiplicative (ZMod 2) × Multiplicative (ZMod 2))
    (hw : Multiplicative.toAdd w.1 + Multiplicative.toAdd w.2 = 0) (j : ℕ) (x : kˣ) :
    LinearThreeFourOuter.inversionAction kˣ (w ^ j) x = x := by
  rw [map_pow]
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ', MulAut.mul_apply, ih, inversionAction_eq,
      ite_eq_left_iff.mpr (fun h => absurd hw h)]

theorem outL34_cases {u v : OutL34 k} (hu3 : u ^ 3 = 1) (hu1 : u ≠ 1)
    (hv : ∃ m, orderOf v = 2 ^ m) (hvu : v * u = u * v) :
    v = 1 ∨ v = ⟨1, (Multiplicative.ofAdd 1, Multiplicative.ofAdd 1)⟩ := by
  have hk3 : ∀ x : kˣ, x ^ 3 = 1 := fun x => LinearThreeFourOuter.units_pow_three hk x
  have hwr : ∀ w : Multiplicative (ZMod 2) × Multiplicative (ZMod 2), w * w = 1 := by
    rintro ⟨a, b⟩
    refine Prod.ext ?_ ?_ <;>
      exact Multiplicative.toAdd.injective (by simp [CharTwo.add_self_eq_zero])
  have hr : u.right = 1 := by
    have h3 := congrArg SemidirectProduct.right hu3
    rw [SemidirectProduct.one_right, pow_three, SemidirectProduct.mul_right,
      SemidirectProduct.mul_right, hwr, mul_one] at h3
    exact h3
  have hl : u.left ≠ 1 := fun h => hu1 (SemidirectProduct.ext h hr)
  have hfix : LinearThreeFourOuter.inversionAction kˣ v.right u.left = u.left := by
    have h := congrArg SemidirectProduct.left hvu
    rw [SemidirectProduct.mul_left, SemidirectProduct.mul_left, hr, map_one, MulAut.one_apply,
      mul_comm u.left] at h
    exact mul_left_cancel h
  have hw : Multiplicative.toAdd v.right.1 + Multiplicative.toAdd v.right.2 = 0 := by
    by_contra hne
    rw [inversionAction_eq, ite_eq_right_iff.mpr (fun h => absurd h hne)] at hfix
    apply hl
    have h2 : u.left ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 1 [← hfix]
      exact inv_mul_cancel _
    have h3 := hk3 u.left
    calc u.left = u.left ^ 3 * (u.left ^ 2)⁻¹ := by group
      _ = 1 := by rw [h2, h3, inv_one, one_mul]
  have hpow : ∀ j : ℕ, (v ^ j).left = v.left ^ j ∧ (v ^ j).right = v.right ^ j := by
    intro j
    induction j with
    | zero => exact ⟨by rw [pow_zero, pow_zero, SemidirectProduct.one_left],
        by rw [pow_zero, pow_zero, SemidirectProduct.one_right]⟩
    | succ j ih =>
      refine ⟨?_, ?_⟩
      · rw [pow_succ, SemidirectProduct.mul_left, ih.1, ih.2,
          inversionAction_pow_left _ hw, pow_succ]
      · rw [pow_succ, SemidirectProduct.mul_right, ih.2, pow_succ]
  obtain ⟨m, hm⟩ := hv
  have hvl : v.left = 1 := by
    have h1 : v ^ 2 ^ m = 1 := by rw [← hm, pow_orderOf_eq_one]
    have h2 : v.left ^ 2 ^ m = 1 := by
      rw [← (hpow _).1, h1, SemidirectProduct.one_left]
    have h3 : orderOf v.left ∣ Nat.gcd (2 ^ m) 3 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one (hk3 _))
    have hg : Nat.gcd (2 ^ m) 3 = 1 := Nat.Coprime.pow_left _ (by norm_num)
    rw [hg] at h3
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  obtain ⟨⟨a, b⟩, hvr⟩ : ∃ w, v.right = w := ⟨_, rfl⟩
  rw [hvr] at hw
  have hab : Multiplicative.toAdd a = Multiplicative.toAdd b := by
    have := hw
    simp only at this
    rw [← CharTwo.add_eq_zero]
    exact this
  rcases LinearThreeFourOuter.zmod_two_cases (Multiplicative.toAdd a) with ha | ha
  · left
    refine SemidirectProduct.ext hvl ?_
    rw [hvr, SemidirectProduct.one_right]
    refine Prod.ext ?_ ?_
    · exact Multiplicative.toAdd.injective (by rw [ha]; rfl)
    · exact Multiplicative.toAdd.injective (by rw [← hab, ha]; rfl)
  · right
    refine SemidirectProduct.ext hvl ?_
    rw [hvr]
    refine Prod.ext ?_ ?_
    · exact Multiplicative.toAdd.injective (by rw [ha]; rfl)
    · exact Multiplicative.toAdd.injective (by rw [← hab, ha]; rfl)

theorem mem_projUnitriangular_of_two_pow {x : projUpperTriangular 3 k} {m : ℕ}
    (hx : x ^ 2 ^ m = 1) : (x : projectiveSL 3 k) ∈ projUnitriangular 3 k := by
  rw [← chiP_eq_one_iff hk]
  have h1 : chiP x ^ 2 ^ m = 1 := by rw [← map_pow, hx, map_one]
  have h2 : orderOf (chiP x) ∣ Nat.gcd (2 ^ m) 3 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one (unit_pow_three hk _))
  rw [Nat.Coprime.pow_left _ (by norm_num : Nat.Coprime 2 3)] at h2
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h2)

omit hk in
@[expose] def w0M : Matrix (Fin 3) (Fin 3) k := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

omit hk in
theorem w0M_mul_self : (w0M : Matrix (Fin 3) (Fin 3) k) * w0M = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [w0M, Matrix.mul_apply, Fin.sum_univ_three]

omit hk in
@[expose] def w0GL : GL (Fin 3) k := ⟨w0M, w0M, w0M_mul_self, w0M_mul_self⟩

omit hk in
theorem w0M_conj_apply (M : Matrix (Fin 3) (Fin 3) k) (i j : Fin 3) :
    (((w0M : Matrix (Fin 3) (Fin 3) k) * M * (w0M : Matrix (Fin 3) (Fin 3) k)) :
      Matrix (Fin 3) (Fin 3) k) i j = M (Fin.rev i) (Fin.rev j) := by
  fin_cases i <;> fin_cases j <;>
    simp [w0M, Matrix.mul_apply, Fin.sum_univ_three, vecMul, dotProduct]

theorem det_w0GL : GeneralLinearGroup.det (w0GL : GL (Fin 3) k) = 1 := by
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply]
  show Matrix.det (w0M : Matrix (Fin 3) (Fin 3) k) = 1
  rw [Matrix.det_fin_three]
  simp [w0M, CharTwo.neg_eq]

section GraphField

variable {σ : k ≃+* k} (hσ : ∀ a, σ a = a ^ 2)
include hσ

omit hk hσ in
theorem alpha0_proj (h : SpecialLinearGroup (Fin 3) k) :
    LinearThreeFourOuter.nf σ w0GL 1 1 (proj 3 k h) =
      proj 3 k (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 k w0GL
        (SpecialLinearGroup.map σ.toRingHom (h⁻¹).transpose)) := by
  simp only [LinearThreeFourOuter.nf, LinearThreeFourOuter.val_one_two, pow_one, MulAut.mul_apply,
    dualAut_proj, fieldAut_proj, conjAut_proj]

omit hk hσ in
theorem alpha0_matrix (h : SpecialLinearGroup (Fin 3) k) (i j : Fin 3) :
    ((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 k w0GL
        (SpecialLinearGroup.map σ.toRingHom (h⁻¹).transpose) : SpecialLinearGroup (Fin 3) k) :
      Matrix (Fin 3) (Fin 3) k) i j =
      σ (((h⁻¹ : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) (Fin.rev j)
        (Fin.rev i)) := by
  rw [coe_slConjugation]
  have hw : ((w0GL⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = w0M := rfl
  rw [hw]
  show (((w0M : Matrix (Fin 3) (Fin 3) k) * _ * (w0M : Matrix (Fin 3) (Fin 3) k)) :
    Matrix (Fin 3) (Fin 3) k) i j = _
  rw [w0M_conj_apply]
  show σ ((((h⁻¹ : SpecialLinearGroup (Fin 3) k).transpose : SpecialLinearGroup (Fin 3) k) :
    Matrix (Fin 3) (Fin 3) k) (Fin.rev i) (Fin.rev j)) = _
  rw [SpecialLinearGroup.coe_transpose, Matrix.transpose_apply]

omit hk hσ in
theorem alpha0_upper {h : SpecialLinearGroup (Fin 3) k} (hh : h ∈ upperTriangular 3 k) :
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 k w0GL
      (SpecialLinearGroup.map σ.toRingHom (h⁻¹).transpose) ∈ upperTriangular 3 k := by
  intro i j hij
  have hU := coe_inv_isUpperTriangular (mem_upperTriangular_iff_isUpperTriangular.mp hh)
  have h0 : ((h⁻¹ : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) (Fin.rev j)
      (Fin.rev i) = 0 := hU (Fin.rev_lt_rev.mpr hij)
  rw [alpha0_matrix, h0, map_zero]

omit hk hσ in
theorem alpha0_unitriangular {h : SpecialLinearGroup (Fin 3) k} (hh : h ∈ unitriangular 3 k) :
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 k w0GL
      (SpecialLinearGroup.map σ.toRingHom (h⁻¹).transpose) ∈ unitriangular 3 k := by
  refine ⟨alpha0_upper (unitriangular_le_upperTriangular 3 k hh), fun i => ?_⟩
  rw [alpha0_matrix, ((unitriangular 3 k).inv_mem hh).2, map_one]

omit hk hσ in
theorem alpha0_mem_projUpperTriangular {x : projectiveSL 3 k}
    (hx : x ∈ projUpperTriangular 3 k) :
    LinearThreeFourOuter.nf σ w0GL 1 1 x ∈ projUpperTriangular 3 k := by
  obtain ⟨h, hh, rfl⟩ := hx
  rw [alpha0_proj]
  exact ⟨_, alpha0_upper hh, rfl⟩

omit hk hσ in
theorem alpha0_mem_projUnitriangular {x : projectiveSL 3 k}
    (hx : x ∈ projUnitriangular 3 k) :
    LinearThreeFourOuter.nf σ w0GL 1 1 x ∈ projUnitriangular 3 k := by
  obtain ⟨h, hh, rfl⟩ := hx
  rw [alpha0_proj]
  exact ⟨_, alpha0_unitriangular hh, rfl⟩

omit hk in
theorem chiP_alpha0 (x : projUpperTriangular 3 k) :
    chiP (⟨LinearThreeFourOuter.nf σ w0GL 1 1 x, alpha0_mem_projUpperTriangular x.2⟩ :
      projUpperTriangular 3 k) = chiP x ^ 2 := by
  obtain ⟨g, rfl⟩ := projB_surjective x
  have hU := mem_upperTriangular_iff_isUpperTriangular.mp g.2
  have he : (⟨LinearThreeFourOuter.nf σ w0GL 1 1 (projB g),
      alpha0_mem_projUpperTriangular (projB g).2⟩ : projUpperTriangular 3 k) =
      projB ⟨_, alpha0_upper (σ := σ) g.2⟩ := by
    apply Subtype.ext
    show LinearThreeFourOuter.nf σ w0GL 1 1 (proj 3 k (g : SpecialLinearGroup (Fin 3) k)) = _
    exact alpha0_proj _
  rw [he, chiP_projB, chiP_projB]
  apply Units.ext
  rw [val_chiB, Units.val_pow_eq_pow_val, val_chiB, alpha0_matrix, alpha0_matrix]
  have h0 := coe_inv_apply_self_of_isUpperTriangular hU 0
  have h2 := coe_inv_apply_self_of_isUpperTriangular hU 2
  have e0 : ((g⁻¹ : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) 0 0 =
      (((g : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) 0 0)⁻¹ :=
    eq_inv_of_mul_eq_one_right h0
  have e2 : ((g⁻¹ : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) 2 2 =
      (((g : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) 2 2)⁻¹ :=
    eq_inv_of_mul_eq_one_right h2
  have r0 : (Fin.rev (0 : Fin 3)) = 2 := rfl
  have r2 : (Fin.rev (2 : Fin 3)) = 0 := rfl
  rw [r0, r2, hσ, hσ, e0, e2, ← inv_pow, inv_inv]
  ring

end GraphField

omit hk in
theorem map_projUnitriangular_eq [Finite k] {β : MulAut (projectiveSL 3 k)}
    (hβ : ∀ x ∈ projUnitriangular 3 k, β x ∈ projUnitriangular 3 k) :
    (projUnitriangular 3 k).map β.toMonoidHom = projUnitriangular 3 k := by
  have hle : (projUnitriangular 3 k).map β.toMonoidHom ≤ projUnitriangular 3 k := by
    rintro _ ⟨x, hx, rfl⟩
    exact hβ x hx
  exact Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective β.injective).ge

theorem eq_conj_of_twoAut {α δ : MulAut (projectiveSL 3 k)} (hα : ∃ m : ℕ, α ^ 2 ^ m = 1)
    (hαU : (projUnitriangular 3 k).map α.toMonoidHom = projUnitriangular 3 k)
    (hδ3 : δ ^ 3 = 1)
    (hδ : δ ∉ (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range)
    (hαδ : ∃ m : ℕ, (α * δ * α⁻¹ * δ⁻¹) ^ 2 ^ m = 1) {b : projectiveSL 3 k}
    (hb : b ∈ projUpperTriangular 3 k) (hbU : b ∉ projUnitriangular 3 k)
    (hαb : α b * b⁻¹ ∈ projUnitriangular 3 k) :
    ∃ x ∈ projUnitriangular 3 k, α = MulAut.conj x := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσ : ∀ a, frobeniusEquiv k 2 a = a ^ 2 := fun a => frobeniusEquiv_apply k 2 a
  obtain ⟨Ψ, hΨ⟩ := LinearThreeFourOuter.exists_outerHom hσ hk
  have hker := LinearThreeFourOuter.ker_eq_range_conj hσ hk hΨ
  have hNU := normalizer_projUnitriangular (n := 3) (K := k) 2
  have hu3 : Ψ δ ^ 3 = 1 := by rw [← map_pow, hδ3, map_one]
  have hu1 : Ψ δ ≠ 1 := fun h1 => hδ (hker ▸ MonoidHom.mem_ker.mpr h1)
  have hcomm : Ψ α * Ψ δ = Ψ δ * Ψ α := by
    obtain ⟨m, hm⟩ := hαδ
    set c := Ψ α * Ψ δ * (Ψ α)⁻¹ * (Ψ δ)⁻¹ with hc
    have hc2 : c ^ 2 ^ m = 1 := by
      rw [hc, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_pow, hm, map_one]
    have hcr : c.right = 1 := by
      rw [hc, SemidirectProduct.mul_right, SemidirectProduct.mul_right,
        SemidirectProduct.mul_right, SemidirectProduct.inv_right, SemidirectProduct.inv_right,
        mul_comm (Ψ α).right (Ψ δ).right]
      group
    have hcl : c = SemidirectProduct.inl c.left := SemidirectProduct.ext rfl hcr
    have hc3 : c ^ 3 = 1 := by
      rw [hcl, ← map_pow, LinearThreeFourOuter.units_pow_three hk, map_one]
    have hord : orderOf c ∣ Nat.gcd (2 ^ m) 3 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hc2) (orderOf_dvd_of_pow_eq_one hc3)
    rw [Nat.Coprime.pow_left _ (by norm_num : Nat.Coprime 2 3)] at hord
    have hc1 : c = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hord)
    rw [hc, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hc1
    exact hc1
  have hv : ∃ j, orderOf (Ψ α) = 2 ^ j := by
    obtain ⟨m, hm⟩ := hα
    have h1 : Ψ α ^ 2 ^ m = 1 := by rw [← map_pow, hm, map_one]
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h1)
    exact ⟨j, hj⟩
  rcases outL34_cases hk hu3 hu1 hv hcomm with h1 | h1
  ·
    obtain ⟨x, hx⟩ : α ∈ (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range :=
      hker ▸ MonoidHom.mem_ker.mpr h1
    refine ⟨x, ?_, hx.symm⟩
    have hxB : x ∈ projUpperTriangular 3 k := by
      rw [← hNU, Subgroup.mem_normalizer_iff_map_conj_eq]
      show (projUnitriangular 3 k).map (MulAut.conj x).toMonoidHom = _
      rw [hx]
      exact hαU
    obtain ⟨m, hm⟩ := hα
    have hxm : x ^ 2 ^ m = 1 := by
      apply CFSG.RankThree.PartTwo.KFacts.L34.conj_injective hk
      rw [map_pow, hx, hm, map_one]
    exact mem_projUnitriangular_of_two_pow hk (x := ⟨x, hxB⟩) (m := m)
      (Subtype.ext (by simpa using hxm))
  ·
    exfalso
    set α₀ := LinearThreeFourOuter.nf (frobeniusEquiv k 2) w0GL 1 1 with hα₀
    have hΨ0 : Ψ α₀ = Ψ α := by
      rw [h1, hα₀, hΨ, det_w0GL hk]
    obtain ⟨g, hg⟩ : α * α₀⁻¹ ∈
        (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hΨ0, mul_inv_cancel]
    have hαg : α = MulAut.conj g * α₀ := by rw [hg, inv_mul_cancel_right]
    have hα₀U : (projUnitriangular 3 k).map α₀.toMonoidHom = projUnitriangular 3 k :=
      map_projUnitriangular_eq (fun x hx => alpha0_mem_projUnitriangular hx)
    have hgB : g ∈ projUpperTriangular 3 k := by
      rw [← hNU, Subgroup.mem_normalizer_iff_map_conj_eq]
      show (projUnitriangular 3 k).map (MulAut.conj g).toMonoidHom = _
      rw [hg]
      calc (projUnitriangular 3 k).map (α * α₀⁻¹).toMonoidHom
          = ((projUnitriangular 3 k).map α₀⁻¹.toMonoidHom).map α.toMonoidHom := by
            rw [Subgroup.map_map]; rfl
        _ = (((projUnitriangular 3 k).map α₀.toMonoidHom).map α₀⁻¹.toMonoidHom).map
              α.toMonoidHom := by rw [hα₀U]
        _ = projUnitriangular 3 k := by
            rw [Subgroup.map_map, Subgroup.map_map]
            convert hαU using 2
            ext x
            simp
    have hα0b : α₀ b ∈ projUpperTriangular 3 k := alpha0_mem_projUpperTriangular hb
    have hmem : α b * b⁻¹ ∈ projUpperTriangular 3 k := by
      rw [hαg, MulAut.mul_apply, MulAut.conj_apply]
      exact (projUpperTriangular 3 k).mul_mem ((projUpperTriangular 3 k).mul_mem
        ((projUpperTriangular 3 k).mul_mem hgB hα0b) ((projUpperTriangular 3 k).inv_mem hgB))
        ((projUpperTriangular 3 k).inv_mem hb)
    have hsub : (⟨α b * b⁻¹, hmem⟩ : projUpperTriangular 3 k) =
        ⟨g, hgB⟩ * ⟨α₀ b, hα0b⟩ * (⟨g, hgB⟩ : projUpperTriangular 3 k)⁻¹ *
          (⟨b, hb⟩ : projUpperTriangular 3 k)⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hαg, MulAut.mul_apply, MulAut.conj_apply]
    have hχ1 : chiP (⟨α b * b⁻¹, hmem⟩ : projUpperTriangular 3 k) = 1 :=
      (chiP_eq_one_iff hk _).mpr hαb
    have hχa : chiP (⟨α₀ b, hα0b⟩ : projUpperTriangular 3 k) =
        chiP (⟨b, hb⟩ : projUpperTriangular 3 k) ^ 2 :=
      chiP_alpha0 hσ ⟨b, hb⟩
    rw [hsub, map_mul, map_mul, map_mul, map_inv, map_inv, hχa] at hχ1
    have hχb : chiP (⟨b, hb⟩ : projUpperTriangular 3 k) = 1 := by
      rw [← hχ1, mul_comm (chiP _) (chiP _ ^ 2)]
      group
    exact hbU ((chiP_eq_one_iff hk _).mp hχb)

end CFSG.Quasithin.H13.KGL34P
