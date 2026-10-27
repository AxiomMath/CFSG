module

public import CFSG.RankThree.PartTwo.Sec21.Item226Eigen
public import CFSG.RankThree.PartTwo.Sec21.MonomialCoords

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo Matrix
open CFSG.Assembly (IsElemAbelian)

variable {G : Type*} [Group G] {A : Subgroup G}

@[expose] noncomputable def glEquiv4 :
    GL (Fin 4) (ZMod 3) ≃* ((Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3)) :=
  Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 3) (Fin 4 → ZMod 3))

theorem glEquiv4_apply (g : GL (Fin 4) (ZMod 3)) (v : Fin 4 → ZMod 3) :
    glEquiv4 g v = (g : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ v := rfl

@[expose] noncomputable def coordLin4 (f : Multiplicative (Fin 4 → ZMod 3) ≃* A) :
    MulAut A →* ((Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3)) :=
  @Sec12.coordHom G _ A (Fin 4 → ZMod 3) _ (Pi.Function.module _ _ _) f

theorem coordLin4_apply (f : Multiplicative (Fin 4 → ZMod 3) ≃* A) (φ : MulAut A)
    (v : Fin 4 → ZMod 3) :
    coordLin4 f φ v = Multiplicative.toAdd (f.symm (φ (f (Multiplicative.ofAdd v)))) := rfl

theorem coordLin4_injective (f : Multiplicative (Fin 4 → ZMod 3) ≃* A) :
    Function.Injective (coordLin4 f) :=
  @Sec12.coordHom_injective G _ A (Fin 4 → ZMod 3) _ (Pi.Function.module _ _ _) f

@[expose] noncomputable def coordGL4 (f : Multiplicative (Fin 4 → ZMod 3) ≃* A) :
    MulAut A →* GL (Fin 4) (ZMod 3) :=
  glEquiv4.symm.toMonoidHom.comp (coordLin4 f)

theorem coordGL4_mulVec (f : Multiplicative (Fin 4 → ZMod 3) ≃* A) (φ : MulAut A)
    (v : Fin 4 → ZMod 3) :
    ((coordGL4 f φ : GL (Fin 4) (ZMod 3)) : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ v =
      coordLin4 f φ v := by
  rw [← glEquiv4_apply, coordGL4, MonoidHom.coe_comp, Function.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]

theorem coordGL4_injective (f : Multiplicative (Fin 4 → ZMod 3) ≃* A) :
    Function.Injective (coordGL4 f) :=
  glEquiv4.symm.injective.comp (coordLin4_injective f)

theorem coordGL4_eq_of_basis (f : Multiplicative (Fin 4 → ZMod 3) ≃* A) (φ : MulAut A)
    (M : Matrix (Fin 4) (Fin 4) (ZMod 3))
    (h : ∀ j, φ (f (Multiplicative.ofAdd (Pi.single j 1))) =
      f (Multiplicative.ofAdd (M.col j))) :
    ((coordGL4 f φ : GL (Fin 4) (ZMod 3)) : Matrix (Fin 4) (Fin 4) (ZMod 3)) = M := by
  ext i j
  have h1 := congrFun (coordGL4_mulVec f φ (Pi.single j 1)) i
  rw [mulVec_single_one, coordLin4_apply, h j, MulEquiv.symm_apply_apply, toAdd_ofAdd] at h1
  exact h1

theorem card_commOf_eq_card_range4 (hA : IsMulCommutative A)
    (f : Multiplicative (Fin 4 → ZMod 3) ≃* A) (φ : MulAut A) :
    Nat.card (commOf φ) = Nat.card (Set.range fun v : Fin 4 → ZMod 3 =>
      (((coordGL4 f φ : GL (Fin 4) (ZMod 3)) : Matrix (Fin 4) (Fin 4) (ZMod 3)) - 1) *ᵥ v) := by
  refine (@card_commOf_eq_range G _ A hA (Fin 4 → ZMod 3) _ (Pi.Function.module _ _ _) f
    φ).trans ?_
  have h1 : ∀ w : Fin 4 → ZMod 3,
      (((coordGL4 f φ : GL (Fin 4) (ZMod 3)) : Matrix (Fin 4) (Fin 4) (ZMod 3)) - 1) *ᵥ w =
        coordLin4 f φ w - w := by
    intro w
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, coordGL4_mulVec]
  simp only [h1]
  rfl

@[expose] def matX : Matrix (Fin 4) (Fin 4) (ZMod 3) := Matrix.diagonal ![1, 1, 2, 2]

@[expose] def matY : Matrix (Fin 4) (Fin 4) (ZMod 3) := Matrix.diagonal ![1, 2, 1, 2]

@[expose] def matS : Matrix (Fin 4) (Fin 4) (ZMod 3) :=
  !![1, 0, 0, 0; 0, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 0]

@[expose] def matR : Matrix (Fin 4) (Fin 4) (ZMod 3) :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 2; 0, 0, 2, 0]

theorem eq_matR_of_shape : ∀ a b c d : ZMod 3,
    (!![a, 0, 0, 0; 0, b, 0, 0; 0, 0, 0, c; 0, 0, d, 0] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ
        Pi.single 0 1 = Pi.single 0 1 →
    (!![a, 0, 0, 0; 0, b, 0, 0; 0, 0, 0, c; 0, 0, d, 0] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *
        !![a, 0, 0, 0; 0, b, 0, 0; 0, 0, 0, c; 0, 0, d, 0] = 1 →
    (Finset.univ.image fun v : Fin 4 → ZMod 3 =>
        ((!![a, 0, 0, 0; 0, b, 0, 0; 0, 0, 0, c; 0, 0, d, 0] :
          Matrix (Fin 4) (Fin 4) (ZMod 3)) - 1) *ᵥ v).card = 3 →
    (!![a, 0, 0, 0; 0, b, 0, 0; 0, 0, 0, c; 0, 0, d, 0] * matS) *
        (!![a, 0, 0, 0; 0, b, 0, 0; 0, 0, 0, c; 0, 0, d, 0] * matS) ≠ 1 →
    (!![a, 0, 0, 0; 0, b, 0, 0; 0, 0, 0, c; 0, 0, d, 0] : Matrix (Fin 4) (Fin 4) (ZMod 3)) =
      matR := by
  decide +kernel

section Basis

variable {P : Type*} [CommGroup P]

theorem pow_mod_three_of {u : P} (hu : u ^ 3 = 1) (n : ℕ) : u ^ (n % 3) = u ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n 3, pow_add, pow_mul, hu, one_pow, mul_one]

theorem pow_val_add_of {u : P} (hu : u ^ 3 = 1) (k l : ZMod 3) :
    u ^ (k + l).val = u ^ k.val * u ^ l.val := by
  rw [ZMod.val_add, pow_mod_three_of hu, pow_add]

theorem pow_val_eq_one_iff {u : P} (hu : u ^ 3 = 1) (hu1 : u ≠ 1) (k : ZMod 3) :
    u ^ k.val = 1 ↔ k = 0 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf u = 3 := orderOf_eq_prime hu hu1
  rw [← orderOf_dvd_iff_pow_eq_one, hord, ← ZMod.val_eq_zero]
  have := ZMod.val_lt k
  omega

theorem pow_two_eq_inv_of {u : P} (hu : u ^ 3 = 1) : u ^ 2 = u⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hu])

@[expose] def basisHom (c v₁ v₂ v₃ : P) (hc : c ^ 3 = 1) (h₁ : v₁ ^ 3 = 1) (h₂ : v₂ ^ 3 = 1)
    (h₃ : v₃ ^ 3 = 1) : Multiplicative (Fin 4 → ZMod 3) →* P where
  toFun n := c ^ (Multiplicative.toAdd n 0).val * v₁ ^ (Multiplicative.toAdd n 1).val *
    v₂ ^ (Multiplicative.toAdd n 2).val * v₃ ^ (Multiplicative.toAdd n 3).val
  map_one' := by simp
  map_mul' n m := by
    simp only [toAdd_mul, Pi.add_apply, pow_val_add_of hc, pow_val_add_of h₁, pow_val_add_of h₂,
      pow_val_add_of h₃]
    apply Additive.ofMul.injective
    simp only [ofMul_mul]
    abel

theorem basisHom_apply (c v₁ v₂ v₃ : P) (hc : c ^ 3 = 1) (h₁ : v₁ ^ 3 = 1) (h₂ : v₂ ^ 3 = 1)
    (h₃ : v₃ ^ 3 = 1) (w : Fin 4 → ZMod 3) :
    basisHom c v₁ v₂ v₃ hc h₁ h₂ h₃ (Multiplicative.ofAdd w) =
      c ^ (w 0).val * v₁ ^ (w 1).val * v₂ ^ (w 2).val * v₃ ^ (w 3).val := rfl

end Basis

section Construction

variable {P : Type*} [CommGroup P]

theorem eq_of_mul_self_eq_of_pow_three {u w : P} (hu : u ^ 3 = 1) (hw : w ^ 3 = 1)
    (h : u * u = w * w) : u = w := by
  have hu4 := mul_mul_mul_self_of_pow_three hu
  have hw4 := mul_mul_mul_self_of_pow_three hw
  calc u = (u * u) * (u * u) := by rw [← mul_assoc, hu4]
    _ = (w * w) * (w * w) := by rw [h]
    _ = w := by rw [← mul_assoc, hw4]

theorem exists_basis_four [Finite P] (hP3 : ∀ a : P, a ^ 3 = 1) (hcard : Nat.card P = 3 ^ 4)
    {x y σ : MulAut P} (hx2 : x * x = 1) (hy2 : y * y = 1) (hxy : x * y = y * x)
    (hσ3 : σ * σ * σ = 1) (hσx : σ * x = y * σ) (hσy : σ * y = x * y * σ) (hne : x ≠ y)
    {c : P} (hc1 : c ≠ 1) (hcx : x c = c) (hcy : y c = c) (hcσ : σ c = c) :
    ∃ F : Multiplicative (Fin 4 → ZMod 3) ≃* P, F (Multiplicative.ofAdd (Pi.single 0 1)) = c ∧
      ∀ j, x (F (Multiplicative.ofAdd (Pi.single j 1))) = F (Multiplicative.ofAdd (matX.col j)) ∧
        y (F (Multiplicative.ofAdd (Pi.single j 1))) = F (Multiplicative.ofAdd (matY.col j)) ∧
        σ (F (Multiplicative.ofAdd (Pi.single j 1))) = F (Multiplicative.ofAdd (matS.col j)) := by
  classical
  have hxx : ∀ a, x (x a) = a := fun a => by rw [← MulAut.mul_apply, hx2, MulAut.one_apply]
  have hyy : ∀ a, y (y a) = a := fun a => by rw [← MulAut.mul_apply, hy2, MulAut.one_apply]
  have hyxy : y * x * y = x := by rw [← hxy, mul_assoc, hy2, mul_one]
  have hxσ : x * σ = σ * (x * y) := by
    calc x * σ = y * x * y * σ := by rw [hyxy]
      _ = y * (x * y * σ) := by simp only [mul_assoc]
      _ = y * (σ * y) := by rw [hσy]
      _ = σ * x * y := by rw [← mul_assoc, ← hσx]
      _ = σ * (x * y) := by rw [mul_assoc]
  have hσa : ∀ a, σ (x a) = y (σ a) := fun a => by
    rw [← MulAut.mul_apply, hσx, MulAut.mul_apply]
  have hσb : ∀ a, σ (y a) = (x * y) (σ a) := fun a => by
    rw [← MulAut.mul_apply, hσy, MulAut.mul_apply]
  have hσc : ∀ a, σ ((x * y) a) = x (σ a) := fun a => by
    rw [← MulAut.mul_apply, ← hxσ, MulAut.mul_apply]
  have hσeig : ∀ a, eig₂ x y (σ a) = σ (eig₁ x y a) := fun a => by
    rw [eig₁_apply, eig₂_apply, map_mul, map_mul, map_mul, map_inv, map_inv, hσa, hσb, hσc]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  obtain ⟨a₀, ha₀⟩ : ∃ a, eig₁ x y a ≠ 1 := by
    by_contra hall
    push Not at hall
    have h2 : ∀ a, eig₂ x y a = 1 := fun a => by
      have := hσeig (σ⁻¹ a)
      rwa [MulAut.apply_inv_self, hall, map_one] at this
    apply hne
    have hz : x * y = 1 := MulEquiv.ext fun a => by
      have h := eig₁_mul_eig₂ (x := x) (y := y) a
      rw [hall, h2, one_mul, eq_comm, mul_inv_eq_one] at h
      exact eq_of_mul_self_eq_of_pow_three (hP3 _) (hP3 _) h.symm
    calc x = x * (y * y) := by rw [hy2, mul_one]
      _ = (x * y) * y := by rw [mul_assoc]
      _ = y := by rw [hz, one_mul]
  set v₁ := eig₁ x y a₀ with hv₁
  obtain ⟨h1x, h1y⟩ := apply_eig₁ hxx hyy hxy a₀
  rw [← hv₁] at h1x h1y
  set v₂ := σ v₁ with hv₂
  set v₃ := σ v₂ with hv₃
  have h2x : x v₂ = v₂⁻¹ := by
    rw [hv₂, ← MulAut.mul_apply, hxσ, MulAut.mul_apply, MulAut.mul_apply, h1y, map_inv, h1x,
      map_inv]
  have h2y : y v₂ = v₂ := by rw [hv₂, ← hσa, h1x]
  have h3x : x v₃ = v₃⁻¹ := by
    rw [hv₃, ← MulAut.mul_apply, hxσ, MulAut.mul_apply, MulAut.mul_apply, h2y, h2x, map_inv]
  have h3y : y v₃ = v₃⁻¹ := by rw [hv₃, ← hσa, h2x, map_inv]
  have hσ3' : σ v₃ = v₁ := by
    rw [hv₃, hv₂, ← MulAut.mul_apply, ← MulAut.mul_apply, hσ3, MulAut.one_apply]
  have hv₂1 : v₂ ≠ 1 := fun h => ha₀ (σ.injective (by rw [← hv₂, h, map_one]))
  have hv₃1 : v₃ ≠ 1 := fun h => hv₂1 (σ.injective (by rw [← hv₃, h, map_one]))
  set F₀ := basisHom c v₁ v₂ v₃ (hP3 c) (hP3 v₁) (hP3 v₂) (hP3 v₃) with hF₀
  have ec := eig_of_pp hP3 hcx hcy
  have e1 := eig_of_pm hP3 h1x h1y
  have e2 := eig_of_mp hP3 h2x h2y
  have e3 := eig_of_mm hP3 h3x h3y
  have hinj : Function.Injective F₀ := by
    rw [injective_iff_map_eq_one]
    intro n hn
    have hn' : F₀ (Multiplicative.ofAdd (Multiplicative.toAdd n)) = 1 := hn
    rw [basisHom_apply] at hn'
    have h0 := congrArg (eig₀ x y) hn'
    have h1 := congrArg (eig₁ x y) hn'
    have h2 := congrArg (eig₂ x y) hn'
    have h3 := congrArg (eig₃ x y) hn'
    simp only [map_mul, map_pow, map_one, ec.1, ec.2.1, ec.2.2.1, ec.2.2.2, e1.1, e1.2.1,
      e1.2.2.1, e1.2.2.2, e2.1, e2.2.1, e2.2.2.1, e2.2.2.2, e3.1, e3.2.1, e3.2.2.1, e3.2.2.2,
      one_pow, mul_one, one_mul] at h0 h1 h2 h3
    rw [pow_val_eq_one_iff (hP3 c) hc1] at h0
    rw [pow_val_eq_one_iff (hP3 v₁) ha₀] at h1
    rw [pow_val_eq_one_iff (hP3 v₂) hv₂1] at h2
    rw [pow_val_eq_one_iff (hP3 v₃) hv₃1] at h3
    apply Multiplicative.toAdd.injective
    ext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  have hbij : Function.Bijective F₀ := by
    have : Fintype P := Fintype.ofFinite P
    refine (Fintype.bijective_iff_injective_and_card F₀).mpr ⟨hinj, ?_⟩
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard, Nat.card_eq_fintype_card,
      Fintype.card_multiplicative, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  set F := MulEquiv.ofBijective F₀ hbij with hF
  have hFw : ∀ w : Fin 4 → ZMod 3, F (Multiplicative.ofAdd w) =
      c ^ (w 0).val * v₁ ^ (w 1).val * v₂ ^ (w 2).val * v₃ ^ (w 3).val := fun w => rfl
  have hv2sq : v₂ ^ 2 = v₂⁻¹ := pow_two_eq_inv_of (hP3 v₂)
  have hv3sq : v₃ ^ 2 = v₃⁻¹ := pow_two_eq_inv_of (hP3 v₃)
  have hv1sq : v₁ ^ 2 = v₁⁻¹ := pow_two_eq_inv_of (hP3 v₁)
  have hval0 : (0 : ZMod 3).val = 0 := rfl
  have hval1 : (1 : ZMod 3).val = 1 := rfl
  have hval2 : (2 : ZMod 3).val = 2 := rfl
  refine ⟨F, ?_, fun j => ?_⟩
  · rw [hFw]
    simp [hval0, hval1]
  · fin_cases j <;>
      simp [hFw, matX, matY, matS, Matrix.col, hval0, hval1, hval2, hcx, hcy, hcσ, h1x, h1y,
        h2x, h2y, h3x, h3y, hσ3', hv2sq, hv3sq, hv1sq, ← hv₂, ← hv₃]

end Construction

theorem entry_eq_zero_of_mul_diagonal {N : Matrix (Fin 4) (Fin 4) (ZMod 3)} {d e : Fin 4 → ZMod 3}
    (h : N * Matrix.diagonal d = Matrix.diagonal e * N) (i j : Fin 4) (hij : d j ≠ e i) :
    N i j = 0 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 := congrFun (congrFun h i) j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
  have h2 : (d j - e i) * N i j = 0 := by linear_combination h1
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (sub_eq_zero.mp h3) hij
  · exact h3

theorem natCard_range_eq_card_image (f : (Fin 4 → ZMod 3) → (Fin 4 → ZMod 3)) :
    Nat.card (Set.range f) = (Finset.univ.image f).card := by
  rw [Nat.card_eq_card_toFinset, Set.toFinset_range]

theorem exists_coord_four (hAe : IsElemAbelian 3 A) [Finite A] (hcard : Nat.card A = 3 ^ 4)
    {x y σ r : MulAut A} (hx2 : x * x = 1) (hy2 : y * y = 1) (hxy : x * y = y * x)
    (hσ3 : σ * σ * σ = 1) (hσx : σ * x = y * σ) (hσy : σ * y = x * y * σ) (hne : x ≠ y)
    (hrx : r * x = x * r) (hry : r * y = x * y * r) (hr2 : r * r = 1)
    (hrσ : r * σ * (r * σ) ≠ 1) (hrefl : Nat.card (commOf r) = 3)
    {c : A} (hc1 : c ≠ 1) (hcx : x c = c) (hcy : y c = c) (hcσ : σ c = c) (hcr : r c = c) :
    ∃ F : Multiplicative (Fin 4 → ZMod 3) ≃* A, F (Multiplicative.ofAdd (Pi.single 0 1)) = c ∧
      ((coordGL4 F x : GL (Fin 4) (ZMod 3)) : Matrix (Fin 4) (Fin 4) (ZMod 3)) = matX ∧
      ((coordGL4 F y : GL (Fin 4) (ZMod 3)) : Matrix (Fin 4) (Fin 4) (ZMod 3)) = matY ∧
      ((coordGL4 F σ : GL (Fin 4) (ZMod 3)) : Matrix (Fin 4) (Fin 4) (ZMod 3)) = matS ∧
      ((coordGL4 F r : GL (Fin 4) (ZMod 3)) : Matrix (Fin 4) (Fin 4) (ZMod 3)) = matR := by
  let _ : CommGroup A :=
    { (inferInstance : Group A) with mul_comm := fun a b => hAe.1.is_comm.comm a b }
  have hA3 : ∀ a : A, a ^ 3 = 1 := fun a => Subtype.ext (by simpa using hAe.2 a a.2)
  obtain ⟨F, hF0, hFj⟩ := exists_basis_four hA3 hcard hx2 hy2 hxy hσ3 hσx hσy hne hc1 hcx hcy
    hcσ
  have hX := coordGL4_eq_of_basis F x matX fun j => (hFj j).1
  have hY := coordGL4_eq_of_basis F y matY fun j => (hFj j).2.1
  have hS := coordGL4_eq_of_basis F σ matS fun j => (hFj j).2.2
  refine ⟨F, hF0, hX, hY, hS, ?_⟩
  set N := ((coordGL4 F r : GL (Fin 4) (ZMod 3)) : Matrix (Fin 4) (Fin 4) (ZMod 3)) with hN
  have hcoe : ∀ φ ψ : MulAut A,
      ((coordGL4 F (φ * ψ) : GL (Fin 4) (ZMod 3)) : Matrix (Fin 4) (Fin 4) (ZMod 3)) =
        (coordGL4 F φ : Matrix (Fin 4) (Fin 4) (ZMod 3)) * (coordGL4 F ψ : Matrix _ _ _) :=
    fun φ ψ => by rw [map_mul, Units.val_mul]
  have hNX : N * Matrix.diagonal ![1, 1, 2, 2] = Matrix.diagonal ![1, 1, 2, 2] * N := by
    have h := congrArg (fun φ => ((coordGL4 F φ : GL (Fin 4) (ZMod 3)) :
      Matrix (Fin 4) (Fin 4) (ZMod 3))) hrx
    simp only [hcoe, hX] at h
    exact h
  have hNY : N * Matrix.diagonal ![1, 2, 1, 2] = Matrix.diagonal ![1, 2, 2, 1] * N := by
    have h := congrArg (fun φ => ((coordGL4 F φ : GL (Fin 4) (ZMod 3)) :
      Matrix (Fin 4) (Fin 4) (ZMod 3))) hry
    simp only [hcoe, hX, hY] at h
    have hd : matX * matY = Matrix.diagonal ![1, 2, 2, 1] := by
      rw [matX, matY, Matrix.diagonal_mul_diagonal]
      congr 1
      ext i
      fin_cases i <;> rfl
    rw [hd] at h
    exact h
  have hshape : N = !![N 0 0, 0, 0, 0; 0, N 1 1, 0, 0; 0, 0, 0, N 2 3; 0, 0, N 3 2, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      first
        | rfl
        | exact entry_eq_zero_of_mul_diagonal hNX _ _ (by decide)
        | exact entry_eq_zero_of_mul_diagonal hNY _ _ (by decide)
  have hN0 : N *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
    rw [hN, coordGL4_mulVec, coordLin4_apply, hF0, hcr, ← hF0, MulEquiv.symm_apply_apply,
      toAdd_ofAdd]
  have hN2 : N * N = 1 := by
    rw [hN, ← hcoe, hr2, map_one, Units.val_one]
  have hN3 : (Finset.univ.image fun v : Fin 4 → ZMod 3 => (N - 1) *ᵥ v).card = 3 := by
    rw [← natCard_range_eq_card_image, ← card_commOf_eq_card_range4 hAe.1 F r]
    exact hrefl
  have hN4 : (N * matS) * (N * matS) ≠ 1 := by
    intro h
    apply hrσ
    apply coordGL4_injective F
    apply Units.ext
    rw [map_one, Units.val_one, hcoe, hcoe, hS, ← hN, h]
  rw [hshape] at hN0 hN2 hN3 hN4 ⊢
  exact eq_matR_of_shape _ _ _ _ hN0 hN2 hN3 hN4

end CFSG.RankThree.PartTwo.Sec21
