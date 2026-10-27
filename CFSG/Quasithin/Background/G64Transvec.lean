module

public import CFSG.GroupTheory.GLnTwoSplitting.Transvection
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Transvection

public section

namespace CFSG.Quasithin.G64

open Matrix Module CFSG.GroupTheory.GLnTwoSplitting

section Linear

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

theorem exists_conj_transvection {f f' : Dual (ZMod 2) E} {d d' : E} (h : f d = 0)
    (h' : f' d' = 0) (hf : f ≠ 0) (hf' : f' ≠ 0) (hd : d ≠ 0) (hd' : d' ≠ 0) :
    ∃ g : E ≃ₗ[ZMod 2] E,
      g * LinearEquiv.transvection h * g⁻¹ = LinearEquiv.transvection h' := by
  obtain ⟨g₁, he₁⟩ : ∃ g₁ : E ≃ₗ[ZMod 2] E, g₁ d = d' := by
    obtain ⟨f₁, d₁, h₁, he₁⟩ := exists_transvection_apply_eq hd hd'
    exact ⟨_, he₁⟩
  set φ : Dual (ZMod 2) E := f ∘ₗ (g₁.symm : E →ₗ[ZMod 2] E) with hφ
  have hφd' : φ d' = 0 := by
    rw [hφ, LinearMap.comp_apply, ← he₁]
    simp [h]
  have hφ0 : φ ≠ 0 := by
    intro h0
    apply hf
    ext x
    have := congrArg (fun ψ : Dual (ZMod 2) E => ψ (g₁ x)) h0
    simpa [hφ] using this
  obtain ⟨g₂, hg₂e, hg₂f⟩ := exists_comp_eq_of_apply_eq_zero hφ0 hf' hφd' h'
  refine ⟨g₂⁻¹ * g₁, LinearEquiv.ext fun x => ?_⟩
  have hg₂e' : g₂.symm d' = d' := by
    rw [LinearEquiv.symm_apply_eq]
    exact hg₂e.symm
  have hfx : f (g₁.symm (g₂ x)) = f' x := by
    have := congrArg (fun ψ : Dual (ZMod 2) E => ψ x) hg₂f
    simpa [hφ] using this
  rw [_root_.mul_inv_rev, inv_inv, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.coe_inv, LinearEquiv.coe_inv,
    transvection_apply h, transvection_apply h', map_add, map_smul, LinearEquiv.apply_symm_apply,
    he₁, map_add, map_smul, LinearEquiv.symm_apply_apply, hg₂e', hfx]

end Linear

variable {n : ℕ}

@[expose] noncomputable def glLin (n : ℕ) :
    GL (Fin n) (ZMod 2) ≃* ((Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2)) :=
  Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _)

theorem glLin_apply (x : GL (Fin n) (ZMod 2)) (v : Fin n → ZMod 2) :
    glLin n x v = (x : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v :=
  rfl

@[expose] def IsTransvecGL (x : GL (Fin n) (ZMod 2)) : Prop :=
  x ≠ 1 ∧ ∃ y : Fin n → ZMod 2, ∀ v : Fin n → ZMod 2,
    (x : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v - v = 0 ∨
      (x : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v - v = y

theorem IsTransvecGL.exists_eq {x : GL (Fin n) (ZMod 2)} (hx : IsTransvecGL x) :
    ∃ (f : Dual (ZMod 2) (Fin n → ZMod 2)) (y : Fin n → ZMod 2) (h : f y = 0),
      f ≠ 0 ∧ y ≠ 0 ∧ glLin n x = LinearEquiv.transvection h := by
  obtain ⟨hx1, y, hy⟩ := hx
  set M : Matrix (Fin n) (Fin n) (ZMod 2) := (x : Matrix (Fin n) (Fin n) (ZMod 2)) with hM
  have hy0 : y ≠ 0 := by
    intro hy0
    apply hx1
    apply Units.ext
    refine Matrix.ext_of_mulVec_single fun j => ?_
    rw [Units.val_one, Matrix.one_mulVec]
    rcases hy (Pi.single j 1) with h | h
    · exact sub_eq_zero.1 h
    · rw [hy0] at h
      exact sub_eq_zero.1 h
  obtain ⟨k, hk⟩ : ∃ k, y k ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hy0 (funext hcon)
  have hk1 : y k = 1 := zmod_two_eq_one_of_ne_zero hk
  set f : Dual (ZMod 2) (Fin n → ZMod 2) :=
    LinearMap.proj k ∘ₗ Matrix.toLin' (M - 1) with hf
  have hfv : ∀ v, f v = (M *ᵥ v - v) k := by
    intro v
    simp [hf]
  have hfy : ∀ v, M *ᵥ v - v = f v • y := by
    intro v
    rcases hy v with h | h
    · rw [hfv, h, Pi.zero_apply, zero_smul]
    · rw [hfv, h, hk1, one_smul]
  have hfy0 : f y = 0 := by
    by_contra hne
    have h1 := hfy y
    rw [zmod_two_eq_one_of_ne_zero hne, one_smul, sub_eq_iff_eq_add, two_add_self] at h1
    apply hy0
    have hinj : Function.Injective (glLin n x) := (glLin n x).injective
    apply hinj
    rw [glLin_apply, glLin_apply, ← hM, h1, Matrix.mulVec_zero]
  have hf0 : f ≠ 0 := by
    intro h0
    apply hx1
    apply Units.ext
    refine Matrix.ext_of_mulVec_single fun j => ?_
    have := hfy (Pi.single j 1)
    rw [h0, LinearMap.zero_apply, zero_smul, sub_eq_zero] at this
    rw [Units.val_one, Matrix.one_mulVec]
    exact this
  refine ⟨f, y, hfy0, hf0, hy0, LinearEquiv.ext fun v => ?_⟩
  rw [glLin_apply, transvection_apply, ← hM, ← hfy v]
  abel

theorem exists_conj_of_isTransvecGL {x x' : GL (Fin n) (ZMod 2)} (hx : IsTransvecGL x)
    (hx' : IsTransvecGL x') : ∃ g : GL (Fin n) (ZMod 2), g * x * g⁻¹ = x' := by
  obtain ⟨f, y, h, hf, hy, he⟩ := hx.exists_eq
  obtain ⟨f', y', h', hf', hy', he'⟩ := hx'.exists_eq
  obtain ⟨g, hg⟩ := exists_conj_transvection h h' hf hf' hy hy'
  refine ⟨(glLin n).symm g, (glLin n).injective ?_⟩
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, he, he', hg]

@[expose] def pathNext (i : Fin n) : Fin n :=
  if h : i.val + 1 < n then ⟨i.val + 1, h⟩ else ⟨0, Nat.zero_lt_of_lt i.isLt⟩

theorem pathNext_of_lt {i : Fin n} (h : i.val + 1 < n) : pathNext i = ⟨i.val + 1, h⟩ := by
  simp [pathNext, h]

theorem pathNext_of_not_lt {i : Fin n} (h : ¬ i.val + 1 < n) :
    pathNext i = ⟨0, Nat.zero_lt_of_lt i.isLt⟩ := by
  simp [pathNext, h]

theorem pathNext_ne (hn : 2 ≤ n) (i : Fin n) : i ≠ pathNext i := by
  intro h
  have := congrArg Fin.val h
  unfold pathNext at this
  split_ifs at this with h'
  · simp at this
  · simp only at this
    omega

@[expose] noncomputable def pathSL (hn : 2 ≤ n) (i : Fin n) : SpecialLinearGroup (Fin n) (ZMod 2) :=
  SpecialLinearGroup.transvection (pathNext_ne hn i) 1

theorem transvection_eq_of_eq {i j i' j' : Fin n} (hij : i ≠ j) (hij' : i' ≠ j') (hi : i = i')
    (hj : j = j') (c : ZMod 2) :
    SpecialLinearGroup.transvection hij c = SpecialLinearGroup.transvection hij' c := by
  subst hi hj
  rfl

theorem closure_pathSL (hn : 2 ≤ n) : Subgroup.closure (Set.range (pathSL hn)) = ⊤ := by
  set C := Subgroup.closure (Set.range (pathSL hn)) with hC
  have hcomm : ∀ {i j l : Fin n} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l),
      SpecialLinearGroup.transvection hij (1 : ZMod 2) ∈ C →
      SpecialLinearGroup.transvection hjl (1 : ZMod 2) ∈ C →
      SpecialLinearGroup.transvection hil (1 : ZMod 2) ∈ C := by
    intro i j l hij hjl hil h1 h2
    have := SpecialLinearGroup.commutatorElement_transvection hij hjl hil (1 : ZMod 2) 1
    rw [mul_one] at this
    rw [← this, commutatorElement_def]
    exact C.mul_mem (C.mul_mem (C.mul_mem h1 h2) (C.inv_mem h1)) (C.inv_mem h2)
  have hsucc : ∀ (i j : Fin n) (hij : i ≠ j), j.val = i.val + 1 →
      SpecialLinearGroup.transvection hij (1 : ZMod 2) ∈ C := by
    intro i j hij hj
    have hnext : pathNext i = j := by
      rw [pathNext_of_lt (by omega)]
      exact Fin.ext hj.symm
    have : SpecialLinearGroup.transvection hij (1 : ZMod 2) = pathSL hn i :=
      transvection_eq_of_eq hij (pathNext_ne hn i) rfl hnext.symm 1
    rw [this]
    exact Subgroup.subset_closure ⟨i, rfl⟩
  have hup : ∀ (d : ℕ) (i j : Fin n) (hij : i ≠ j), j.val = i.val + d + 1 →
      SpecialLinearGroup.transvection hij (1 : ZMod 2) ∈ C := by
    intro d
    induction d with
    | zero => intro i j hij hj; exact hsucc i j hij (by omega)
    | succ d ih =>
      intro i j hij hj
      set m : Fin n := ⟨i.val + d + 1, by omega⟩ with hm
      have him : i ≠ m := by
        intro h
        have := congrArg Fin.val h
        simp only [hm] at this
        omega
      have hmj : m ≠ j := by
        intro h
        have := congrArg Fin.val h
        simp only [hm] at this
        omega
      exact hcomm him hmj hij (ih i m him rfl) (hsucc m j hmj (by simp [hm]; omega))
  have hlt : ∀ (i j : Fin n) (hij : i ≠ j), i.val < j.val →
      SpecialLinearGroup.transvection hij (1 : ZMod 2) ∈ C := fun i j hij h =>
    hup (j.val - i.val - 1) i j hij (by omega)
  set top : Fin n := ⟨n - 1, by omega⟩ with htop
  set zero : Fin n := ⟨0, by omega⟩ with hzero
  have htz : top ≠ zero := by
    intro h
    have h1 : n - 1 = 0 := congrArg Fin.val h
    omega
  have htop0 : SpecialLinearGroup.transvection htz (1 : ZMod 2) ∈ C := by
    have hnext : pathNext top = zero := by
      rw [pathNext_of_not_lt (by simp only [htop]; omega)]
    have : SpecialLinearGroup.transvection htz (1 : ZMod 2) = pathSL hn top :=
      transvection_eq_of_eq htz (pathNext_ne hn top) rfl hnext.symm 1
    rw [this]
    exact Subgroup.subset_closure ⟨top, rfl⟩
  have hlast : ∀ (j : Fin n) (hj : top ≠ j),
      SpecialLinearGroup.transvection hj (1 : ZMod 2) ∈ C := by
    intro j hj
    by_cases hj0 : j = zero
    · subst hj0
      exact htop0
    · have hzj : zero ≠ j := Ne.symm hj0
      refine hcomm htz hzj hj htop0 (hlt zero j hzj ?_)
      have : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
      show 0 < j.val
      omega
  have hall : ∀ (i j : Fin n) (hij : i ≠ j),
      SpecialLinearGroup.transvection hij (1 : ZMod 2) ∈ C := by
    intro i j hij
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
    · exact hlt i j hij h
    · by_cases hi : i = top
      · subst hi
        exact hlast j hij
      · have hit : i ≠ top := hi
        have htj : top ≠ j := by
          intro e
          have h1 : n - 1 = j.val := congrArg Fin.val e
          have h2 := i.isLt
          omega
        refine hcomm hit htj hij (hlt i top hit ?_) (hlast j htj)
        have : i.val ≠ n - 1 := fun e => hi (Fin.ext e)
        have := i.isLt
        show i.val < n - 1
        omega
  rw [eq_top_iff, ← SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field,
    Subgroup.closure_le]
  rintro _ ⟨⟨i, j, hij, c⟩, rfl⟩
  rw [TransvectionStruct.toSpecialLinearGroup_mk]
  rcases zmod_two_eq_zero_or_one c with rfl | rfl
  · rw [SpecialLinearGroup.transvection_coeff_zero]
    exact C.one_mem
  · exact hall i j hij

theorem det_eq_one (x : GL (Fin n) (ZMod 2)) :
    (x : Matrix (Fin n) (Fin n) (ZMod 2)).det = 1 :=
  zmod_two_eq_one_of_ne_zero (x.isUnit.map Matrix.detMonoidHom).ne_zero

theorem range_toGL : (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) (ZMod 2) →* _).range =
    ⊤ := by
  rw [eq_top_iff]
  intro x _
  exact ⟨⟨x, det_eq_one x⟩, Units.ext rfl⟩

@[expose] noncomputable def pathGL (hn : 2 ≤ n) (i : Fin n) : GL (Fin n) (ZMod 2) :=
  SpecialLinearGroup.toGL (pathSL hn i)

theorem closure_pathGL (hn : 2 ≤ n) : Subgroup.closure (Set.range (pathGL hn)) = ⊤ := by
  have : Set.range (pathGL hn) = SpecialLinearGroup.toGL '' Set.range (pathSL hn) := by
    rw [← Set.range_comp]
    rfl
  rw [this, ← MonoidHom.map_closure, closure_pathSL hn, ← MonoidHom.range_eq_map, range_toGL]

theorem isTransvecGL_pathGL (hn : 2 ≤ n) (i : Fin n) : IsTransvecGL (pathGL hn i) := by
  have hne := pathNext_ne hn i
  have hcoe : ((pathGL hn i : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) =
      1 + Matrix.single i (pathNext i) 1 :=
    SpecialLinearGroup.transvection_coe hne 1
  have hmv : ∀ v : Fin n → ZMod 2,
      ((pathGL hn i : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v - v =
        v (pathNext i) • Pi.single i 1 := by
    intro v
    rw [hcoe, Matrix.add_mulVec, Matrix.one_mulVec, add_sub_cancel_left]
    funext l
    simp only [Matrix.mulVec, dotProduct, Matrix.single_apply, Pi.smul_apply, Pi.single_apply,
      smul_eq_mul]
    by_cases hl : l = i
    · subst hl
      simp
    · simp [hl, Ne.symm hl]
  refine ⟨?_, Pi.single i 1, fun v => ?_⟩
  · intro h1
    have h := hmv (Pi.single (pathNext i) 1)
    rw [h1, Units.val_one, Matrix.one_mulVec, sub_self, Pi.single_eq_same, one_smul] at h
    have := congrFun h i
    simp at this
  · rw [hmv]
    rcases zmod_two_eq_zero_or_one (v (pathNext i)) with h | h
    · left
      rw [h, zero_smul]
    · right
      rw [h, one_smul]

theorem exists_conj_closure_eq_top (hn : 2 ≤ n) {x : GL (Fin n) (ZMod 2)} (hx : IsTransvecGL x) :
    ∃ g : Fin n → GL (Fin n) (ZMod 2),
      Subgroup.closure (Set.range fun i => g i * x * (g i)⁻¹) = ⊤ := by
  choose g hg using fun i => exists_conj_of_isTransvecGL hx (isTransvecGL_pathGL hn i)
  refine ⟨g, ?_⟩
  have : (fun i => g i * x * (g i)⁻¹) = pathGL hn := funext hg
  rw [this, closure_pathGL hn]

end CFSG.Quasithin.G64
