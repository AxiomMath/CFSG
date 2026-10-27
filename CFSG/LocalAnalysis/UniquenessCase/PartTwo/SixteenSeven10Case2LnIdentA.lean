module

public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenDefs
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma5MultG
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.WeakClosure81
open scoped TensorProduct

@[expose] def s16c1610_b1 : ↥(CFSG.Quasithin.permCore 3) :=
  ⟨![1, 0, 1], by
    show ∑ i, (![1, 0, 1] : Fin 3 → ZMod 2) i = 0
    decide⟩

@[expose] def s16c1610_b2 : ↥(CFSG.Quasithin.permCore 3) :=
  ⟨![0, 1, 1], by
    show ∑ i, (![0, 1, 1] : Fin 3 → ZMod 2) i = 0
    decide⟩

@[expose] def s16c1610_permMat (σ : Equiv.Perm (Fin 3)) : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  Matrix.of fun i j =>
    (![![1, 0, 1], ![0, 1, 1]] : Fin 2 → Fin 3 → ZMod 2) j (σ⁻¹ (Fin.castSucc i))

@[expose] def s16c1610_slPermHom :
    Equiv.Perm (Fin 3) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) where
  toFun σ := ⟨s16c1610_permMat σ, by revert σ; decide +kernel⟩
  map_one' := Subtype.ext (by decide +kernel)
  map_mul' σ τ := Subtype.ext (by revert σ τ; decide +kernel)

theorem s16c1610_slPermHom_bijective : Function.Bijective s16c1610_slPermHom := by
  constructor
  · intro σ τ h
    have key : ∀ σ τ : Equiv.Perm (Fin 3),
        s16c1610_permMat σ = s16c1610_permMat τ → σ = τ := by
      decide +kernel
    exact key σ τ (congrArg Subtype.val h)
  · intro A
    have key : ∀ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2),
        ∃ σ : Equiv.Perm (Fin 3),
          s16c1610_permMat σ = (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) := by
      decide +kernel
    obtain ⟨σ, hσ⟩ := key A
    exact ⟨σ, Subtype.ext hσ⟩

@[expose] noncomputable def s16c1610_slPermEquiv :
    Equiv.Perm (Fin 3) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) :=
  MulEquiv.ofBijective s16c1610_slPermHom s16c1610_slPermHom_bijective

private theorem s16c1610_zmod_two_eq_one_of_ne_zero {a : ZMod 2} (ha : a ≠ 0) : a = 1 := by
  revert a
  decide +kernel

theorem s16c1610_toGL_bijective : Function.Bijective
    (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) →* GL (Fin 2) (ZMod 2)) := by
  refine ⟨Matrix.SpecialLinearGroup.toGL_injective, fun A => ?_⟩
  have hmul : (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) *
      ((A⁻¹ : GL (Fin 2) (ZMod 2)) : Matrix (Fin 2) (Fin 2) (ZMod 2)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 := congrArg Matrix.det hmul
  rw [Matrix.det_mul, Matrix.det_one] at h2
  have hunit : IsUnit (Matrix.det (A : Matrix (Fin 2) (Fin 2) (ZMod 2))) :=
    IsUnit.of_mul_eq_one _ h2
  have h1 : Matrix.det (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) = 1 :=
    s16c1610_zmod_two_eq_one_of_ne_zero hunit.ne_zero
  exact ⟨⟨A, h1⟩, by ext; rfl⟩

@[expose] noncomputable def s16c1610_permGL :
    Equiv.Perm (Fin 3) ≃* GL (Fin 2) (ZMod 2) :=
  s16c1610_slPermEquiv.trans
    (MulEquiv.ofBijective (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) →* GL (Fin 2) (ZMod 2))
      s16c1610_toGL_bijective)

@[simp] theorem s16c1610_permGL_coe (σ : Equiv.Perm (Fin 3)) :
    ((s16c1610_permGL σ : GL (Fin 2) (ZMod 2)) : Matrix (Fin 2) (Fin 2) (ZMod 2)) =
      s16c1610_permMat σ := rfl

@[expose] def s16c1610_pi0 : ↥(CFSG.Quasithin.permCore 3) →ₗ[ZMod 2] (ZMod 2) where
  toFun x := (x : Fin 3 → ZMod 2) 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[expose] def s16c1610_pi1 : ↥(CFSG.Quasithin.permCore 3) →ₗ[ZMod 2] (ZMod 2) where
  toFun x := (x : Fin 3 → ZMod 2) 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem s16c1610_zmod_two_sum_zero (p0 p1 p2 : ZMod 2) (h : p0 + p1 + p2 = 0) :
    p2 = p0 + p1 := by
  revert p0 p1 p2
  decide +kernel

theorem s16c1610_pi0_smul_b1_add_pi1_smul_b2 (x : ↥(CFSG.Quasithin.permCore 3)) :
    s16c1610_pi0 x • s16c1610_b1 + s16c1610_pi1 x • s16c1610_b2 = x := by
  apply Subtype.ext
  funext i
  have hsum : ∑ j, (x : Fin 3 → ZMod 2) j = 0 := x.2
  rw [Fin.sum_univ_three] at hsum
  have h2 : (x : Fin 3 → ZMod 2) 2 = (x : Fin 3 → ZMod 2) 0 + (x : Fin 3 → ZMod 2) 1 :=
    s16c1610_zmod_two_sum_zero _ _ _ hsum
  fin_cases i <;>
    simp [s16c1610_pi0, s16c1610_pi1, s16c1610_b1, s16c1610_b2, h2]

@[expose] noncomputable def s16c1610_tensorEquiv (m : ℕ) :
    ((Fin m → ZMod 2) × (Fin m → ZMod 2)) ≃ₗ[ZMod 2]
      (↥(CFSG.Quasithin.permCore 3) ⊗[ZMod 2] (Fin m → ZMod 2)) where
  toFun p := s16c1610_b1 ⊗ₜ[ZMod 2] p.1 + s16c1610_b2 ⊗ₜ[ZMod 2] p.2
  map_add' p q := by
    obtain ⟨x, y⟩ := p
    obtain ⟨x', y'⟩ := q
    simp only [Prod.fst_add, Prod.snd_add, TensorProduct.tmul_add, TensorProduct.add_tmul]
    abel
  map_smul' c p := by
    obtain ⟨x, y⟩ := p
    simp only [Prod.smul_fst, Prod.smul_snd, TensorProduct.tmul_smul, smul_add,
      TensorProduct.smul_tmul, RingHom.id_apply]
  invFun z :=
    (TensorProduct.lid (ZMod 2) (Fin m → ZMod 2) (s16c1610_pi0.rTensor (Fin m → ZMod 2) z),
      TensorProduct.lid (ZMod 2) (Fin m → ZMod 2) (s16c1610_pi1.rTensor (Fin m → ZMod 2) z))
  left_inv p := by
    obtain ⟨x, y⟩ := p
    have h1 : TensorProduct.lid (ZMod 2) (Fin m → ZMod 2)
        (s16c1610_pi0.rTensor (Fin m → ZMod 2)
          (s16c1610_b1 ⊗ₜ[ZMod 2] x + s16c1610_b2 ⊗ₜ[ZMod 2] y)) = x := by
      simp [s16c1610_pi0, s16c1610_b1, s16c1610_b2]
    have h2 : TensorProduct.lid (ZMod 2) (Fin m → ZMod 2)
        (s16c1610_pi1.rTensor (Fin m → ZMod 2)
          (s16c1610_b1 ⊗ₜ[ZMod 2] x + s16c1610_b2 ⊗ₜ[ZMod 2] y)) = y := by
      simp [s16c1610_pi1, s16c1610_b1, s16c1610_b2]
    exact Prod.ext h1 h2
  right_inv z := by
    have hz : s16c1610_b1 ⊗ₜ[ZMod 2] (TensorProduct.lid (ZMod 2) (Fin m → ZMod 2)
          (s16c1610_pi0.rTensor (Fin m → ZMod 2) z)) +
        s16c1610_b2 ⊗ₜ[ZMod 2] (TensorProduct.lid (ZMod 2) (Fin m → ZMod 2)
          (s16c1610_pi1.rTensor (Fin m → ZMod 2) z)) = z := by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul a c =>
        simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, TensorProduct.tmul_smul,
          TensorProduct.smul_tmul']
        rw [← TensorProduct.add_tmul, s16c1610_pi0_smul_b1_add_pi1_smul_b2]
      | add u v hu hv =>
        simp only [map_add, TensorProduct.tmul_add]
        rw [add_add_add_comm, hu, hv]
    exact hz

@[simp] theorem s16c1610_tensorEquiv_apply (m : ℕ) (x y : Fin m → ZMod 2) :
    s16c1610_tensorEquiv m (x, y) = s16c1610_b1 ⊗ₜ[ZMod 2] x + s16c1610_b2 ⊗ₜ[ZMod 2] y :=
  rfl

section Coordinates

variable {W : Type*} [CommGroup W] [Module (ZMod 2) (Additive W)] {K L : Subgroup W} {m : ℕ}

theorem s16c1610_mem_toSub {K : Subgroup W} {x : Additive W} :
    x ∈ CFSG.Quasithin.H13.Mult.toSub K ↔ x.toMul ∈ K := Iff.rfl

@[expose] noncomputable def s16c1610_subAddEquiv (K : Subgroup W) :
    CFSG.Quasithin.H13.Mult.toSub K ≃+ Additive ↥K where
  toFun y := Additive.ofMul ⟨(y : Additive W).toMul, s16c1610_mem_toSub.1 y.2⟩
  invFun x := ⟨Additive.ofMul (x.toMul : W), s16c1610_mem_toSub.2 x.toMul.2⟩
  left_inv y := by ext; rfl
  right_inv x := by ext; rfl
  map_add' y z := rfl

private theorem s16c1610_zmod_two_eq_zero_or_one (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c
  decide +kernel

@[expose] noncomputable def s16c1610_bLinearEquiv
    (b : ↥K ≃* Multiplicative (Fin m → ZMod 2)) :
    CFSG.Quasithin.H13.Mult.toSub K ≃ₗ[ZMod 2] (Fin m → ZMod 2) where
  toFun y := Multiplicative.toAdd (b ⟨(y : Additive W).toMul, s16c1610_mem_toSub.1 y.2⟩)
  invFun v := ⟨Additive.ofMul ((b.symm (Multiplicative.ofAdd v) : ↥K) : W),
    s16c1610_mem_toSub.2 (b.symm (Multiplicative.ofAdd v)).2⟩
  left_inv y := by
    apply Subtype.ext
    simp only [ofAdd_toAdd, MulEquiv.symm_apply_apply, ofMul_toMul]
  right_inv v := by
    simp only [toMul_ofMul]
    rw [Subtype.coe_eta, MulEquiv.apply_symm_apply, toAdd_ofAdd]
  map_add' y z := by
    change Multiplicative.toAdd (b ⟨((y : Additive W) + (z : Additive W)).toMul,
        s16c1610_mem_toSub.1 (add_mem y.2 z.2)⟩) =
      Multiplicative.toAdd (b ⟨(y : Additive W).toMul, s16c1610_mem_toSub.1 y.2⟩) +
        Multiplicative.toAdd (b ⟨(z : Additive W).toMul, s16c1610_mem_toSub.1 z.2⟩)
    have h : (⟨((y : Additive W) + (z : Additive W)).toMul,
        s16c1610_mem_toSub.1 (add_mem y.2 z.2)⟩ : ↥K) =
        ⟨(y : Additive W).toMul, s16c1610_mem_toSub.1 y.2⟩ *
          ⟨(z : Additive W).toMul, s16c1610_mem_toSub.1 z.2⟩ := rfl
    rw [h, map_mul]
    rfl
  map_smul' c v := by
    rcases s16c1610_zmod_two_eq_zero_or_one c with rfl | rfl <;> simp

@[simp] theorem s16c1610_bLinearEquiv_apply (b : ↥K ≃* Multiplicative (Fin m → ZMod 2))
    (u : ↥K) :
    s16c1610_bLinearEquiv b
        ⟨Additive.ofMul (u : W), s16c1610_mem_toSub.2 u.2⟩ = Multiplicative.toAdd (b u) :=
  congrArg (fun w : ↥K => Multiplicative.toAdd (b w)) (Subtype.ext rfl)

theorem s16c1610_bLinearEquiv_natural {Lb : Subgroup (MulAut W)} {U : Subgroup W}
    {m : ℕ} (b : ↥U ≃* Multiplicative (Fin m → ZMod 2))
    (ρ : ↥Lb ≃* GL (Fin m) (ZMod 2))
    (hb : ∀ (x : ↥Lb) (u : ↥U) (hu : (x : MulAut W) (u : W) ∈ U),
      Multiplicative.toAdd (b ⟨(x : MulAut W) (u : W), hu⟩) =
        (((ρ x : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec
          (Multiplicative.toAdd (b u))))
    (hstab : ∀ (x : ↥Lb) (u : ↥U), (x : MulAut W) (u : W) ∈ U)
    (l : ↥Lb) (u : ↥U) :
    s16c1610_bLinearEquiv b ⟨Additive.ofMul ((l : MulAut W) (u : W)),
        s16c1610_mem_toSub.2 (hstab l u)⟩ =
      (((ρ l : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec
        (s16c1610_bLinearEquiv b ⟨Additive.ofMul (u : W), s16c1610_mem_toSub.2 u.2⟩)) := by
  have h1 := s16c1610_bLinearEquiv_apply b (⟨(l : MulAut W) (u : W), hstab l u⟩ : ↥U)
  have h2 := s16c1610_bLinearEquiv_apply b u
  rw [h1, h2]
  exact hb l u (hstab l u)

theorem s16c1610_projectionOnto_comm {Y0 Y1 : Submodule (ZMod 2) (Additive W)}
    (h : IsCompl Y0 Y1) (T : Additive W ≃ₗ[ZMod 2] Additive W)
    (hT0 : ∀ x ∈ Y0, T x ∈ Y0) (hT1 : ∀ x ∈ Y1, T x ∈ Y1) (x : Additive W) :
    Submodule.projectionOnto Y0 Y1 h (T x) = T (Submodule.projectionOnto Y0 Y1 h x) := by
  have hmem : T x - T (Submodule.projectionOnto Y0 Y1 h x) ∈ Y1 := by
    rw [← map_sub]
    refine hT1 _ ?_
    rw [← Submodule.projectionOnto_apply_eq_zero_iff h, map_sub,
      Submodule.projectionOnto_apply_of_mem_left h (Submodule.coe_mem _), sub_self]
  have h_eq : Submodule.projectionOnto Y0 Y1 h (T x) =
      Submodule.projectionOnto Y0 Y1 h
        (T (Submodule.projectionOnto Y0 Y1 h x) +
          (T x - T (Submodule.projectionOnto Y0 Y1 h x))) := by
    congr 1
    abel
  rw [h_eq, map_add,
    Submodule.projectionOnto_apply_of_mem_left h (hT0 _ (Submodule.coe_mem _)),
    Submodule.projectionOnto_apply_eq_zero_iff h |>.2 hmem, add_zero]

theorem s16c1610_isCompl_toSub (hinf : K ⊓ L = ⊥) (hsup : K ⊔ L = ⊤) :
    IsCompl (CFSG.Quasithin.H13.Mult.toSub K) (CFSG.Quasithin.H13.Mult.toSub L) := by
  have h1 : CFSG.Quasithin.H13.Mult.toSub K ⊓ CFSG.Quasithin.H13.Mult.toSub L = ⊥ := by
    have h : CFSG.Quasithin.H13.Mult.toSub K ⊓ CFSG.Quasithin.H13.Mult.toSub L =
        CFSG.Quasithin.H13.Mult.toSubIso (K ⊓ L) := by
      rw [← CFSG.Quasithin.H13.Mult.toSubIso_apply K,
        ← CFSG.Quasithin.H13.Mult.toSubIso_apply L, ← OrderIso.map_inf,
        CFSG.Quasithin.H13.Mult.toSubIso_apply]
    rw [h, hinf]
    simp
  have h2 : CFSG.Quasithin.H13.Mult.toSub K ⊔ CFSG.Quasithin.H13.Mult.toSub L = ⊤ := by
    have h : CFSG.Quasithin.H13.Mult.toSub K ⊔ CFSG.Quasithin.H13.Mult.toSub L =
        CFSG.Quasithin.H13.Mult.toSubIso (K ⊔ L) := by
      rw [← CFSG.Quasithin.H13.Mult.toSubIso_apply K,
        ← CFSG.Quasithin.H13.Mult.toSubIso_apply L, ← OrderIso.map_sup,
        CFSG.Quasithin.H13.Mult.toSubIso_apply]
    rw [h, hsup]
    simp
  exact ⟨disjoint_iff.2 h1, codisjoint_iff.2 h2⟩

@[expose] noncomputable def s16c1610_coordEquiv {I : Fin 2 → Subgroup W}
    (hinf : I 0 ⊓ I 1 = ⊥) (hsup : I 0 ⊔ I 1 = ⊤)
    (b0 : ↥(I 0) ≃* Multiplicative (Fin m → ZMod 2))
    (b1 : ↥(I 1) ≃* Multiplicative (Fin m → ZMod 2)) :
    Additive W ≃ₗ[ZMod 2] ((Fin m → ZMod 2) × (Fin m → ZMod 2)) :=
  (Submodule.prodEquivOfIsCompl (CFSG.Quasithin.H13.Mult.toSub (I 0))
    (CFSG.Quasithin.H13.Mult.toSub (I 1)) (s16c1610_isCompl_toSub hinf hsup)).symm.trans
    ((s16c1610_bLinearEquiv b0).prodCongr (s16c1610_bLinearEquiv b1))

@[simp] theorem s16c1610_coordEquiv_fst {I : Fin 2 → Subgroup W}
    (hinf : I 0 ⊓ I 1 = ⊥) (hsup : I 0 ⊔ I 1 = ⊤)
    (b0 : ↥(I 0) ≃* Multiplicative (Fin m → ZMod 2))
    (b1 : ↥(I 1) ≃* Multiplicative (Fin m → ZMod 2)) (x : Additive W) :
    (s16c1610_coordEquiv hinf hsup b0 b1 x).1 =
      s16c1610_bLinearEquiv b0 (Submodule.projectionOnto
        (CFSG.Quasithin.H13.Mult.toSub (I 0)) (CFSG.Quasithin.H13.Mult.toSub (I 1))
        (s16c1610_isCompl_toSub hinf hsup) x) := rfl

@[simp] theorem s16c1610_coordEquiv_snd {I : Fin 2 → Subgroup W}
    (hinf : I 0 ⊓ I 1 = ⊥) (hsup : I 0 ⊔ I 1 = ⊤)
    (b0 : ↥(I 0) ≃* Multiplicative (Fin m → ZMod 2))
    (b1 : ↥(I 1) ≃* Multiplicative (Fin m → ZMod 2)) (x : Additive W) :
    (s16c1610_coordEquiv hinf hsup b0 b1 x).2 =
      s16c1610_bLinearEquiv b1 (Submodule.projectionOnto
        (CFSG.Quasithin.H13.Mult.toSub (I 1)) (CFSG.Quasithin.H13.Mult.toSub (I 0))
        (s16c1610_isCompl_toSub hinf hsup).symm x) := by
  show s16c1610_bLinearEquiv b1
    ((Submodule.prodEquivOfIsCompl (CFSG.Quasithin.H13.Mult.toSub (I 0))
      (CFSG.Quasithin.H13.Mult.toSub (I 1)) (s16c1610_isCompl_toSub hinf hsup)).symm x).2 = _
  rw [Submodule.prodEquivOfIsCompl_symm_apply]

theorem s16c1610_mem_toSub_linEquiv {K : Subgroup W} {Lb : Subgroup (MulAut W)}
    (hstab : ∀ (x : ↥Lb) (u : ↥K), (x : MulAut W) (u : W) ∈ K) (l : ↥Lb)
    {y : Additive W} (hy : y ∈ CFSG.Quasithin.H13.Mult.toSub K) :
    CFSG.Quasithin.H13.Mult.linEquiv (l : MulAut W) y ∈
      CFSG.Quasithin.H13.Mult.toSub K := by
  rw [s16c1610_mem_toSub] at hy ⊢
  rw [CFSG.Quasithin.H13.Mult.linEquiv_apply, toMul_ofMul]
  exact hstab l ⟨y.toMul, hy⟩

theorem s16c1610_coordEquiv_natural {I : Fin 2 → Subgroup W} {Lb : Subgroup (MulAut W)}
    {m : ℕ} (hinf : I 0 ⊓ I 1 = ⊥) (hsup : I 0 ⊔ I 1 = ⊤)
    (b0 : ↥(I 0) ≃* Multiplicative (Fin m → ZMod 2))
    (b1 : ↥(I 1) ≃* Multiplicative (Fin m → ZMod 2))
    (ρ0 ρ1 : ↥Lb ≃* GL (Fin m) (ZMod 2))
    (hb0 : ∀ (x : ↥Lb) (u : ↥(I 0)) (hu : (x : MulAut W) (u : W) ∈ I 0),
      Multiplicative.toAdd (b0 ⟨(x : MulAut W) (u : W), hu⟩) =
        (((ρ0 x : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec
          (Multiplicative.toAdd (b0 u))))
    (hb1 : ∀ (x : ↥Lb) (u : ↥(I 1)) (hu : (x : MulAut W) (u : W) ∈ I 1),
      Multiplicative.toAdd (b1 ⟨(x : MulAut W) (u : W), hu⟩) =
        (((ρ1 x : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec
          (Multiplicative.toAdd (b1 u))))
    (hstab0 : ∀ (x : ↥Lb) (u : ↥(I 0)), (x : MulAut W) (u : W) ∈ I 0)
    (hstab1 : ∀ (x : ↥Lb) (u : ↥(I 1)), (x : MulAut W) (u : W) ∈ I 1)
    (l : ↥Lb) (x : Additive W) :
    s16c1610_coordEquiv hinf hsup b0 b1 (CFSG.Quasithin.H13.Mult.linEquiv (l : MulAut W) x) =
      (Matrix.mulVec (((ρ0 l : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)))
          (s16c1610_coordEquiv hinf hsup b0 b1 x).1,
       Matrix.mulVec (((ρ1 l : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)))
          (s16c1610_coordEquiv hinf hsup b0 b1 x).2) := by
  have hT0 : ∀ y ∈ CFSG.Quasithin.H13.Mult.toSub (I 0),
      CFSG.Quasithin.H13.Mult.linEquiv (l : MulAut W) y ∈
        CFSG.Quasithin.H13.Mult.toSub (I 0) :=
    fun y hy => s16c1610_mem_toSub_linEquiv hstab0 l hy
  have hT1 : ∀ y ∈ CFSG.Quasithin.H13.Mult.toSub (I 1),
      CFSG.Quasithin.H13.Mult.linEquiv (l : MulAut W) y ∈
        CFSG.Quasithin.H13.Mult.toSub (I 1) :=
    fun y hy => s16c1610_mem_toSub_linEquiv hstab1 l hy
  have hcomm0 : (Submodule.projectionOnto (CFSG.Quasithin.H13.Mult.toSub (I 0))
        (CFSG.Quasithin.H13.Mult.toSub (I 1)) (s16c1610_isCompl_toSub hinf hsup)
        (CFSG.Quasithin.H13.Mult.linEquiv (l : MulAut W) x) :
        CFSG.Quasithin.H13.Mult.toSub (I 0)) =
      ⟨CFSG.Quasithin.H13.Mult.linEquiv (l : MulAut W)
        (Submodule.projectionOnto (CFSG.Quasithin.H13.Mult.toSub (I 0))
          (CFSG.Quasithin.H13.Mult.toSub (I 1)) (s16c1610_isCompl_toSub hinf hsup) x),
        hT0 _ (Submodule.coe_mem _)⟩ :=
    Subtype.ext (s16c1610_projectionOnto_comm (s16c1610_isCompl_toSub hinf hsup)
      (CFSG.Quasithin.H13.Mult.linEquiv (l : MulAut W)) hT0 hT1 x)
  have hcomm1 : (Submodule.projectionOnto (CFSG.Quasithin.H13.Mult.toSub (I 1))
        (CFSG.Quasithin.H13.Mult.toSub (I 0)) (s16c1610_isCompl_toSub hinf hsup).symm
        (CFSG.Quasithin.H13.Mult.linEquiv (l : MulAut W) x) :
        CFSG.Quasithin.H13.Mult.toSub (I 1)) =
      ⟨CFSG.Quasithin.H13.Mult.linEquiv (l : MulAut W)
        (Submodule.projectionOnto (CFSG.Quasithin.H13.Mult.toSub (I 1))
          (CFSG.Quasithin.H13.Mult.toSub (I 0)) (s16c1610_isCompl_toSub hinf hsup).symm x),
        hT1 _ (Submodule.coe_mem _)⟩ :=
    Subtype.ext (s16c1610_projectionOnto_comm (s16c1610_isCompl_toSub hinf hsup).symm
      (CFSG.Quasithin.H13.Mult.linEquiv (l : MulAut W)) hT1 hT0 x)
  refine Prod.ext ?_ ?_
  · simp only [s16c1610_coordEquiv_fst, hcomm0]
    exact s16c1610_bLinearEquiv_natural b0 ρ0 hb0 hstab0 l
        (Submodule.projectionOnto (CFSG.Quasithin.H13.Mult.toSub (I 0))
          (CFSG.Quasithin.H13.Mult.toSub (I 1)) (s16c1610_isCompl_toSub hinf hsup) x)
  · simp only [s16c1610_coordEquiv_snd, hcomm1]
    exact s16c1610_bLinearEquiv_natural b1 ρ1 hb1 hstab1 l
        (Submodule.projectionOnto (CFSG.Quasithin.H13.Mult.toSub (I 1))
          (CFSG.Quasithin.H13.Mult.toSub (I 0)) (s16c1610_isCompl_toSub hinf hsup).symm x)

@[expose] noncomputable def s16c1610_glAction (m : ℕ) :
    GL (Fin m) (ZMod 2) ≃* ((Fin m → ZMod 2) ≃ₗ[ZMod 2] (Fin m → ZMod 2)) :=
  Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin m → ZMod 2))

@[simp] theorem s16c1610_glAction_apply (m : ℕ) (A : GL (Fin m) (ZMod 2))
    (v : Fin m → ZMod 2) :
    s16c1610_glAction m A v =
      (((A : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec v) := by
  change ((Matrix.GeneralLinearGroup.toLin A :
    (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2))) v = _
  rw [Matrix.GeneralLinearGroup.toLin_apply]
  rfl

theorem s16c1610_end_eq_zero_or_id_pi {m : ℕ} (hm : 2 ≤ m)
    {φ : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2)}
    (hφ : ∀ τ : (Fin m → ZMod 2) ≃ₗ[ZMod 2] (Fin m → ZMod 2), ∀ y, φ (τ y) = τ (φ y)) :
    φ = 0 ∨ φ = LinearMap.id := by
  have hd : 2 ≤ Module.finrank (ZMod 2) (Fin m → ZMod 2) := by
    rw [Module.finrank_fin_fun]
    omega
  exact @CFSG.Quasithin.H13.Mult.eq_zero_or_eq_id_of_commute (Fin m → ZMod 2)
    (inferInstance : AddCommGroup (Fin m → ZMod 2))
    (inferInstance : Module (ZMod 2) (Fin m → ZMod 2))
    (inferInstance : Module.Finite (ZMod 2) (Fin m → ZMod 2)) hd φ hφ

theorem s16c1610_eq_zero_or_injective_pi {m : ℕ}
    {φ : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2)}
    (hker : ∀ τ : (Fin m → ZMod 2) ≃ₗ[ZMod 2] (Fin m → ZMod 2), ∀ z, φ z = 0 → φ (τ z) = 0) :
    φ = 0 ∨ Function.Injective φ := by
  by_cases h0 : φ = 0
  · exact Or.inl h0
  right
  intro x y hxy
  by_contra hne
  have hxy' : φ (x - y) = 0 := by
    rw [map_sub, hxy]
    exact sub_self _
  have hsub : x - y ≠ 0 := sub_ne_zero.2 hne
  have hzero : ∀ z, φ z = 0 := by
    intro z
    by_cases hz : z = 0
    · rw [hz, map_zero]
    · obtain ⟨τ, hτ⟩ :=
        @CFSG.Quasithin.H13.Mult.exists_linearEquiv_apply_eq (Fin m → ZMod 2)
          (inferInstance : AddCommGroup (Fin m → ZMod 2))
          (inferInstance : Module (ZMod 2) (Fin m → ZMod 2)) (x - y) z hsub hz
      rw [← hτ]
      exact hker τ (x - y) hxy'
  apply h0
  exact LinearMap.ext fun z => by rw [hzero z, LinearMap.zero_apply]

theorem s16c1610_injective_surjective_pi {m : ℕ}
    {φ : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2)} (h : Function.Injective φ) :
    Function.Surjective φ :=
  (Finite.injective_iff_surjective).mp h

theorem s16c1610_permAct_eq (σ : Equiv.Perm (Fin 3)) (a : ↥(CFSG.Quasithin.permCore 3))
    (i : Fin 2) :
    CFSG.Quasithin.permAct σ (a : Fin 3 → ZMod 2) (Fin.castSucc i) =
      (s16c1610_permMat σ).mulVec ![s16c1610_pi0 a, s16c1610_pi1 a] i := by
  have ha : (a : Fin 3 → ZMod 2) 2 = (a : Fin 3 → ZMod 2) 0 + (a : Fin 3 → ZMod 2) 1 := by
    have hsum : ∑ j, (a : Fin 3 → ZMod 2) j = 0 := a.2
    rw [Fin.sum_univ_three] at hsum
    exact s16c1610_zmod_two_sum_zero _ _ _ hsum
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    s16c1610_pi0, s16c1610_pi1, s16c1610_permMat]
  rw [CFSG.Quasithin.permAct]
  have key : ∀ w : Fin 3, (a : Fin 3 → ZMod 2) w =
      ![1, 0, 1] w * (a : Fin 3 → ZMod 2) 0 +
        ![0, 1, 1] w * (a : Fin 3 → ZMod 2) 1 := by
    intro w
    fin_cases w <;> simp_all
  exact key _

theorem s16c1610_tensorEquiv_symm_tmul (m : ℕ) (a : ↥(CFSG.Quasithin.permCore 3))
    (c : Fin m → ZMod 2) :
    (s16c1610_tensorEquiv m).symm (a ⊗ₜ[ZMod 2] c) =
      (s16c1610_pi0 a • c, s16c1610_pi1 a • c) := by
  rw [LinearEquiv.symm_apply_eq, s16c1610_tensorEquiv_apply]
  rw [← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul, ← TensorProduct.add_tmul,
    s16c1610_pi0_smul_b1_add_pi1_smul_b2]

end Coordinates

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
