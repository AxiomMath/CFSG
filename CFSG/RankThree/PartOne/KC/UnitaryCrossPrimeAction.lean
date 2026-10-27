module

public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeCentralizer

public section

namespace CFSG.RankThree.PartOne.KCUnitaryModel

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCUnitaryRegular

variable {ℓ f : ℕ} {K : Type} [Field K]

@[expose] noncomputable def conjRingAut (n : ℕ) (K : Type) [Field K] :
    GL (Fin n) K →* RingAut (Matrix (Fin n) (Fin n) K) :=
  (MulSemiringAction.toRingAut (ConjAct (GL (Fin n) K)) (Matrix (Fin n) (Fin n) K)).comp
    (ConjAct.toConjAct : GL (Fin n) K ≃* ConjAct (GL (Fin n) K)).toMonoidHom

theorem conjRingAut_apply {n : ℕ} (A : GL (Fin n) K) (Y : Matrix (Fin n) (Fin n) K) :
    conjRingAut n K A Y =
      (A : Matrix (Fin n) (Fin n) K) * Y * ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  simp [conjRingAut, ConjAct.units_smul_def]

@[expose] noncomputable def fieldRingAut (n : ℕ) (K : Type) [Field K] :
    (K ≃+* K) →* RingAut (Matrix (Fin n) (Fin n) K) where
  toFun σ := σ.mapMatrix
  map_one' := by ext; rfl
  map_mul' σ τ := by ext; rfl

theorem fieldRingAut_apply {n : ℕ} (σ : K ≃+* K) (Y : Matrix (Fin n) (Fin n) K) :
    fieldRingAut n K σ Y = Y.map σ := rfl

variable (h : UnitaryFieldData ℓ f K) (n)

noncomputable def idMatAction :
    primeFormUnitary h (idGram K n) ⋊[primeFormFieldU h
      (isPrimeFormGram_idGram (K := K) (n := n))] (K ≃+* K) →*
      RingAut (Matrix (Fin n) (Fin n) K) :=
  SemidirectProduct.lift ((conjRingAut n K).comp (primeFormUnitary h (idGram K n)).subtype)
    (fieldRingAut n K) fun σ => MonoidHom.ext fun A => by
      refine RingEquiv.ext fun Y => ?_
      change conjRingAut n K (glAut σ (A : GL (Fin n) K)) Y =
        (fieldRingAut n K σ) ((conjRingAut n K (A : GL (Fin n) K))
          ((fieldRingAut n K σ).symm Y))
      rw [conjRingAut_apply, conjRingAut_apply, fieldRingAut_apply]
      have h1 : (fieldRingAut n K σ).symm Y = Y.map ⇑σ.symm := rfl
      have h2 : (Y.map ⇑σ.symm).map ⇑σ = Y := by
        ext i j
        simp
      have hmul : ∀ P Q : Matrix (Fin n) (Fin n) K, (P * Q).map ⇑σ = P.map ⇑σ * Q.map ⇑σ :=
        fun P Q => Matrix.map_mul (f := (σ : K →+* K))
      rw [h1, ← map_inv (glAut σ) (A : GL (Fin n) K), coe_glAut, coe_glAut, hmul, hmul, h2]

noncomputable def idUAction :
    primeFormUnitary h (idGram K n) ⋊[primeFormFieldU h
      (isPrimeFormGram_idGram (K := K) (n := n))] (K ≃+* K) →*
      MulAut (primeFormUnitary h (idGram K n)) :=
  SemidirectProduct.lift (MulAut.conj : primeFormUnitary h (idGram K n) →*
    MulAut (primeFormUnitary h (idGram K n)))
    (primeFormFieldU h (isPrimeFormGram_idGram (K := K) (n := n))) fun σ =>
    MonoidHom.ext fun A => by
      refine MulEquiv.ext fun X => ?_
      change (primeFormFieldU h (isPrimeFormGram_idGram (K := K) (n := n)) σ A) * X *
        (primeFormFieldU h (isPrimeFormGram_idGram (K := K) (n := n)) σ A)⁻¹ =
        (primeFormFieldU h (isPrimeFormGram_idGram (K := K) (n := n)) σ)
          (A * (primeFormFieldU h (isPrimeFormGram_idGram (K := K) (n := n)) σ).symm X * A⁻¹)
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

variable {h n}

theorem idMatAction_mk (A : primeFormUnitary h (idGram K n)) (σ : K ≃+* K)
    (Y : Matrix (Fin n) (Fin n) K) :
    idMatAction h n ⟨A, σ⟩ Y =
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Y.map σ *
        (((A : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  have : (⟨A, σ⟩ : primeFormUnitary h (idGram K n) ⋊[primeFormFieldU h
      (isPrimeFormGram_idGram (K := K) (n := n))] (K ≃+* K)) =
      SemidirectProduct.inl A * SemidirectProduct.inr σ := SemidirectProduct.mk_eq_inl_mul_inr σ A
  rw [this, map_mul, idMatAction, SemidirectProduct.lift_inl, SemidirectProduct.lift_inr]
  change conjRingAut n K (A : GL (Fin n) K) (fieldRingAut n K σ Y) = _
  rw [conjRingAut_apply, fieldRingAut_apply]

theorem idUAction_mk (A : primeFormUnitary h (idGram K n)) (σ : K ≃+* K)
    (X : primeFormUnitary h (idGram K n)) :
    idUAction h n ⟨A, σ⟩ X =
      A * primeFormFieldU h (isPrimeFormGram_idGram (K := K) (n := n)) σ X * A⁻¹ := by
  have : (⟨A, σ⟩ : primeFormUnitary h (idGram K n) ⋊[primeFormFieldU h
      (isPrimeFormGram_idGram (K := K) (n := n))] (K ≃+* K)) =
      SemidirectProduct.inl A * SemidirectProduct.inr σ := SemidirectProduct.mk_eq_inl_mul_inr σ A
  rw [this, map_mul, idUAction, SemidirectProduct.lift_inl, SemidirectProduct.lift_inr]
  rfl

theorem conj_scalar_eq {n : ℕ} (c : Kˣ) (Y : Matrix (Fin n) (Fin n) K) :
    ((GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Y *
      (((GeneralLinearGroup.scalar (Fin n) c)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        Y := by
  have hc : Commute ((GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) Y := by
    rw [GeneralLinearGroup.coe_scalar]
    exact Matrix.scalar_commute _ (fun r => Commute.all _ r) _
  rw [hc.eq, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]

section Descent

variable (hn : 3 ≤ n) (hq : 3 < ℓ ^ f)

include hn hq in
theorem idMatAction_eq_one_of_primeFormPsi_eq_one
    (g : primeFormUnitary h (idGram K n) ⋊[primeFormFieldU h
      (isPrimeFormGram_idGram (K := K) (n := n))] (K ≃+* K))
    (hg : primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) g = 1) :
    idMatAction h n g = 1 := by
  obtain ⟨hr, c, -, hc⟩ := (primeFormPsi_eq_one_iff' hn hq g).mp hg
  obtain ⟨A, σ⟩ := g
  change σ = RingEquiv.refl K at hr
  subst hr
  refine RingEquiv.ext fun Y => ?_
  rw [idMatAction_mk]
  change _ * Y.map (RingEquiv.refl K) * _ = Y
  rw [show Y.map (RingEquiv.refl K) = Y from by ext; rfl]
  have hA : (A : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) c := hc
  rw [hA]
  exact conj_scalar_eq c Y

include hn hq in
theorem idUAction_eq_one_of_primeFormPsi_eq_one
    (g : primeFormUnitary h (idGram K n) ⋊[primeFormFieldU h
      (isPrimeFormGram_idGram (K := K) (n := n))] (K ≃+* K))
    (hg : primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) g = 1) :
    idUAction h n g = 1 := by
  obtain ⟨hr, c, -, hc⟩ := (primeFormPsi_eq_one_iff' hn hq g).mp hg
  obtain ⟨A, σ⟩ := g
  change σ = RingEquiv.refl K at hr
  subst hr
  refine MulEquiv.ext fun X => ?_
  rw [idUAction_mk]
  have hA : (A : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) c := hc
  have hX : primeFormFieldU h (isPrimeFormGram_idGram (K := K) (n := n)) (RingEquiv.refl K) X =
      X := Subtype.ext (by
    change glAut (1 : K ≃+* K) (X : GL (Fin n) K) = X
    rw [map_one]
    rfl)
  rw [hX, MulAut.one_apply]
  apply Subtype.ext
  show (A : GL (Fin n) K) * (X : GL (Fin n) K) * (A : GL (Fin n) K)⁻¹ = (X : GL (Fin n) K)
  rw [hA, ← (commute_scalar c (X : GL (Fin n) K)).eq, mul_inv_cancel_right]

end Descent

section Act

variable (h n)

noncomputable def idAct (hn : 3 ≤ n) (hq : 3 < ℓ ^ f) :
    MulAut (primeFormP h (idGram K n)) →* RingAut (Matrix (Fin n) (Fin n) K) :=
  MonoidHom.liftOfRightInverse (primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)))
    (Function.surjInv (surjective_primeFormPsi hn hq))
    (Function.rightInverse_surjInv (surjective_primeFormPsi hn hq))
    ⟨idMatAction h n, fun g hg =>
      (MonoidHom.mem_ker).mpr (idMatAction_eq_one_of_primeFormPsi_eq_one hn hq g
        ((MonoidHom.mem_ker).mp hg))⟩

noncomputable def idActU (hn : 3 ≤ n) (hq : 3 < ℓ ^ f) :
    MulAut (primeFormP h (idGram K n)) →* MulAut (primeFormUnitary h (idGram K n)) :=
  MonoidHom.liftOfRightInverse (primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)))
    (Function.surjInv (surjective_primeFormPsi hn hq))
    (Function.rightInverse_surjInv (surjective_primeFormPsi hn hq))
    ⟨idUAction h n, fun g hg =>
      (MonoidHom.mem_ker).mpr (idUAction_eq_one_of_primeFormPsi_eq_one hn hq g
        ((MonoidHom.mem_ker).mp hg))⟩

variable {h n} (hn : 3 ≤ n) (hq : 3 < ℓ ^ f)

theorem idAct_primeFormPsi (g : primeFormUnitary h (idGram K n) ⋊[primeFormFieldU h
      (isPrimeFormGram_idGram (K := K) (n := n))] (K ≃+* K)) :
    idAct h n hn hq (primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) g) =
      idMatAction h n g :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ g

theorem idActU_primeFormPsi (g : primeFormUnitary h (idGram K n) ⋊[primeFormFieldU h
      (isPrimeFormGram_idGram (K := K) (n := n))] (K ≃+* K)) :
    idActU h n hn hq (primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) g) =
      idUAction h n g :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ g

theorem primeFormConjHom_eq_primeFormPsi (A : primeFormUnitary h (idGram K n)) :
    primeFormConjHom h (idGram K n) A =
      primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) ⟨A, 1⟩ := by
  rw [primeFormPsi_apply, map_one, mul_one]

theorem idAct_primeFormConjHom (A : primeFormUnitary h (idGram K n))
    (Y : Matrix (Fin n) (Fin n) K) :
    idAct h n hn hq (primeFormConjHom h (idGram K n) A) Y =
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Y *
        (((A : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  rw [primeFormConjHom_eq_primeFormPsi, idAct_primeFormPsi, idMatAction_mk]
  congr 2

theorem idAct_primeFormFieldHom (σ : K ≃+* K) (Y : Matrix (Fin n) (Fin n) K) :
    idAct h n hn hq (primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := n)) σ) Y =
      Y.map σ := by
  have : primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := n)) σ =
      primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) ⟨1, σ⟩ := by
    rw [primeFormPsi_apply, map_one, one_mul]
  rw [this, idAct_primeFormPsi, idMatAction_mk]
  simp

theorem coe_idActU (α : MulAut (primeFormP h (idGram K n))) (A : primeFormUnitary h (idGram K n)) :
    (((idActU h n hn hq α A : primeFormUnitary h (idGram K n)) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) =
      idAct h n hn hq α ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  obtain ⟨⟨M, σ⟩, rfl⟩ := surjective_primeFormPsi hn hq α
  rw [idActU_primeFormPsi, idAct_primeFormPsi, idUAction_mk, idMatAction_mk]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, coe_primeFormFieldU, coe_glAut]

theorem conj_primeFormConjHom (α : MulAut (primeFormP h (idGram K n)))
    (A : primeFormUnitary h (idGram K n)) :
    α * primeFormConjHom h (idGram K n) A * α⁻¹ =
      primeFormConjHom h (idGram K n) (idActU h n hn hq α A) := by
  obtain ⟨⟨M, σ⟩, rfl⟩ := surjective_primeFormPsi hn hq α
  rw [idActU_primeFormPsi, idUAction_mk]
  have h1 := primeFormField_conj_eq h (isPrimeFormGram_idGram (K := K) (n := n)) σ A
  rw [primeFormPsi_apply, map_mul, map_mul, map_inv, ← h1]
  group

theorem det_idAct (α : MulAut (primeFormP h (idGram K n))) {X : Matrix (Fin n) (Fin n) K}
    (hX : X.det = 1) : (idAct h n hn hq α X).det = 1 := by
  obtain ⟨⟨M, σ⟩, rfl⟩ := surjective_primeFormPsi hn hq α
  rw [idAct_primeFormPsi, idMatAction_mk, Matrix.det_mul, Matrix.det_mul]
  have hMM : ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det *
      (((M : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have hσ : (X.map σ).det = 1 := by
    rw [show X.map σ = (σ : K →+* K).mapMatrix X from rfl, ← RingHom.map_det, hX, map_one]
  rw [hσ, mul_one, hMM]

variable {p : ℕ} {x : gramSU h (idGram K n)} (L : LiftData h n p x)

include L in
theorem LiftData.idAct_eq_of_conj_eq (α : MulAut (primeFormP h (idGram K n)))
    (hα : α * primeFormConjHom h (idGram K n) (liftUnitary x) * α⁻¹ =
      primeFormConjHom h (idGram K n) (liftUnitary x)) :
    idAct h n L.three_le L.four_le α ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  have hn := L.three_le
  have hq := L.four_le
  set y := idActU h n hn hq α (liftUnitary x) with hy
  have hymat : ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      idAct h n hn hq α ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := coe_idActU hn hq α _
  have hyρ : primeFormConjHom h (idGram K n) y =
      primeFormConjHom h (idGram K n) (liftUnitary x) := by
    rw [← conj_primeFormConjHom hn hq α, hα]
  have hdet : (((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).det = 1 := by
    rw [hymat]
    exact det_idAct hn hq α x.2.2
  let y' : gramSU h (idGram K n) := ⟨y, y.2, hdet⟩
  have hxp : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = 1 := by
    have := congrArg (fun z : gramSU h (idGram K n) => ((z : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K)) L.pow_eq_one
    simpa using this
  have hyp : y' ^ p = 1 := by
    apply Subtype.ext
    apply Units.ext
    have h1 : (((y' ^ p : gramSU h (idGram K n)) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        (idAct h n hn hq α ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ^ p := by
      rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]
      exact congrArg (· ^ p) hymat
    rw [h1, ← map_pow, hxp, map_one]
    rfl
  have hπ : (y' : primeFormP h (idGram K n)) = (x : primeFormP h (idGram K n)) := by
    apply conj_injective hn hq
    rw [← primeFormConjHom_eq_conj h _ y', ← primeFormConjHom_eq_conj h _ x]
    exact hyρ
  have hyx : y' = x :=
    eq_of_mk_eq_of_pow_eq_one_of_noTorsion L.noTorsion (by omega) hyp L.pow_eq_one hπ
  rw [← hymat]
  exact congrArg (fun z : gramSU h (idGram K n) => ((z : GL (Fin n) K) :
    Matrix (Fin n) (Fin n) K)) hyx

end Act

end CFSG.RankThree.PartOne.KCUnitaryModel
