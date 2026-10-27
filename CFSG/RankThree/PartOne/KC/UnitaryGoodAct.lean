module

public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeAction
public import CFSG.RankThree.PartOne.KC.UnitaryGoodModel

public section

namespace CFSG.RankThree.PartOne.KCUnitaryModel

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCUnitaryRegular
open scoped commutatorElement

variable {ℓ f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K} {n : ℕ}

theorem surjective_primeFormPsi_of_ne (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) :
    Function.Surjective (primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n))) :=
  (unitary_prime_form_full_semilinear_realization h (isPrimeFormGram_idGram (K := K) (n := n))
    hn hne).2.1

theorem primeFormPsi_eq_one_iff'_of_ne (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    (g : primeFormUnitary h (idGram K n) ⋊[primeFormFieldU h
      (isPrimeFormGram_idGram (K := K) (n := n))] (K ≃+* K)) :
    primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) g = 1 ↔
      g.right = RingEquiv.refl K ∧ g.left ∈ idScalarKernel h n := by
  have key := (unitary_prime_form_full_semilinear_realization h
    (isPrimeFormGram_idGram (K := K) (n := n)) hn hne).2.2.1 g
  rw [key]
  constructor
  · rintro ⟨hr, c, hc, hA⟩
    exact ⟨hr, c, (pow_succ_eq_one_iff_norm h c).mpr hc, hA⟩
  · rintro ⟨hr, c, hc, hA⟩
    exact ⟨hr, c, (pow_succ_eq_one_iff_norm h c).mp hc, hA⟩

theorem primeFormD_normal_of_ne (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) :
    (primeFormD h (idGram K n)).Normal :=
  (unitary_prime_form_full_semilinear_realization h (isPrimeFormGram_idGram (K := K) (n := n))
    hn hne).2.2.2.2.2.2.2.2.1

theorem commutator_mem_primeFormD_of_ne (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    (α β : MulAut (primeFormP h (idGram K n))) : ⁅α, β⁆ ∈ primeFormD h (idGram K n) := by
  have hker := (unitary_prime_form_full_semilinear_realization h
    (isPrimeFormGram_idGram (K := K) (n := n)) hn hne).2.2.2.2.2.2.2.1
  rw [← hker, MonoidHom.mem_ker, map_commutatorElement,
    commutatorElement_eq_one_iff_commute]
  exact ringAut_commute h _ _

theorem conj_injective_of_ne (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) :
    Function.Injective (MulAut.conj : primeFormP h (idGram K n) →*
      MulAut (primeFormP h (idGram K n))) :=
  conj_injective_primeFormP h (isPrimeFormGram_idGram (K := K) (n := n)) hn hne

section Descent

variable (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))

include hn hne in
theorem idMatAction_eq_one_of_primeFormPsi_eq_one'
    (g : primeFormUnitary h (idGram K n) ⋊[primeFormFieldU h
      (isPrimeFormGram_idGram (K := K) (n := n))] (K ≃+* K))
    (hg : primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) g = 1) :
    idMatAction h n g = 1 := by
  obtain ⟨hr, c, -, hc⟩ := (primeFormPsi_eq_one_iff'_of_ne hn hne g).mp hg
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

include hn hne in
theorem idUAction_eq_one_of_primeFormPsi_eq_one'
    (g : primeFormUnitary h (idGram K n) ⋊[primeFormFieldU h
      (isPrimeFormGram_idGram (K := K) (n := n))] (K ≃+* K))
    (hg : primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) g = 1) :
    idUAction h n g = 1 := by
  obtain ⟨hr, c, -, hc⟩ := (primeFormPsi_eq_one_iff'_of_ne hn hne g).mp hg
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

noncomputable def idAct' (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) :
    MulAut (primeFormP h (idGram K n)) →* RingAut (Matrix (Fin n) (Fin n) K) :=
  MonoidHom.liftOfRightInverse (primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)))
    (Function.surjInv (surjective_primeFormPsi_of_ne hn hne))
    (Function.rightInverse_surjInv (surjective_primeFormPsi_of_ne hn hne))
    ⟨idMatAction h n, fun g hg =>
      (MonoidHom.mem_ker).mpr (idMatAction_eq_one_of_primeFormPsi_eq_one' hn hne g
        ((MonoidHom.mem_ker).mp hg))⟩

noncomputable def idActU' (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) :
    MulAut (primeFormP h (idGram K n)) →* MulAut (primeFormUnitary h (idGram K n)) :=
  MonoidHom.liftOfRightInverse (primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)))
    (Function.surjInv (surjective_primeFormPsi_of_ne hn hne))
    (Function.rightInverse_surjInv (surjective_primeFormPsi_of_ne hn hne))
    ⟨idUAction h n, fun g hg =>
      (MonoidHom.mem_ker).mpr (idUAction_eq_one_of_primeFormPsi_eq_one' hn hne g
        ((MonoidHom.mem_ker).mp hg))⟩

variable {h n} (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))

theorem idAct'_primeFormPsi (g : primeFormUnitary h (idGram K n) ⋊[primeFormFieldU h
      (isPrimeFormGram_idGram (K := K) (n := n))] (K ≃+* K)) :
    idAct' h n hn hne (primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) g) =
      idMatAction h n g :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ g

theorem idActU'_primeFormPsi (g : primeFormUnitary h (idGram K n) ⋊[primeFormFieldU h
      (isPrimeFormGram_idGram (K := K) (n := n))] (K ≃+* K)) :
    idActU' h n hn hne (primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) g) =
      idUAction h n g :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ g

theorem idAct'_primeFormConjHom (A : primeFormUnitary h (idGram K n))
    (Y : Matrix (Fin n) (Fin n) K) :
    idAct' h n hn hne (primeFormConjHom h (idGram K n) A) Y =
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Y *
        (((A : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  rw [primeFormConjHom_eq_primeFormPsi, idAct'_primeFormPsi, idMatAction_mk]
  congr 2

theorem idAct'_primeFormFieldHom (σ : K ≃+* K) (Y : Matrix (Fin n) (Fin n) K) :
    idAct' h n hn hne (primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := n)) σ) Y =
      Y.map σ := by
  have : primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := n)) σ =
      primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) ⟨1, σ⟩ := by
    rw [primeFormPsi_apply, map_one, one_mul]
  rw [this, idAct'_primeFormPsi, idMatAction_mk]
  simp

theorem coe_idActU' (α : MulAut (primeFormP h (idGram K n))) (A : primeFormUnitary h (idGram K n)) :
    (((idActU' h n hn hne α A : primeFormUnitary h (idGram K n)) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) =
      idAct' h n hn hne α ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  obtain ⟨⟨M, σ⟩, rfl⟩ := surjective_primeFormPsi_of_ne hn hne α
  rw [idActU'_primeFormPsi, idAct'_primeFormPsi, idUAction_mk, idMatAction_mk]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, coe_primeFormFieldU, coe_glAut]

theorem conj_primeFormConjHom' (α : MulAut (primeFormP h (idGram K n)))
    (A : primeFormUnitary h (idGram K n)) :
    α * primeFormConjHom h (idGram K n) A * α⁻¹ =
      primeFormConjHom h (idGram K n) (idActU' h n hn hne α A) := by
  obtain ⟨⟨M, σ⟩, rfl⟩ := surjective_primeFormPsi_of_ne hn hne α
  rw [idActU'_primeFormPsi, idUAction_mk]
  have h1 := primeFormField_conj_eq h (isPrimeFormGram_idGram (K := K) (n := n)) σ A
  rw [primeFormPsi_apply, map_mul, map_mul, map_inv, ← h1]
  group

theorem det_idAct' (α : MulAut (primeFormP h (idGram K n))) {X : Matrix (Fin n) (Fin n) K}
    (hX : X.det = 1) : (idAct' h n hn hne α X).det = 1 := by
  obtain ⟨⟨M, σ⟩, rfl⟩ := surjective_primeFormPsi_of_ne hn hne α
  rw [idAct'_primeFormPsi, idMatAction_mk, Matrix.det_mul, Matrix.det_mul]
  have hMM : ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det *
      (((M : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have hσ : (X.map σ).det = 1 := by
    rw [show X.map σ = (σ : K →+* K).mapMatrix X from rfl, ← RingHom.map_det, hX, map_one]
  rw [hσ, mul_one, hMM]

variable {p : ℕ} {x : gramSU h (idGram K n)} (L : PlaneData h n p x)

include L in
theorem PlaneData.idAct'_eq_of_conj_eq (α : MulAut (primeFormP h (idGram K n)))
    (hα : α * primeFormConjHom h (idGram K n) (liftUnitary x) * α⁻¹ =
      primeFormConjHom h (idGram K n) (liftUnitary x)) :
    idAct' h n L.three_le L.ne α ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  have hn := L.three_le
  have hne := L.ne
  set y := idActU' h n hn hne α (liftUnitary x) with hy
  have hymat : ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      idAct' h n hn hne α ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := coe_idActU' hn hne α _
  have hyρ : primeFormConjHom h (idGram K n) y =
      primeFormConjHom h (idGram K n) (liftUnitary x) := by
    rw [← conj_primeFormConjHom' hn hne α, hα]
  have hdet : (((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).det = 1 := by
    rw [hymat]
    exact det_idAct' hn hne α x.2.2
  let y' : gramSU h (idGram K n) := ⟨y, y.2, hdet⟩
  have hxp : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = 1 := by
    have := congrArg (fun z : gramSU h (idGram K n) => ((z : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K)) L.pow_eq_one
    simpa using this
  have hyp : y' ^ p = 1 := by
    apply Subtype.ext
    apply Units.ext
    have h1 : (((y' ^ p : gramSU h (idGram K n)) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        (idAct' h n hn hne α ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ^ p := by
      rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]
      exact congrArg (· ^ p) hymat
    rw [h1, ← map_pow, hxp, map_one]
    rfl
  have hπ : (y' : primeFormP h (idGram K n)) = (x : primeFormP h (idGram K n)) := by
    apply conj_injective_of_ne hn hne
    rw [← primeFormConjHom_eq_conj h _ y', ← primeFormConjHom_eq_conj h _ x]
    exact hyρ
  have hyx : y' = x :=
    eq_of_mk_eq_of_pow_eq_one_of_noTorsion L.noTorsion (by omega) hyp L.pow_eq_one hπ
  rw [← hymat]
  exact congrArg (fun z : gramSU h (idGram K n) => ((z : GL (Fin n) K) :
    Matrix (Fin n) (Fin n) K)) hyx

theorem idAct'_eq_idAct (hn : 3 ≤ n) (hq : 3 < ℓ ^ f) :
    idAct' h n hn (not_three_two hq) = idAct h n hn hq := by
  refine MonoidHom.ext fun α => ?_
  obtain ⟨g, rfl⟩ := surjective_primeFormPsi hn hq α
  rw [idAct'_primeFormPsi, idAct_primeFormPsi]

theorem idActU'_eq_idActU (hn : 3 ≤ n) (hq : 3 < ℓ ^ f) :
    idActU' h n hn (not_three_two hq) = idActU h n hn hq := by
  refine MonoidHom.ext fun α => ?_
  obtain ⟨g, rfl⟩ := surjective_primeFormPsi hn hq α
  rw [idActU'_primeFormPsi, idActU_primeFormPsi]

end Act

end CFSG.RankThree.PartOne.KCUnitaryModel
