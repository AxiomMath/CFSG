module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphismCoset
public import CFSG.LinearAlgebra.LinearGroups.UnitaryHeisenberg

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups

universe u

variable {f : ℕ} {K : Type u} [Field K] (h : UnitaryFieldData 2 f K)

@[expose] def fieldDataHermitianForm : HermitianForm 3 K where
  conj := RingEquiv.ofBijective h.bar (Function.Involutive.bijective h.bar_bar)
  conj_involutive := h.bar_bar
  form := !![0, 0, 1; 0, 1, 0; 1, 0, 0]
  form_hermitian i j := by fin_cases i <;> fin_cases j <;> simp
  form_nondegenerate := by simp [Matrix.det_fin_three]

theorem fieldDataHermitianForm_conj (x : K) : (fieldDataHermitianForm h).conj x = h.bar x :=
  rfl

theorem card_fixed_fieldDataHermitianForm :
    Nat.card {x : K // (fieldDataHermitianForm h).conj x = x} = 2 ^ f :=
  (Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)).trans h.card_fixedField

@[expose] def heisenbergRoot : Subgroup (GL (Fin 3) K) where
  carrier := {g | ∃ a b : K, h.norm a + h.trace b = 0 ∧
    (g : Matrix (Fin 3) (Fin 3) K) = heisenbergMatrix h a b}
  one_mem' := ⟨0, 0, by simp [UnitaryFieldData.norm, UnitaryFieldData.trace],
    (heisenbergMatrix_zero_zero h).symm⟩
  mul_mem' := by
    rintro g g' ⟨a, b, hab, hg⟩ ⟨c, d, hcd, hg'⟩
    obtain ⟨hQ, hrel⟩ := (unitary_heisenberg_identities h).2.1 a b c d hab hcd
    exact ⟨a + c, b + d - h.bar a * c, hrel, by
      rw [Matrix.GeneralLinearGroup.coe_mul, hg, hg', hQ]⟩
  inv_mem' := by
    rintro g ⟨a, b, hab, hg⟩
    refine ⟨-a, h.bar b, ?_, by
      rw [Matrix.GeneralLinearGroup.coe_inv, hg, (unitary_heisenberg_identities h).2.2 a b hab]⟩
    simp only [UnitaryFieldData.norm, UnitaryFieldData.trace, map_neg, h.bar_bar] at hab ⊢
    linear_combination hab

@[expose] def heisenbergCoordHom :
    hermitianUnipotentCoord (fieldDataHermitianForm h) →* GL (Fin 3) K :=
  (fieldDataHermitianForm h).specialSubgroup.subtype.comp (hermitianUnipotentSU _ rfl)

theorem coe_heisenbergCoordHom (z : hermitianUnipotentCoord (fieldDataHermitianForm h)) :
    ((heisenbergCoordHom h z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      heisenbergMatrix h (-h.bar z.1.1) z.1.2 := by
  change hermitianUnipotentMatrix _ z = _
  rw [hermitianUnipotentMatrix_eq, heisenbergMatrix, map_neg, h.bar_bar, neg_neg]
  rfl

theorem heisenbergMatrix_inj {a b c d : K} :
    heisenbergMatrix h a b = heisenbergMatrix h c d ↔ a = c ∧ b = d := by
  refine ⟨fun hQ => ⟨?_, ?_⟩, fun hQ => by rw [hQ.1, hQ.2]⟩
  · simpa [heisenbergMatrix] using congrFun (congrFun hQ 1) 2
  · simpa [heisenbergMatrix] using congrFun (congrFun hQ 0) 2

theorem heisenbergCoordHom_mem (z : hermitianUnipotentCoord (fieldDataHermitianForm h)) :
    heisenbergCoordHom h z ∈ heisenbergRoot h := by
  refine ⟨-h.bar z.1.1, z.1.2, ?_, coe_heisenbergCoordHom h z⟩
  have hz := z.2
  simp only [fieldDataHermitianForm_conj] at hz
  simp only [UnitaryFieldData.norm, UnitaryFieldData.trace, map_neg, h.bar_bar]
  linear_combination hz

@[expose] def heisenbergRootEquiv :
    hermitianUnipotentCoord (fieldDataHermitianForm h) ≃* heisenbergRoot h :=
  MulEquiv.ofBijective ((heisenbergCoordHom h).codRestrict _ (heisenbergCoordHom_mem h)) (by
    refine ⟨fun z w hzw => ?_, ?_⟩
    · have hQ := congrArg (fun x : heisenbergRoot h =>
        ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hzw
      simp only [MonoidHom.codRestrict_apply, coe_heisenbergCoordHom, heisenbergMatrix_inj,
        neg_inj] at hQ
      exact coord_ext (h.bar_bar z.1.1 ▸ h.bar_bar w.1.1 ▸ congrArg h.bar hQ.1) hQ.2
    · rintro ⟨g, a, b, hab, hg⟩
      refine ⟨⟨(-h.bar a, b), ?_⟩, Subtype.ext (Matrix.GeneralLinearGroup.ext fun i j => ?_)⟩
      · simp only [UnitaryFieldData.norm, UnitaryFieldData.trace] at hab
        change b + h.bar b + -h.bar a * h.bar (-h.bar a) = 0
        rw [map_neg, h.bar_bar]
        linear_combination hab
      · change (heisenbergCoordHom h _ : Matrix (Fin 3) (Fin 3) K) i j = (g : Matrix _ _ K) i j
        rw [coe_heisenbergCoordHom, hg]
        change heisenbergMatrix h (-h.bar (-h.bar a)) b i j = _
        rw [map_neg, h.bar_bar, neg_neg])

theorem coe_heisenbergRootEquiv (z : hermitianUnipotentCoord (fieldDataHermitianForm h)) :
    ((heisenbergRootEquiv h z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      heisenbergMatrix h (-h.bar z.1.1) z.1.2 :=
  coe_heisenbergCoordHom h z

theorem coe_eq_heisenbergMatrix (x : heisenbergRoot h) :
    ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      heisenbergMatrix h (-h.bar ((heisenbergRootEquiv h).symm x).1.1)
        ((heisenbergRootEquiv h).symm x).1.2 := by
  rw [← coe_heisenbergRootEquiv, MulEquiv.apply_symm_apply]

theorem coord_of_coe_eq {x : heisenbergRoot h} {a b : K}
    (hx : ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = heisenbergMatrix h a b) :
    ((heisenbergRootEquiv h).symm x).1.1 = -h.bar a ∧ ((heisenbergRootEquiv h).symm x).1.2 = b := by
  rw [coe_eq_heisenbergMatrix, heisenbergMatrix_inj] at hx
  refine ⟨?_, hx.2⟩
  rw [← hx.1, map_neg, h.bar_bar, neg_neg]

theorem entry_one_two (x : heisenbergRoot h) :
    ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 2 =
      -h.bar ((heisenbergRootEquiv h).symm x).1.1 := by
  rw [coe_eq_heisenbergMatrix]
  simp [heisenbergMatrix]

@[expose] def heisenbergRootCenter : Subgroup (heisenbergRoot h) :=
  rootCenter (fieldDataHermitianForm h) (heisenbergRootEquiv h)

instance : (heisenbergRootCenter h).Normal :=
  inferInstanceAs (rootCenter _ _).Normal

theorem mem_heisenbergRootCenter (x : heisenbergRoot h) :
    x ∈ heisenbergRootCenter h ↔ ∃ b ∈ h.fixedField,
      ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = heisenbergMatrix h 0 b := by
  have : CharP K 2 := h.charP
  rw [heisenbergRootCenter, mem_rootCenter]
  constructor
  · intro hx
    refine ⟨((heisenbergRootEquiv h).symm x).1.2, ?_, ?_⟩
    · exact conj_snd_of_fst_eq_zero (fieldDataHermitianForm h) hx
    · rw [coe_eq_heisenbergMatrix, hx, map_zero, neg_zero]
  · rintro ⟨b, -, hx⟩
    rw [(coord_of_coe_eq h hx).1, map_zero, neg_zero]

theorem coe_fieldInvolution {x : heisenbergRoot h} {a b : K}
    (hx : ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = heisenbergMatrix h a b) :
    ((fieldInvolution (fieldDataHermitianForm h) (heisenbergRootEquiv h) x : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = heisenbergMatrix h (h.bar a) (h.bar b) := by
  obtain ⟨h₁, h₂⟩ := coord_of_coe_eq h hx
  rw [coe_eq_heisenbergMatrix, symm_fieldInvolution_apply, fst_rootTau, snd_rootTau, h₁, h₂,
    fieldDataHermitianForm_conj, fieldDataHermitianForm_conj, map_neg, h.bar_bar, map_neg,
    neg_neg]

@[expose] def heisenbergRootBar : MulAut (heisenbergRoot h) :=
  fieldInvolution (fieldDataHermitianForm h) (heisenbergRootEquiv h)

theorem coe_heisenbergRootBar {x : heisenbergRoot h} {a b : K}
    (hx : ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = heisenbergMatrix h a b) :
    ((heisenbergRootBar h x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      heisenbergMatrix h (h.bar a) (h.bar b) :=
  coe_fieldInvolution h hx

end CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism
