module

public import CFSG.OddTranspositions.PartThree.Eleven.Five.Hom
import CFSG.OddTranspositions.PartThree.Eleven.Five.FiveFormAux

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.ClassicalGroups.Orthogonal
open Matrix
open scoped commutatorElement
open FiveAux FiveHom

private theorem det_sq_eq_one_of_mem_four_true_false {g : GL (Fin 5) (ZMod 5)}
    (hg : g ∈ fiveReflectionGroup 4 true false) :
    ((Matrix.GeneralLinearGroup.det g : (ZMod 5)ˣ) : ZMod 5) ^ 2 = 1 := by
  classical
  refine Subgroup.closure_induction (p := fun g _ =>
    ((Matrix.GeneralLinearGroup.det g : (ZMod 5)ˣ) : ZMod 5) ^ 2 = 1) ?_ ?_ ?_ ?_ hg
  · intro r hr
    obtain ⟨x, hx, hπ, rfl⟩ := exists_eq_fiveReflOf hr
    have hrr : fiveReflOf 4 true x * fiveReflOf 4 true x = 1 := by
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_one]
      exact fiveReflMatrix_mul_self 4 true x
    have hdet : Matrix.GeneralLinearGroup.det (fiveReflOf 4 true x) *
        Matrix.GeneralLinearGroup.det (fiveReflOf 4 true x) = 1 := by
      rw [← map_mul, hrr, map_one]
    rw [pow_two, ← Units.val_mul, hdet]
    rfl
  · simp
  · intro x y hx hy hpx hpy
    rw [map_mul, Units.val_mul, mul_pow, hpx, hpy, one_mul]
  · intro x hx hpx
    rw [map_inv, Units.val_inv_eq_inv_val, inv_pow, hpx, inv_one]

theorem fivePlusMap_mem_O_of_mem_four_true_false {g : GL (Fin 5) (ZMod 5)}
    (hg : g ∈ fiveReflectionGroup 4 true false) :
    fiveGLEquiv (fivePlusMap g) ∈ FiveSquareFrameGeneration.O := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro x
  rw [fivePlusMap_apply_vec, Q_smul, det_sq_eq_one_of_mem_four_true_false hg, one_mul]
  have hmat : (((fiveT * g * fiveT⁻¹ : GL (Fin 5) (ZMod 5)) :
      Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ x) =
      (fiveT : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ
        ((g : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ
          (((fiveT⁻¹ : GL (Fin 5) (ZMod 5)) :
            Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ x)) := by
    simp only [Matrix.GeneralLinearGroup.coe_mul]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [hmat, Q_T, fiveForm_mulVec_of_mem hg, Q_Tinv]

private abbrev GL5 := GL (Fin 5) (ZMod 5)

private abbrev R5 : Subgroup GL5 := fiveReflectionGroup 4 true false

private noncomputable def fiveMinusPsi : ↥R5 →* (V5 ≃ₗ[ZMod 5] V5) :=
  fiveGLEquiv.toMonoidHom.comp (fivePlusMap.comp R5.subtype)

private theorem fiveMinusPsi_range_le_O :
    fiveMinusPsi.range ≤ FiveSquareFrameGeneration.O := by
  rintro _ ⟨g, rfl⟩
  exact fivePlusMap_mem_O_of_mem_four_true_false g.2

private theorem fiveMinusPsi_mem_derived_of_mem_commutator {k : ↥R5}
    (hk : k ∈ commutator ↥R5) : fiveMinusPsi k ∈ FiveSquareFrameGeneration.derived := by
  have h := Subgroup.mem_map_of_mem fiveMinusPsi hk
  rw [map_commutator_eq] at h
  exact Subgroup.commutator_mono fiveMinusPsi_range_le_O fiveMinusPsi_range_le_O h

private noncomputable def fiveMinusDerivedHom :
    ↥(commutator ↥R5) →* ↥FiveSquareFrameGeneration.derived where
  toFun k := ⟨fiveGLEquiv (fivePlusMap k.1.1), by
    have h := fiveMinusPsi_mem_derived_of_mem_commutator k.2
    simpa [fiveMinusPsi, MonoidHom.comp_apply] using h⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' := by
    intro a b
    apply Subtype.ext
    simp [map_mul]

private theorem fiveMinusDerivedHom_apply (k : ↥(commutator ↥R5)) :
    ((fiveMinusDerivedHom k : ↥FiveSquareFrameGeneration.derived) : V5 ≃ₗ[ZMod 5] V5) =
      fiveGLEquiv (fivePlusMap k.1.1) := rfl

private noncomputable def fiveMinusDetHom : ↥R5 →* (ZMod 5)ˣ :=
  Matrix.GeneralLinearGroup.det.comp R5.subtype

private theorem fiveMinusDerivedHom_eq_one {z : ↥(commutator ↥R5)}
    (hz : fiveMinusDerivedHom z = 1) : z = 1 := by
  have hfive : fiveGLEquiv (fivePlusMap z.1.1) = 1 := by
    have h := congrArg (fun w : ↥FiveSquareFrameGeneration.derived =>
      (w : V5 ≃ₗ[ZMod 5] V5)) hz
    simpa [fiveMinusDerivedHom] using h
  have hmap : fivePlusMap z.1.1 = 1 := by
    apply fiveGLEquiv.injective
    rw [hfive, map_one]
  have hdet : Matrix.GeneralLinearGroup.det z.1.1 = 1 := by
    have hker : fiveMinusDetHom z.1 = 1 :=
      MonoidHom.mem_ker.mp (Abelianization.commutator_subset_ker fiveMinusDetHom z.2)
    simpa [fiveMinusDetHom] using hker
  have hT : fiveT * z.1.1 * fiveT⁻¹ = 1 := by
    have h := hmap
    rw [show fivePlusMap z.1.1 = Matrix.GeneralLinearGroup.scalar (Fin 5)
        (Matrix.GeneralLinearGroup.det z.1.1) * (fiveT * z.1.1 * fiveT⁻¹) from rfl,
      hdet, map_one, one_mul] at h
    exact h
  apply Subtype.ext
  apply Subtype.ext
  calc z.1.1 = fiveT⁻¹ * (fiveT * z.1.1 * fiveT⁻¹) * fiveT := by group
    _ = 1 := by rw [hT]; group

private theorem fiveMinusDerivedHom_injective : Function.Injective fiveMinusDerivedHom := by
  intro x y hxy
  have h1 : fiveMinusDerivedHom (x * y⁻¹) = 1 := by
    rw [map_mul, map_inv, hxy, mul_inv_cancel]
  have h2 : x * y⁻¹ = 1 := fiveMinusDerivedHom_eq_one h1
  calc x = x * y⁻¹ * y := by group
    _ = 1 * y := by rw [h2]
    _ = y := by rw [one_mul]

private theorem conj_mem_fiveReflectionGroup_four_true_false
    {g : GL5}
    (hg : ∀ x y, fiveForm 4 true ((g : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ x)
      ((g : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ y) = fiveForm 4 true x y)
    {x : GL5} (hx : x ∈ R5) : g * x * g⁻¹ ∈ R5 := by
  refine Subgroup.closure_induction (p := fun x _ => g * x * g⁻¹ ∈ R5) ?_ ?_ ?_ ?_ hx
  · intro r hr
    exact Subgroup.subset_closure (conj_mem_fiveReflections hg hr)
  · simp
  · intro x y _ _ ihx ihy
    rw [show g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) by group]
    exact mul_mem ihx ihy
  · intro x _ ih
    rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]
    exact inv_mem ih

private theorem fiveMinusDerivedHom_range_normal :
    fiveMinusDerivedHom.range.Normal := by
  refine ⟨fun n hn d => ?_⟩
  obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hn
  have hdO : (d : V5 ≃ₗ[ZMod 5] V5) ∈ FiveSquareFrameGeneration.O :=
    Subgroup.commutator_le_self FiveSquareFrameGeneration.O d.2
  obtain ⟨g, hg, hconj⟩ := exists_isometry_fivePlusMap_conj hdO
  let c : ↥R5 →* ↥R5 :=
    { toFun := fun x =>
        ⟨g * x.1 * g⁻¹, conj_mem_fiveReflectionGroup_four_true_false hg x.2⟩
      map_one' := by ext; simp
      map_mul' := by
        intro x y
        ext
        simp only [Subgroup.coe_mul]
        group }
  have hc : (commutator ↥R5).map c ≤ commutator ↥R5 := by
    rw [map_commutator_eq]
    exact Subgroup.commutator_mono le_top le_top
  let k' : ↥(commutator ↥R5) := ⟨c k.1, hc (Subgroup.mem_map_of_mem c k.2)⟩
  refine MonoidHom.mem_range.mpr ⟨k', ?_⟩
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [fiveMinusDerivedHom_apply, fiveMinusDerivedHom_apply]
  rw [show k'.1.1 = g * k.1.1 * g⁻¹ from rfl, hconj (k.1.1)]

private def va : V5 := Pi.single 0 1 + Pi.single 1 1

private def vb : V5 := Pi.single 1 1 + Pi.single 2 1

private theorem fiveForm_va : fiveForm 4 true va va = 2 := by
  simp [fiveForm, va, Pi.single_apply, Fin.sum_univ_four]
  decide

private theorem fiveForm_vb : fiveForm 4 true vb vb = 2 := by
  simp [fiveForm, vb, Pi.single_apply, Fin.sum_univ_four]
  decide

private theorem fiveReflOf_va_mem : fiveReflOf 4 true va ∈ R5 := by
  apply Subgroup.subset_closure
  refine fiveReflOf_mem ?_ ?_
  · rw [fiveForm_va]; decide
  · rw [fiveForm_va]; decide

private theorem fiveReflOf_vb_mem : fiveReflOf 4 true vb ∈ R5 := by
  apply Subgroup.subset_closure
  refine fiveReflOf_mem ?_ ?_
  · rw [fiveForm_vb]; decide
  · rw [fiveForm_vb]; decide

private theorem inv_two : ((1 + 1 - 0 : ZMod 5))⁻¹ = 3 :=
  ZMod.inv_eq_of_mul_eq_one 5 (1 + 1 - 0) 3 (by decide)

private theorem commutator_va_vb_ne_one :
    ⁅fiveReflOf 4 true va, fiveReflOf 4 true vb⁆ ≠ (1 : GL5) := by
  intro h
  have hcomm : fiveReflOf 4 true va * fiveReflOf 4 true vb =
      fiveReflOf 4 true vb * fiveReflOf 4 true va :=
    commutatorElement_eq_one_iff_mul_comm.mp h
  have hleft : (fiveReflOf 4 true va * fiveReflOf 4 true vb :
      Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ Pi.single 0 1 = -Pi.single 1 1 := by
    rw [← Matrix.mulVec_mulVec, fiveReflOf_mulVec, fiveReflOf_mulVec]
    ext i
    fin_cases i <;>
      simp [fiveForm, va, vb, Pi.single_apply, Fin.sum_univ_four, Pi.sub_apply, Pi.smul_apply]
    all_goals try rw [inv_two]
    all_goals decide
  have hright : (fiveReflOf 4 true vb * fiveReflOf 4 true va :
      Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ Pi.single 0 1 = Pi.single 2 1 := by
    rw [← Matrix.mulVec_mulVec, fiveReflOf_mulVec, fiveReflOf_mulVec]
    ext i
    fin_cases i <;>
      simp [fiveForm, va, vb, Pi.single_apply, Fin.sum_univ_four, Pi.sub_apply, Pi.smul_apply]
    all_goals try rw [inv_two]
    all_goals decide
  have h0 : (fiveReflOf 4 true va * fiveReflOf 4 true vb :
      Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ Pi.single 0 1 =
      (fiveReflOf 4 true vb * fiveReflOf 4 true va :
      Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ Pi.single 0 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_mul, ← Matrix.GeneralLinearGroup.coe_mul, hcomm]
  have hcontra : (-Pi.single 1 1 : V5) = Pi.single 2 1 := by
    rw [← hleft, h0, hright]
  exact (by decide : ¬((-Pi.single 1 1 : V5) = Pi.single 2 1)) hcontra

private theorem fiveMinusDerivedHom_range_ne_bot :
    fiveMinusDerivedHom.range ≠ ⊥ := by
  intro hbot
  have hk_mem : ⁅(⟨fiveReflOf 4 true va, fiveReflOf_va_mem⟩ : ↥R5),
      (⟨fiveReflOf 4 true vb, fiveReflOf_vb_mem⟩ : ↥R5)⁆ ∈ commutator ↥R5 :=
    Subgroup.commutator_mem_commutator (H₁ := ⊤) (H₂ := ⊤)
      (Subgroup.mem_top _) (Subgroup.mem_top _)
  let k : ↥(commutator ↥R5) :=
    ⟨⁅(⟨fiveReflOf 4 true va, fiveReflOf_va_mem⟩ : ↥R5),
      (⟨fiveReflOf 4 true vb, fiveReflOf_vb_mem⟩ : ↥R5)⁆, hk_mem⟩
  have hk1 : fiveMinusDerivedHom k = 1 := by
    have hmem : fiveMinusDerivedHom k ∈ (⊥ : Subgroup ↥FiveSquareFrameGeneration.derived) := by
      rw [← hbot]
      exact MonoidHom.mem_range.mpr ⟨k, rfl⟩
    simpa using hmem
  have hk : k = 1 := fiveMinusDerivedHom_eq_one hk1
  have hkval : (k.1 : ↥R5) = 1 := by
    have h := congrArg (fun z : ↥(commutator ↥R5) => z.1) hk
    simpa using h
  have hval : ⁅fiveReflOf 4 true va, fiveReflOf 4 true vb⁆ = (1 : GL5) := by
    have h := congrArg R5.subtype hkval
    dsimp [k] at h
    have h2 : ((⁅(⟨fiveReflOf 4 true va, fiveReflOf_va_mem⟩ : ↥R5),
        (⟨fiveReflOf 4 true vb, fiveReflOf_vb_mem⟩ : ↥R5)⁆ : ↥R5) : GL5) =
        ⁅fiveReflOf 4 true va, fiveReflOf 4 true vb⁆ :=
      map_commutatorElement R5.subtype
        (⟨fiveReflOf 4 true va, fiveReflOf_va_mem⟩ : ↥R5)
        (⟨fiveReflOf 4 true vb, fiveReflOf_vb_mem⟩ : ↥R5)
    rw [h2] at h
    simpa using h
  exact commutator_va_vb_ne_one hval

theorem nonempty_commutator_fiveReflectionGroup_four_true_false_mulEquiv :
    Nonempty (commutator (fiveReflectionGroup 4 true false) ≃*
      FiveSquareFrameGeneration.derived) := by
  haveI : IsSimpleGroup FiveSquareFrameGeneration.derived :=
    FiveSquareFrameGeneration.derived_isSimpleGroup
  haveI hnormal : fiveMinusDerivedHom.range.Normal := fiveMinusDerivedHom_range_normal
  have htop : fiveMinusDerivedHom.range = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal fiveMinusDerivedHom.range with h | h
    · exact absurd h fiveMinusDerivedHom_range_ne_bot
    · exact h
  have hsurj : Function.Surjective fiveMinusDerivedHom := MonoidHom.range_eq_top.mp htop
  exact ⟨MulEquiv.ofBijective fiveMinusDerivedHom
    ⟨fiveMinusDerivedHom_injective, hsurj⟩⟩

end CFSG.OddTranspositions.PartThree
