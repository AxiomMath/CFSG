
module

public import CFSG.Monster.B.TwoA.Co2Inv.RowsInputs
public import CFSG.Monster.B.TwoA.Base.FrameBase

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Co2Inv

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B.Co2 CFSG.Monster.VisCert CFSG.Monster.B.Short
  CFSG.Monster.Visible CFSG.Monster.ScalarKernel CFSG.Monster.VisQuot CFSG.Monster.SpinLattice
  CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Census CFSG.Monster.Lifts

@[expose] def PresJ (p : Equiv.Perm (Fin 24)) : Prop := ∀ i : Fin 24, (i : ℕ) < 8 ↔ (p i : ℕ) < 8

theorem presJ_mul {p q : Equiv.Perm (Fin 24)} (hp : PresJ p) (hq : PresJ q) : PresJ (p * q) :=
  fun i => (hq i).trans (hp (q i))

theorem presJ_inv {p : Equiv.Perm (Fin 24)} (hp : PresJ p) : PresJ p⁻¹ := fun i => by
  have := hp (p⁻¹ i)
  rw [show p (p⁻¹ i) = i from p.apply_symm_apply i] at this
  exact this.symm

@[expose] def Foct : Subgroup AutPerm where
  carrier := {p | p ∈ Ppair ∧ PresJ (p : Equiv.Perm (Fin 24))}
  one_mem' := ⟨Ppair.one_mem, fun _ => Iff.rfl⟩
  mul_mem' := fun ⟨hp, hpJ⟩ ⟨hq, hqJ⟩ => ⟨Ppair.mul_mem hp hq, presJ_mul hpJ hqJ⟩
  inv_mem' := fun ⟨hp, hpJ⟩ => ⟨Ppair.inv_mem hp, presJ_inv hpJ⟩

theorem mem_Foct {p : AutPerm} : p ∈ Foct ↔ p ∈ Ppair ∧ PresJ (p : Equiv.Perm (Fin 24)) :=
  Iff.rfl

theorem Foct_le_Ppair : Foct ≤ Ppair := fun _ hp => hp.1

theorem foctHyp : MonoHyp Ceq Foct :=
  ⟨ceqHyp.le_C, ceqHyp.Ω_mem, fun p hp a ha => ceqHyp.preserves p hp.1 a ha⟩

theorem dC_apply : ∀ i : Fin 24,
    ((dC : C) : Fin 24 → ZMod 2) i = if (i : ℕ) < 8 then 1 else 0 := by decide +kernel

theorem hammingNorm_dC : hammingNorm ((dC : C) : Fin 24 → ZMod 2) = 8 := by decide +kernel

theorem hammingNorm_dC_add_Ω : hammingNorm (((dC + VisQuot.ΩC : C)) : Fin 24 → ZMod 2) = 16 := by
  decide +kernel

theorem permC_dC_iff (p : AutPerm) : permC p dC = dC ↔ PresJ (p : Equiv.Perm (Fin 24)) := by
  constructor
  · intro h i
    have e := congrFun (congrArg (fun x : C => (x : Fin 24 → ZMod 2)) h)
      ((p : Equiv.Perm (Fin 24)) i)
    simp only [coe_permC, permWord_apply] at e
    rw [dC_apply, dC_apply] at e
    by_cases hi : (i : ℕ) < 8 <;>
      by_cases hpi : (((p : Equiv.Perm (Fin 24)) i : Fin 24) : ℕ) < 8
    · exact iff_of_true hi hpi
    · rw [ite_eq_left hi, ite_eq_right hpi] at e
      exact absurd e (by decide)
    · rw [ite_eq_right hi, ite_eq_left hpi] at e
      exact absurd e (by decide)
    · exact iff_of_false hi hpi
  · intro h
    apply Subtype.ext
    funext i
    rw [coe_permC, permWord_apply', dC_apply, dC_apply]
    have := presJ_inv h i
    by_cases hi : (i : ℕ) < 8
    · rw [ite_eq_left (this.1 hi), ite_eq_left hi]
    · rw [ite_eq_right (fun h' => hi (this.2 h')), ite_eq_right hi]

theorem mk_eq_mk_monomial_iff {x y : C} {p : AutPerm} :
    (QuotientGroup.mk (gO x * PO p) : OLq) = QuotientGroup.mk (gO y * PO p) ↔
      y = x ∨ y = x + VisQuot.ΩC := by
  rw [QuotientGroup.eq, mem_zpowers_negOneO_iff]
  constructor
  · rintro (h | h)
    · left
      exact (gO_mul_PO_inj (inv_mul_eq_one.1 h).symm).1
    · right
      have e : gO y * PO p = gO (x + VisQuot.ΩC) * PO p := by
        rw [gO_add, gO_ΩC, mul_assoc, negOneO_mul_comm, ← mul_assoc, ← h, mul_inv_cancel_left]
      exact (gO_mul_PO_inj e).1
  · rintro (rfl | rfl)
    · left
      exact inv_mul_cancel _
    · right
      rw [gO_add, gO_ΩC, mul_assoc (gO x), negOneO_mul_comm, ← mul_assoc (gO x),
        inv_mul_cancel_left]

end CFSG.Monster.B.TwoA.Co2Inv
