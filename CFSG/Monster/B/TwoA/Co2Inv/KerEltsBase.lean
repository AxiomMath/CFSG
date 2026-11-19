
module

public import CFSG.Monster.B.TwoA.Co2Inv.FrameCertInputs
public import CFSG.Monster.B.TwoA.Co2Inv.KerDataInputs
public import CFSG.Monster.B.TwoA.Co2Inv.MrBase

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Co2Inv

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B.Co2 CFSG.Monster.VisCert CFSG.Monster.B.Short
  CFSG.Monster.Visible CFSG.Monster.ScalarKernel CFSG.Monster.VisQuot CFSG.Monster.SpinLattice
  CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Census CFSG.Monster.Lifts

theorem xor_lt_two {a b : ℕ} (ha : a < 2) (hb : b < 2) : a ^^^ b < 2 :=
  Nat.xor_lt_two_pow (n := 1) ha hb

theorem xor_lt_sixteen {a b : ℕ} (ha : a < 16) (hb : b < 16) : a ^^^ b < 16 :=
  Nat.xor_lt_two_pow (n := 4) ha hb

def affC (e l : ℕ) : C := if h : bvec 24 (affMask e l) ∈ C then ⟨_, h⟩ else 0

theorem coe_dC_eq : (dC : Fin 24 → ZMod 2) = bvec 24 255 := by decide +kernel

theorem dC_apply_eq_zero (i : Fin 24) : (dC : Fin 24 → ZMod 2) i = 0 ↔ ¬ (i : ℕ) < 8 := by
  rw [dC_apply]
  split_ifs with h <;> simp [h]

def Tperm : Subgroup AutPerm where
  carrier := {p | ∀ i : Fin 24, (i : ℕ) < 8 → (p : Equiv.Perm (Fin 24)) i = i}
  one_mem' := fun _ _ => rfl
  mul_mem' {p q} hp hq i hi := by
    change (p : Equiv.Perm (Fin 24)) ((q : Equiv.Perm (Fin 24)) i) = i
    rw [hq i hi, hp i hi]
  inv_mem' {p} hp i hi := by
    change ((p : Equiv.Perm (Fin 24)))⁻¹ i = i
    rw [Equiv.Perm.inv_eq_iff_eq, hp i hi]

theorem mem_Tperm {p : AutPerm} :
    p ∈ Tperm ↔ ∀ i : Fin 24, (i : ℕ) < 8 → (p : Equiv.Perm (Fin 24)) i = i := Iff.rfl

theorem Tperm_le_Foct : Tperm ≤ Foct := by
  intro p hp
  refine mem_Foct.2 ⟨(mem_Ppair_iff p).2 (Or.inl ⟨hp 0 (by decide), hp 1 (by decide)⟩), ?_⟩
  intro i
  constructor
  · intro hi
    rw [hp i hi]
    exact hi
  · intro hpi
    by_contra hi
    have h := hp ((p : Equiv.Perm (Fin 24)) i) hpi
    exact hi ((p : Equiv.Perm (Fin 24)).injective h ▸ hpi)

theorem fixJ_eq_true {a : Array ℕ} (ha : PermArr a = true)
    (h : ∀ i : Fin 24, (i : ℕ) < 8 → decode a i = i) : fixJ a = true := by
  rw [fixJ, List.all_eq_true]
  intro j hj
  have hj8 := List.mem_range.1 hj
  have e := congrArg Fin.val (h ⟨j, by omega⟩ hj8)
  rw [decode_apply ha] at e
  exact beq_iff_eq.2 e

theorem mk_monomial_eq {x y : C} {p q : AutPerm}
    (h : (QuotientGroup.mk (gO x * PO p) : OLq) = QuotientGroup.mk (gO y * PO q)) :
    (y = x ∨ y = x + VisQuot.ΩC) ∧ q = p := by
  rw [QuotientGroup.eq, mem_zpowers_negOneO_iff] at h
  rcases h with h | h
  · have := gO_mul_PO_inj (inv_mul_eq_one.1 h)
    exact ⟨Or.inl this.1.symm, this.2.symm⟩
  · have e : gO y * PO q = gO (x + VisQuot.ΩC) * PO p := by
      rw [gO_add, gO_ΩC, mul_assoc, negOneO_mul_comm, ← mul_assoc, ← h, mul_inv_cancel_left]
    have := gO_mul_PO_inj e
    exact ⟨Or.inr this.1, this.2⟩

def Agrp : Subgroup OLq where
  carrier := {x | ∃ c : C, (c : Fin 24 → ZMod 2) ∈ CJc (dC : Fin 24 → ZMod 2) ∧
    x = QuotientGroup.mk (gO c)}
  one_mem' := ⟨0, Submodule.zero_mem _, by rw [gO_zero, QuotientGroup.mk_one]⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, Submodule.add_mem _ ha hb, by rw [gO_add, QuotientGroup.mk_mul]⟩
  inv_mem' := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨a, ha, ?_⟩
    rw [← QuotientGroup.mk_inv, inv_eq_of_mul_eq_one_right (gO_mul_self a)]

def Tgrp : Subgroup OLq where
  carrier := {x | ∃ p ∈ Tperm, x = QuotientGroup.mk (PO p)}
  one_mem' := ⟨1, Tperm.one_mem, by rw [PO_one, QuotientGroup.mk_one]⟩
  mul_mem' := by
    rintro _ _ ⟨p, hp, rfl⟩ ⟨q, hq, rfl⟩
    exact ⟨q * p, Tperm.mul_mem hq hp, by rw [PO_mul, QuotientGroup.mk_mul]⟩
  inv_mem' := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨p⁻¹, Tperm.inv_mem hp, by rw [PO_inv, QuotientGroup.mk_inv]⟩

def Qgrp : Subgroup OLq := Agrp ⊔ Tgrp

end CFSG.Monster.B.TwoA.Co2Inv
