module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

set_option maxRecDepth 100000

public section

namespace CFSG.Quasithin.C124.YL.A6

open Equiv

abbrev P6 : Type := Perm (Fin 6)

@[expose] def eqP (a b : P6) : Bool :=
  a 0 == b 0 && a 1 == b 1 && a 2 == b 2 && a 3 == b 3 && a 4 == b 4 && a 5 == b 5

@[expose] def memP (x : P6) (l : List P6) : Bool := l.any (eqP x)

theorem eqP_iff {a b : P6} : eqP a b = true ↔ a = b := by
  constructor
  · intro h
    simp only [eqP, Bool.and_eq_true, beq_iff_eq] at h
    ext i
    fin_cases i <;> simp [h]
  · rintro rfl
    simp [eqP]

theorem memP_iff {x : P6} {l : List P6} : memP x l = true ↔ x ∈ l := by
  simp only [memP, List.any_eq_true, eqP_iff]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ha
  · intro h
    exact ⟨x, h, rfl⟩

@[expose] def klist : List P6 :=
  [1, swap 3 4 * swap 2 5, swap 3 4 * swap 0 1, swap 2 5 * swap 0 1]

@[expose] def plist : List P6 :=
  [1, swap 4 5 * swap 2 3, swap 3 5 * swap 2 4, swap 3 4 * swap 2 5, swap 3 4 * swap 0 1,
    swap 2 5 * swap 0 1, swap 4 5 * swap 3 4 * swap 2 4 * swap 0 1,
    swap 4 5 * swap 3 5 * swap 2 3 * swap 0 1]

@[expose] def totL : List P6 :=
  [swap 0 1 * swap 2 5 * swap 3 4, swap 0 4 * swap 1 2 * swap 3 5,
    swap 0 2 * swap 1 3 * swap 4 5, swap 0 5 * swap 1 4 * swap 2 3,
    swap 0 3 * swap 1 5 * swap 2 4]

@[expose] def witY : List P6 :=
  [1, swap 0 1 * swap 2 5, swap 0 2 * swap 4 5, swap 0 3 * swap 2 4, swap 0 4 * swap 3 5,
    swap 0 5 * swap 1 4]

@[expose] def inY (g : P6) : Bool :=
  (Perm.sign g == 1) && totL.all (fun t => totL.any (fun t' => eqP (g * t) (t' * g)))

theorem inY_iff {g : P6} : inY g = true ↔
    Perm.sign g = 1 ∧ ∀ t ∈ totL, ∃ t' ∈ totL, g * t = t' * g := by
  simp only [inY, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.any_eq_true, eqP_iff]

theorem klist_mul : ∀ a ∈ klist, ∀ b ∈ klist, memP (a * b) klist = true := by decide +kernel

theorem klist_inv : ∀ a ∈ klist, memP a⁻¹ klist = true := by decide +kernel

theorem plist_mul : ∀ a ∈ plist, ∀ b ∈ plist, memP (a * b) plist = true := by decide +kernel

theorem plist_inv : ∀ a ∈ plist, memP a⁻¹ plist = true := by decide +kernel

@[expose] def sgOfList (l : List P6) (h1 : memP 1 l = true)
    (hm : ∀ a ∈ l, ∀ b ∈ l, memP (a * b) l = true) (hi : ∀ a ∈ l, memP a⁻¹ l = true) :
    Subgroup P6 where
  carrier := {g | g ∈ l}
  one_mem' := memP_iff.1 h1
  mul_mem' := fun {a b} ha hb => memP_iff.1 (hm a ha b hb)
  inv_mem' := fun {a} ha => memP_iff.1 (hi a ha)

@[expose] def Kg : Subgroup P6 :=
  sgOfList klist (by decide +kernel) klist_mul klist_inv

@[expose] def Pg : Subgroup P6 :=
  sgOfList plist (by decide +kernel) plist_mul plist_inv

theorem inY_one : inY 1 = true := by decide +kernel

theorem inY_inv : ∀ g : P6, inY g = true → inY g⁻¹ = true := by decide +kernel

@[expose] def Yg : Subgroup P6 where
  carrier := {g | inY g = true}
  one_mem' := inY_one
  mul_mem' := fun {a b} ha hb => by
    obtain ⟨hsa, hta⟩ := inY_iff.1 ha
    obtain ⟨hsb, htb⟩ := inY_iff.1 hb
    refine inY_iff.2 ⟨by rw [map_mul, hsa, hsb]; rfl, fun t ht => ?_⟩
    obtain ⟨t', ht', e1⟩ := htb t ht
    obtain ⟨t'', ht'', e2⟩ := hta t' ht'
    exact ⟨t'', ht'', by rw [mul_assoc, e1, ← mul_assoc, e2, mul_assoc]⟩
  inv_mem' := fun {g} hg => inY_inv g hg

theorem mem_Yg {g : P6} : g ∈ Yg ↔ inY g = true := Iff.rfl

theorem Kg_le_Pg : Kg ≤ Pg := fun g hg =>
  memP_iff.1 ((by decide +kernel : ∀ g ∈ klist, memP g plist = true) g hg)

theorem Kg_le_Yg : Kg ≤ Yg := fun g hg =>
  (by decide +kernel : ∀ g ∈ klist, inY g = true) g hg

theorem Pg_le_A6 : Pg ≤ alternatingGroup (Fin 6) := fun g hg => by
  rw [Equiv.Perm.mem_alternatingGroup]
  exact (by decide +kernel : ∀ g ∈ plist, Perm.sign g = 1) g hg

theorem Kg_le_A6 : Kg ≤ alternatingGroup (Fin 6) := Kg_le_Pg.trans Pg_le_A6

theorem Yg_le_A6 : Yg ≤ alternatingGroup (Fin 6) := fun g hg => by
  rw [Equiv.Perm.mem_alternatingGroup]
  exact (inY_iff.1 hg).1

theorem Pg_norm_Kg : ∀ p ∈ Pg, ∀ k ∈ Kg, p * k * p⁻¹ ∈ Kg := fun p hp k hk =>
  memP_iff.1 ((by decide +kernel : ∀ p ∈ plist, ∀ k ∈ klist,
    memP (p * k * p⁻¹) klist = true) p hp k hk)

theorem nu_mem_Pg : swap 4 5 * swap 2 3 ∈ Pg := memP_iff.1 (by decide +kernel :
  memP (swap 4 5 * swap 2 3) plist = true)

theorem nu_not_mem_Yg : swap 4 5 * swap 2 3 ∉ Yg := by
  rw [mem_Yg]
  have : inY (swap 4 5 * swap 2 3) = false := by decide +kernel
  simp [this]

theorem Kg_comm : ∀ a ∈ Kg, ∀ b ∈ Kg, a * b = b * a := fun a ha b hb =>
  eqP_iff.1 ((by decide +kernel : ∀ a ∈ klist, ∀ b ∈ klist, eqP (a * b) (b * a) = true) a ha b hb)

theorem Kg_sq : ∀ a ∈ Kg, a * a = 1 := fun a ha =>
  eqP_iff.1 ((by decide +kernel : ∀ a ∈ klist, eqP (a * a) 1 = true) a ha)

theorem Kg_ne_bot : Kg ≠ ⊥ := by
  intro h
  have : swap 3 4 * swap 2 5 ∈ Kg := memP_iff.1 (by decide +kernel :
    memP (swap 3 4 * swap 2 5) klist = true)
  rw [h, Subgroup.mem_bot] at this
  have h0 := congrArg (fun g : P6 => g 2) this
  revert h0
  decide +kernel

theorem Yg_trans : ∀ y : Fin 6, ∃ g ∈ Yg, g 0 = y := by
  have h1 : ∀ g ∈ witY, inY g = true := by decide +kernel
  have h2 : ∀ y : Fin 6, ∃ g ∈ witY, g 0 = y := by decide +kernel
  intro y
  obtain ⟨g, hg, e⟩ := h2 y
  exact ⟨g, h1 g hg, e⟩

theorem card_Yg : Nat.card Yg = 60 := by
  have h : (Finset.univ.filter (fun g : P6 => inY g = true)).card = 60 := by decide +kernel
  rw [← h, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  rfl

end CFSG.Quasithin.C124.YL.A6
