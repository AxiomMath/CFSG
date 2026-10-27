module

public import CFSG.Fischer.F4
public import Mathlib.Algebra.Group.Equiv.Finite
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin.F112R.St84.Heis

open CFSG.Fischer
open scoped commutatorElement

local instance (priority := high) f4DecEq : DecidableEq F4 := fun a b =>
  decidable_of_iff (a.code = b.code) (by cases a; cases b; simp)

theorem F4.ext_code {x y : F4} (h : x.code = y.code) : x = y := by
  cases x; cases y; simpa using h

@[ext] structure Q1M where
  a : F4
  b : F4
  c : F4
deriving Fintype

@[expose] def Q1M.decEq (p q : Q1M) : Decidable (p = q) :=
  decidable_of_iff (p.a.code = q.a.code ∧ p.b.code = q.b.code ∧ p.c.code = q.c.code) (by
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact Q1M.ext (F4.ext_code h1) (F4.ext_code h2) (F4.ext_code h3)
    · rintro rfl
      exact ⟨rfl, rfl, rfl⟩)

instance : DecidableEq Q1M := Q1M.decEq

namespace Q1M

@[expose] def mul (p q : Q1M) : Q1M := ⟨p.a + q.a, p.b + q.b, p.c + q.c + p.a * q.b⟩

instance : Mul Q1M := ⟨mul⟩

instance : One Q1M := ⟨⟨0, 0, 0⟩⟩

instance : Inv Q1M := ⟨fun p => ⟨-p.a, -p.b, -p.c + p.a * p.b⟩⟩

theorem mul_def (p q : Q1M) :
    p * q = ⟨p.a + q.a, p.b + q.b, p.c + q.c + p.a * q.b⟩ := rfl

theorem one_def : (1 : Q1M) = ⟨0, 0, 0⟩ := rfl

theorem inv_def (p : Q1M) : p⁻¹ = ⟨-p.a, -p.b, -p.c + p.a * p.b⟩ := rfl

instance : Group Q1M where
  mul_assoc p q r := by
    ext <;> simp only [mul_def] <;> ring
  one_mul p := by
    ext <;> simp only [mul_def, one_def] <;> ring
  mul_one p := by
    ext <;> simp only [mul_def, one_def] <;> ring
  inv_mul_cancel p := by
    ext <;> simp only [mul_def, inv_def, one_def] <;> ring

end Q1M

theorem card_Q1M : Nat.card Q1M = 64 := by
  rw [Nat.card_eq_fintype_card]
  decide

@[expose] def e1 : Q1M := ⟨1, 0, 0⟩

@[expose] def e2 : Q1M := ⟨F4.ω, 0, 0⟩

@[expose] def f1 : Q1M := ⟨0, 1, 0⟩

@[expose] def f2 : Q1M := ⟨0, F4.ω, 0⟩

@[expose] def zc : Q1M := ⟨0, 0, 1⟩

@[expose] def E (a : F4) : Q1M := e1 ^ (a.code.val % 2) * e2 ^ (a.code.val / 2)

@[expose] def F (b : F4) : Q1M := f1 ^ (b.code.val % 2) * f2 ^ (b.code.val / 2)

@[expose] def C (c : F4) : Q1M := ⟨0, 0, c⟩

theorem E_val : ∀ a : F4, E a = ⟨a, 0, 0⟩ := by decide +kernel

theorem F_val : ∀ b : F4, F b = ⟨0, b, 0⟩ := by decide +kernel

theorem C_eq_comm : ∀ c : F4, C c = ⁅e1, F c⁆ := by decide +kernel

theorem normal_form : ∀ a b c : F4, E a * F b * C (c + a * b) = ⟨a, b, c⟩ := by decide +kernel

theorem e1_mem : e1 ∈ Subgroup.closure ({e1, e2, f1, f2} : Set Q1M) :=
  Subgroup.subset_closure (by simp)

theorem e2_mem : e2 ∈ Subgroup.closure ({e1, e2, f1, f2} : Set Q1M) :=
  Subgroup.subset_closure (by simp)

theorem f1_mem : f1 ∈ Subgroup.closure ({e1, e2, f1, f2} : Set Q1M) :=
  Subgroup.subset_closure (by simp)

theorem f2_mem : f2 ∈ Subgroup.closure ({e1, e2, f1, f2} : Set Q1M) :=
  Subgroup.subset_closure (by simp)

theorem closure_gens : Subgroup.closure ({e1, e2, f1, f2} : Set Q1M) = ⊤ := by
  apply le_antisymm le_top
  intro q _
  obtain ⟨a, b, c⟩ := q
  rw [← normal_form a b c]
  have hE : E a ∈ Subgroup.closure ({e1, e2, f1, f2} : Set Q1M) :=
    Subgroup.mul_mem _ (Subgroup.pow_mem _ e1_mem _) (Subgroup.pow_mem _ e2_mem _)
  have hF : F b ∈ Subgroup.closure ({e1, e2, f1, f2} : Set Q1M) :=
    Subgroup.mul_mem _ (Subgroup.pow_mem _ f1_mem _) (Subgroup.pow_mem _ f2_mem _)
  have hF' : F (c + a * b) ∈ Subgroup.closure ({e1, e2, f1, f2} : Set Q1M) :=
    Subgroup.mul_mem _ (Subgroup.pow_mem _ f1_mem _) (Subgroup.pow_mem _ f2_mem _)
  have hC : C (c + a * b) ∈ Subgroup.closure ({e1, e2, f1, f2} : Set Q1M) := by
    rw [C_eq_comm (c + a * b)]
    exact Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ e1_mem hF') (Subgroup.inv_mem _ e1_mem))
      (Subgroup.inv_mem _ hF')
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hE hF) hC

theorem hom_ext {H : Type*} [Group H] {φ ψ : Q1M →* H}
    (h1 : φ e1 = ψ e1) (h2 : φ e2 = ψ e2) (h3 : φ f1 = ψ f1) (h4 : φ f2 = ψ f2) :
    φ = ψ := by
  apply MonoidHom.eq_of_eqOn_dense closure_gens
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> assumption

theorem aut_ext {α γ : MulAut Q1M}
    (h1 : α e1 = γ e1) (h2 : α e2 = γ e2) (h3 : α f1 = γ f1) (h4 : α f2 = γ f2) :
    α = γ := by
  refine MulEquiv.ext fun q => ?_
  exact DFunLike.congr_fun (hom_ext (φ := α.toMonoidHom) (ψ := γ.toMonoidHom) h1 h2 h3 h4) q

@[expose] def βM : MulAut Q1M where
  toFun p := ⟨F4.ω * F4.ω * p.a, F4.ω * p.b, p.c⟩
  invFun p := ⟨F4.ω * p.a, F4.ω * F4.ω * p.b, p.c⟩
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_mul' := by decide +kernel

@[expose] def ρM : MulAut Q1M where
  toFun p := ⟨F4.ω * F4.ω * p.a, F4.ω * F4.ω * p.b, F4.ω * p.c⟩
  invFun p := ⟨F4.ω * p.a, F4.ω * p.b, F4.ω * F4.ω * p.c⟩
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_mul' := by decide +kernel

@[expose] def τM : MulAut Q1M where
  toFun p := ⟨p.b * p.b, p.a * p.a, p.c * p.c + (p.a * p.a) * (p.b * p.b)⟩
  invFun p := ⟨p.b * p.b, p.a * p.a, p.c * p.c + (p.a * p.a) * (p.b * p.b)⟩
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_mul' := by decide +kernel

@[expose] def γM : MulAut Q1M where
  toFun p := ⟨p.b, p.a, p.c + p.a * p.b⟩
  invFun p := ⟨p.b, p.a, p.c + p.a * p.b⟩
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_mul' := by decide +kernel

def AJ3 : Subgroup (MulAut Q1M) := Subgroup.closure {ρM, βM}

def AJ : Subgroup (MulAut Q1M) := Subgroup.closure {ρM, βM, τM}

def AJ' : Subgroup (MulAut Q1M) := Subgroup.closure {ρM, βM, τM, γM}

@[expose] def aj3List : List (MulAut Q1M) :=
  (List.ofFn fun i : Fin 3 => List.ofFn fun j : Fin 3 =>
    ρM ^ (i : ℕ) * βM ^ (j : ℕ)).flatten

@[expose] def ajList : List (MulAut Q1M) :=
  (List.ofFn fun i : Fin 3 => List.ofFn fun j : Fin 3 => List.ofFn fun k : Fin 2 =>
    ρM ^ (i : ℕ) * βM ^ (j : ℕ) * τM ^ (k : ℕ)).flatten.flatten

@[expose] def aj'List : List (MulAut Q1M) :=
  (List.ofFn fun i : Fin 3 => List.ofFn fun j : Fin 3 => List.ofFn fun k : Fin 2 =>
    List.ofFn fun l : Fin 2 =>
      ρM ^ (i : ℕ) * βM ^ (j : ℕ) * τM ^ (k : ℕ) * γM ^ (l : ℕ)).flatten.flatten.flatten

theorem aj3List_exponents_mem : ∀ i j : Fin 3,
    ρM ^ (i : ℕ) * βM ^ (j : ℕ) ∈ aj3List := by
  decide +kernel

theorem mem_aj3List {α : MulAut Q1M} :
    α ∈ aj3List ↔ ∃ i j : Fin 3, α = ρM ^ (i : ℕ) * βM ^ (j : ℕ) := by
  constructor
  · intro h
    rw [aj3List, List.mem_flatten] at h
    obtain ⟨l, hl, hx⟩ := h
    rw [List.mem_ofFn] at hl
    obtain ⟨i, rfl⟩ := hl
    rw [List.mem_ofFn] at hx
    obtain ⟨j, rfl⟩ := hx
    exact ⟨i, j, rfl⟩
  · rintro ⟨i, j, rfl⟩
    exact aj3List_exponents_mem i j

theorem ajList_exponents_mem : ∀ i j : Fin 3, ∀ k : Fin 2,
    ρM ^ (i : ℕ) * βM ^ (j : ℕ) * τM ^ (k : ℕ) ∈ ajList := by
  decide +kernel

theorem mem_ajList {α : MulAut Q1M} :
    α ∈ ajList ↔ ∃ i j : Fin 3, ∃ k : Fin 2, α = ρM ^ (i : ℕ) * βM ^ (j : ℕ) * τM ^ (k : ℕ) := by
  constructor
  · intro h
    rw [ajList, List.mem_flatten] at h
    obtain ⟨l, hl, hx⟩ := h
    rw [List.mem_flatten] at hl
    obtain ⟨m, hm, hlm⟩ := hl
    rw [List.mem_ofFn] at hm
    obtain ⟨i, rfl⟩ := hm
    rw [List.mem_ofFn] at hlm
    obtain ⟨j, rfl⟩ := hlm
    rw [List.mem_ofFn] at hx
    obtain ⟨k, rfl⟩ := hx
    exact ⟨i, j, k, rfl⟩
  · rintro ⟨i, j, k, rfl⟩
    exact ajList_exponents_mem i j k

theorem aj'List_exponents_mem : ∀ i j : Fin 3, ∀ k l : Fin 2,
    ρM ^ (i : ℕ) * βM ^ (j : ℕ) * τM ^ (k : ℕ) * γM ^ (l : ℕ) ∈ aj'List := by
  decide +kernel

theorem mem_aj'List {α : MulAut Q1M} :
    α ∈ aj'List ↔ ∃ i j : Fin 3, ∃ k l : Fin 2,
      α = ρM ^ (i : ℕ) * βM ^ (j : ℕ) * τM ^ (k : ℕ) * γM ^ (l : ℕ) := by
  constructor
  · intro h
    rw [aj'List, List.mem_flatten] at h
    obtain ⟨l, hl, hx⟩ := h
    rw [List.mem_flatten] at hl
    obtain ⟨m, hm, hlm⟩ := hl
    rw [List.mem_flatten] at hm
    obtain ⟨n, hn, hmn⟩ := hm
    rw [List.mem_ofFn] at hn
    obtain ⟨i, rfl⟩ := hn
    rw [List.mem_ofFn] at hmn
    obtain ⟨j, rfl⟩ := hmn
    rw [List.mem_ofFn] at hlm
    obtain ⟨k, rfl⟩ := hlm
    rw [List.mem_ofFn] at hx
    obtain ⟨l, rfl⟩ := hx
    exact ⟨i, j, k, l, rfl⟩
  · rintro ⟨i, j, k, l, rfl⟩
    exact aj'List_exponents_mem i j k l

theorem aj3List_mul : ∀ i j k l : Fin 3,
    (ρM ^ (i : ℕ) * βM ^ (j : ℕ)) * (ρM ^ (k : ℕ) * βM ^ (l : ℕ)) ∈ aj3List := by
  decide +kernel

theorem aj3List_inv : ∀ i j : Fin 3, (ρM ^ (i : ℕ) * βM ^ (j : ℕ))⁻¹ ∈ aj3List := by
  decide +kernel

def aj3Sub : Subgroup (MulAut Q1M) where
  carrier := {α | α ∈ aj3List}
  mul_mem' := by
    intro a b ha hb
    change a ∈ aj3List at ha
    change b ∈ aj3List at hb
    change a * b ∈ aj3List
    rw [mem_aj3List] at ha hb
    obtain ⟨i, j, rfl⟩ := ha
    obtain ⟨k, l, rfl⟩ := hb
    exact aj3List_mul i j k l
  one_mem' := by
    change (1 : MulAut Q1M) ∈ aj3List
    rw [mem_aj3List]
    exact ⟨0, 0, by simp⟩
  inv_mem' := by
    intro a ha
    change a ∈ aj3List at ha
    change a⁻¹ ∈ aj3List
    rw [mem_aj3List] at ha
    obtain ⟨i, j, rfl⟩ := ha
    exact aj3List_inv i j

theorem AJ3_eq_aj3Sub : AJ3 = aj3Sub := by
  apply le_antisymm
  · rw [AJ3, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · change ρM ∈ aj3List
      rw [mem_aj3List]
      exact ⟨1, 0, by simp⟩
    · change βM ∈ aj3List
      rw [mem_aj3List]
      exact ⟨0, 1, by simp⟩
  · intro x hx
    change x ∈ aj3List at hx
    rw [mem_aj3List] at hx
    obtain ⟨i, j, rfl⟩ := hx
    exact Subgroup.mul_mem _
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp [AJ3])) _)
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp [AJ3])) _)

theorem mem_AJ3_iff {α : MulAut Q1M} : α ∈ AJ3 ↔ α ∈ aj3List := by
  rw [AJ3_eq_aj3Sub]
  rfl

theorem ajList_mul : ∀ i j : Fin 3, ∀ k : Fin 2, ∀ i' j' : Fin 3, ∀ k' : Fin 2,
    (ρM ^ (i : ℕ) * βM ^ (j : ℕ) * τM ^ (k : ℕ)) *
      (ρM ^ (i' : ℕ) * βM ^ (j' : ℕ) * τM ^ (k' : ℕ)) ∈ ajList := by
  decide +kernel

theorem ajList_inv : ∀ i j : Fin 3, ∀ k : Fin 2,
    (ρM ^ (i : ℕ) * βM ^ (j : ℕ) * τM ^ (k : ℕ))⁻¹ ∈ ajList := by
  decide +kernel

def ajSub : Subgroup (MulAut Q1M) where
  carrier := {α | α ∈ ajList}
  mul_mem' := by
    intro a b ha hb
    change a ∈ ajList at ha
    change b ∈ ajList at hb
    change a * b ∈ ajList
    rw [mem_ajList] at ha hb
    obtain ⟨i, j, k, rfl⟩ := ha
    obtain ⟨i', j', k', rfl⟩ := hb
    exact ajList_mul i j k i' j' k'
  one_mem' := by
    change (1 : MulAut Q1M) ∈ ajList
    rw [mem_ajList]
    exact ⟨0, 0, 0, by simp⟩
  inv_mem' := by
    intro a ha
    change a ∈ ajList at ha
    change a⁻¹ ∈ ajList
    rw [mem_ajList] at ha
    obtain ⟨i, j, k, rfl⟩ := ha
    exact ajList_inv i j k

theorem AJ_eq_ajSub : AJ = ajSub := by
  apply le_antisymm
  · rw [AJ, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · change ρM ∈ ajList
      rw [mem_ajList]
      exact ⟨1, 0, 0, by simp⟩
    · change βM ∈ ajList
      rw [mem_ajList]
      exact ⟨0, 1, 0, by simp⟩
    · change τM ∈ ajList
      rw [mem_ajList]
      exact ⟨0, 0, 1, by simp⟩
  · intro x hx
    change x ∈ ajList at hx
    rw [mem_ajList] at hx
    obtain ⟨i, j, k, rfl⟩ := hx
    exact Subgroup.mul_mem _
      (Subgroup.mul_mem _
        (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp [AJ])) _)
        (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp [AJ])) _))
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp [AJ])) _)

theorem mem_AJ_iff {α : MulAut Q1M} : α ∈ AJ ↔ α ∈ ajList := by
  rw [AJ_eq_ajSub]
  rfl

theorem aj'List_mul : ∀ i j : Fin 3, ∀ k l : Fin 2, ∀ i' j' : Fin 3, ∀ k' l' : Fin 2,
    (ρM ^ (i : ℕ) * βM ^ (j : ℕ) * τM ^ (k : ℕ) * γM ^ (l : ℕ)) *
      (ρM ^ (i' : ℕ) * βM ^ (j' : ℕ) * τM ^ (k' : ℕ) * γM ^ (l' : ℕ)) ∈ aj'List := by
  decide +kernel

theorem aj'List_inv : ∀ i j : Fin 3, ∀ k l : Fin 2,
    (ρM ^ (i : ℕ) * βM ^ (j : ℕ) * τM ^ (k : ℕ) * γM ^ (l : ℕ))⁻¹ ∈ aj'List := by
  decide +kernel

def aj'Sub : Subgroup (MulAut Q1M) where
  carrier := {α | α ∈ aj'List}
  mul_mem' := by
    intro a b ha hb
    change a ∈ aj'List at ha
    change b ∈ aj'List at hb
    change a * b ∈ aj'List
    rw [mem_aj'List] at ha hb
    obtain ⟨i, j, k, l, rfl⟩ := ha
    obtain ⟨i', j', k', l', rfl⟩ := hb
    exact aj'List_mul i j k l i' j' k' l'
  one_mem' := by
    change (1 : MulAut Q1M) ∈ aj'List
    rw [mem_aj'List]
    exact ⟨0, 0, 0, 0, by simp⟩
  inv_mem' := by
    intro a ha
    change a ∈ aj'List at ha
    change a⁻¹ ∈ aj'List
    rw [mem_aj'List] at ha
    obtain ⟨i, j, k, l, rfl⟩ := ha
    exact aj'List_inv i j k l

theorem AJ'_eq_aj'Sub : AJ' = aj'Sub := by
  apply le_antisymm
  · rw [AJ', Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · change ρM ∈ aj'List
      rw [mem_aj'List]
      exact ⟨1, 0, 0, 0, by simp⟩
    · change βM ∈ aj'List
      rw [mem_aj'List]
      exact ⟨0, 1, 0, 0, by simp⟩
    · change τM ∈ aj'List
      rw [mem_aj'List]
      exact ⟨0, 0, 1, 0, by simp⟩
    · change γM ∈ aj'List
      rw [mem_aj'List]
      exact ⟨0, 0, 0, 1, by simp⟩
  · intro x hx
    change x ∈ aj'List at hx
    rw [mem_aj'List] at hx
    obtain ⟨i, j, k, l, rfl⟩ := hx
    have hρ : ρM ∈ AJ' := Subgroup.subset_closure (by simp [AJ'])
    have hβ : βM ∈ AJ' := Subgroup.subset_closure (by simp [AJ'])
    have hτ : τM ∈ AJ' := Subgroup.subset_closure (by simp [AJ'])
    have hγ : γM ∈ AJ' := Subgroup.subset_closure (by simp [AJ'])
    exact Subgroup.mul_mem _
      (Subgroup.mul_mem _
        (Subgroup.mul_mem _ (Subgroup.pow_mem _ hρ _) (Subgroup.pow_mem _ hβ _))
        (Subgroup.pow_mem _ hτ _))
      (Subgroup.pow_mem _ hγ _)

theorem mem_AJ'_iff {α : MulAut Q1M} : α ∈ AJ' ↔ α ∈ aj'List := by
  rw [AJ'_eq_aj'Sub]
  rfl

theorem aj3List_nodup : aj3List.Nodup := by decide +kernel

theorem ajList_nodup : ajList.Nodup := by decide +kernel

theorem aj'List_nodup : aj'List.Nodup := by decide +kernel

theorem card_AJ3 : Nat.card AJ3 = 9 := by
  have hset : (AJ3 : Set (MulAut Q1M)) = ↑aj3List.toFinset := by
    ext α
    rw [SetLike.mem_coe, mem_AJ3_iff]
    simp
  change Nat.card (AJ3 : Set (MulAut Q1M)) = 9
  rw [Nat.card_coe_set_eq, hset, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup aj3List_nodup]
  decide

theorem card_AJ : Nat.card AJ = 18 := by
  have hset : (AJ : Set (MulAut Q1M)) = ↑ajList.toFinset := by
    ext α
    rw [SetLike.mem_coe, mem_AJ_iff]
    simp
  change Nat.card (AJ : Set (MulAut Q1M)) = 18
  rw [Nat.card_coe_set_eq, hset, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup ajList_nodup]
  decide

theorem card_AJ' : Nat.card AJ' = 36 := by
  have hset : (AJ' : Set (MulAut Q1M)) = ↑aj'List.toFinset := by
    ext α
    rw [SetLike.mem_coe, mem_AJ'_iff]
    simp
  change Nat.card (AJ' : Set (MulAut Q1M)) = 36
  rw [Nat.card_coe_set_eq, hset, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup aj'List_nodup]
  decide

theorem AJ3_le_AJ : AJ3 ≤ AJ := by
  rw [AJ3, AJ]
  apply Subgroup.closure_mono
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  rcases hx with rfl | rfl <;> simp

theorem AJ_le_AJ' : AJ ≤ AJ' := by
  rw [AJ, AJ']
  apply Subgroup.closure_mono
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  rcases hx with rfl | rfl | rfl <;> simp

theorem aj'_conj_aj3_aux : ∀ i j : Fin 3, ∀ k l : Fin 2, ∀ i' j' : Fin 3,
    (ρM ^ (i : ℕ) * βM ^ (j : ℕ) * τM ^ (k : ℕ) * γM ^ (l : ℕ)) *
      (ρM ^ (i' : ℕ) * βM ^ (j' : ℕ)) *
      (ρM ^ (i : ℕ) * βM ^ (j : ℕ) * τM ^ (k : ℕ) * γM ^ (l : ℕ))⁻¹ ∈ aj3List := by
  decide +kernel

theorem aj'_conj_aj3 : ∀ i j : Fin 3, ∀ k l : Fin 2, ∀ h : MulAut Q1M, h ∈ aj3List →
    (ρM ^ (i : ℕ) * βM ^ (j : ℕ) * τM ^ (k : ℕ) * γM ^ (l : ℕ)) * h *
      (ρM ^ (i : ℕ) * βM ^ (j : ℕ) * τM ^ (k : ℕ) * γM ^ (l : ℕ))⁻¹ ∈ aj3List := by
  intro i j k l h hh
  rw [mem_aj3List] at hh
  obtain ⟨i', j', rfl⟩ := hh
  exact aj'_conj_aj3_aux i j k l i' j'

theorem AJ3_normal : (AJ3.subgroupOf AJ').Normal := by
  rw [Subgroup.normal_subgroupOf_iff (AJ3_le_AJ.trans AJ_le_AJ')]
  intro h k hh hk
  rw [mem_AJ3_iff] at hh
  rw [mem_AJ'_iff] at hk
  rw [mem_aj'List] at hk
  obtain ⟨i, j, k', l, rfl⟩ := hk
  exact mem_AJ3_iff.mpr (aj'_conj_aj3 i j k' l h hh)

end CFSG.Quasithin.F112R.St84.Heis
