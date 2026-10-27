module

public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationNineModel
public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationQ
import all CFSG.Quasithin.EmptyFaithful.A10ConfigurationModel
import all CFSG.Quasithin.EmptyFaithful.A10ConfigurationFacts
import all CFSG.Quasithin.EmptyFaithful.A10ConfigurationClasses
import all CFSG.Quasithin.EmptyFaithful.A10ConfigurationQ
import all CFSG.Quasithin.EmptyFaithful.A10ConfigurationNineModel

public section

namespace CFSG.Quasithin.A10

open CFSG.Open CFSG.Quasithin S4 Wc

def ptList (ℓ : Bool) : List Wc :=
  if ℓ then [z0, ⟨f1, 1, false⟩, ⟨f2, 1, false⟩, ⟨1, f1, false⟩, ⟨1, f2, false⟩]
  else [z0, ⟨f1, tau, false⟩, ⟨f2, tau, false⟩, ⟨tau, f1, false⟩, ⟨tau, f2, false⟩]

def ptm (ℓ : Bool) (i : Fin 5) : Wc := (ptList ℓ).getD i.val 1

theorem ptm_zero (ℓ : Bool) : ptm ℓ 0 = z0 := by cases ℓ <;> decide +kernel

theorem A2_sq : ∀ w ∈ A2, w * w = 1 := by decide +kernel

theorem ptm_mem_A2 : ∀ ℓ : Bool, ∀ i : Fin 5, ptm ℓ i ∈ A2 := by decide +kernel

theorem ptm_sq : ∀ ℓ : Bool, ∀ i : Fin 5, ptm ℓ i * ptm ℓ i = 1 := by decide +kernel

theorem ptm_comm : ∀ ℓ : Bool, ∀ i j : Fin 5, ptm ℓ i * ptm ℓ j = ptm ℓ j * ptm ℓ i := by
  decide +kernel

theorem ptm_inj : ∀ ℓ : Bool, ∀ i j : Fin 5, ptm ℓ i = ptm ℓ j → i = j := by decide +kernel

theorem ptm_one_two : ∀ ℓ : Bool, ptm ℓ 1 * ptm ℓ 2 = t0 := by decide +kernel

theorem ptm_three_four : ∀ ℓ : Bool, ptm ℓ 3 * ptm ℓ 4 = t0' := by decide +kernel

theorem A2_cases : ∀ ℓ : Bool, ∀ w ∈ A2,
    w = 1 ∨ (∃ i : Fin 5, w = ptm ℓ i) ∨ ∃ i j : Fin 5, i < j ∧ w = ptm ℓ i * ptm ℓ j := by
  decide +kernel

theorem pair_inj : ∀ ℓ : Bool, ∀ i j k l : Fin 5, i ≠ j → k ≠ l →
    ptm ℓ i * ptm ℓ j = ptm ℓ k * ptm ℓ l → (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
  decide +kernel

theorem pair_ne_pt : ∀ ℓ : Bool, ∀ i j k : Fin 5, i ≠ j → ptm ℓ i * ptm ℓ j ≠ ptm ℓ k := by
  decide +kernel

theorem pair_ne_one : ∀ ℓ : Bool, ∀ i j : Fin 5, i ≠ j → ptm ℓ i * ptm ℓ j ≠ 1 := by
  decide +kernel

theorem yset_iff_pt : ∀ ℓ : Bool, ∀ w : Wc,
    (w = z0 ∨ (ℓ = true ∧ w ∈ A2 ∧ D3 w = true) ∨ ((!ℓ) = true ∧ w ∈ A2 ∧ D5 w = true)) ↔
      ∃ i : Fin 5, w = ptm ℓ i := by
  decide +kernel

theorem mem_Yset_iff_pt (ℓ : Bool) (w : Wc) : w ∈ Yset ℓ (!ℓ) ↔ ∃ i : Fin 5, w = ptm ℓ i := by
  rw [mem_Yset]
  exact yset_iff_pt ℓ w

def s3 : Equiv.Perm (Fin 5) := Equiv.swap 0 4 * Equiv.swap 0 3

def sw12 : Equiv.Perm (Fin 5) := Equiv.swap 1 2

def sw34 : Equiv.Perm (Fin 5) := Equiv.swap 3 4

theorem s3_apply : s3 0 = 3 ∧ s3 3 = 4 ∧ s3 4 = 0 ∧ s3 1 = 1 ∧ s3 2 = 2 := by decide +kernel

theorem perm_classify : ∀ σ : Equiv.Perm (Fin 5), σ ^ 3 = 1 →
    ((σ 1 = 1 ∧ σ 2 = 2) ∨ (σ 1 = 2 ∧ σ 2 = 1)) → σ ≠ 1 → σ = s3 ∨ σ = s3⁻¹ := by
  decide +kernel

theorem sw12_fix : sw12 0 = 0 ∧ sw12 3 = 3 ∧ sw12 4 = 4 := by decide +kernel

theorem sw12_s3 : sw12 * s3 * sw12⁻¹ * s3⁻¹ = 1 := by decide +kernel

theorem sw34_s3 : sw34 * s3 * sw34⁻¹ * s3 = 1 := by decide +kernel

def e1 : Wc := ⟨v2, 1, false⟩

def u1 : Wc := ⟨1, v2, false⟩

theorem e1_act : ∀ ℓ : Bool, ∀ i : Fin 5, e1 * ptm ℓ i * e1⁻¹ = ptm ℓ (sw12 i) := by
  decide +kernel

theorem u1_act : ∀ ℓ : Bool, ∀ i : Fin 5, u1 * ptm ℓ i * u1⁻¹ = ptm ℓ (sw34 i) := by
  decide +kernel

theorem e1_u1 : e1 * u1 = u1 * e1 := by decide +kernel

theorem e1_transvection : ∀ w ∈ A2, e1 * w * e1⁻¹ * w = 1 ∨ e1 * w * e1⁻¹ * w = t0 := by
  decide +kernel

def E0h : Subgroup Wc := baseSub V ⊥

instance : DecidablePred (· ∈ E0h) :=
  inferInstanceAs (DecidablePred (· ∈ baseSub V ⊥))

theorem E0h_cases : ∀ w ∈ E0h, w = 1 ∨ w = t0 ∨ w = e1 ∨ w = e1 * t0 := by decide +kernel

theorem t0_mem_E0h : t0 ∈ E0h := by decide +kernel

theorem e1_mem_E0h : e1 ∈ E0h := by decide +kernel

def wList (ℓ : Bool) : List Wc := [1, t0', z0 * ptm ℓ 3, z0 * ptm ℓ 4]

theorem wList_mul : ∀ ℓ : Bool, ∀ x ∈ wList ℓ, ∀ y ∈ wList ℓ, x * y ∈ wList ℓ := by
  decide +kernel

theorem wList_inv : ∀ ℓ : Bool, ∀ x ∈ wList ℓ, x⁻¹ ∈ wList ℓ := by decide +kernel

def Wm (ℓ : Bool) : Subgroup Wc where
  carrier := {w | w ∈ wList ℓ}
  one_mem' := by cases ℓ <;> decide +kernel
  mul_mem' := fun {a b} ha hb => wList_mul ℓ a ha b hb
  inv_mem' := fun {a} ha => wList_inv ℓ a ha

theorem mem_Wm {ℓ : Bool} {w : Wc} : w ∈ Wm ℓ ↔ w ∈ wList ℓ := Iff.rfl

instance (ℓ : Bool) : DecidablePred (· ∈ Wm ℓ) := fun x =>
  decidable_of_iff (x ∈ wList ℓ) mem_Wm.symm

theorem mem_Wm_iff {ℓ : Bool} {w : Wc} :
    w ∈ Wm ℓ ↔ w = 1 ∨ w = ptm ℓ 3 * ptm ℓ 4 ∨ w = ptm ℓ 0 * ptm ℓ 3 ∨ w = ptm ℓ 0 * ptm ℓ 4 := by
  rw [mem_Wm, wList]
  have h1 := ptm_three_four ℓ
  have h0 := ptm_zero ℓ
  rw [h0, ← h1]
  simp only [List.mem_cons, List.not_mem_nil, or_false]

theorem card_Wm : ∀ ℓ : Bool, Nat.card (Wm ℓ) = 4 := by
  intro ℓ
  rw [card_eq_finset_card]
  cases ℓ <;> decide +kernel

theorem Wm_le_A2 : ∀ ℓ : Bool, Wm ℓ ≤ A2 := by
  intro ℓ w hw
  have key : ∀ ℓ : Bool, ∀ w ∈ wList ℓ, w ∈ A2 := by decide +kernel
  exact key ℓ w hw

theorem Wm_s3 : ∀ ℓ : Bool, ∀ i j : Fin 5,
    ((i = 0 ∧ j = 3) ∨ (i = 0 ∧ j = 4) ∨ (i = 3 ∧ j = 4)) →
      ptm ℓ (s3 i) * ptm ℓ (s3 j) ∈ Wm ℓ := by
  decide +kernel

theorem Wm_fixed : ∀ ℓ : Bool, ∀ i j : Fin 5,
    ((i = 0 ∧ j = 3) ∨ (i = 0 ∧ j = 4) ∨ (i = 3 ∧ j = 4)) →
      ptm ℓ (s3 i) * ptm ℓ (s3 j) ≠ ptm ℓ i * ptm ℓ j := by
  decide +kernel

theorem norm_pt : ∀ ℓ : Bool, ∀ i : Fin 5,
    ptm ℓ i * ptm ℓ (s3 i) * ptm ℓ (s3 (s3 i)) ≠ 1 := by decide +kernel

theorem norm_pair : ∀ ℓ : Bool, ∀ i j : Fin 5, i < j →
    ptm ℓ i * ptm ℓ j * (ptm ℓ (s3 i) * ptm ℓ (s3 j)) *
      (ptm ℓ (s3 (s3 i)) * ptm ℓ (s3 (s3 j))) = 1 →
    (i = 0 ∧ j = 3) ∨ (i = 0 ∧ j = 4) ∨ (i = 3 ∧ j = 4) := by decide +kernel

theorem eq2_pair : ∀ ℓ : Bool, ∀ i j : Fin 5,
    ((i = 0 ∧ j = 3) ∨ (i = 0 ∧ j = 4) ∨ (i = 3 ∧ j = 4)) →
    (ptm ℓ (sw34 i) * ptm ℓ (sw34 j) * (ptm ℓ (s3⁻¹ i) * ptm ℓ (s3⁻¹ j)) = 1 ∨
      ptm ℓ (sw34 i) * ptm ℓ (sw34 j) * (ptm ℓ (s3⁻¹ i) * ptm ℓ (s3⁻¹ j)) = t0) →
    i = 0 ∧ j = 3 := by decide +kernel

theorem bad_model : ∀ ℓ : Bool, ∃ m : Wc, m⁻¹ * z0 * m = e1 * z0 ∧
    ¬ ∀ w ∈ wList ℓ, m * w * m⁻¹ ∈ Qh := by decide +kernel

instance : DecidablePred (· ∈ (A2 ⊓ Qh : Subgroup Wc)) := fun x =>
  decidable_of_iff (x ∈ A2 ∧ x ∈ Qh) Subgroup.mem_inf.symm

theorem card_A2_inf_Qh : Nat.card (A2 ⊓ Qh : Subgroup Wc) = 8 := by
  rw [card_eq_finset_card]
  decide +kernel

end CFSG.Quasithin.A10
