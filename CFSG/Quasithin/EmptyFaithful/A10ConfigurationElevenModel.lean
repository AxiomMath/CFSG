module

public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationTenModel
import all CFSG.Quasithin.EmptyFaithful.A10ConfigurationModel
import all CFSG.Quasithin.EmptyFaithful.A10ConfigurationFacts
import all CFSG.Quasithin.EmptyFaithful.A10ConfigurationClasses
import all CFSG.Quasithin.EmptyFaithful.A10ConfigurationNineModel
import all CFSG.Quasithin.EmptyFaithful.A10ConfigurationTenModel
public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationCaseModel

public section

namespace CFSG.Quasithin.A10

open CFSG.Open CFSG.Quasithin S4 Wc

def alt4Pred (x : S4) : Bool := vList.contains x || (x * x * x == 1)

def Alt4 : Subgroup S4 where
  carrier := {x | alt4Pred x = true}
  one_mem' := by decide +kernel
  mul_mem' := by
    intro a b ha hb
    have key : ∀ a b : S4, alt4Pred a = true → alt4Pred b = true → alt4Pred (a * b) = true := by
      decide +kernel
    exact key a b ha hb
  inv_mem' := by
    intro a ha
    have key : ∀ a : S4, alt4Pred a = true → alt4Pred a⁻¹ = true := by decide +kernel
    exact key a ha

theorem mem_Alt4 {x : S4} : x ∈ Alt4 ↔ alt4Pred x = true := Iff.rfl

instance : DecidablePred (· ∈ Alt4) := fun x => decidable_of_iff (alt4Pred x = true) mem_Alt4.symm

def H1m : Subgroup Wc := baseSub ⊥ Alt4

instance : DecidablePred (· ∈ H1m) := inferInstanceAs (DecidablePred (· ∈ baseSub ⊥ Alt4))

theorem H1m_comm_E0 : ∀ x ∈ E0h, ∀ y ∈ H1m, x * y = y * x := by decide +kernel

theorem H1m_odd : ∀ y ∈ H1m, ∃ a ∈ H1m, ∃ b ∈ H1m, a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ y = a * b := by
  decide +kernel

theorem V2_conj : ∀ y ∈ baseSub ⊥ V, y ≠ 1 → ∃ m ∈ H1m, m⁻¹ * y * m = t0' := by decide +kernel

theorem V2_le_H1m : baseSub ⊥ V ≤ H1m := by
  intro y hy
  have key : ∀ y ∈ baseSub ⊥ V, y ∈ H1m := by decide +kernel
  exact key y hy

theorem Jh_center : ∀ f ∈ Jh, (∀ g ∈ Jh, f * g = g * f) → f = 1 ∨ f = t0 ∨ f = t0' ∨ f = z0 := by
  decide +kernel

theorem t0'_eq : t0' = t0 * z0 := by decide +kernel

theorem T2h_decomp : ∀ y ∈ T2h, ∃ v ∈ baseSub ⊥ V, ∃ w ∈ Wm false, y = v * w := by
  decide +kernel

theorem T2h_inv : ∀ y ∈ T2h, y ≠ 1 → y * y = 1 → y ∈ baseSub ⊥ V ∨ y ∈ Wm false := by
  decide +kernel

def dmap : DihedralGroup 4 → Wc
  | DihedralGroup.r i => (⟨1, S4.r, false⟩ : Wc) ^ i.val
  | DihedralGroup.sr i => (⟨1, f1, false⟩ : Wc) * (⟨1, S4.r, false⟩ : Wc) ^ i.val

theorem dmap_mul : ∀ x y : DihedralGroup 4, dmap (x * y) = dmap x * dmap y := by decide +kernel

theorem dmap_inj : Function.Injective dmap := by decide +kernel

theorem dmap_mem : ∀ x : DihedralGroup 4, dmap x ∈ T2h := by decide +kernel

def dhom : DihedralGroup 4 →* Wc := MonoidHom.mk' dmap dmap_mul

theorem dhom_injective : Function.Injective dhom := dmap_inj

theorem dhom_range : dhom.range = T2h := by
  have hle : dhom.range ≤ T2h := by
    rintro _ ⟨x, rfl⟩
    exact dmap_mem x
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have h1 : Nat.card dhom.range = Nat.card (DihedralGroup 4) :=
    (Nat.card_congr (MonoidHom.ofInjective dhom_injective).toEquiv).symm
  have h2 : Nat.card (DihedralGroup 4) = 8 := by
    rw [Nat.card_eq_fintype_card]
    decide
  rw [h1, h2, card_T2h]

theorem z0_conj_e1u1 : ∃ m : Wc, m⁻¹ * z0 * m = e1 * u1 := by decide +kernel

theorem e1u1_conj_e1t0' : ∃ m : Wc, m⁻¹ * (e1 * u1) * m = e1 * t0' := by decide +kernel

theorem wrong_conj : ∃ m : Wc, m⁻¹ * (e1 * (ptm true 0 * ptm true 4)) * m =
    ptm true 0 * ptm true 4 := by decide +kernel

def Fv2 : Subgroup S4 :=
  subOfList [1, v2] (by decide +kernel) (by decide +kernel) (by decide +kernel)

def Ftau : Subgroup S4 :=
  subOfList [1, tau] (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem mem_Fv2 {x : S4} : x ∈ Fv2 ↔ x ∈ [1, v2] := Iff.rfl
theorem mem_Ftau {x : S4} : x ∈ Ftau ↔ x ∈ [1, tau] := Iff.rfl

instance : DecidablePred (· ∈ Fv2) := fun x => decidable_of_iff (x ∈ [1, v2]) mem_Fv2.symm
instance : DecidablePred (· ∈ Ftau) := fun x => decidable_of_iff (x ∈ [1, tau]) mem_Ftau.symm

def S0m : Subgroup Wc := baseSub V D

def Kv2 : Subgroup Wc := baseSub Fv2 D

def Ktau : Subgroup Wc := baseSub Ftau D

instance : DecidablePred (· ∈ S0m) := inferInstanceAs (DecidablePred (· ∈ baseSub V D))
instance : DecidablePred (· ∈ Kv2) := inferInstanceAs (DecidablePred (· ∈ baseSub Fv2 D))
instance : DecidablePred (· ∈ Ktau) := inferInstanceAs (DecidablePred (· ∈ baseSub Ftau D))

theorem card_S0m : Nat.card S0m = 32 := by
  rw [card_eq_finset_card]
  decide +kernel

theorem Kv2_le_S0m : Kv2 ≤ S0m := by
  intro y hy
  have key : ∀ y ∈ Kv2, y ∈ S0m := by decide +kernel
  exact key y hy

theorem Ktau_le_S0m : Ktau ≤ S0m := by
  intro y hy
  have key : ∀ y ∈ Ktau, y ∈ S0m := by decide +kernel
  exact key y hy

theorem S0m_comm_E0 : ∀ x ∈ E0h, ∀ y ∈ S0m, x * y = y * x := by decide +kernel

theorem Kv2_normal : ∀ h ∈ S0m, ∀ k ∈ Kv2, h * k * h⁻¹ ∈ Kv2 := by decide +kernel

theorem Ktau_normal : ∀ h ∈ S0m, ∀ k ∈ Ktau, h * k * h⁻¹ ∈ Ktau := by decide +kernel

theorem Kv2_comm : ∀ x ∈ S0m, ∀ y ∈ S0m, x * y * x⁻¹ * y⁻¹ ∈ Kv2 := by decide +kernel

theorem Ktau_comm : ∀ x ∈ S0m, ∀ y ∈ S0m, x * y * x⁻¹ * y⁻¹ ∈ Ktau := by decide +kernel

theorem t0_not_mem_Kv2 : t0 ∉ Kv2 := by decide +kernel

theorem e1_not_mem_Ktau : e1 ∉ Ktau := by decide +kernel

theorem e1t0_not_mem_Ktau : e1 * t0 ∉ Ktau := by decide +kernel

theorem t0_mem_S0m : t0 ∈ S0m := by decide +kernel

theorem e1_mem_S0m : e1 ∈ S0m := by decide +kernel

theorem e1t0_mem_S0m : e1 * t0 ∈ S0m := by decide +kernel

theorem E0h_comm : ∀ x ∈ E0h, ∀ y ∈ E0h, x * y = y * x := by decide +kernel

theorem card_E0h : Nat.card E0h = 4 := by
  rw [card_eq_finset_card]
  decide +kernel

theorem e1_ne_one : e1 ≠ 1 := by decide +kernel

theorem e1_ne_t0 : e1 ≠ t0 := by decide +kernel

theorem e1_conj_t0 : ∃ m : Wc, m⁻¹ * t0 * m = e1 := by decide +kernel

theorem e1t0_conj_t0 : ∃ m : Wc, m⁻¹ * t0 * m = e1 * t0 := by decide +kernel

theorem W_norm : ∀ ℓ : Bool, ∀ i j : Fin 5,
    ((i = 0 ∧ j = 3) ∨ (i = 0 ∧ j = 4) ∨ (i = 3 ∧ j = 4)) →
    ptm ℓ i * ptm ℓ j * (ptm ℓ (s3 i) * ptm ℓ (s3 j)) *
      (ptm ℓ (s3 (s3 i)) * ptm ℓ (s3 (s3 j))) = 1 := by decide +kernel

theorem T2h_comm_t0' : ∀ y ∈ T2h, y * t0' = t0' * y := by decide +kernel

theorem t0'_ne_one : t0' ≠ 1 := by decide +kernel

theorem t0'_sq : t0' * t0' = 1 := by decide +kernel

theorem t0_mul_t0'_eq : t0 * t0' = z0 := by decide +kernel

end CFSG.Quasithin.A10
