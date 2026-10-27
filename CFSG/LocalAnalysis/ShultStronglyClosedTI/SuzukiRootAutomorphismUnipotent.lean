module

public import CFSG.LieType.Ree.SuzukiUnipotentStructure

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.SuzukiRootAutomorphism

open CFSG.Blueprint CFSG.LieType.Ree
open scoped commutatorElement

variable (a : ℕ) (K : Type) [Field K]

@[expose] def unipotentElt (u v : K) : suzukiU a K :=
  ⟨suzukiSElt a K u v, suzukiSElt_mem_suzukiU a K u v⟩

variable {a K}

@[expose] def unipotentFst (x : suzukiU a K) : K :=
  (((x : suzukiGroup a K) : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 1 0

@[expose] def unipotentSnd (x : suzukiU a K) : K :=
  (((x : suzukiGroup a K) : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 2 0

theorem coe_unipotentElt (u v : K) :
    (unipotentElt a K u v : suzukiGroup a K) = suzukiSElt a K u v :=
  rfl

@[simp] theorem unipotentFst_unipotentElt
    (u v : K) : unipotentFst (unipotentElt a K u v) = u := by
  simp [unipotentFst, unipotentElt, coe_suzukiSElt, suzukiS]

@[simp] theorem unipotentSnd_unipotentElt
    (u v : K) : unipotentSnd (unipotentElt a K u v) = v := by
  simp [unipotentSnd, unipotentElt, coe_suzukiSElt, suzukiS]

theorem unipotentElt_inj {u v c d : K} :
    unipotentElt a K u v = unipotentElt a K c d ↔ u = c ∧ v = d :=
  Subtype.ext_iff.trans suzukiSElt_inj

theorem unipotentElt_zero_mem_suzukiZ0 (b : K) :
    (unipotentElt a K 0 b : suzukiGroup a K) ∈ suzukiZ0 a K :=
  Subgroup.subset_closure ⟨b, rfl⟩

variable [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
include hK

theorem unipotentElt_mul (u v c d : K) :
    unipotentElt a K u v * unipotentElt a K c d =
      unipotentElt a K (u + c) (v + d + u ^ 2 ^ (a + 1) * c) :=
  Subtype.ext (suzukiSElt_mul hK u v c d)

theorem unipotentElt_inv (u v : K) :
    (unipotentElt a K u v)⁻¹ = unipotentElt a K u (v + u ^ (2 ^ (a + 1) + 1)) :=
  Subtype.ext (suzukiSElt_inv hK u v)

theorem unipotentElt_zero_zero : unipotentElt a K 0 0 = 1 :=
  Subtype.ext (suzukiSElt_zero_zero hK)

theorem exists_unipotentElt_eq
    (x : suzukiU a K) : ∃ u v : K, unipotentElt a K u v = x := by
  obtain ⟨u, v, h⟩ := (mem_suzukiU_iff hK).1 x.2
  exact ⟨u, v, Subtype.ext h⟩

theorem unipotentFst_mul (x y : suzukiU a K) :
    unipotentFst (x * y) = unipotentFst x + unipotentFst y := by
  obtain ⟨u, v, rfl⟩ := exists_unipotentElt_eq hK x
  obtain ⟨c, d, rfl⟩ := exists_unipotentElt_eq hK y
  simp [unipotentElt_mul hK]

theorem unipotentElt_sq (u v : K) :
    unipotentElt a K u v ^ 2 = unipotentElt a K 0 (u ^ (2 ^ (a + 1) + 1)) := by
  obtain ⟨h2, -⟩ := suzuki_frob_data a hK
  rw [sq, unipotentElt_mul hK, unipotentElt_inj]
  constructor
  · linear_combination u * h2
  · rw [pow_succ]
    linear_combination v * h2

theorem unipotent_sq (x : suzukiU a K) :
    x ^ 2 = unipotentElt a K 0 (unipotentFst x ^ (2 ^ (a + 1) + 1)) := by
  obtain ⟨u, v, rfl⟩ := exists_unipotentElt_eq hK x
  rw [unipotentElt_sq hK, unipotentFst_unipotentElt]

theorem commutatorElement_unipotentElt (u v c d : K) :
    ⁅unipotentElt a K u v, unipotentElt a K c d⁆ =
      unipotentElt a K 0 (u ^ 2 ^ (a + 1) * c + c ^ 2 ^ (a + 1) * u) := by
  obtain ⟨h2, hadd, -⟩ := suzuki_frob_data a hK
  rw [commutatorElement_def, unipotentElt_inv hK, unipotentElt_inv hK, unipotentElt_mul hK,
    unipotentElt_mul hK, unipotentElt_mul hK, unipotentElt_inj]
  refine ⟨by linear_combination (u + c) * h2, ?_⟩
  simp only [hadd]
  linear_combination (v + d + u ^ 2 ^ (a + 1) * c + u ^ 2 ^ (a + 1) * u +
    c ^ 2 ^ (a + 1) * c) * h2

theorem exists_add_pow_ne_zero (ha : 1 ≤ a) : ∃ h : K, h + h ^ 2 ^ (a + 1) ≠ 0 := by
  classical
  obtain ⟨h2, -, hθθ⟩ := suzuki_frob_data a hK
  by_contra! hcon
  have hfix : ∀ x : K, x ^ 2 ^ (a + 1) = x := fun x => by
    linear_combination hcon x - x * h2
  have h01 : ∀ x : K, x = 0 ∨ x = 1 := fun x => by
    have hx := hθθ x
    rw [hfix, hfix] at hx
    have : x * (x - 1) = 0 := by linear_combination -hx
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.1 h)
  have : Fintype K := Fintype.ofFinite K
  have hle : Fintype.card K ≤ 2 :=
    calc Fintype.card K = (Finset.univ : Finset K).card := rfl
      _ ≤ ({0, 1} : Finset K).card := Finset.card_le_card fun x _ => by
          rcases h01 x with rfl | rfl <;> simp
      _ ≤ 2 := Finset.card_le_two
  rw [← Nat.card_eq_fintype_card, hK] at hle
  have : 2 ^ 3 ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem center_suzukiU (ha : 1 ≤ a) :
    Subgroup.center (suzukiU a K) = (suzukiZ0 a K).subgroupOf (suzukiU a K) := by
  obtain ⟨h2, -⟩ := suzuki_frob_data a hK
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨c, d, rfl⟩ := exists_unipotentElt_eq hK x
    have hcomm : ∀ v : K, c ^ 2 ^ (a + 1) * v = v ^ 2 ^ (a + 1) * c := fun v => by
      have h := Subgroup.mem_center_iff.1 hx (unipotentElt a K v 0)
      rw [unipotentElt_mul hK, unipotentElt_mul hK, unipotentElt_inj] at h
      linear_combination -h.2
    obtain rfl : c = 0 := by
      by_contra hc
      obtain ⟨h, hh⟩ := exists_add_pow_ne_zero hK ha
      have h1 := hcomm 1
      rw [mul_one, one_pow, one_mul] at h1
      refine hh ((mul_eq_zero.1 ?_).resolve_left hc)
      linear_combination (-h) * h1 + hcomm h + c * h ^ 2 ^ (a + 1) * h2
    exact Subgroup.mem_subgroupOf.2 (unipotentElt_zero_mem_suzukiZ0 d)
  · obtain ⟨b, hb⟩ := (mem_suzukiZ0_iff hK).1 (Subgroup.mem_subgroupOf.1 hx)
    obtain rfl : unipotentElt a K 0 b = x := Subtype.ext hb
    refine Subgroup.mem_center_iff.2 fun y => ?_
    obtain ⟨u, v, rfl⟩ := exists_unipotentElt_eq hK y
    exact Subtype.ext (suzukiSElt_zero_commute hK b u v).symm

theorem commutator_suzukiU (ha : 1 ≤ a) :
    commutator (suzukiU a K) = (suzukiZ0 a K).subgroupOf (suzukiU a K) := by
  refine le_antisymm ?_ (fun x hx => ?_)
  · rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    exact Subgroup.mem_subgroupOf.2 (commutatorElement_mem_suzukiZ0 hK x.2 y.2)
  · obtain ⟨b, hb⟩ := (mem_suzukiZ0_iff hK).1 (Subgroup.mem_subgroupOf.1 hx)
    obtain rfl : unipotentElt a K 0 b = x := Subtype.ext hb
    obtain rfl | hb0 := eq_or_ne b 0
    · rw [unipotentElt_zero_zero hK]
      exact Subgroup.one_mem _
    obtain ⟨h, hh⟩ := exists_add_pow_ne_zero hK ha
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hbij, -⟩ := suzuki_frobenius_exponents a K hK
    obtain ⟨c, hc⟩ := hbij.2 (Units.mk0 (b / (h + h ^ 2 ^ (a + 1))) (div_ne_zero hb0 hh))
    have hc1 : c ^ (2 ^ (a + 1) + 1) =
        Units.mk0 (b / (h + h ^ 2 ^ (a + 1))) (div_ne_zero hb0 hh) := by
      rw [← hc]
      change c ^ (2 ^ (a + 1) + 1) = c ^ (2 ^ (a + 1) + 1 : ℤ)
      exact_mod_cast (zpow_natCast c (2 ^ (a + 1) + 1)).symm
    have hc' : (c : K) ^ (2 ^ (a + 1) + 1) * (h + h ^ 2 ^ (a + 1)) = b := by
      have hcK := congrArg Units.val hc1
      rw [Units.val_pow_eq_pow_val, Units.val_mk0] at hcK
      rw [hcK, div_mul_cancel₀ _ hh]
    have hkey : (c : K) ^ 2 ^ (a + 1) * (c * h) + (c * h) ^ 2 ^ (a + 1) * c = b := by
      rw [← hc', mul_pow]
      ring
    rw [← hkey, ← commutatorElement_unipotentElt hK (c : K) 0 (c * h) 0, commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

end CFSG.ShultStronglyClosedTI.SuzukiRootAutomorphism
