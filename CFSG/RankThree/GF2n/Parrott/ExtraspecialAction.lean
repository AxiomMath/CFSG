module

public import Certificates.Certificate946008
public import Certificates.Data.ParrottExtraspecialBridge

public section

namespace CFSG.RankThree.GF2n.Parrott

open scoped Matrix BigOperators

theorem s1s2inv_cube : Certificates.cubeCheck Ms1s2invH cMs1s2inv = true :=
  Certificates.certificate946008.s1s2inv.cube

@[expose] def fixedSubgroup (α : MulAut E8) : Subgroup E8 where
  carrier := {e | α e = e}
  one_mem' := map_one α
  mul_mem' := by
    intro a b ha hb
    show α (a * b) = a * b
    rw [map_mul, ha, hb]
  inv_mem' := by
    intro a ha
    show α a⁻¹ = a⁻¹
    rw [map_inv, ha]

@[simp] theorem mem_fixedSubgroup {α : MulAut E8} {e : E8} :
    e ∈ fixedSubgroup α ↔ α e = e := Iff.rfl

noncomputable def e8MaskEquiv : E8 ≃ Fin 512 :=
  Equiv.ofBijective (fun e => (⟨e8Mask e, e8Mask_lt_512 e⟩ : Fin 512)) (by
    rw [Fintype.bijective_iff_injective_and_card]
    constructor
    · intro e f h
      exact e8Mask_injective (congrArg Fin.val h)
    · rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, E8.card_E8]
      norm_num)

@[simp] theorem e8MaskEquiv_apply (e : E8) :
    e8MaskEquiv e = (⟨e8Mask e, e8Mask_lt_512 e⟩ : Fin 512) :=
  Equiv.ofBijective_apply _ _ e

@[simp] theorem e8Mask_e8MaskEquiv_symm (p : Fin 512) : e8Mask (e8MaskEquiv.symm p) = p := by
  have h := e8MaskEquiv.apply_symm_apply p
  rw [e8MaskEquiv_apply] at h
  exact congrArg Fin.val h

@[simp] theorem e8MaskEquiv_apply_val (e : E8) : (e8MaskEquiv e).val = e8Mask e :=
  congrArg Fin.val (e8MaskEquiv_apply e)

noncomputable instance fixedSubgroupFintype (α : MulAut E8) : Fintype (fixedSubgroup α) :=
  Fintype.ofInjective (fun x : fixedSubgroup α => (x : E8)) Subtype.coe_injective

open scoped commutatorElement

end CFSG.RankThree.GF2n.Parrott
