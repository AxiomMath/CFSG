module

public import CFSG.Quasithin.SteinbergCBAlternatingAut
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

open Equiv

abbrev AFive : Type := ↥(alternatingGroup (Fin 5))

theorem eq_one_of_forall_commute_aFive {z : AFive} (h : ∀ a : AFive, z * a = a * z) : z = 1 := by
  have h1 : CFSG.Quasithin.SteinbergCB.conjPerm 5 (z : Perm (Fin 5)) =
      CFSG.Quasithin.SteinbergCB.conjPerm 5 1 := by
    refine MulEquiv.ext fun a => Subtype.ext ?_
    rw [CFSG.Quasithin.SteinbergCB.conjPerm_apply, CFSG.Quasithin.SteinbergCB.conjPerm_apply,
      ← Subgroup.coe_mul, h a, Subgroup.coe_mul, mul_inv_cancel_right, one_mul, inv_one,
      mul_one]
  exact Subtype.ext (CFSG.Quasithin.SteinbergCB.conjPerm_injective (by norm_num) h1)

theorem eq_one_or_injective_aFive (f : AFive →* AFive) : f = 1 ∨ Function.Injective f := by
  rcases (f.normal_ker).eq_bot_or_eq_top with h | h
  · exact Or.inr ((MonoidHom.ker_eq_bot_iff f).mp h)
  · left
    ext a
    have : a ∈ f.ker := h ▸ Subgroup.mem_top a
    rw [MonoidHom.mem_ker] at this
    rw [this, MonoidHom.one_apply]

variable {Q : Type*} [Group Q]

@[expose] noncomputable def wrSMul (w : Perm (Fin 5) ≀ᵣ Q) (g : Q → AFive) : Q → AFive :=
  fun x => CFSG.Quasithin.SteinbergCB.conjPerm 5 (w.left x) (g (w.right⁻¹ * x))

theorem wrSMul_apply (w : Perm (Fin 5) ≀ᵣ Q) (g : Q → AFive) (x : Q) :
    wrSMul w g x = CFSG.Quasithin.SteinbergCB.conjPerm 5 (w.left x) (g (w.right⁻¹ * x)) := rfl

@[expose, instance_reducible] noncomputable def wrAction :
    MulDistribMulAction (Perm (Fin 5) ≀ᵣ Q) (Q → AFive) where
  smul := wrSMul
  one_smul g := by
    show wrSMul 1 g = g
    funext x
    simp [wrSMul_apply, RegularWreathProduct.one_left, RegularWreathProduct.one_right]
  mul_smul a b g := by
    show wrSMul (a * b) g = wrSMul a (wrSMul b g)
    funext x
    rw [wrSMul_apply, wrSMul_apply, wrSMul_apply, RegularWreathProduct.mul_left,
      RegularWreathProduct.mul_right, Pi.mul_apply, map_mul, MulAut.mul_apply, mul_inv_rev,
      mul_assoc]
  smul_one w := by
    show wrSMul w 1 = 1
    funext x
    simp [wrSMul_apply]
  smul_mul w g h := by
    show wrSMul w (g * h) = wrSMul w g * wrSMul w h
    funext x
    simp [wrSMul_apply]

@[expose] noncomputable def wrAut : Perm (Fin 5) ≀ᵣ Q →* MulAut (Q → AFive) :=
  @MulDistribMulAction.toMulAut _ _ _ _ wrAction

theorem wrAut_apply (w : Perm (Fin 5) ≀ᵣ Q) (g : Q → AFive) : wrAut w g = wrSMul w g := rfl

theorem wrAut_injective : Function.Injective (wrAut (Q := Q)) := by
  classical
  rw [injective_iff_map_eq_one]
  intro w hw
  have key : ∀ g, wrSMul w g = g := fun g => by
    rw [← wrAut_apply, hw, MulAut.one_apply]
  obtain ⟨a₀, ha₀⟩ := exists_ne (1 : AFive)
  have hr : w.right = 1 := by
    by_contra hne
    have h1 := congrFun (key (Pi.mulSingle w.right⁻¹ a₀)) 1
    rw [wrSMul_apply, mul_one, Pi.mulSingle_eq_same,
      Pi.mulSingle_eq_of_ne (by rw [ne_eq, eq_comm, inv_eq_one]; exact hne)] at h1
    exact ha₀ ((map_eq_one_iff _ (MulEquiv.injective _)).mp h1)
  have hl : w.left = 1 := by
    funext x
    apply CFSG.Quasithin.SteinbergCB.conjPerm_injective (n := 5) (by norm_num)
    rw [Pi.one_apply, map_one]
    refine MulEquiv.ext fun a => ?_
    have h1 := congrFun (key (Pi.mulSingle x a)) x
    rw [wrSMul_apply, hr, inv_one, one_mul, Pi.mulSingle_eq_same] at h1
    rw [h1, MulAut.one_apply]
  exact RegularWreathProduct.ext hl hr

omit [Group Q] in
theorem card_wr [Finite Q] (hQ : Nat.card Q = 2) : Nat.card (Perm (Fin 5) ≀ᵣ Q) = 28800 := by
  rw [RegularWreathProduct.card, Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 5),
    Fintype.card_fin, hQ]
  rfl

theorem natCard_qTwo : Nat.card (Multiplicative (ZMod 2)) = 2 := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

end C11AmS

end CFSG.Quasithin.Vol2.Ch10.SecB
