module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Extraspecial
public import Mathlib.Data.Matrix.Mul

public section

namespace CFSG.Quasithin

namespace Stellmacher.PU.L3YC

@[ext] structure Heis where
  x : Fin 3 → ZMod 2
  y : Fin 3 → ZMod 2
  w : ZMod 2
deriving DecidableEq

namespace Heis

instance : Mul Heis := ⟨fun a b => ⟨a.x + b.x, a.y + b.y, a.w + b.w + a.x ⬝ᵥ b.y⟩⟩
instance : One Heis := ⟨⟨0, 0, 0⟩⟩
instance : Inv Heis := ⟨fun a => ⟨a.x, a.y, a.w + a.x ⬝ᵥ a.y⟩⟩

@[simp] theorem mul_x (a b : Heis) : (a * b).x = a.x + b.x := rfl
@[simp] theorem mul_y (a b : Heis) : (a * b).y = a.y + b.y := rfl
@[simp] theorem mul_w (a b : Heis) : (a * b).w = a.w + b.w + a.x ⬝ᵥ b.y := rfl
@[simp] theorem one_x : (1 : Heis).x = 0 := rfl
@[simp] theorem one_y : (1 : Heis).y = 0 := rfl
@[simp] theorem one_w : (1 : Heis).w = 0 := rfl
@[simp] theorem inv_x (a : Heis) : (a⁻¹).x = a.x := rfl
@[simp] theorem inv_y (a : Heis) : (a⁻¹).y = a.y := rfl
@[simp] theorem inv_w (a : Heis) : (a⁻¹).w = a.w + a.x ⬝ᵥ a.y := rfl

theorem zmod2_add_self (t : ZMod 2) : t + t = 0 := CharTwo.add_self_eq_zero t

theorem fn_add_self (f : Fin 3 → ZMod 2) : f + f = 0 := by
  ext i
  exact zmod2_add_self _

instance : Group Heis where
  mul_assoc a b c := by
    ext <;> simp [add_assoc, add_dotProduct, dotProduct_add] <;> ring
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp
  inv_mul_cancel a := by
    ext
    · exact zmod2_add_self _
    · exact zmod2_add_self _
    · simp only [mul_w, inv_w, inv_x, one_w]
      rw [show a.w + a.x ⬝ᵥ a.y + a.w + a.x ⬝ᵥ a.y =
        (a.w + a.x ⬝ᵥ a.y) + (a.w + a.x ⬝ᵥ a.y) by ring]
      exact zmod2_add_self _

def equivProd : Heis ≃ (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2) × ZMod 2 where
  toFun a := (a.x, a.y, a.w)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype Heis := Fintype.ofEquiv _ equivProd.symm

theorem card_heis : Nat.card Heis = 2 ^ 7 := by
  rw [Nat.card_congr equivProd, Nat.card_prod, Nat.card_prod, Nat.card_fun, Nat.card_fin,
    Nat.card_zmod]
  norm_num

theorem mem_center_iff {z : Heis} : z ∈ Subgroup.center Heis ↔ z.x = 0 ∧ z.y = 0 := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro h
    have hw : ∀ g : Heis, g.x ⬝ᵥ z.y = z.x ⬝ᵥ g.y := by
      intro g
      have := congrArg Heis.w (h g)
      simp only [mul_w] at this
      have h2 : g.w + z.w + g.x ⬝ᵥ z.y = g.w + z.w + z.x ⬝ᵥ g.y := by
        rw [show g.w + z.w + z.x ⬝ᵥ g.y = z.w + g.w + z.x ⬝ᵥ g.y by ring]
        exact this.symm ▸ rfl
      exact add_left_cancel h2
    constructor
    · ext i
      have := hw ⟨0, Pi.single i 1, 0⟩
      simpa [dotProduct_single] using this.symm
    · ext i
      have := hw ⟨Pi.single i 1, 0, 0⟩
      simpa [single_dotProduct] using this
  · rintro ⟨hx, hy⟩ g
    ext <;> simp [hx, hy, add_comm]

theorem card_center : Nat.card (Subgroup.center Heis) = 2 := by
  let f : ZMod 2 → Subgroup.center Heis := fun t => ⟨⟨0, 0, t⟩, mem_center_iff.mpr ⟨rfl, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro s t h
      exact congrArg Heis.w (congrArg Subtype.val h)
    · rintro ⟨z, hz⟩
      obtain ⟨hx, hy⟩ := mem_center_iff.mp hz
      exact ⟨z.w, Subtype.ext (by ext <;> simp [f, hx, hy])⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_zmod]

instance isExtraspecial : CFSG.IsExtraspecial 2 Heis where
  center_order_p := card_center
  quotient_elementary_abelian :=
    { is_comm := ⟨fun a b => by
        induction a using QuotientGroup.induction_on with
        | H a =>
          induction b using QuotientGroup.induction_on with
          | H b =>
            rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
              mem_center_iff]
            constructor <;> ext i <;> simp <;> exact zmod2_add_self _⟩
      exponent_dvd_p := by
        refine Monoid.exponent_dvd_of_forall_pow_eq_one fun g => ?_
        induction g using QuotientGroup.induction_on with
        | H a =>
          rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_center_iff]
          constructor <;> ext i <;> simp [pow_two, zmod2_add_self] }
  quotient_nontrivial := by
    refine ⟨⟨1, QuotientGroup.mk ⟨Pi.single 0 1, 0, 0⟩, fun h => ?_⟩⟩
    have h2 : (⟨Pi.single 0 1, 0, 0⟩ : Heis) ∈ Subgroup.center Heis :=
      (QuotientGroup.eq_one_iff _).mp h.symm
    have := congrFun (mem_center_iff.mp h2).1 0
    simp at this

end Heis

end Stellmacher.PU.L3YC

end CFSG.Quasithin
