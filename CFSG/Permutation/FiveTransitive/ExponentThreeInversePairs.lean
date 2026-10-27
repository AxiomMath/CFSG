module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Data.Nat.Totient

public section

namespace CFSG

namespace FiveTransitive.ExponentThreeInversePairs

theorem even_ncard
    {G : Type*} [Group G] [Finite G] (hpow : ∀ g : G, g ^ 3 = 1)
    (s : Set G) (hone : (1 : G) ∉ s) (hinv : ∀ g ∈ s, g⁻¹ ∈ s) : Even s.ncard := by
  classical
  let _ : Fintype s := Fintype.ofFinite s
  let e : Equiv.Perm s :=
    { toFun := fun g => ⟨g.val⁻¹,hinv g.val g.property⟩
      invFun := fun g => ⟨g.val⁻¹,hinv g.val g.property⟩
      left_inv := fun g => Subtype.ext (inv_inv g.val)
      right_inv := fun g => Subtype.ext (inv_inv g.val) }
  have he : e ^ 2 = 1 := by
    ext g
    exact inv_inv g.val
  have hempty : IsEmpty (Function.fixedPoints e) := by
    refine ⟨fun g => ?_⟩
    have heq : g.val.val⁻¹ = g.val.val := congrArg Subtype.val g.property
    have hsq : g.val.val * g.val.val = 1 := by
      calc
        g.val.val * g.val.val = g.val.val⁻¹ * g.val.val := congrArg (· * g.val.val) heq.symm
        _ = 1 := inv_mul_cancel _
    have hc := hpow g.val.val
    rw [pow_succ,pow_two,hsq,one_mul] at hc
    exact hone (hc ▸ g.val.property)
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  let f : Function.End s := e.toFun
  have hf : f ^ 2 = 1 := by
    funext x
    exact DFunLike.congr_fun he x
  have hm := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 2) (n := 1)
    (by simpa only [pow_one] using hf)
  change Fintype.card s % 2 = Fintype.card (Function.fixedPoints e) % 2 at hm
  let _ := hempty
  rw [Fintype.card_of_isEmpty (α := Function.fixedPoints e)] at hm
  rw [← Nat.card_eq_fintype_card,Nat.card_coe_set_eq] at hm
  exact even_iff_two_dvd.mpr (Nat.dvd_iff_mod_eq_zero.mpr hm)

end FiveTransitive.ExponentThreeInversePairs

end CFSG
