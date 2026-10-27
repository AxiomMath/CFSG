module

public import CFSG.Permutation.FiveTransitive.ExponentTwoDisplacement
public import Mathlib.Tactic.Group

public section

namespace CFSG

namespace FiveTransitive.ExponentTwoCosetFusion

theorem exists_conjugating_element
    (G : Type*) [Group G] (Q : Subgroup G) [Finite Q]
    (hcomm : ∀ q r : Q, q * r = r * q) (h2 : ∀ q : Q, q * q = 1)
    (hcard : Nat.card Q = 16)
    (b : G) (hb : b ∈ Subgroup.normalizer (Q : Set G)) (hb2 : b * b = 1)
    (hfix : Nat.card {q : Q // Q.normalizerMonoidHom ⟨b, hb⟩ q = q} = 4)
    (a : G) (ha2 : a * a = 1) (hab : a * b⁻¹ ∈ Q) :
    ∃ q : Q, (q : G) * b * (q : G)⁻¹ = a := by
  let _ : CommGroup Q := { (inferInstance : Group Q) with mul_comm := hcomm }
  let f : Q →* Q := (Q.normalizerMonoidHom ⟨b, hb⟩).toMonoidHom
  have hfval (q : Q) : (f q : G) = b * (q : G) * b⁻¹ :=
    Q.normalizerMonoidHom_apply_apply_coe ⟨b, hb⟩ q
  have hf : Function.Involutive f := by
    intro q
    apply Subtype.ext
    simp only [hfval]
    calc
      b * (b * (q : G) * b⁻¹) * b⁻¹ = (b * b) * (q : G) * (b * b)⁻¹ := by
        simp only [mul_inv_rev, mul_assoc]
      _ = (q : G) := by rw [hb2]; simp
  let x : Q := ⟨a * b⁻¹, hab⟩
  have hxmul : (x : G) * b = a := by simp [x]
  have hx2 : (x : G) * (x : G) = 1 := congrArg Subtype.val (h2 x)
  have hxinv : (x : G)⁻¹ = (x : G) := (eq_inv_iff_mul_eq_one.mpr hx2).symm
  have hbinv : b⁻¹ = b := (eq_inv_iff_mul_eq_one.mpr hb2).symm
  have hainv : a⁻¹ = a := (eq_inv_iff_mul_eq_one.mpr ha2).symm
  have hcommxb : b * (x : G) = (x : G) * b := by
    calc
      b * (x : G) = ((x : G) * b)⁻¹ := by rw [mul_inv_rev, hxinv, hbinv]
      _ = a⁻¹ := congrArg Inv.inv hxmul
      _ = a := hainv
      _ = (x : G) * b := hxmul.symm
  have hx : f x = x := by
    apply Subtype.ext
    rw [hfval, hcommxb, mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨q, hq⟩ := ExponentTwoDisplacement.exists_displacement_of_sixteen_four Q f hf h2 hcard hfix x hx
  have hqval : (f q : G) * (q : G) = (x : G) := congrArg Subtype.val hq
  have hqinv : (q : G)⁻¹ = (q : G) := by
    symm
    apply eq_inv_iff_mul_eq_one.mpr
    exact congrArg Subtype.val (h2 q)
  have hswap : (q : G) * (f q : G) = (f q : G) * (q : G) := congrArg Subtype.val (hcomm q (f q))
  refine ⟨q, ?_⟩
  calc
    (q : G) * b * (q : G)⁻¹ = ((q : G) * (f q : G)) * b := by
      rw [hfval, hqinv]
      group
    _ = ((f q : G) * (q : G)) * b := by rw [hswap]
    _ = (x : G) * b := by rw [hqval]
    _ = a := hxmul

end FiveTransitive.ExponentTwoCosetFusion

end CFSG
