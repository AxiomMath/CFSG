module

public import CFSG.Permutation.FiveTransitive.SemiregularNormalizerBound
public import CFSG.Permutation.FiveTransitive.ExponentTwoCosetFusion
public import Mathlib.Tactic.Linarith.Frontend

public section

namespace CFSG

namespace FiveTransitive.SixteenNormalizerFixedFour

open MulAction

private theorem fixed_card_eq_four
    (G X : Type*) [Group G] [Finite G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (hcomm : ∀ q r : Q, q * r = r * q) (h2 : ∀ q : Q, q * q = 1)
    (hcard : Nat.card Q = 16)
    (b : G) (hb : b ∈ Subgroup.normalizer (Q : Set G)) (hb2 : b * b = 1)
    (hfree : ∀ (q : Q) (x : X), x ∉ fixedPoints Q X → q • x = x → q = 1)
    (x : X) (hbx : b • x = x) (hx : x ∉ fixedPoints Q X)
    (hsmall : (fixedBy X b \ fixedPoints Q X).ncard ≤ 4) :
    Nat.card {q : Q // Q.normalizerMonoidHom ⟨b, hb⟩ q = q} = 4 := by
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
  have hcompat : ∀ (q : Q) (y : X), b • (q • y) = f q • (b • y) := by
    intro q y
    change b • ((q : G) • y) = (f q : G) • (b • y)
    rw [hfval, mul_smul, mul_smul, inv_smul_smul]
  have heq := RegularOrbitAutomorphism.fixed_card_eq Q X f (fun y => b • y) x hbx hcompat
    (fun q => hfree q x hx)
  have hle : Nat.card {q : Q // f q = q} ≤ 4 := by
    rw [heq]
    calc
      Nat.card {y : X // y ∈ orbit Q x ∧ b • y = y} ≤
          Nat.card ↥(fixedBy X b \ fixedPoints Q X) :=
        Nat.card_le_card_of_injective
          (fun y => ⟨y.val, ⟨y.property.2,
            SemiregularNormalizerBound.orbit_not_fixed Q X x hx y.property.1⟩⟩)
          (by intro y z h; apply Subtype.ext; exact congrArg (fun w : ↥(fixedBy X b \ fixedPoints Q X) => w.val) h)
      _ = (fixedBy X b \ fixedPoints Q X).ncard := Nat.card_coe_set_eq _
      _ ≤ 4 := hsmall
  have hbound := InvolutiveAutomorphismBound.card_le_fixed_sq Q f hf h2
  rw [hcard] at hbound
  change Nat.card {q : Q // f q = q} = 4
  nlinarith

private theorem fixed_card_eq_four_of_fixed_six
    (G X : Type*) [Group G] [Finite G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (hcomm : ∀ q r : Q, q * r = r * q) (h2 : ∀ q : Q, q * q = 1)
    (hcard : Nat.card Q = 16)
    (b : G) (hb : b ∈ Subgroup.normalizer (Q : Set G)) (hb2 : b * b = 1)
    (hfree : ∀ (q : Q) (x : X), x ∉ fixedPoints Q X → q • x = x → q = 1)
    (hsix : (fixedBy X b).ncard = 6)
    (htwo : (fixedBy X b ∩ fixedPoints Q X).ncard = 2) :
    Nat.card {q : Q // Q.normalizerMonoidHom ⟨b, hb⟩ q = q} = 4 := by
  have hcount := Set.ncard_inter_add_ncard_sdiff_eq_ncard (fixedBy X b) (fixedPoints Q X)
  have hfour : (fixedBy X b \ fixedPoints Q X).ncard = 4 := by omega
  obtain ⟨x, hbx, hx⟩ := (Set.ncard_pos (Set.toFinite _)).mp
    (by omega : 0 < (fixedBy X b \ fixedPoints Q X).ncard)
  exact fixed_card_eq_four G X Q hcomm h2 hcard b hb hb2 hfree x hbx hx (by omega)

theorem coset_conjugate_of_fixed_six
    (G X : Type*) [Group G] [Finite G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (hcomm : ∀ q r : Q, q * r = r * q) (h2 : ∀ q : Q, q * q = 1)
    (hcard : Nat.card Q = 16)
    (b : G) (hb : b ∈ Subgroup.normalizer (Q : Set G)) (hb2 : b * b = 1)
    (hfree : ∀ (q : Q) (x : X), x ∉ fixedPoints Q X → q • x = x → q = 1)
    (hsix : (fixedBy X b).ncard = 6)
    (htwo : (fixedBy X b ∩ fixedPoints Q X).ncard = 2)
    (a : G) (ha2 : a * a = 1) (hab : a * b⁻¹ ∈ Q) :
    ∃ q : Q, (q : G) * b * (q : G)⁻¹ = a :=
  ExponentTwoCosetFusion.exists_conjugating_element G Q hcomm h2 hcard b hb hb2
    (fixed_card_eq_four_of_fixed_six G X Q hcomm h2 hcard b hb hb2 hfree hsix htwo) a ha2 hab

end FiveTransitive.SixteenNormalizerFixedFour

end CFSG
