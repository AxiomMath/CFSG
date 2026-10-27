module

public import CFSG.Permutation.FiveTransitive.SixteenOrbitLocalization
public import CFSG.Permutation.FiveTransitive.ExponentTwoOrderEight

public section

namespace CFSG

namespace FiveTransitive.SixteenOrderFourCentralizer

open MulAction

private theorem fixed_card_eq_two
    (G X : Type*) [Group G] [Finite G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (hcomm : ∀ q r : Q, q * r = r * q) (h2 : ∀ q : Q, q * q = 1)
    (hcard : Nat.card Q = 16)
    (hfree : ∀ (q : Q) (x : X), x ∉ fixedPoints Q X → q • x = x → q = 1)
    (a : G) (haN : a ∈ Subgroup.normalizer (Q : Set G)) (ha4 : a ^ 4 = 1)
    (haFix : (fixedBy X a).ncard = 2)
    (haZero : (fixedBy X a ∩ fixedPoints Q X).ncard = 0)
    (haSqSix : (fixedBy X (a ^ 2)).ncard = 6)
    (haSqTwo : (fixedBy X (a ^ 2) ∩ fixedPoints Q X).ncard = 2) :
    Nat.card {q : Q // Q.normalizerMonoidHom ⟨a, haN⟩ q = q} = 2 := by
  have hnot (y : X) (hy : a • y = y) : y ∉ fixedPoints Q X := by
    intro hyF
    have he : fixedBy X a ∩ fixedPoints Q X = ∅ := (Set.ncard_eq_zero (Set.toFinite _)).mp haZero
    have hm : y ∈ fixedBy X a ∩ fixedPoints Q X := ⟨hy, hyF⟩
    rw [he] at hm
    exact hm
  obtain ⟨x, hx⟩ := (Set.ncard_pos (Set.toFinite _)).mp (by omega : 0 < (fixedBy X a).ncard)
  have hx2 : a ^ 2 • x = x := by rw [pow_two, mul_smul, hx, hx]
  have haSqN := (Subgroup.normalizer (Q : Set G)).pow_mem haN 2
  have haSq2 : a ^ 2 * a ^ 2 = 1 := by rw [← pow_add]; exact ha4
  have hlocal := SixteenOrbitLocalization.fixed_outside_subset_orbit Q hcomm h2 hcard
    (a ^ 2) haSqN haSq2 hfree haSqSix haSqTwo x hx2 (hnot x hx)
  have hsub : fixedBy X a ⊆ orbit Q x := by
    intro y hy
    apply hlocal
    exact ⟨by change a ^ 2 • y = y; rw [pow_two, mul_smul, hy, hy], hnot y hy⟩
  let f : Q →* Q := (Q.normalizerMonoidHom ⟨a, haN⟩).toMonoidHom
  have hcompat : ∀ (q : Q) (y : X), a • (q • y) = f q • (a • y) := by
    intro q y
    change a • ((q : G) • y) = (Q.normalizerMonoidHom ⟨a, haN⟩ q : G) • (a • y)
    rw [Q.normalizerMonoidHom_apply_apply_coe, mul_smul, mul_smul, inv_smul_smul]
  have heq := RegularOrbitAutomorphism.fixed_card_eq Q X f (fun y => a • y) x hx hcompat
    (fun q => hfree q x (hnot x hx))
  change Nat.card {q : Q // f q = q} = 2
  rw [heq]
  calc
    Nat.card {y : X // y ∈ orbit Q x ∧ a • y = y} = Nat.card (fixedBy X a) := Nat.card_congr
      { toFun := fun y => ⟨y.val, y.property.2⟩
        invFun := fun y => ⟨y.val, hsub y.property, y.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    _ = 2 := (Nat.card_coe_set_eq _).trans haFix

theorem exists_order_eight
    (G X : Type*) [Group G] [Finite G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (hcomm : ∀ q r : Q, q * r = r * q) (h2 : ∀ q : Q, q * q = 1)
    (hcard : Nat.card Q = 16)
    (hfree : ∀ (q : Q) (x : X), x ∉ fixedPoints Q X → q • x = x → q = 1)
    (a : G) (haN : a ∈ Subgroup.normalizer (Q : Set G)) (ha4 : a ^ 4 = 1)
    (haFix : (fixedBy X a).ncard = 2)
    (haZero : (fixedBy X a ∩ fixedPoints Q X).ncard = 0)
    (haSqSix : (fixedBy X (a ^ 2)).ncard = 6)
    (haSqTwo : (fixedBy X (a ^ 2) ∩ fixedPoints Q X).ncard = 2) :
    ∃ q : Q, orderOf ((q : G) * a) = 8 :=
  ExponentTwoOrderEight.exists_order_eight_in_coset G Q hcomm h2 hcard a haN ha4
    (fixed_card_eq_two G X Q hcomm h2 hcard hfree a haN ha4 haFix haZero haSqSix haSqTwo)

end FiveTransitive.SixteenOrderFourCentralizer

end CFSG
