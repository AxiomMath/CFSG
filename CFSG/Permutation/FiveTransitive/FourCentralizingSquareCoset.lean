module

public import CFSG.Permutation.FiveTransitive.SixteenOrbitLocalization
public import CFSG.Permutation.FiveTransitive.FixedSetNormalizerPerm

public section

namespace CFSG

namespace FiveTransitive.FourCentralizingSquareCoset

open MulAction

theorem square_eq
    (G X : Type*) [Group G] [Finite G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (hcard : Nat.card Q = 4) (h2 : ∀ q : Q, q * q = 1)
    (hfree : ∀ (q : Q) (x : X), x ∉ fixedPoints Q X → q • x = x → q = 1)
    (a b : G) (haN : a ∈ Subgroup.normalizer (Q : Set G))
    (haC : ∀ q : Q, a * (q : G) = (q : G) * a)
    (hbC : ∀ q : Q, b * (q : G) = (q : G) * b)
    (hcoset : a ^ 2 * b⁻¹ ∈ Q)
    (hbSix : (fixedBy X b).ncard = 6)
    (hbTwo : (fixedBy X b ∩ fixedPoints Q X).ncard = 2) : a ^ 2 = b := by
  have hc0 : Commute a (a ^ 2 * b⁻¹) := haC ⟨a ^ 2 * b⁻¹, hcoset⟩
  have hc1 := ((Commute.pow_self a 2).symm.inv_right).mul_right hc0
  have hab : Commute a b := Commute.inv_right_iff.mp (by
    simpa only [inv_mul_cancel_left] using hc1)
  let B := fixedBy X b \ fixedPoints Q X
  have hB : B.ncard = 4 := by
    have h := Set.ncard_inter_add_ncard_sdiff_eq_ncard (fixedBy X b) (fixedPoints Q X)
    change (fixedBy X b \ fixedPoints Q X).ncard = 4
    omega
  obtain ⟨x, hbx, hx⟩ := (Set.ncard_pos (Set.toFinite _)).mp (by omega : 0 < B.ncard)
  have hsub : orbit Q x ⊆ B := by
    intro y hy
    obtain ⟨q, rfl⟩ := mem_orbit_iff.mp hy
    refine ⟨?_, SemiregularNormalizerBound.orbit_not_fixed Q X x hx (mem_orbit_iff.mpr ⟨q, rfl⟩)⟩
    change b • ((q : G) • x) = (q : G) • x
    rw [← mul_smul, hbC q, mul_smul, hbx]
  have hOrbit : (orbit Q x).ncard = 4 :=
    (SixteenOrbitLocalization.orbit_card_of_free Q x (fun q => hfree q x hx)).trans hcard
  have hEq : orbit Q x = B := Set.eq_of_subset_of_ncard_le hsub (by omega)
  have haxF : a • x ∉ fixedPoints Q X := by
    intro h
    have h' := FixedSetNormalizerPerm.smul_mem_fixedPoints G X Q a⁻¹
      ((Subgroup.normalizer (Q : Set G)).inv_mem haN) h
    exact hx (by simpa only [inv_smul_smul] using h')
  have haxb : b • (a • x) = a • x := by
    rw [← mul_smul, ← hab.eq, mul_smul, hbx]
  have haxO : a • x ∈ orbit Q x := hEq.symm ▸ (show a • x ∈ B from ⟨haxb, haxF⟩)
  obtain ⟨q, hq⟩ := mem_orbit_iff.mp haxO
  have hax2 : a ^ 2 • x = x := by
    calc
      a ^ 2 • x = a • (a • x) := by rw [pow_two, mul_smul]
      _ = a • ((q : G) • x) := by rw [← hq]; rfl
      _ = (q : G) • (a • x) := by rw [← mul_smul, haC q, mul_smul]
      _ = (q : G) • ((q : G) • x) := by rw [← hq]; rfl
      _ = x := by
        change q • (q • x) = x
        rw [← mul_smul, h2, one_smul]
  have hbix : b⁻¹ • x = x := by
    have h := congrArg (fun y : X => b⁻¹ • y) hbx
    simpa only [inv_smul_smul] using h.symm
  have hr : (⟨a ^ 2 * b⁻¹, hcoset⟩ : Q) = 1 := hfree _ x hx (by
    change (a ^ 2 * b⁻¹) • x = x
    rw [mul_smul, hbix, hax2])
  exact mul_inv_eq_one.mp (congrArg Subtype.val hr)

end FiveTransitive.FourCentralizingSquareCoset

end CFSG
