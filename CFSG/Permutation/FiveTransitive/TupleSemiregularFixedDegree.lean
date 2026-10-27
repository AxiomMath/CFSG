module

public import CFSG.Permutation.FiveTransitive.TupleSemiregularFour
public import CFSG.Permutation.FiveTransitive.DoubleSwapFourSupport

public section

namespace CFSG

namespace FiveTransitive.TupleSemiregularFixedDegree

open MulAction TupleSemiregularFour

theorem involution_fixed_card
    (G X : Type*) [Group G] [Finite G] [Fintype X] [MulAction G X]
    (k : ℕ) (hk : IsMultiplyPretransitive G X k) (e : Fin k ↪ X)
    (S : Sylow 2 (stabilizer G e))
    (hfix : Nat.card (fixedPoints (image e S) X) = k)
    (hfree : ∀ q : G, q ∈ image e S → q ≠ 1 →
      ∀ x : X, x ∉ fixedPoints (image e S) X → q • x ≠ x)
    (g : G) (hg : orderOf g = 2) (hge : k ≤ (fixedBy X g).ncard) :
    (fixedBy X g).ncard = k := by
  obtain ⟨c, hc⟩ := exists_conjugate_into_sylow G X k hk e S g hg hge
  let q : image e S := ⟨c * g * c⁻¹, hc⟩
  have hg1 : g ≠ 1 := by intro h; rw [h, orderOf_one] at hg; omega
  have hq1 : q ≠ 1 := by
    intro h
    apply hg1
    have hconj : c * g * c⁻¹ = 1 := congrArg Subtype.val h
    apply (MulAut.conj c).injective
    simpa only [MulAut.conj_apply, map_one] using hconj
  have hfreeQ : ∀ (a : image e S) (x : X),
      x ∉ fixedPoints (image e S) X → a • x = x → a = 1 := by
    intro a x hx ha
    by_contra hne
    exact hfree a a.property (fun h => hne (Subtype.ext h)) x hx ha
  have heq := SemiregularSylowFixedSet.fixedBy_eq_fixedPoints (image e S) X hfreeQ q hq1
  calc
    (fixedBy X g).ncard = (fixedBy X (c * g * c⁻¹)).ncard := by
      rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
      exact Nat.card_congr (SemiregularSylowFixedSet.fixedByConjugateEquiv G X g c)
    _ = (fixedPoints (image e S) X).ncard := congrArg Set.ncard heq
    _ = k := by simpa only [Nat.card_coe_set_eq] using hfix

theorem card_le_fixed_add_four
    (X : Type*) [Fintype X] [DecidableEq X] (P : Subgroup (Equiv.Perm X))
    (k : ℕ) (hk : IsMultiplyPretransitive P X k) (hAlt : alternatingGroup X ≤ P)
    (e : Fin k ↪ X) (S : Sylow 2 (stabilizer P e))
    (hfix : Nat.card (fixedPoints (image e S) X) = k)
    (hfree : ∀ q : P, q ∈ image e S → q ≠ 1 →
      ∀ x : X, x ∉ fixedPoints (image e S) X → q • x ≠ x) :
    Fintype.card X ≤ k + 4 := by
  by_contra hlarge
  obtain ⟨g, hgAlt, hgorder, _, hgfix⟩ :=
    DoubleSwapFourSupport.exists_even_involution X (by omega)
  let u : P := ⟨g, hAlt hgAlt⟩
  have hu : orderOf u = 2 := (Subgroup.orderOf_coe u).symm.trans hgorder
  have hufix : (fixedBy X u).ncard = Fintype.card X - 4 := by
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
    exact hgfix
  have hexact := involution_fixed_card P X k hk e S hfix hfree u hu (by omega)
  omega

end FiveTransitive.TupleSemiregularFixedDegree

end CFSG
