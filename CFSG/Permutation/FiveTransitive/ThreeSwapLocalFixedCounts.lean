module

public import CFSG.Permutation.FiveTransitive.FixedNormalizerLocalCard

public section

namespace CFSG

open scoped Classical

namespace FiveTransitive.ThreeSwapLocalFixedCounts

open MulAction FixedNormalizerAction

theorem pair_counts
    {F : Type*} [Fintype F] [DecidableEq F] (hseven : Nat.card F = 7) (e : Fin 6 ↪ F) :
    Nat.card (Function.fixedPoints (Equiv.swap (e 0) (e 1) * Equiv.swap (e 2) (e 3))) = 3 ∧
    Nat.card (Function.fixedPoints (Equiv.swap (e 0) (e 1) * Equiv.swap (e 4) (e 5))) = 3 ∧
    Nat.card (Function.fixedPoints (Equiv.swap (e 2) (e 3) * Equiv.swap (e 4) (e 5))) = 3 := by
  have h (i j k l : Fin 6) (hn : [i, j, k, l].Nodup) :
      Nat.card (Function.fixedPoints (Equiv.swap (e i) (e j) * Equiv.swap (e k) (e l))) = 3 := by
    let d := Equiv.swap (e i) (e j) * Equiv.swap (e k) (e l)
    have ht : d.cycleType = {2, 2} := Equiv.Perm.cycleType_swap_mul_swap_of_nodup
      (by simpa only [List.map_cons, List.map_nil] using hn.map e.injective)
    change Nat.card (Function.fixedPoints d) = 3
    rw [Nat.card_eq_fintype_card, d.card_fixedPoints, ht, ← Nat.card_eq_fintype_card, hseven]
    rfl
  exact ⟨h 0 1 2 3 (by decide), h 0 1 4 5 (by decide), h 2 3 4 5 (by decide)⟩

theorem actual_pair_counts
    {G X : Type*} [Group G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (hseven : Nat.card (Fixed (X := X) Q) = 7)
    (e : Fin 6 ↪ Fixed (X := X) Q) (x y z : Normalizer Q)
    (hx : toPermHom (Normalizer Q) (Fixed (X := X) Q) x = Equiv.swap (e 0) (e 1))
    (hy : toPermHom (Normalizer Q) (Fixed (X := X) Q) y = Equiv.swap (e 2) (e 3))
    (hz : toPermHom (Normalizer Q) (Fixed (X := X) Q) z = Equiv.swap (e 4) (e 5)) :
    (fixedBy X (x.val * y.val) ∩ fixedPoints Q X).ncard = 3 ∧
    (fixedBy X (x.val * z.val) ∩ fixedPoints Q X).ncard = 3 ∧
    (fixedBy X (y.val * z.val) ∩ fixedPoints Q X).ncard = 3 := by
  classical
  let _ : Fintype (Fixed (X := X) Q) := Fintype.ofFinite _
  have h := pair_counts hseven e
  have hxy := FixedNormalizerLocalCard.fixed_card (X := X) Q (x * y)
  have hxz := FixedNormalizerLocalCard.fixed_card (X := X) Q (x * z)
  have hyz := FixedNormalizerLocalCard.fixed_card (X := X) Q (y * z)
  rw [map_mul, hx, hy] at hxy
  rw [map_mul, hx, hz] at hxz
  rw [map_mul, hy, hz] at hyz
  exact ⟨hxy.symm.trans h.1, hxz.symm.trans h.2.1, hyz.symm.trans h.2.2⟩

end FiveTransitive.ThreeSwapLocalFixedCounts

end CFSG
