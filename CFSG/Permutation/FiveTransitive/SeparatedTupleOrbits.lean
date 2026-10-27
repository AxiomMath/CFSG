module

public import CFSG.Permutation.FiveTransitive.CyclicPatternOrder
public import Mathlib.GroupTheory.GroupAction.Embedding

public section

namespace CFSG

namespace FiveTransitive.SeparatedTupleOrbits

open MulAction Equiv

@[expose] def rotate {X : Type*} (e : Fin 4 ↪ X) : Fin 4 ↪ X :=
  (finRotate 4).toEmbedding.trans e

theorem projected_twice_card_le
    {H X T I : Type*} [Group H] [Finite H] [MulAction H X] [MulAction H T]
    [Finite T] [Fintype I]
    (S : Sylow 2 H) (hS : ∀ q : S, q * q = 1)
    (p : T → (Fin 4 ↪ X)) (hp : ∀ (g : H) (t : T), p (g • t) = g • p t)
    (r : T → T) (hr : ∀ t, p (r t) = rotate (p t))
    (e : I → T)
    (hsep : ∀ i j : I, i ≠ j → ∀ b c : Bool,
      ¬ orbitRel H X (p (e i) (if b then 1 else 0))
        (p (e j) (if c then 1 else 0))) :
    2 * Fintype.card I ≤ Nat.card (orbitRel.Quotient H T) := by
  classical
  have hnr (x : T) : ¬ orbitRel H T (r x) x := by
    intro h
    obtain ⟨g,hg⟩ := mem_orbit_iff.mp (orbitRel_apply.mp h)
    have hh := congrArg p hg
    rw [hp,hr] at hh
    exact CyclicPatternOrder.not_four_rotation H X S hS g (p x)
      (fun i => DFunLike.congr_fun hh i)
  let t : I × Bool → T := fun q => if q.2 then r (e q.1) else e q.1
  let f : I × Bool → orbitRel.Quotient H T := fun q => Quotient.mk'' (t q)
  have ht (i : I) (b : Bool) : p (t (i,b)) 0 = p (e i) (if b then 1 else 0) := by
    cases b
    · rfl
    · change p (r (e i)) 0 = p (e i) 1
      rw [hr]
      rfl
  have hf : Function.Injective f := by
    rintro ⟨i,b⟩ ⟨j,c⟩ heq
    have hrel : orbitRel H T (t (i,b)) (t (j,c)) := Quotient.exact heq
    have hij : i = j := by
      by_contra hne
      apply hsep i j hne b c
      obtain ⟨g,hg⟩ := mem_orbit_iff.mp (orbitRel_apply.mp hrel)
      apply orbitRel_apply.mpr
      apply mem_orbit_iff.mpr
      refine ⟨g, ?_⟩
      have h := congrArg p hg
      rw [hp] at h
      have h0 := DFunLike.congr_fun h 0
      change g • p (t (j,c)) 0 = p (t (i,b)) 0 at h0
      simpa only [ht] using h0
    subst j
    have hbc : b = c := by
      cases b <;> cases c
      · rfl
      · exact False.elim (hnr (e i) ((orbitRel H T).symm hrel))
      · exact False.elim (hnr (e i) hrel)
      · rfl
    subst c
    rfl
  have hcard := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_eq_fintype_card, Fintype.card_bool, Fintype.card_prod,
    Nat.mul_comm] using hcard

end FiveTransitive.SeparatedTupleOrbits

end CFSG
