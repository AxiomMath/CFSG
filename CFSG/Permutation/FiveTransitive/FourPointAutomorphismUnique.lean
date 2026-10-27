module

public import Mathlib.Data.Set.Card

public section

namespace CFSG

namespace FiveTransitive.FourPointAutomorphismUnique

private theorem permutation_unique
    {X : Type*} [Finite X] (hX : Nat.card X = 4)
    (p q : X) (hpq : p ≠ q) (f g : Equiv.Perm X)
    (hf : f ≠ 1) (hg : g ≠ 1)
    (hfp : f p = p) (hfq : f q = q) (hgp : g p = p) (hgq : g q = q) :
    f = g := by
  classical
  have hcard : ({p, q}ᶜ : Set X).ncard = 2 := by
    rw [Set.ncard_compl, hX, Set.ncard_pair hpq]
  obtain ⟨u, v, huv, hset⟩ := Set.ncard_eq_two.mp hcard
  have hu : u ∈ ({p, q}ᶜ : Set X) := by rw [hset]; simp
  have hv : v ∈ ({p, q}ᶜ : Set X) := by rw [hset]; simp
  have hup : u ≠ p := fun h => hu (by simp [h])
  have huq : u ≠ q := fun h => hu (by simp [h])
  have hvp : v ≠ p := fun h => hv (by simp [h])
  have hvq : v ≠ q := fun h => hv (by simp [h])
  have hall (t : X) : t = p ∨ t = q ∨ t = u ∨ t = v := by
    by_cases ht : t ∈ ({p, q} : Set X)
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      exact ht.elim Or.inl (fun h => Or.inr (Or.inl h))
    · have he : t ∈ ({p, q}ᶜ : Set X) := ht
      rw [hset] at he
      exact Or.inr (Or.inr (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using he))
  have hvalues (e : Equiv.Perm X) (he : e ≠ 1) (hep : e p = p) (heq : e q = q) :
      e u = v ∧ e v = u := by
    have hpU : e u ≠ p := fun h => hup (e.injective (h.trans hep.symm))
    have hqU : e u ≠ q := fun h => huq (e.injective (h.trans heq.symm))
    have hpV : e v ≠ p := fun h => hvp (e.injective (h.trans hep.symm))
    have hqV : e v ≠ q := fun h => hvq (e.injective (h.trans heq.symm))
    have eu : e u = u ∨ e u = v := ((hall (e u)).resolve_left hpU).resolve_left hqU
    have ev : e v = u ∨ e v = v := ((hall (e v)).resolve_left hpV).resolve_left hqV
    rcases eu with eu | eu
    · have ev' : e v = v := ev.resolve_left (fun h => huv (e.injective (eu.trans h.symm)))
      apply False.elim
      apply he
      ext t
      rcases hall t with rfl | rfl | rfl | rfl <;> assumption
    · exact ⟨eu, ev.resolve_right (fun h => huv (e.injective (eu.trans h.symm)))⟩
  have hfv := hvalues f hf hfp hfq
  have hgv := hvalues g hg hgp hgq
  ext t
  rcases hall t with rfl | rfl | rfl | rfl
  · exact hfp.trans hgp.symm
  · exact hfq.trans hgq.symm
  · exact hfv.1.trans hgv.1.symm
  · exact hfv.2.trans hgv.2.symm

theorem automorphism_unique
    {Q : Type*} [Group Q] [Finite Q] (hQ : Nat.card Q = 4)
    (a : Q) (ha : a ≠ 1) (f g : MulAut Q)
    (hf : f ≠ 1) (hg : g ≠ 1) (hfa : f a = a) (hga : g a = a) : f = g := by
  have hperm : f.toEquiv = g.toEquiv := permutation_unique hQ 1 a ha.symm f.toEquiv g.toEquiv
    (fun h => hf (MulEquiv.ext (fun t => Equiv.congr_fun h t)))
    (fun h => hg (MulEquiv.ext (fun t => Equiv.congr_fun h t)))
    (f.map_one) hfa (g.map_one) hga
  exact MulEquiv.ext (Equiv.congr_fun hperm)

end FiveTransitive.FourPointAutomorphismUnique

end CFSG
