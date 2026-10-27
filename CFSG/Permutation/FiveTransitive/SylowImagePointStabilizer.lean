module

public import CFSG.Permutation.FiveTransitive.GenericSylowFixedAction

public section

namespace CFSG

namespace FiveTransitive.SylowImagePointStabilizer

open MulAction GenericSylowFixedAction

theorem orbit_eq (G X : Type) [Group G] [MulAction G X]
    (s : Set X) {p : ℕ} (S : Sylow p (fixingSubgroup G s)) (x : X) :
    orbit (sylowImage G X s S) x = orbit S x := by
  ext y
  constructor
  · rintro ⟨g,hg⟩
    obtain ⟨r,hr,he⟩ := g.property
    refine ⟨⟨r,hr⟩, ?_⟩
    change r.val • x = y
    change g.val • x = y at hg
    change r.val = g.val at he
    rwa [he]
  · rintro ⟨r,hr⟩
    exact ⟨⟨r.val.val,⟨r.val,r.property,rfl⟩⟩,hr⟩

theorem fixed_eq (G X : Type) [Group G] [MulAction G X]
    (s : Set X) {p : ℕ} (S : Sylow p (fixingSubgroup G s)) :
    fixedPoints (sylowImage G X s S) X = fixedPoints S X := by
  ext x
  constructor
  · intro hx r
    exact hx ⟨r.val.val,⟨r.val,r.property,rfl⟩⟩
  · intro hx r
    obtain ⟨q,hq,he⟩ := r.property
    have h := hx ⟨q,hq⟩
    change q.val • x = x at h
    change r.val • x = x
    change q.val = r.val at he
    rwa [he] at h

theorem stabilizer_image_eq (G X : Type) [Group G] [MulAction G X]
    (s : Set X) {p : ℕ} (S : Sylow p (fixingSubgroup G s)) (x : X) :
    (stabilizer (sylowImage G X s S) x).map (sylowImage G X s S).subtype =
      (stabilizer S x).map ((fixingSubgroup G s).subtype.comp (S : Subgroup _).subtype) := by
  ext g
  constructor
  · rintro ⟨q,hq,rfl⟩
    obtain ⟨r,hr,he⟩ := q.property
    refine ⟨⟨r,hr⟩, ?_,he⟩
    change r.val • x = x
    change q.val • x = x at hq
    change r.val = q.val at he
    rwa [he]
  · rintro ⟨q,hq,rfl⟩
    exact ⟨⟨q.val.val,⟨q.val,q.property,rfl⟩⟩,hq,rfl⟩

end FiveTransitive.SylowImagePointStabilizer

end CFSG
