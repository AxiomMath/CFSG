module

public import CFSG.Permutation.FiveTransitive.ElementaryOrientedSemiregular

public section

namespace CFSG

namespace FiveTransitive.ElementaryShortOrbitSemiregular

open MulAction

theorem semiregular
    {G X : Type*} [CommGroup G] [Finite X] [MulAction G X]
    (h2 : ∀ g : G, g * g = 1)
    (hmax : ∀ g : G, g ≠ 1 → (fixedBy X g).ncard ≤ 7)
    (a b c d : G) (ha : (fixedBy X a).ncard = 7)
    (hb : (fixedBy X b \ fixedBy X a).ncard = 2)
    (hab : (fixedBy X (a * b) \ fixedBy X a).ncard = 2)
    (hc : (fixedBy X c \ fixedBy X a).ncard = 2)
    (hac : (fixedBy X (a * c) \ fixedBy X a).ncard = 2)
    (hd : (fixedBy X d \ fixedBy X a).ncard = 2)
    (had : (fixedBy X (a * d) \ fixedBy X a).ncard = 2)
    (hbc : (fixedBy X (b * c) ∩ fixedBy X a).ncard = 3)
    (hbd : (fixedBy X (b * d) ∩ fixedBy X a).ncard = 3)
    (hcd : (fixedBy X (c * d) ∩ fixedBy X a).ncard = 3) :
    let E := (fixedBy X b \ fixedBy X a) ∪ (fixedBy X (a * b) \ fixedBy X a)
    E.ncard = 4 ∧ ∀ g : G, g ≠ 1 → ∀ t ∉ fixedBy X a ∪ E, g • t ≠ t := by
  have haa (u : G) : a * (a * u) = u := by rw [← mul_assoc, h2, one_mul]
  have hor (u : G) (hu : (fixedBy X u \ fixedBy X a).ncard = 2)
      (hau : (fixedBy X (a * u) \ fixedBy X a).ncard = 2) :
      ∃ v : G, (v = u ∨ v = a * u) ∧
        fixedBy X v \ fixedBy X a = fixedBy X b \ fixedBy X a ∧
        fixedBy X (a * v) \ fixedBy X a = fixedBy X (a * b) \ fixedBy X a := by
    rcases ElementaryPairOrientation.orient h2 a b u hb hab hu hau with h | h
    · exact ⟨u, Or.inl rfl, h⟩
    · exact ⟨a * u, Or.inr rfl, h.1, by simpa only [haa] using h.2⟩
  obtain ⟨c', hcc', hc', hac'⟩ := hor c hc hac
  obtain ⟨d', hdd', hd', had'⟩ := hor d hd had
  have hleft (u v u' : G) (hu : u' = u ∨ u' = a * u) :
      fixedBy X (u' * v) ∩ fixedBy X a = fixedBy X (u * v) ∩ fixedBy X a := by
    rcases hu with rfl | rfl
    · rfl
    · rw [mul_assoc, ElementaryOrientedSemiregular.fixed_inter_mul]
  have hright (u v v' : G) (hv : v' = v ∨ v' = a * v) :
      fixedBy X (u * v') ∩ fixedBy X a = fixedBy X (u * v) ∩ fixedBy X a := by
    rw [mul_comm u v', mul_comm u v]
    exact hleft v u v' hv
  apply ElementaryOrientedSemiregular.semiregular h2 hmax a b c' d' ha hb hab hc' hd' hac' had'
  · rwa [hright b c c' hcc']
  · rwa [hright b d d' hdd']
  · rwa [hleft c d' c' hcc', hright c d d' hdd']

end FiveTransitive.ElementaryShortOrbitSemiregular

end CFSG
