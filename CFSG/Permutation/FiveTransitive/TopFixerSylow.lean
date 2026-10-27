module

public import CFSG.Permutation.FiveTransitive.GenericSylowFixedAction

public section

namespace CFSG

namespace FiveTransitive.TopFixerSylow

open MulAction GenericSylowFixedAction

def fixerEquiv (G X : Type) [Group G] [MulAction G X] (s : Set X) :
    fixingSubgroup (⊤ : Subgroup G) s ≃* fixingSubgroup G s where
  toFun g := ⟨g.val.val, g.property⟩
  invFun g := ⟨⟨g.val, Subgroup.mem_top _⟩, g.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem fixed_eq (G X : Type) [Group G] [Finite G] [MulAction G X]
    (s : Set X) {p : ℕ} [Fact p.Prime] (S : Sylow p (fixingSubgroup G s)) :
    let T := S.mapSurjective (f := (fixerEquiv G X s).symm.toMonoidHom)
      (fixerEquiv G X s).symm.surjective
    fixedPoints T X = fixedPoints S X := by
  dsimp only
  ext x
  constructor
  · intro hx
    rw [mem_fixedPoints] at hx ⊢
    intro q
    exact hx ⟨(fixerEquiv G X s).symm q.val,
      Subgroup.mem_map.mpr ⟨q.val, q.property, rfl⟩⟩
  · intro hx
    rw [mem_fixedPoints] at hx ⊢
    intro q
    obtain ⟨r, hr, he⟩ := Subgroup.mem_map.mp q.property
    have hh := hx ⟨r, hr⟩
    change q.val.val.val • x = x
    have hv := congrArg (fun g : fixingSubgroup (⊤ : Subgroup G) s => g.val.val) he
    change r.val = q.val.val.val at hv
    rwa [← hv]

end FiveTransitive.TopFixerSylow

end CFSG
