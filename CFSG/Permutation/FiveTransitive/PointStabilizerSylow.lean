module

public import CFSG.Permutation.FiveTransitive.GenericSylowFixedAction

public section

namespace CFSG

namespace FiveTransitive.PointStabilizerSylow

open MulAction SubMulAction GenericSylowFixedAction

def restrictedBase (G X : Type) [Group G] [MulAction G X]
    (s : Set X) (x : X) : Set (ofStabilizer G x) := Subtype.val ⁻¹' s

def fixerHom (G X : Type) [Group G] [MulAction G X]
    (s : Set X) (x : X) (hx : x ∉ s) :
    fixingSubgroup (stabilizer G x) (restrictedBase G X s x) →* fixingSubgroup G s where
  toFun g := ⟨g.val.val, by
    rw [mem_fixingSubgroup_iff]
    intro y hy
    have hne : y ≠ x := fun h => hx (h ▸ hy)
    have hg := (mem_fixingSubgroup_iff (stabilizer G x)).mp g.property
      ⟨y, hne⟩ hy
    exact congrArg Subtype.val hg⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem fixerHom_injective (G X : Type) [Group G] [MulAction G X]
    (s : Set X) (x : X) (hx : x ∉ s) :
    Function.Injective (fixerHom G X s x hx) := by
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun q : fixingSubgroup G s => q.val) h

theorem sylow_le_range (G X : Type) [Group G] [MulAction G X]
    (s : Set X) (x : X) (hx : x ∉ s) (S : Sylow 2 (fixingSubgroup G s))
    (hfix : ∀ q : S, q • x = x) :
    (S : Subgroup (fixingSubgroup G s)) ≤ (fixerHom G X s x hx).range := by
  intro q hq
  let qx : stabilizer G x := ⟨q.val, hfix ⟨q,hq⟩⟩
  have hqx : qx ∈ fixingSubgroup (stabilizer G x) (restrictedBase G X s x) := by
    rw [mem_fixingSubgroup_iff]
    intro y hy
    apply Subtype.ext
    exact (mem_fixingSubgroup_iff G).mp q.property y.val hy
  exact ⟨⟨qx,hqx⟩, rfl⟩

def restrictedSylow (G X : Type) [Group G] [MulAction G X]
    (s : Set X) (x : X) (hx : x ∉ s) (S : Sylow 2 (fixingSubgroup G s))
    (hfix : ∀ q : S, q • x = x) :
    Sylow 2 (fixingSubgroup (stabilizer G x) (restrictedBase G X s x)) :=
  S.comapOfInjective (fixerHom G X s x hx) (fixerHom_injective G X s x hx)
    (sylow_le_range G X s x hx S hfix)

theorem restrictedSylow_image (G X : Type) [Group G] [MulAction G X]
    (s : Set X) (x : X) (hx : x ∉ s) (S : Sylow 2 (fixingSubgroup G s))
    (hfix : ∀ q : S, q • x = x) :
    (sylowImage (stabilizer G x) (ofStabilizer G x) (restrictedBase G X s x)
      (restrictedSylow G X s x hx S hfix)).map (stabilizer G x).subtype =
      sylowImage G X s S := by
  ext g
  constructor
  · rintro ⟨a, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨fixerHom G X s x hx b, hb, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨b, hb⟩ := sylow_le_range G X s x hx S hfix ha
    refine ⟨b.val, ⟨b, ?_, rfl⟩, ?_⟩
    · change fixerHom G X s x hx b ∈ (S : Subgroup (fixingSubgroup G s))
      rwa [hb]
    · exact congrArg Subtype.val hb

theorem restrictedBase_card (G X : Type) [Group G] [MulAction G X]
    [Finite X] (s : Set X) (x : X) (hx : x ∉ s) :
    (restrictedBase G X s x).ncard = s.ncard := by
  let e : restrictedBase G X s x ≃ s :=
    { toFun := fun y => ⟨y.val.val, y.property⟩
      invFun := fun y => ⟨⟨y.val, fun h => hx (h ▸ y.property)⟩, y.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  simpa only [Nat.card_coe_set_eq] using Nat.card_congr e

end FiveTransitive.PointStabilizerSylow

end CFSG
