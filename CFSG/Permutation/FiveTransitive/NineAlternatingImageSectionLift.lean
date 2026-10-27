module

public import CFSG.Permutation.FiveTransitive.SylowPreimageNormalizer

public section

namespace CFSG

namespace FiveTransitive.NineAlternatingImageSectionLift

private theorem exists_lift
    {G H : Type*} [Group G] [Finite G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) (hker : IsPGroup 5 f.ker)
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 5) (y : H) (hy : orderOf y = p) :
    ∃ x : G, f x = y ∧ orderOf x = p := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let V := Subgroup.zpowers y
  have hV : IsPGroup p V := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers,hy,pow_one])
  let R : Sylow p (V.comap f) := Sylow.nonempty.some
  let S := SylowPreimageNormalizer.ambient f V R
  have hS : IsPGroup p S := R.isPGroup'.map (V.comap f).subtype
  have hmap : S.map f = V := SylowPreimageNormalizer.ambient_map f hf V hV R
  have hdis : Disjoint S f.ker := IsPGroup.disjoint_of_ne p 5 hp S f.ker hS hker
  have hinj : Function.Injective (f.comp S.subtype) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [Subgroup.eq_bot_iff_forall]
    intro u hu
    apply Subtype.ext
    exact Subgroup.mem_bot.mp (hdis.le_bot ⟨u.property,hu⟩)
  have hymem : y ∈ S.map f := by rw [hmap]; exact Subgroup.mem_zpowers y
  obtain ⟨x,hx,hxy⟩ := hymem
  refine ⟨x,hxy,?_⟩
  have he := orderOf_injective (f.comp S.subtype) hinj (⟨x,hx⟩ : S)
  calc
    orderOf x = orderOf (⟨x,hx⟩ : S) := Subgroup.orderOf_coe (⟨x,hx⟩ : S)
    _ = orderOf (f x) := he.symm
    _ = p := by rw [hxy,hy]

theorem exists_involution_lift
    {G H : Type*} [Group G] [Finite G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) (hker : IsPGroup 5 f.ker)
    (u : H) (hu : orderOf u = 2) :
    ∃ g : G, f g = u ∧ orderOf g = 2 := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact exists_lift f hf hker (by decide : 2 ≠ 5) u hu

end FiveTransitive.NineAlternatingImageSectionLift

end CFSG
