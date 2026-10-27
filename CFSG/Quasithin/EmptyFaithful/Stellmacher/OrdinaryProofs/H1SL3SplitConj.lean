module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3SplitQuot

public section

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3

variable {G : Type} [Group G]

@[expose] def conjSub (S : AbelSub G) {g : G}
    (hg : g ∈ Subgroup.normalizer (S.carrier : Set G)) : S.carrier →* S.carrier where
  toFun h := ⟨g * h * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg _).mp h.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

@[expose] def conjQuot (S : AbelSub G) (W : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (S.carrier : Set G))
    (hgW : g ∈ Subgroup.normalizer (W : Set G)) :
    (S.carrier ⧸ W.subgroupOf S.carrier) →* (S.carrier ⧸ W.subgroupOf S.carrier) :=
  QuotientGroup.map (W.subgroupOf S.carrier) (W.subgroupOf S.carrier) (conjSub S hg)
    (fun x hx => by
      rw [Subgroup.mem_subgroupOf] at hx
      rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
      exact (Subgroup.mem_normalizer_iff.mp hgW _).mp hx)

@[expose] def conjE (S : AbelSub G) (W : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (S.carrier : Set G))
    (hgW : g ∈ Subgroup.normalizer (W : Set G)) : AddMonoid.End (S.quot W) :=
  MonoidHom.toAdditive (conjQuot S W hg hgW)

theorem conjE_mk (S : AbelSub G) (W : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (S.carrier : Set G))
    (hgW : g ∈ Subgroup.normalizer (W : Set G)) (h : S.carrier) :
    conjE S W hg hgW (Additive.ofMul (QuotientGroup.mk h)) =
      Additive.ofMul (QuotientGroup.mk (conjSub S hg h)) := by
  show Additive.ofMul (conjQuot S W hg hgW (QuotientGroup.mk h)) = _
  rw [conjQuot, QuotientGroup.map_mk]

end CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3

end
