module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3SplitConj

public section

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3

variable {G : Type} [Group G]

theorem conjE_one (S : AbelSub G) (W : Subgroup G) {g : G} (hg : g ∈ Subgroup.normalizer (S.carrier : Set G))
    (hgW : g ∈ Subgroup.normalizer (W : Set G)) (h1 : g = 1) :
    conjE S W hg hgW = 1 := by
  subst h1
  refine AddMonoidHom.ext fun x => ?_
  obtain ⟨h, hh⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
  have hx : x = Additive.ofMul (QuotientGroup.mk h : S.carrier ⧸ W.subgroupOf S.carrier) := by
    rw [hh]
    rfl
  have key : conjSub S hg h = h := Subtype.ext (by simp [conjSub])
  show conjE S W hg hgW x = x
  rw [hx, conjE_mk, key]

theorem conjE_mul (S : AbelSub G) (W : Subgroup G) {g k : G}
    (hg : g ∈ Subgroup.normalizer (S.carrier : Set G))
    (hgW : g ∈ Subgroup.normalizer (W : Set G))
    (hk : k ∈ Subgroup.normalizer (S.carrier : Set G))
    (hkW : k ∈ Subgroup.normalizer (W : Set G))
    (hgk : g * k ∈ Subgroup.normalizer (S.carrier : Set G))
    (hgkW : g * k ∈ Subgroup.normalizer (W : Set G)) :
    conjE S W hgk hgkW = conjE S W hg hgW * conjE S W hk hkW := by
  refine AddMonoidHom.ext fun x => ?_
  obtain ⟨h, hh⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
  have hx : x = Additive.ofMul (QuotientGroup.mk h : S.carrier ⧸ W.subgroupOf S.carrier) := by
    rw [hh]
    rfl
  have key : conjSub S hgk h = conjSub S hg (conjSub S hk h) :=
    Subtype.ext (by simp [conjSub, mul_assoc, mul_inv_rev])
  show conjE S W hgk hgkW x = conjE S W hg hgW (conjE S W hk hkW x)
  rw [hx, conjE_mk, conjE_mk, conjE_mk, key]

@[expose] def rhoE (S : AbelSub G) (W A : Subgroup G) (hAS : A ≤ Subgroup.normalizer (S.carrier : Set G))
    (hAW : A ≤ Subgroup.normalizer (W : Set G)) : A →* AddMonoid.End (S.quot W) where
  toFun a := conjE S W (hAS a.2) (hAW a.2)
  map_one' := conjE_one S W (hAS (1 : A).2) (hAW (1 : A).2) rfl
  map_mul' a b := conjE_mul S W (hAS a.2) (hAW a.2) (hAS b.2) (hAW b.2) (hAS (a * b).2)
    (hAW (a * b).2)

theorem rhoE_mk (S : AbelSub G) (W A : Subgroup G) (hAS : A ≤ Subgroup.normalizer (S.carrier : Set G))
    (hAW : A ≤ Subgroup.normalizer (W : Set G)) (a : A) (h : S.carrier) :
    rhoE S W A hAS hAW a (Additive.ofMul (QuotientGroup.mk h)) =
      Additive.ofMul (QuotientGroup.mk (conjSub S (hAS a.2) h)) :=
  conjE_mk S W (hAS a.2) (hAW a.2) h

end CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3

end
