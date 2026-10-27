module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3SplitQuot

public section

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3

variable {G : Type} [Group G]

@[expose] noncomputable def betaQuot (S : AbelSub G) (W : Subgroup G) {N : Type} [AddCommGroup N]
    (β : ↥S.carrier →* Multiplicative N) (hβW : ∀ x : S.carrier, (x : G) ∈ W → β x = 1) :
    (S.carrier ⧸ W.subgroupOf S.carrier) →* Multiplicative N :=
  QuotientGroup.lift (W.subgroupOf S.carrier) β fun x hx => by
    rw [MonoidHom.mem_ker]
    exact hβW x (Subgroup.mem_subgroupOf.mp hx)

@[expose] noncomputable def piAdd (S : AbelSub G) (W : Subgroup G) {N : Type} [AddCommGroup N]
    (β : ↥S.carrier →* Multiplicative N) (hβW : ∀ x : S.carrier, (x : G) ∈ W → β x = 1) :
    S.quot W →+ N where
  toFun x := Multiplicative.toAdd (betaQuot S W β hβW (Additive.toMul x))
  map_zero' := by
    show Multiplicative.toAdd (betaQuot S W β hβW 1) = 0
    rw [map_one]
    rfl
  map_add' x y := by
    show Multiplicative.toAdd (betaQuot S W β hβW (Additive.toMul x * Additive.toMul y)) = _
    rw [map_mul]
    rfl

@[expose] noncomputable def piL (S : AbelSub G) (W : Subgroup G) [Module (ZMod 2) (S.quot W)]
    {N : Type} [AddCommGroup N] [Module (ZMod 2) N]
    (β : ↥S.carrier →* Multiplicative N) (hβW : ∀ x : S.carrier, (x : G) ∈ W → β x = 1) :
    S.quot W →ₗ[ZMod 2] N :=
  AddMonoidHom.toZModLinearMap 2 (piAdd S W β hβW)

theorem piL_mk (S : AbelSub G) (W : Subgroup G) [Module (ZMod 2) (S.quot W)]
    {N : Type} [AddCommGroup N] [Module (ZMod 2) N]
    (β : ↥S.carrier →* Multiplicative N) (hβW : ∀ x : S.carrier, (x : G) ∈ W → β x = 1)
    (x : S.carrier) :
    piL S W β hβW (Additive.ofMul (QuotientGroup.mk x)) = Multiplicative.toAdd (β x) := by
  show Multiplicative.toAdd (betaQuot S W β hβW (QuotientGroup.mk x)) = _
  rw [betaQuot, QuotientGroup.lift_mk]

theorem exists_mk (S : AbelSub G) (W : Subgroup G) (e : S.quot W) :
    ∃ x : S.carrier, e = Additive.ofMul (QuotientGroup.mk x) := by
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul e)
  exact ⟨x, by rw [hx]; rfl⟩

theorem piL_surjective (S : AbelSub G) (W : Subgroup G) [Module (ZMod 2) (S.quot W)]
    {N : Type} [AddCommGroup N] [Module (ZMod 2) N]
    (β : ↥S.carrier →* Multiplicative N) (hβW : ∀ x : S.carrier, (x : G) ∈ W → β x = 1)
    (hβs : Function.Surjective β) : Function.Surjective (piL S W β hβW) := by
  intro n
  obtain ⟨x, hx⟩ := hβs (Multiplicative.ofAdd n)
  exact ⟨Additive.ofMul (QuotientGroup.mk x), by rw [piL_mk, hx]; rfl⟩

end CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3

end
