module

public import CFSG.RankThree.PerfectCover.HopfCover

public section

namespace CFSG.RankThree.PerfectCover

open Subgroup

universe u v

@[expose] def centralQuotientMap {K : Type u} {X : Type v} [Group K] [Group X]
    (e : K ⧸ center K ≃* X) : K →* X :=
  e.toMonoidHom.comp (QuotientGroup.mk' (center K))

theorem centralQuotientMap_surjective {K : Type u} {X : Type v} [Group K] [Group X]
    (e : K ⧸ center K ≃* X) : Function.Surjective (centralQuotientMap e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

theorem centralQuotientMap_ker {K : Type u} {X : Type v} [Group K] [Group X]
    (e : K ⧸ center K ≃* X) : (centralQuotientMap e).ker = center K := by
  ext x
  rw [MonoidHom.mem_ker]
  change e (QuotientGroup.mk' (center K) x) = 1 ↔ x ∈ center K
  rw [map_eq_one_iff e e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem centralQuotientMap_apply {K : Type u} {X : Type v} [Group K] [Group X]
    (e : K ⧸ center K ≃* X) (x : K) : centralQuotientMap e x = e (QuotientGroup.mk x) := rfl

theorem card_eq_card_mul_card_ker {G : Type u} {H : Type v} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f) : Nat.card G = Nat.card H * Nat.card f.ker := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv]

theorem finite_of_surjective_monoidHom {G : Type u} {H : Type v} [Group G] [Group H] [Finite G]
    (f : G →* H) (hf : Function.Surjective f) : Finite H :=
  Finite.of_surjective f hf

theorem isPerfect_of_quasisimple_quotient {L : Type u} {X : Type v} [Group L] [Group X]
    (hL : CFSG.IsQuasisimple L) (e : L ⧸ center L ≃* X) : Group.IsPerfect X := by
  have := hL.1
  exact Group.IsPerfect.ofSurjective (f := centralQuotientMap e) (centralQuotientMap_surjective e)

@[expose] noncomputable def hopfMultiplierToKer {E : Type u} {X : Type v} [Group E] [Group X]
    [Group.IsPerfect E] (q : E →* X) (hq : Function.Surjective q) (hker : q.ker ≤ center E) :
    hopfMultiplier X →* q.ker :=
  ((hopfLift q hq hker).comp (hopfMultiplier X).subtype).codRestrict q.ker fun m ↦ by
    rw [← map_hopfMultiplier_hopfLift q hq hker]
    exact ⟨m, m.2, rfl⟩

theorem hopfMultiplierToKer_apply {E : Type u} {X : Type v} [Group E] [Group X]
    [Group.IsPerfect E] (q : E →* X) (hq : Function.Surjective q) (hker : q.ker ≤ center E)
    (m : hopfMultiplier X) :
    ((hopfMultiplierToKer q hq hker m : q.ker) : E) = hopfLift q hq hker m := rfl

theorem hopfMultiplierToKer_surjective {E : Type u} {X : Type v} [Group E] [Group X]
    [Group.IsPerfect E] (q : E →* X) (hq : Function.Surjective q) (hker : q.ker ≤ center E) :
    Function.Surjective (hopfMultiplierToKer q hq hker) := by
  rintro ⟨c, hc⟩
  rw [← map_hopfMultiplier_hopfLift q hq hker] at hc
  obtain ⟨m, hm, rfl⟩ := hc
  exact ⟨⟨m, hm⟩, rfl⟩

theorem hopfMultiplierToKer_ker {E : Type u} {X : Type v} [Group E] [Group X]
    [Group.IsPerfect E] (q : E →* X) (hq : Function.Surjective q) (hker : q.ker ≤ center E) :
    (hopfMultiplierToKer q hq hker).ker =
      (hopfLift q hq hker).ker.subgroupOf (hopfMultiplier X) := by
  ext m
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
  exact Subtype.ext_iff

end CFSG.RankThree.PerfectCover
