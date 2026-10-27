module

public import CFSG.Quasithin.H13.NQCatExcludesJ4
public import CFSG.Quasithin.SteinbergBTTitsPermutableSylowCyclic
public import CFSG.Sporadic.Schreier.TitsOuter

public section

namespace CFSG.Quasithin.H13.NQCat

open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj)
open scoped Pointwise

open CFSG.Quasithin.H13.NQTerm in
theorem exists_noncyclic_permutable_of_witness
    {G : Type} [Group G] [Finite G]
    {T L M : Subgroup G} (h : QTNQ T L M) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {X : Subgroup G} (hXL : X ≤ L) (hXc : (X.subgroupOf L).Characteristic)
    (hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X))
    (hW : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2)
    (hLW : ∃ l : normalizer (X : Set G), (l : G) ∈ L ∧ normalizerFrattiniConj X l ≠ 1)
    {Y K : Subgroup G} (hXTY : X ⊔ T ≤ Y) (hKY : K ≤ Y) (hKn : (K.subgroupOf Y).Normal)
    (hXK : X ≤ K) (hZ : ¬ p ∣ Nat.card (center (K ⧸ CFSG.pCore 2 K))) :
    ∃ A : Subgroup ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)), IsPGroup p A ∧
      ¬ IsCyclic A ∧ ∃ U : Sylow 2 ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)),
        (A : Set ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K))) *
          ((U : Subgroup ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K))) :
            Set ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K))) =
        ((U : Subgroup ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K))) :
          Set ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K))) * A := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf p X
  have hPK : P ≤ K := hP.le.trans hXK
  have hnc :=
    original_characteristic_witness_normal_quotient_common_normalizer_action_is_noncyclic
      h hp hp5 hXL hXc hXA hW hLW hXTY hKY hKn hXK hZ P hP
  rcases hnc with ⟨hσinj, ⟨U', hU'⟩, hAU, -⟩
  set σ : K →* (K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K) :=
    (QuotientGroup.mk' (center (K ⧸ CFSG.pCore 2 K))).comp (QuotientGroup.mk' (CFSG.pCore 2 K))
    with hσ
  set A := (P.subgroupOf K).map σ with hA
  have hrange : (σ.comp (P.subgroupOf K).subtype).range = A := by
    rw [MonoidHom.range_comp, range_subtype]
  let e : P.subgroupOf K ≃* A :=
    (MonoidHom.ofInjective hσinj).trans (MulEquiv.subgroupCongr hrange)
  have hAp : IsPGroup p A := by
    have h1 : IsPGroup p (P.subgroupOf K) := by
      rw [← comap_subtype]
      exact hP.isPGroup.comap_subtype
    exact h1.map σ
  have hAnc : ¬ IsCyclic A := by
    intro hc
    apply not_isCyclic_of_isSylowOf_of_card_eq_sq hXA hW hP
    have : IsCyclic (P.subgroupOf K) := isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
    exact isCyclic_of_surjective (subgroupOfEquivOfLe hPK).toMonoidHom
      (subgroupOfEquivOfLe hPK).surjective
  refine ⟨A, hAp, hAnc, U', ?_⟩
  rw [hU']
  exact hAU

theorem original_characteristic_witness_excludes_normal_Tits_quotient
    {G : Type} [Group G]
    [Finite G] {T L M : Subgroup G} (h : QTNQ T L M) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {X : Subgroup G} (hXL : X ≤ L) (hXc : (X.subgroupOf L).Characteristic)
    (hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X))
    (hW : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2)
    (hLW : ∃ l : normalizer (X : Set G), (l : G) ∈ L ∧ normalizerFrattiniConj X l ≠ 1)
    {Y K : Subgroup G} (hXTY : X ⊔ T ≤ Y) (hKY : K ≤ Y) (hKn : (K.subgroupOf Y).Normal)
    (hXK : X ≤ K) (hZ : ¬ p ∣ Nat.card (center (K ⧸ CFSG.pCore 2 K))) :
    ¬ CFSG.Blueprint.ReeTitsModel ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K))
      .Tits 2 1 := by
  intro hT
  have hw := exists_noncyclic_permutable_of_witness h hp hp5 hXL hXc hXA hW hLW hXTY hKY hKn
    hXK hZ
  rcases hw with ⟨A, hAp, hAnc, U, hAU⟩
  obtain ⟨ψ⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv _ 2 1 hT
  have hψs : Function.Surjective ψ.toMonoidHom := ψ.surjective
  have hU'coe : ((U.mapSurjective hψs : Sylow 2 CFSG.Sporadic.Schreier.Tits.titsD) :
      Subgroup CFSG.Sporadic.Schreier.Tits.titsD) =
      (U : Subgroup ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K))).map ψ.toMonoidHom :=
    Sylow.coe_mapSurjective _ _
  have hA'U' : ((A.map ψ.toMonoidHom : Subgroup CFSG.Sporadic.Schreier.Tits.titsD) :
      Set CFSG.Sporadic.Schreier.Tits.titsD) *
      (((U.mapSurjective hψs : Sylow 2 CFSG.Sporadic.Schreier.Tits.titsD) :
        Subgroup CFSG.Sporadic.Schreier.Tits.titsD) : Set CFSG.Sporadic.Schreier.Tits.titsD) =
      (((U.mapSurjective hψs : Sylow 2 CFSG.Sporadic.Schreier.Tits.titsD) :
        Subgroup CFSG.Sporadic.Schreier.Tits.titsD) : Set CFSG.Sporadic.Schreier.Tits.titsD) *
        ((A.map ψ.toMonoidHom : Subgroup CFSG.Sporadic.Schreier.Tits.titsD) :
          Set CFSG.Sporadic.Schreier.Tits.titsD) := by
    rw [hU'coe, coe_map, coe_map, ← Set.image_mul, hAU, Set.image_mul]
  have hcyc :=
    (SteinbergBT.tits_common_sylow_and_prime_subgroup_normalizer_action_is_cyclic hp (by omega)
      (U.mapSurjective hψs) (A.map ψ.toMonoidHom) (hAp.map _) hA'U').2.2.1
  exact hAnc (isCyclic_of_surjective
    (A.equivMapOfInjective ψ.toMonoidHom ψ.injective).symm.toMonoidHom (MulEquiv.surjective _))

end CFSG.Quasithin.H13.NQCat
