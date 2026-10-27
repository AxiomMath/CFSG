module

public import CFSG.Quasithin.H13.NQTermNoncyclicAction
public import CFSG.Quasithin.H13.NQTermG2Cyclic

public section

namespace CFSG.Quasithin.H13.NQTerm

open Subgroup CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial (pairAutSubgroup pairAutRestrict)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj)
open scoped Pointwise

theorem isCyclic_pairAutRestrict_range_of_mulEquiv {M N : Type*} [Group M] [Group N]
    (ψ : M ≃* N) (A U : Subgroup M)
    (h : IsCyclic (pairAutRestrict (A.map ψ.toMonoidHom) (U.map ψ.toMonoidHom)).range) :
    IsCyclic (pairAutRestrict A U).range := by
  set A' := A.map ψ.toMonoidHom
  set U' := U.map ψ.toMonoidHom
  obtain ⟨eA, heA⟩ : ∃ eA : A ≃* A', ∀ a : A, ((eA a : A') : N) = ψ (a : M) :=
    ⟨A.equivMapOfInjective ψ.toMonoidHom ψ.injective, fun _ => rfl⟩
  have hsymm : ∀ a' : A', ((eA.symm a' : A) : M) = ψ.symm (a' : N) := by
    intro a'
    apply ψ.injective
    rw [MulEquiv.apply_symm_apply, ← heA, MulEquiv.apply_symm_apply]
  have hmap : ∀ (α : MulAut M) (X : Subgroup M), X.map α.toMonoidHom = X →
      (X.map ψ.toMonoidHom).map (MulAut.congr ψ α).toMonoidHom = X.map ψ.toMonoidHom := by
    intro α X hX
    have hcomp : (MulAut.congr ψ α).toMonoidHom.comp ψ.toMonoidHom =
        ψ.toMonoidHom.comp α.toMonoidHom := by
      ext x
      simp [MulAut.congr_apply]
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hX]
  let Φ : pairAutSubgroup A U →* pairAutSubgroup A' U' :=
    { toFun := fun α => ⟨MulAut.congr ψ α.1, hmap α.1 A α.2.1, hmap α.1 U α.2.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun _ _ => Subtype.ext (map_mul _ _ _) }
  have hle : (pairAutRestrict A U).range.map (MulAut.congr eA).toMonoidHom ≤
      (pairAutRestrict A' U').range := by
    rintro _ ⟨_, ⟨α, rfl⟩, rfl⟩
    refine ⟨Φ α, MulEquiv.ext fun a' => Subtype.ext ?_⟩
    change (MulAut.congr ψ α.1) (a' : N) =
      ((eA (pairAutRestrict A U α (eA.symm a')) : A') : N)
    rw [heA]
    change ψ (α.1 (ψ.symm (a' : N))) = ψ (α.1 ((eA.symm a' : A) : M))
    rw [hsymm]
  have : IsCyclic (pairAutRestrict A' U').range := h
  let e := (pairAutRestrict A U).range.equivMapOfInjective (MulAut.congr eA).toMonoidHom
    (MulAut.congr eA).injective
  exact isCyclic_of_injective ((Subgroup.inclusion hle).comp e.toMonoidHom)
    ((Subgroup.inclusion_injective hle).comp e.injective)

variable {G : Type} [Group G] [Finite G]

theorem original_characteristic_witness_excludes_normal_even_G2_quotient
    {T L M : Subgroup G} (h : QTNQ T L M) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {X : Subgroup G} (hXL : X ≤ L) (hXc : (X.subgroupOf L).Characteristic)
    (hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X))
    (hW : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2)
    (hLW : ∃ l : normalizer (X : Set G), (l : G) ∈ L ∧ normalizerFrattiniConj X l ≠ 1)
    {Y K : Subgroup G} (hXTY : X ⊔ T ≤ Y) (hKY : K ≤ Y) (hKn : (K.subgroupOf Y).Normal)
    (hXK : X ≤ K) (hZ : ¬ p ∣ Nat.card (center (K ⧸ CFSG.pCore 2 K))) :
    ∀ f : ℕ, 2 ≤ f → ¬ CFSG.Blueprint.ChevalleyExceptionalModel
      ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) .G2 2 f := by
  classical
  intro f hf hmod
  obtain ⟨-, k, _, _, hk, ⟨η⟩⟩ := hmod
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf p X
  have hPp : IsPGroup p (P.subgroupOf K) := by
    obtain ⟨Q, hQ⟩ := hP
    rw [← hQ]
    exact (Q.2.map X.subtype).comap_of_injective K.subtype K.subtype_injective
  obtain ⟨-, ⟨U', hU'⟩, hAU, hnc⟩ :=
    original_characteristic_witness_normal_quotient_common_normalizer_action_is_noncyclic h hp
      hp5 hXL hXc hXA hW hLW hXTY hKY hKn hXK hZ P hP
  set σ : K →* (K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K) :=
    (QuotientGroup.mk' (center (K ⧸ CFSG.pCore 2 K))).comp (QuotientGroup.mk' (CFSG.pCore 2 K))
  set A := (P.subgroupOf K).map σ
  set U := (T.subgroupOf K).map σ
  let ψ : ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) ≃* adjointGroup .G2 k :=
    η.trans ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot)
  obtain ⟨Ustar, hUstar⟩ : ∃ Ustar : Sylow 2 (adjointGroup .G2 k),
      (Ustar : Subgroup (adjointGroup .G2 k)) = U.map ψ.toMonoidHom :=
    have hsurj : Function.Surjective ψ.toMonoidHom := ψ.surjective
    ⟨U'.mapSurjective hsurj, by rw [Sylow.coe_mapSurjective, hU']⟩
  obtain ⟨m, hm⟩ := (hPp.map σ).exists_card_eq
  have hcardA : Nat.card (A.map ψ.toMonoidHom) = p ^ m := by
    rw [Subgroup.card_map_of_injective ψ.injective]
    exact hm
  have hAodd : Odd (Nat.card (A.map ψ.toMonoidHom)) := by
    rw [hcardA]
    exact (hp.odd_of_ne_two (by omega)).pow
  have hA3 : ¬ 3 ∣ Nat.card (A.map ψ.toMonoidHom) := by
    rw [hcardA]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hAUstar : ((A.map ψ.toMonoidHom : Subgroup (adjointGroup .G2 k)) :
      Set (adjointGroup .G2 k)) * ((Ustar : Subgroup (adjointGroup .G2 k)) :
        Set (adjointGroup .G2 k)) =
      ((Ustar : Subgroup (adjointGroup .G2 k)) : Set (adjointGroup .G2 k)) *
        ((A.map ψ.toMonoidHom : Subgroup (adjointGroup .G2 k)) : Set (adjointGroup .G2 k)) := by
    rw [hUstar, Subgroup.coe_map ψ.toMonoidHom A, Subgroup.coe_map ψ.toMonoidHom U,
      ← Set.image_mul, hAU, Set.image_mul]
  obtain ⟨-, -, ⟨hcyc, -⟩, -⟩ := even_G2_common_sylow_odd_subgroup_normalizer_action_is_cyclic hf
    k hk Ustar (A.map ψ.toMonoidHom) hAodd hA3 hAUstar
  rw [hUstar] at hcyc
  exact hnc (isCyclic_pairAutRestrict_range_of_mulEquiv ψ A U hcyc)

end CFSG.Quasithin.H13.NQTerm
