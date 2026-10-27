module

public import CFSG.Quasithin.H13.NQBlockLargeRee
public import CFSG.Quasithin.H13.NQTermNoncyclicAction

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.LieType.Ree CFSG.Blueprint
open CFSG.LocalAnalysis.ComponentInitial (pairAutSubgroup pairAutRestrict)
open scoped Pointwise

theorem range_pairAutRestrict_congr {S Γ : Type*} [Group S] [Group Γ] (ψ : S ≃* Γ)
    (A U : Subgroup S) :
    Nonempty ((pairAutRestrict A U).range ≃*
      (pairAutRestrict (A.map ψ.toMonoidHom) (U.map ψ.toMonoidHom)).range) := by
  classical
  set A' := A.map ψ.toMonoidHom with hA'
  set U' := U.map ψ.toMonoidHom with hU'
  have hcongr : ∀ (β : MulAut S) (x : S), MulAut.congr ψ β (ψ x) = ψ (β x) := by
    intro β x
    simp [MulAut.congr_apply]
  have hmap : ∀ (β : MulAut S) (B : Subgroup S),
      (B.map ψ.toMonoidHom).map (MulAut.congr ψ β).toMonoidHom =
        (B.map β.toMonoidHom).map ψ.toMonoidHom := by
    intro β B
    rw [map_map, map_map]
    congr 1
    exact MonoidHom.ext fun x => hcongr β x
  have hc : ∀ α ∈ pairAutSubgroup A U, MulAut.congr ψ α ∈ pairAutSubgroup A' U' := by
    intro α hα
    refine ⟨?_, ?_⟩
    · rw [hA', hmap, hα.1]
    · rw [hU', hmap, hα.2]
  have hcinv : ∀ α' ∈ pairAutSubgroup A' U', (MulAut.congr ψ).symm α' ∈ pairAutSubgroup A U := by
    intro α' hα'
    have h1 : ∀ B : Subgroup S, (B.map ψ.toMonoidHom).map α'.toMonoidHom = B.map ψ.toMonoidHom →
        B.map ((MulAut.congr ψ).symm α').toMonoidHom = B := by
      intro B hB
      have h2 := hmap ((MulAut.congr ψ).symm α') B
      rw [MulEquiv.apply_symm_apply, hB] at h2
      exact (map_injective ψ.injective h2).symm
    exact ⟨h1 A hα'.1, h1 U hα'.2⟩
  set ψA : A ≃* A' := A.equivMapOfInjective ψ.toMonoidHom ψ.injective with hψA
  have hrel : ∀ α (hα : α ∈ pairAutSubgroup A U),
      pairAutRestrict A' U' ⟨MulAut.congr ψ α, hc α hα⟩ =
        MulAut.congr ψA (pairAutRestrict A U ⟨α, hα⟩) := by
    intro α hα
    ext a'
    obtain ⟨a, rfl⟩ := ψA.surjective a'
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    change ((MulAut.congr ψ α) (ψ a) : Γ) = ψ (α a)
    exact hcongr α a
  have heq : (pairAutRestrict A' U').range =
      (pairAutRestrict A U).range.map (MulAut.congr ψA).toMonoidHom := by
    apply le_antisymm
    · rintro _ ⟨⟨α', hα'⟩, rfl⟩
      refine ⟨pairAutRestrict A U ⟨_, hcinv α' hα'⟩, ⟨_, rfl⟩, ?_⟩
      have h1 := hrel _ (hcinv α' hα')
      simp only [MulEquiv.apply_symm_apply] at h1
      exact h1.symm
    · rintro _ ⟨_, ⟨⟨α, hα⟩, rfl⟩, rfl⟩
      exact ⟨_, hrel α hα⟩
  exact ⟨((pairAutRestrict A U).range.equivMapOfInjective _ (MulAut.congr ψA).injective).trans
    (MulEquiv.subgroupCongr heq.symm)⟩

open CFSG.Quasithin.H13.NQTerm in
theorem original_characteristic_witness_excludes_normal_large_Ree_quotient
    {G : Type} [Group G]
    [Finite G] {T L M : Subgroup G} (h : QTNQ T L M) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {X : Subgroup G} (hXL : X ≤ L) (hXc : (X.subgroupOf L).Characteristic)
    (hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X))
    (hW : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2)
    (hLW : ∃ l : normalizer (X : Set G), (l : G) ∈ L ∧
      CFSG.Quasithin.SteinbergCC.normalizerFrattiniConj X l ≠ 1)
    {Y K : Subgroup G} (hXTY : X ⊔ T ≤ Y) (hKY : K ≤ Y) (hKn : (K.subgroupOf Y).Normal)
    (hXK : X ≤ K) (hZ : ¬ p ∣ Nat.card (center (K ⧸ CFSG.pCore 2 K))) :
    ∀ a : ℕ, 1 ≤ a →
      ¬ ReeTitsModel ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) .twistedF4 2
        (2 * a + 1) := by
  intro a ha hRee
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨P'⟩ : Nonempty (Sylow p X) := inferInstance
  have hP : CFSG.ABGLocalTools.IsSylowOf p ((P' : Subgroup X).map X.subtype) X := ⟨P', rfl⟩
  obtain ⟨-, ⟨U', hU'⟩, hAU, hncyc⟩ :=
    original_characteristic_witness_normal_quotient_common_normalizer_action_is_noncyclic
      h hp hp5 hXL hXc hXA hW hLW hXTY hKY hKn hXK hZ _ hP
  set σ : K →* (K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K) :=
    (QuotientGroup.mk' (center (K ⧸ CFSG.pCore 2 K))).comp (QuotientGroup.mk' (CFSG.pCore 2 K))
    with hσ
  set A := ((((P' : Subgroup X).map X.subtype : Subgroup G)).subgroupOf K).map σ with hA
  set U := (T.subgroupOf K).map σ with hU
  obtain ⟨F, hF, hFfin, hFchar, hFcard, ⟨ψ⟩⟩ := exists_mulEquiv_reeGamma_of_reeTitsModel ha hRee
  set A' := A.map ψ.toMonoidHom with hA'
  have hψs : Function.Surjective ψ.toMonoidHom := fun y => ⟨ψ.symm y, by simp⟩
  set U'' : Sylow 2 (ReeTag.F4.reeGamma F a) := U'.mapSurjective hψs with hU''
  have hU''coe : (U'' : Subgroup (ReeTag.F4.reeGamma F a)) = U.map ψ.toMonoidHom := by
    rw [hU'', Sylow.coe_mapSurjective, hU']
  have hAp : IsPGroup p A' := by
    have h1 : IsPGroup p (((P' : Subgroup X).map X.subtype : Subgroup G).subgroupOf K) := by
      rw [← comap_subtype]
      exact (P'.isPGroup'.map _).comap_subtype
    exact (h1.map σ).map _
  have hAU' : (A' : Set (ReeTag.F4.reeGamma F a)) * (U'' : Set (ReeTag.F4.reeGamma F a)) =
      (U'' : Set (ReeTag.F4.reeGamma F a)) * (A' : Set (ReeTag.F4.reeGamma F a)) := by
    have hUset : (U'' : Set (ReeTag.F4.reeGamma F a)) = ψ.toMonoidHom '' (U : Set _) := by
      rw [← coe_map, ← hU''coe]
      rfl
    have hAset : (A' : Set (ReeTag.F4.reeGamma F a)) = ψ.toMonoidHom '' (A : Set _) := rfl
    rw [hUset, hAset, ← Set.image_mul, hAU, Set.image_mul]
  have hcyc :=
    (CFSG.Quasithin.H13.NQCat.large_Ree_common_sylow_prime_subgroup_normalizer_action_is_cyclic
      ha hFcard hp hp2 U'' A' hAp hAU').2.2.1.1
  rw [hU''coe] at hcyc
  obtain ⟨e⟩ := range_pairAutRestrict_congr ψ A U
  exact hncyc (isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective)

end CFSG.Quasithin.H13.NQBlock
