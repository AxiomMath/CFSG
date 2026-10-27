module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDivExcTags
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcPilotNonsplit
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixENonsplit
public import CFSG.LieType.Chevalley.D4TripleA2Lemmas

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.SeitzReduction

namespace LayerPDivExc

theorem mulAut_conj_injective {C : Type*} [Group C] (h : Subgroup.center C = ⊥) :
    Function.Injective (MulAut.conj : C →* MulAut C) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hgc : g ∈ Subgroup.center C := Subgroup.mem_center_iff.mpr fun x => by
    have h1 := congrArg (fun φ : MulAut C => φ x) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc x * g = g * x * g⁻¹ * g := by rw [h1]
      _ = g * x := by group
  rw [h, Subgroup.mem_bot] at hgc
  exact hgc

theorem centralizer_zpowers_eq {L : Type*} [Group L] (a : L) :
    Subgroup.centralizer (Subgroup.zpowers a : Set L) = Subgroup.centralizer {a} := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem dvd_of_card_zpowers {L : Type*} [Group L] {K : Type} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) {a : L} (ha : a ^ p = 1) (h : Nat.card (Subgroup.zpowers a) = Nat.card K + 1) :
    p ∣ Nat.card K + 1 := by
  rw [Nat.card_zpowers] at h
  have h1 : orderOf a ∣ p := orderOf_dvd_of_pow_eq_one ha
  rcases (Nat.dvd_prime hp).mp h1 with h2 | h2
  · have : 1 < Nat.card K := Finite.one_lt_card
    omega
  · rw [← h2, h]

theorem map_centralizer_eq_of_map_zpowers {L : Type} [Group L] {a g : L} {Y : Subgroup L}
    (h : (Subgroup.zpowers a).map (MulAut.conj g).toMonoidHom = Y) :
    (Subgroup.centralizer {a}).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer (Y : Set L) := by
  rw [← centralizer_zpowers_eq, LayerFacts.centralizer_eq_comap_map (MulAut.conj g), h,
    Subgroup.map_comap_eq_self_of_surjective (MulAut.conj g).surjective]

section Orders


variable {τ : Tag} {K : Type} [Field K]

theorem sq_sub_one_dvd_card_rootSpan [Finite K] [CharP K 2] {S : Set (Fin τ.rank → ℤ)}
    {j : Fin τ.rank} (hj : Pi.single j 1 ∈ S) (hj' : -Pi.single j 1 ∈ S) :
    Nat.card K ^ 2 - 1 ∣ Nat.card ((rootSpan τ K S).subgroupOf (adjointGroup τ K)) := by
  have hinj := rankOneRep_injective_of_charTwo (τ := τ) (K := K) j
  have hle : (rankOneRep τ K j).range ≤ (rootSpan τ K S).subgroupOf (adjointGroup τ K) := by
    rintro _ ⟨g, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    have h1 : ((rankOneRep τ K j g : adjointGroup τ K) : ModGL τ K) ∈
        (exceptional_ordinary_rank_one_central_image τ K j).choose.range := ⟨g, rfl⟩
    rw [(exceptional_ordinary_rank_one_central_image τ K j).choose_spec.2.2.2.2.1] at h1
    refine (Subgroup.closure_le _).2 ?_ h1
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact (le_iSup₂_of_le _ hj le_rfl : rootSubgroup τ K _ ≤ rootSpan τ K S)
        (xUnit_mem_rootSubgroup j c)
    · exact (le_iSup₂_of_le _ hj' le_rfl : rootSubgroup τ K _ ≤ rootSpan τ K S)
        (yUnit_mem_rootSubgroup j c)
  have h := Subgroup.card_dvd_of_le hle
  rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv] at h
  exact (LayerPDiv.sq_sub_one_dvd_card_SL (D := K) (d := 2) le_rfl).trans h

end Orders


section Pilots


variable {K : Type} [Field K]

theorem dvd_card_of_isComponentOf_highNonsplit_F4 [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime)
    {a : adjointGroup .F4 K} (ha : a ^ p = 1) (hn : GGExcHighNonsplit .F4 K (Subgroup.zpowers a))
    {X : Subgroup (adjointGroup .F4 K)} (hX : IsComponentOf X (Subgroup.centralizer {a})) :
    p ∣ Nat.card X := by
  obtain ⟨g, Y, hYJ, hcyc, hY, hAY⟩ := hn
  have hpK : p ∣ Nat.card K + 1 := dvd_of_card_zpowers hp ha (by
    rw [← hY, ← hAY, Subgroup.card_map_of_injective (MulAut.conj g).injective])
  have hX' := isComponentOf_map (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective hX
  rw [map_centralizer_eq_of_map_zpowers hAY] at hX'
  have hYJ' : Y ≤ (F4Pilot.highestRootRankOne K).subgroupOf (adjointGroup .F4 K) := by
    rw [F4Pilot.highestRootRankOne_eq_rootSL2R]
    exact hYJ
  obtain ⟨hCY, -, hYD⟩ := F4Pilot.centralizer_nonsplit hYJ' hcyc hY
  rw [hCY] at hX'
  rw [← Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
    (MulAut.conj g).injective]
  refine dvd_card_of_isComponentOf_of_subCoreFamily (LayerExc.isSubCoreFamily_sup_of_centralizer
    (LayerExc.commute_of_isCyclic hcyc) hYD F4Pilot.isQuasisimple_C3Levi
    F4Pilot.center_C3Levi_eq_bot) (fun _ => ?_) hX'
  exact (LayerPDiv.dvd_sq_sub_one (Or.inr hpK)).trans (sq_sub_one_dvd_card_rootSpan (j := 1)
    (EPilot.single_mem_perpRoots (by decide)) (EPilot.neg_single_mem_perpRoots (by decide)))

theorem dvd_card_of_isComponentOf_highNonsplit_E7 [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime)
    {a : adjointGroup .E7 K} (ha : a ^ p = 1) (hn : GGExcHighNonsplit .E7 K (Subgroup.zpowers a))
    {X : Subgroup (adjointGroup .E7 K)} (hX : IsComponentOf X (Subgroup.centralizer {a})) :
    p ∣ Nat.card X := by
  obtain ⟨g, Y, hYJ, hcyc, hY, hAY⟩ := hn
  have hpK : p ∣ Nat.card K + 1 := dvd_of_card_zpowers hp ha (by
    rw [← hY, ← hAY, Subgroup.card_map_of_injective (MulAut.conj g).injective])
  have hX' := isComponentOf_map (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective hX
  rw [map_centralizer_eq_of_map_zpowers hAY] at hX'
  obtain ⟨hCY, -, hYD⟩ := E6Pilot.centralizer_nonsplit_of_descent (Or.inr (Or.inl rfl))
    E7Pilot.perpLeviFrobDescent_E7_of_finite hYJ hcyc hY
  rw [hCY] at hX'
  rw [← Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
    (MulAut.conj g).injective]
  refine dvd_card_of_isComponentOf_of_subCoreFamily (LayerExc.isSubCoreFamily_sup_of_centralizer
    (LayerExc.commute_of_isCyclic hcyc) hYD E7Pilot.isQuasisimple_perpLevi_E7
    E7Pilot.center_perpLevi_E7_eq_bot) (fun _ => ?_) hX'
  exact (LayerPDiv.dvd_sq_sub_one (Or.inr hpK)).trans (sq_sub_one_dvd_card_rootSpan (j := 1)
    (EPilot.single_mem_perpRoots (by decide)) (EPilot.neg_single_mem_perpRoots (by decide)))

theorem dvd_card_of_isComponentOf_highNonsplit_E8 [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime)
    {a : adjointGroup .E8 K} (ha : a ^ p = 1) (hn : GGExcHighNonsplit .E8 K (Subgroup.zpowers a))
    {X : Subgroup (adjointGroup .E8 K)} (hX : IsComponentOf X (Subgroup.centralizer {a})) :
    p ∣ Nat.card X := by
  obtain ⟨g, Y, hYJ, hcyc, hY, hAY⟩ := hn
  have hpK : p ∣ Nat.card K + 1 := dvd_of_card_zpowers hp ha (by
    rw [← hY, ← hAY, Subgroup.card_map_of_injective (MulAut.conj g).injective])
  have hX' := isComponentOf_map (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective hX
  rw [map_centralizer_eq_of_map_zpowers hAY] at hX'
  obtain ⟨hCY, -, hYD⟩ := E8Pilot.centralizer_nonsplit_E8 hYJ hY hcyc
  rw [hCY] at hX'
  rw [← Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
    (MulAut.conj g).injective]
  refine dvd_card_of_isComponentOf_of_subCoreFamily (LayerExc.isSubCoreFamily_sup_of_centralizer
    (LayerExc.commute_of_isCyclic hcyc) hYD E8Pilot.isQuasisimple_e7Levi
    E8Pilot.center_e7Levi_eq_bot) (fun _ => ?_) hX'
  exact (LayerPDiv.dvd_sq_sub_one (Or.inr hpK)).trans (sq_sub_one_dvd_card_rootSpan (j := 0)
    (EPilot.single_mem_perpRoots (by decide)) (EPilot.neg_single_mem_perpRoots (by decide)))

theorem dvd_card_of_isComponentOf_autFix_highNonsplit_E6 [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) {α : MulAut (adjointGroup .E6 K)} (hα : α ^ p = 1)
    (hn : GGE6InndiagHighNonsplit K (Subgroup.zpowers α)) {X : Subgroup (adjointGroup .E6 K)}
    (hX : IsComponentOf X (LayerSixE.autFix (Subgroup.zpowers α))) : p ∣ Nat.card X := by
  obtain ⟨g, Y, hYJ, hcyc, hY, hAY⟩ := hn
  have hpK : p ∣ Nat.card K + 1 := dvd_of_card_zpowers hp hα (by
    rw [hAY, Subgroup.card_map_of_injective (mulAut_conj_injective center_adjointGroup_eq_bot),
      Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hY])
  rw [hAY, LayerSixE.autFix_map_conj] at hX
  have hmap : (Y.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = Y := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id Y
    refine MonoidHom.ext fun x => ?_
    change g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ = x
    group
  have hX' := isComponentOf_map (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective hX
  rw [LayerFacts.centralizer_eq_comap_map (MulAut.conj g), hmap,
    Subgroup.map_comap_eq_self_of_surjective (MulAut.conj g).surjective] at hX'
  obtain ⟨hCY, -, hYD⟩ := E6Pilot.centralizer_nonsplit_E6 hYJ hY hcyc
  rw [hCY] at hX'
  rw [← Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
    (MulAut.conj g).injective]
  refine dvd_card_of_isComponentOf_of_subCoreFamily (LayerExc.isSubCoreFamily_sup_of_centralizer
    (LayerExc.commute_of_isCyclic hcyc) hYD E6Pilot.isQuasisimple_a5Levi
    E6Pilot.center_a5Levi_eq_bot) (fun _ => ?_) hX'
  exact (LayerPDiv.dvd_sq_sub_one (Or.inr hpK)).trans (sq_sub_one_dvd_card_rootSpan (j := 0)
    (EPilot.single_mem_perpRoots (by decide)) (EPilot.neg_single_mem_perpRoots (by decide)))

end Pilots

end LayerPDivExc

section Defs


@[expose] def GGExcPDivNonToralRestInput (τ : Tag) : Prop :=
  ∀ f : ℕ, 1 ≤ f → ∀ p : ℕ, p.Prime → p ≠ 2 → (p ∣ 2 ^ f - 1 ∨ p ∣ 2 ^ f + 1) →
    ∀ a : adjointGroup τ (GaloisField 2 f), a ^ p = 1 →
      ¬ GGExcToral τ (GaloisField 2 f) (Subgroup.zpowers a) →
        ¬ GGExcHighNonsplit τ (GaloisField 2 f) (Subgroup.zpowers a) →
          ∀ X : Subgroup (adjointGroup τ (GaloisField 2 f)),
            IsComponentOf X (Subgroup.centralizer {a}) → p ∣ Nat.card X

@[expose] def GGE6PDivNonToralRestInput : Prop :=
  ∀ f : ℕ, 1 ≤ f → ∀ p : ℕ, p.Prime → p ≠ 2 → (p ∣ 2 ^ f - 1 ∨ p ∣ 2 ^ f + 1) →
    ∀ α ∈ LayerSixE.inndiagAut .E6 (GaloisField 2 f), α ^ p = 1 →
      ¬ LayerSixE.GGInndiagToral .E6 (GaloisField 2 f) (Subgroup.zpowers α) →
        ¬ GGE6InndiagHighNonsplit (GaloisField 2 f) (Subgroup.zpowers α) →
          ∀ X : Subgroup (adjointGroup .E6 (GaloisField 2 f)),
            IsComponentOf X (LayerSixE.autFix (Subgroup.zpowers α)) → p ∣ Nat.card X

end Defs

section Reductions


theorem ggExcPDivNonToralInput_of_rest_F4 (h : GGExcPDivNonToralRestInput .F4) :
    GGExcPDivNonToralInput .F4 := by
  intro f hf p hp hp2 hpq a ha ht X hX
  by_cases hn : GGExcHighNonsplit .F4 (GaloisField 2 f) (Subgroup.zpowers a)
  · exact LayerPDivExc.dvd_card_of_isComponentOf_highNonsplit_F4 hp ha hn hX
  · exact h f hf p hp hp2 hpq a ha ht hn X hX

theorem ggExcPDivNonToralInput_of_rest_E7 (h : GGExcPDivNonToralRestInput .E7) :
    GGExcPDivNonToralInput .E7 := by
  intro f hf p hp hp2 hpq a ha ht X hX
  by_cases hn : GGExcHighNonsplit .E7 (GaloisField 2 f) (Subgroup.zpowers a)
  · exact LayerPDivExc.dvd_card_of_isComponentOf_highNonsplit_E7 hp ha hn hX
  · exact h f hf p hp hp2 hpq a ha ht hn X hX

theorem ggExcPDivNonToralInput_of_rest_E8 (h : GGExcPDivNonToralRestInput .E8) :
    GGExcPDivNonToralInput .E8 := by
  intro f hf p hp hp2 hpq a ha ht X hX
  by_cases hn : GGExcHighNonsplit .E8 (GaloisField 2 f) (Subgroup.zpowers a)
  · exact LayerPDivExc.dvd_card_of_isComponentOf_highNonsplit_E8 hp ha hn hX
  · exact h f hf p hp hp2 hpq a ha ht hn X hX

theorem ggE6PDivNonToralInput_of_rest (h : GGE6PDivNonToralRestInput) :
    GGE6PDivNonToralInput := by
  intro f hf p hp hp2 hpq α hαD hαp ht X hX
  by_cases hn : GGE6InndiagHighNonsplit (GaloisField 2 f) (Subgroup.zpowers α)
  · exact LayerPDivExc.dvd_card_of_isComponentOf_autFix_highNonsplit_E6 hp hαp hn hX
  · exact h f hf p hp hp2 hpq α hαD hαp ht hn X hX

end Reductions

end CFSG.StandardType
