module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotQ2FamilyCount

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphLevi CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_perfect le_perfectCore_of_perfect)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.E6Pilot (adjDatumE6 E6Neighbour amalgamRoots amalgamPlacement)
open CFSG.LieType.CurtisTits (IsCompatible)

local instance twistedE6PilotQ2FamilyMainNeZero : NeZero TwistTag.E6.tag.rank := ⟨by decide⟩

local instance twistedE6PilotQ2FamilyMainNeZeroE6 : NeZero Tag.E6.rank := ⟨by decide⟩

theorem amalgamPlacement_cases {J J' : Finset (Fin (Tag.rank .E6))} (h : J ⊆ J')
    (hJ' : J'.card ≤ 2) :
    amalgamPlacement J = amalgamPlacement J' ∨
      (amalgamPlacement J = .high ∧ amalgamPlacement J' = .six ∧ J ⊆ {0, 2, 3}) ∨
      (amalgamPlacement J = .high ∧ amalgamPlacement J' = .three ∧ J ⊆ {4, 5}) ∨
      (amalgamPlacement J = .six ∧ amalgamPlacement J' = .three ∧ J ⊆ {1}) := by
  have hN' := E6Pilot.subset_nodes_amalgamPlacement hJ'
  have k1 : ∀ j : Fin (Tag.rank .E6), j ∈ E6Neighbour.six.nodes → j ≠ 1 →
      j ∈ ({0, 2, 3} : Finset (Fin (Tag.rank .E6))) := by decide
  have k2 : ∀ j : Fin (Tag.rank .E6), j ∈ E6Neighbour.three.nodes → j ≠ 1 →
      j ∈ ({4, 5} : Finset (Fin (Tag.rank .E6))) := by decide
  have k3 : ∀ j : Fin (Tag.rank .E6), j ∈ E6Neighbour.three.nodes → j ≠ 4 → j ≠ 5 →
      j ∈ ({1} : Finset (Fin (Tag.rank .E6))) := by decide
  by_cases h1 : (1 : Fin (Tag.rank .E6)) ∈ J
  · have h1' : (1 : Fin (Tag.rank .E6)) ∈ J' := h h1
    by_cases h45 : (4 : Fin (Tag.rank .E6)) ∈ J ∨ (5 : Fin (Tag.rank .E6)) ∈ J
    · left
      rw [E6Pilot.amalgamPlacement_of_four_or_five_mem h1 h45,
        E6Pilot.amalgamPlacement_of_four_or_five_mem h1' (h45.imp (fun h4 => h h4) fun h5 => h h5)]
    · have h4 : (4 : Fin (Tag.rank .E6)) ∉ J := fun h4 => h45 (Or.inl h4)
      have h5 : (5 : Fin (Tag.rank .E6)) ∉ J := fun h5 => h45 (Or.inr h5)
      rw [E6Pilot.amalgamPlacement_of_not_four_five h1 h4 h5]
      by_cases h45' : (4 : Fin (Tag.rank .E6)) ∈ J' ∨ (5 : Fin (Tag.rank .E6)) ∈ J'
      · have hP := E6Pilot.amalgamPlacement_of_four_or_five_mem h1' h45'
        rw [hP] at hN'
        refine Or.inr (Or.inr (Or.inr ⟨rfl, hP, fun j hj => k3 j (hN' (h hj)) ?_ ?_⟩))
        · rintro rfl
          exact h4 hj
        · rintro rfl
          exact h5 hj
      · have h4' : (4 : Fin (Tag.rank .E6)) ∉ J' := fun h4 => h45' (Or.inl h4)
        have h5' : (5 : Fin (Tag.rank .E6)) ∉ J' := fun h5 => h45' (Or.inr h5)
        exact Or.inl (E6Pilot.amalgamPlacement_of_not_four_five h1' h4' h5').symm
  · rw [E6Pilot.amalgamPlacement_of_one_not_mem h1]
    by_cases h1' : (1 : Fin (Tag.rank .E6)) ∈ J'
    · by_cases h45' : (4 : Fin (Tag.rank .E6)) ∈ J' ∨ (5 : Fin (Tag.rank .E6)) ∈ J'
      · have hP := E6Pilot.amalgamPlacement_of_four_or_five_mem h1' h45'
        rw [hP] at hN'
        refine Or.inr (Or.inr (Or.inl ⟨rfl, hP, fun j hj => k2 j (hN' (h hj)) ?_⟩))
        rintro rfl
        exact h1 hj
      · have h4' : (4 : Fin (Tag.rank .E6)) ∉ J' := fun h4 => h45' (Or.inl h4)
        have h5' : (5 : Fin (Tag.rank .E6)) ∉ J' := fun h5 => h45' (Or.inr h5)
        have hP := E6Pilot.amalgamPlacement_of_not_four_five h1' h4' h5'
        rw [hP] at hN'
        refine Or.inr (Or.inl ⟨rfl, hP, fun j hj => k1 j (hN' (h hj)) ?_⟩)
        rintro rfl
        exact h1 hj
    · exact Or.inl (E6Pilot.amalgamPlacement_of_one_not_mem h1').symm

theorem memCoords_subset_ovlSet {J : Finset (Fin (Tag.rank .E6))} :
    (J ⊆ {0, 2, 3} → memCoords .high J ⊆ ovlSet 2) ∧
      (J ⊆ {4, 5} → memCoords .high J ⊆ ovlSet 1) ∧
      (J ⊆ {1} → memCoords .six J ⊆ ovlSet 2) := by
  have e1 : memCoords .high ({0, 2, 3} : Finset (Fin (Tag.rank .E6))) ⊆ ovlSet 2 := by decide
  have e2 : memCoords .high ({4, 5} : Finset (Fin (Tag.rank .E6))) ⊆ ovlSet 1 := by decide
  have e3 : memCoords .six ({1} : Finset (Fin (Tag.rank .E6))) ⊆ ovlSet 2 := by decide
  exact ⟨fun hJ => (Finset.biUnion_subset_biUnion_of_subset_left _ hJ).trans e1,
    fun hJ => (Finset.biUnion_subset_biUnion_of_subset_left _ hJ).trans e2,
    fun hJ => (Finset.biUnion_subset_biUnion_of_subset_left _ hJ).trans e3⟩

section Family


variable {G : Type} [Group G] {K : Type} [Field K]

@[expose] def nbFam {M : Type*} [Group M] (c₁ c₂ c₃ : QCover G M) : E6Neighbour → QCover G M
  | .high => c₁
  | .six => c₂
  | .three => c₃

@[expose] noncomputable def secFamily
    (s : ∀ J : {J : Finset (Fin (Tag.rank .E6)) // J.card ≤ 2}, memModel K J.1 →* G) :
    ∀ J, (adjDatumE6 K).leviAmalgam J →* G :=
  fun J => (s J).comp (memIncl J.1)

theorem secFamily_apply
    (s : ∀ J : {J : Finset (Fin (Tag.rank .E6)) // J.card ≤ 2}, memModel K J.1 →* G)
    (J : {J : Finset (Fin (Tag.rank .E6)) // J.card ≤ 2}) (x : (adjDatumE6 K).leviAmalgam J) :
    secFamily s J x = s J (memIncl J.1 x) :=
  rfl

theorem isCompatible_secFamily {c : E6Neighbour → QCover G (ModGL TwistTag.E6.tag K)}
    (hperf : ∀ J : {J : Finset (Fin (Tag.rank .E6)) // J.card ≤ 2},
      ⁅memModel K J.1, memModel K J.1⁆ = memModel K J.1)
    {s : ∀ J : {J : Finset (Fin (Tag.rank .E6)) // J.card ≤ 2}, memModel K J.1 →* G}
    (hs : ∀ J, (c (amalgamPlacement J.1)).IsSection (s J))
    (htr : ∀ J J' : {J : Finset (Fin (Tag.rank .E6)) // J.card ≤ 2}, J.1 ⊆ J'.1 →
      ∀ u : memModel K J.1 →* G, (c (amalgamPlacement J.1)).IsSection u →
        (c (amalgamPlacement J'.1)).IsSection u) :
    IsCompatible (adjDatumE6 K).leviAmalgam (secFamily s) := by
  intro J J' hJJ' x y hxy
  have hsub : J.1 ⊆ J'.1 := hJJ'
  have h1 : (s J').comp (Subgroup.inclusion (memModel_mono (K := K) hsub)) = s J :=
    ((hs J').restrict (memModel_mono hsub)).eq_of_perfect (hperf J) (htr J J' hsub (s J) (hs J))
  have h2 : Subgroup.inclusion (memModel_mono (K := K) hsub) (memIncl J.1 x) = memIncl J'.1 y := by
    apply Subtype.ext
    change memHom K J.1 x = memHom K J'.1 y
    rw [memHom_apply, memHom_apply, hxy]
  rw [secFamily_apply, secFamily_apply, ← h1, MonoidHom.comp_apply, h2]

end Family

section Weyl

variable {K : Type} [Field K]

theorem triW_mem_adjointGroup : triW K ∈ adjointGroup TwistTag.E6.tag K :=
  list_prod_mem fun g hg => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
    exact weylElt_mem_adjointGroup i 1

theorem triW_mem_subsystemGroup : triW K ∈ subsystemGroup TwistTag.E6.tag K setA := by
  have hA : ∀ i ∈ triangleWord, i ≠ CFSG.LieType.Chevalley.E6GraphHighestRoot.e6Idx 1 := by decide
  refine list_prod_mem fun g hg => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hg
  exact weylElt_mem_subsystemGroup (hA i hi) 1

end Weyl

section CT


variable {G : Type} [Group G] {K : Type} [Field K] [Finite K]

theorem exists_ctHom (φ : ∀ J, (adjDatumE6 K).leviAmalgam J →* G)
    (hφ : IsCompatible (adjDatumE6 K).leviAmalgam φ) (hnt : ∃ J, ∃ x, φ J x ≠ 1)
    {G₀ : Subgroup G} (hG₀ : ⨆ J, (φ J).range = G₀) :
    ∃ f : G₀ →* ModGL TwistTag.E6.tag K, f.ker ≤ center G₀ ∧
      f.range = adjointGroup TwistTag.E6.tag K ∧
      ∀ J x (hx : φ J x ∈ G₀), f ⟨φ J x, hx⟩ = memHom K J.1 x := by
  obtain ⟨ψ, hsurj, hker, -, hZ, hψφ⟩ :=
    exists_surjective_iSup_range_of_isCompatible_adj φ hφ hnt hG₀
  let Ψ : adjointGroup .E6 K ≃* G₀ ⧸ center G₀ :=
    (E6Pilot.centerQuotientIsogenyEquiv (K := K)).symm.trans
      (E6Pilot.centerQuotientMulEquiv ψ hsurj hker hZ)
  have hΨθ : ∀ s, Ψ (CFSG.LieType.Steinberg.Isogeny.e6Isogeny K s) = QuotientGroup.mk (ψ s) := by
    intro s
    change (E6Pilot.centerQuotientMulEquiv ψ hsurj hker hZ)
      ((E6Pilot.centerQuotientIsogenyEquiv (K := K)).symm
        (CFSG.LieType.Steinberg.Isogeny.e6Isogeny K s)) = _
    rw [← E6Pilot.centerQuotientIsogenyEquiv_mk, MulEquiv.symm_apply_apply,
      E6Pilot.centerQuotientMulEquiv_mk]
  have hΨφ : ∀ J (x : (adjDatumE6 K).leviAmalgam J) (hx : φ J x ∈ G₀),
      Ψ x = QuotientGroup.mk ⟨φ J x, hx⟩ := by
    intro J x hx
    obtain ⟨y, rfl⟩ := E6Pilot.leviIsogeny_surjective (K := K) J.1 x
    rw [E6Pilot.coe_leviIsogeny, hΨθ]
    congr 1
    exact Subtype.ext (hψφ J y)
  let pbar : G₀ →* adjointGroup .E6 K := Ψ.symm.toMonoidHom.comp (QuotientGroup.mk' (center G₀))
  have hpbar : Function.Surjective pbar := Ψ.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  let f : G₀ →* ModGL TwistTag.E6.tag K :=
    (MulAut.conj (triW K)).toMonoidHom.comp ((adjointGroup .E6 K).subtype.comp pbar)
  refine ⟨f, ?_, ?_, ?_⟩
  · intro g hg
    have h2 : (((pbar g : adjointGroup .E6 K) : ModGL .E6 K) : ModGL TwistTag.E6.tag K) = 1 :=
      (map_eq_one_iff (MulAut.conj (triW K)) (MulAut.conj (triW K)).injective).1 hg
    have h3 : pbar g = 1 := Subtype.ext h2
    have h4 : (QuotientGroup.mk g : G₀ ⧸ center G₀) = 1 := (MulEquiv.map_eq_one_iff Ψ.symm).1 h3
    exact (QuotientGroup.eq_one_iff g).1 h4
  · ext y
    constructor
    · rintro ⟨g, rfl⟩
      exact mul_mem (mul_mem triW_mem_adjointGroup (pbar g).2) (inv_mem triW_mem_adjointGroup)
    · intro hy
      have hy' : (triW K)⁻¹ * y * triW K ∈ adjointGroup .E6 K :=
        mul_mem (mul_mem (inv_mem triW_mem_adjointGroup) hy) triW_mem_adjointGroup
      obtain ⟨g, hg⟩ := hpbar ⟨_, hy'⟩
      refine ⟨g, ?_⟩
      change MulAut.conj (triW K) ((pbar g : adjointGroup .E6 K) : ModGL .E6 K) = y
      rw [hg, MulAut.conj_apply]
      group
  · intro J x hx
    have h1 : pbar ⟨φ J x, hx⟩ = x := by
      change Ψ.symm (QuotientGroup.mk ⟨φ J x, hx⟩) = x
      rw [← hΨφ J x hx, MulEquiv.symm_apply_apply]
    change MulAut.conj (triW K) ((pbar ⟨φ J x, hx⟩ : adjointGroup .E6 K) : ModGL .E6 K) =
      MulAut.conj (triW K) ((x : adjointGroup .E6 K) : ModGL .E6 K)
    rw [h1]

end CT

section High


variable {G : Type} [Group G] {K : Type} [Field K] [CharP K 2]

theorem highCover_E_le_of_family (h2 : (2 : K) = 0) (Φ : SpecialLinearGroup (Fin 6) K →* G)
    (hΦ : Φ.ker ≤ center (SpecialLinearGroup (Fin 6) K))
    (hEperf : ⁅(highCover h2 Φ hΦ).E, (highCover h2 Φ hΦ).E⁆ = (highCover h2 Φ hΦ).E)
    (s : ∀ J : {J : Finset (Fin (Tag.rank .E6)) // J.card ≤ 2}, memModel K J.1 →* G)
    (hhigh : ∀ J : {J : Finset (Fin (Tag.rank .E6)) // J.card ≤ 2},
      (1 : Fin (Tag.rank .E6)) ∉ J.1 → (highCover h2 Φ hΦ).IsSection (s J))
    {G₀ : Subgroup G} (hG₀ : ∀ J x, secFamily s J x ∈ G₀) (f : G₀ →* ModGL TwistTag.E6.tag K)
    (hf : ∀ J x (hx : secFamily s J x ∈ G₀), f ⟨secFamily s J x, hx⟩ = memHom K J.1 x) :
    ∃ hEX : (highCover h2 Φ hΦ).E ≤ G₀, ∀ y (hy : y ∈ (highCover h2 Φ hΦ).E),
      f ⟨y, hEX hy⟩ = (highCover h2 Φ hΦ).p ⟨y, hy⟩ := by
  set c := highCover h2 Φ hΦ with hc
  set S : Set c.E := {g | ∃ J : {J : Finset (Fin (Tag.rank .E6)) // J.card ≤ 2},
    (1 : Fin (Tag.rank .E6)) ∉ J.1 ∧ ∃ x, (g : G) = secFamily s J x} with hSdef
  have hTop : ⁅(⊤ : Subgroup c.E), (⊤ : Subgroup c.E)⁆ = ⊤ :=
    (Subgroup.isPerfect_iff.2 hEperf).commutator_eq_top
  have key : ∀ j : Fin (Tag.rank .E6), j ≠ 1 → ∀ x : adjointGroup .E6 K,
      x ∈ CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {j} →
        MulAut.conj (triW K) ((x : adjointGroup .E6 K) : ModGL .E6 K) ∈ (closure S).map c.p := by
    intro j hj x hx
    have h1 : (1 : Fin (Tag.rank .E6)) ∉ ({j} : Finset (Fin (Tag.rank .E6))) := by
      rw [Finset.mem_singleton]
      exact fun h => hj h.symm
    have hJ : ({j} : Finset (Fin (Tag.rank .E6))).card ≤ 2 := by
      rw [Finset.card_singleton]
      norm_num
    exact ⟨⟨secFamily s ⟨{j}, hJ⟩ ⟨x, hx⟩, (hhigh ⟨{j}, hJ⟩ h1).mem _⟩,
      subset_closure ⟨⟨{j}, hJ⟩, h1, ⟨x, hx⟩, rfl⟩,
      (hhigh ⟨{j}, hJ⟩ h1).p_apply (memIncl {j} ⟨x, hx⟩)⟩
  have hgen : subsystemGroup TwistTag.E6.tag K setA ≤
      ((closure S).map c.p).comap (MulAut.conj (triW K)).toMonoidHom := by
    refine (closure_le _).2 ?_
    rintro _ ⟨i, hi, a, rfl | rfl⟩
    · rw [SetLike.mem_coe, mem_comap, MulEquiv.coe_toMonoidHom]
      have h := key i hi (xElement i a) (E6Pilot.xElement_mem_levi_adjDatumE6 (k := K) i a)
      rwa [show ((xElement i a : adjointGroup .E6 K) : ModGL .E6 K) = xUnit .E6 K i a from rfl]
        at h
    · rw [SetLike.mem_coe, mem_comap, MulEquiv.coe_toMonoidHom]
      have h := key i hi (yElement i a) (E6Pilot.yElement_mem_levi_adjDatumE6 (k := K) i a)
      rwa [show ((yElement i a : adjointGroup .E6 K) : ModGL .E6 K) = yUnit .E6 K i a from rfl]
        at h
  have hS : closure S = ⊤ := by
    refine E6Pilot.eq_top_of_forall_exists_map_eq_of_perfect hTop c.ker_le fun g => ?_
    have hgL : c.p g ∈ subsystemGroup TwistTag.E6.tag K setA :=
      highCover_image_le h2 Φ hΦ ⊤ (c.mem_image (mem_top (g : G)) g.2)
    have hz : (triW K)⁻¹ * c.p g * triW K ∈ subsystemGroup TwistTag.E6.tag K setA :=
      mul_mem (mul_mem (inv_mem triW_mem_subsystemGroup) hgL) triW_mem_subsystemGroup
    obtain ⟨g', hg', hpg'⟩ := hgen hz
    refine ⟨g', hg', ?_⟩
    rw [hpg', MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hEX : c.E ≤ G₀ := by
    have hle : closure S ≤ G₀.subgroupOf c.E := by
      rw [closure_le]
      rintro g ⟨J, -, x, hx⟩
      rw [SetLike.mem_coe, mem_subgroupOf, hx]
      exact hG₀ J x
    intro y hy
    have hmem : (⟨y, hy⟩ : c.E) ∈ closure S := hS ▸ mem_top _
    exact mem_subgroupOf.1 (hle hmem)
  refine ⟨hEX, ?_⟩
  have heq : c.p = f.comp (Subgroup.inclusion hEX) := by
    refine MonoidHom.eq_of_eqOn_dense hS ?_
    rintro g ⟨J, h1, x, hx⟩
    have hg : g = ⟨secFamily s J x, (hhigh J h1).mem _⟩ := Subtype.ext hx
    subst hg
    rw [MonoidHom.comp_apply,
      show Subgroup.inclusion hEX ⟨secFamily s J x, (hhigh J h1).mem _⟩ =
        ⟨secFamily s J x, hG₀ J x⟩ from rfl, hf J x (hG₀ J x)]
    exact (hhigh J h1).p_apply _
  intro y hy
  exact (DFunLike.congr_fun heq ⟨y, hy⟩).symm

end High

section Main


theorem twistedE6TwoFieldFamilyInput_holds : TwistedE6TwoFieldFamilyInput := by
  intro G _ _ L k K _ _ _ hset hk hK σ hσ e t htC ht A hAJ hA hcyc hX
  have : Finite K := finite_of_card hK
  have : CharP K 2 := charP_two_of_card le_rfl hK
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  set h2 : (2 : K) = 0 := E6GraphLevi.two_eq_zero_of_card_sq le_rfl hK with hh2
  have hk2 : Nat.card k = 2 := by rw [hk]; rfl
  have hA3 : Nat.card A = 3 := by rw [hA]; rfl
  have hK4 : 4 ≤ Nat.card K := by rw [hK]; norm_num
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk2]; norm_num)
  have hσσ : ∀ c, σ (σ c) = c := fun c => by
    rw [hσ, hσ]
    exact CFSG.LieType.Simplicity.pow_pow_card_sq hK c
  have hι : ∀ c, σ (algebraMap k K c) = algebraMap k K c :=
    E6GraphLevi.fixed_algebraMap (sigma_eq_pow_card (f := 1) (by rw [hk2]; rfl) hσ)
  have hm2 := triN2_facts (algebraMap k K) hAJ σ
  have hm3 := triN3_facts (algebraMap k K) hAJ σ
  have hm23 := triN23_facts (algebraMap k K) hAJ σ
  obtain ⟨c₂, c₃, hc₂, hc₃, a₁₂, a₁₃, a₂₃⟩ :=
    exists_aligned_covers hk2 hK hσ e hAJ hA3 h2 hX hσσ
  have hperf : ∀ J : {J : Finset (Fin (Tag.rank .E6)) // J.card ≤ 2},
      ⁅memModel K J.1, memModel K J.1⁆ = memModel K J.1 := fun J => memModel_perfect hK4 J.2
  have hsec : ∀ J : {J : Finset (Fin (Tag.rank .E6)) // J.card ≤ 2}, ∃ s : memModel K J.1 →* G,
      (nbFam (highCover h2 hX.Φ hX.ker_le) c₂ c₃ (amalgamPlacement J.1)).IsSection s := by
    intro J
    have hJN := E6Pilot.subset_nodes_amalgamPlacement J.2
    generalize amalgamPlacement J.1 = N at hJN ⊢
    cases N with
    | high => exact exists_isSection_highCover h2 hX.Φ hX.ker_le hJN J.2
    | six =>
      have h := exists_isSection_nbCover e h2 hX.Φ hX.ker_le hσσ (triN2 σ) .six
        (triN2_conj_pinnedX_matRoot σ) hJN J.2
      change ∃ s : memModel K J.1 →* G, c₂.IsSection s
      rcases hc₂ with hc | hc <;> rw [hc]
      exacts [h.1, h.2]
    | three =>
      have h := exists_isSection_nbCover e h2 hX.Φ hX.ker_le hσσ (triN3 σ) .three
        (triN3_conj_pinnedX_matRoot σ) hJN J.2
      change ∃ s : memModel K J.1 →* G, c₃.IsSection s
      rcases hc₃ with hc | hc <;> rw [hc]
      exacts [h.1, h.2]
  choose s hs using hsec
  have htr : ∀ J J' : {J : Finset (Fin (Tag.rank .E6)) // J.card ≤ 2}, J.1 ⊆ J'.1 →
      ∀ u : memModel K J.1 →* G,
        (nbFam (highCover h2 hX.Φ hX.ker_le) c₂ c₃ (amalgamPlacement J.1)).IsSection u →
          (nbFam (highCover h2 hX.Φ hX.ker_le) c₂ c₃ (amalgamPlacement J'.1)).IsSection u := by
    intro J J' hJJ' u hu
    obtain ⟨e1, e2, e3⟩ := memCoords_subset_ovlSet (J := J.1)
    rcases amalgamPlacement_cases hJJ' J'.2 with heq | ⟨h1, h1', hJ⟩ | ⟨h1, h1', hJ⟩ |
      ⟨h1, h1', hJ⟩
    · rw [← heq]
      exact hu
    · rw [h1] at hu
      rw [h1']
      exact isSection_of_highCover hk2 hK hσ e h2 hX (triN2 σ) 2 hm2.1 a₁₂
        (hJ.trans (by decide)) (e1 hJ) (hperf J) hu
    · rw [h1] at hu
      rw [h1']
      exact isSection_of_highCover hk2 hK hσ e h2 hX (triN3 σ) 1 hm3.1 a₁₃
        (hJ.trans (by decide)) (e2 hJ) (hperf J) hu
    · rw [h1] at hu
      rw [h1']
      exact isSection_of_nbCover hk2 hK hσ e hAJ h2 hX hσσ (triN2 σ) (triN3 σ) .six
        (triN2_conj_pinnedX_matRoot σ) 2 hm23.1 hc₂ a₂₃ (hJ.trans (by decide)) (e3 hJ)
        (hperf J) hu
  set φ := secFamily s with hφdef
  have hφ : IsCompatible (adjDatumE6 K).leviAmalgam φ := isCompatible_secFamily hperf hs htr
  have hnt : ∃ J, ∃ x, φ J x ≠ 1 := by
    obtain ⟨u, hu, hu1⟩ := E6Pilot.exists_ne_one_mem_levi_adjDatumE6 (k := K) 0
    have hJ0 : ({0} : Finset (Fin (Tag.rank .E6))).card ≤ 2 := by
      rw [Finset.card_singleton]
      norm_num
    refine ⟨⟨{0}, hJ0⟩, ⟨u, hu⟩, fun h => hu1 ?_⟩
    obtain ⟨z, hz, hpz⟩ := hs ⟨{0}, hJ0⟩ (memIncl {0} ⟨u, hu⟩)
    have hz1 : z = 1 := Subtype.ext (hz.trans h)
    rw [hz1, map_one] at hpz
    have h3 : memIncl (K := K) {0} ⟨u, hu⟩ = 1 := Subtype.ext hpz.symm
    have h4 := memIncl_injective (K := K) {0} (h3.trans (map_one _).symm)
    exact congrArg Subtype.val h4
  set G₀ : Subgroup G := ⨆ J, (φ J).range with hG₀
  have hφG₀ : ∀ J x, φ J x ∈ G₀ := fun J x => le_iSup (fun J => (φ J).range) J ⟨x, rfl⟩
  obtain ⟨f, hfker, hfrange, hfφ⟩ := exists_ctHom φ hφ hnt hG₀.symm
  have hEperf : ⁅(highCover h2 hX.Φ hX.ker_le).E, (highCover h2 hX.Φ hX.ker_le).E⁆ =
      (highCover h2 hX.Φ hX.ker_le).E := by
    rw [highCover_E, hX.range_eq]
    exact perfectCore_perfect _
  have hhigh : ∀ J : {J : Finset (Fin (Tag.rank .E6)) // J.card ≤ 2},
      (1 : Fin (Tag.rank .E6)) ∉ J.1 → (highCover h2 hX.Φ hX.ker_le).IsSection (s J) := by
    intro J h1
    have h := hs J
    rw [E6Pilot.amalgamPlacement_of_one_not_mem h1] at h
    exact h
  obtain ⟨hEX, hfp⟩ := highCover_E_le_of_family h2 hX.Φ hX.ker_le hEperf s hhigh hφG₀ f
    fun J x hx => hfφ J x hx
  have hE2 := nbCover_E_le hk2 hK hσ e hAJ hA3 h2 hX (triN2 σ)
    (hm2.1.trans (rootRankOneGroup_ovlRoot_le_su6Levi hι 2)) f hfker hfrange hEX hfp
  have hE3 := nbCover_E_le hk2 hK hσ e hAJ hA3 h2 hX (triN3 σ)
    (hm3.1.trans (rootRankOneGroup_ovlRoot_le_su6Levi hι 1)) f hfker hfrange hEX hfp
  have hc₂E : c₂.E = (nbCover e h2 hX.Φ hX.ker_le (triN2 σ)).E := by
    rcases hc₂ with hc | hc <;> rw [hc]
    exact nbCoverF_E e h2 hX.Φ hX.ker_le hσσ _
  have hc₃E : c₃.E = (nbCover e h2 hX.Φ hX.ker_le (triN3 σ)).E := by
    rcases hc₃ with hc | hc <;> rw [hc]
    exact nbCoverF_E e h2 hX.Φ hX.ker_le hσσ _
  have hG₀eq : G₀ = (highCover h2 hX.Φ hX.ker_le).E ⊔
      (nbCover e h2 hX.Φ hX.ker_le (triN2 σ)).E ⊔ (nbCover e h2 hX.Φ hX.ker_le (triN3 σ)).E := by
    apply le_antisymm
    · refine iSup_le fun J => ?_
      rintro _ ⟨x, rfl⟩
      have hmem := (hs J).mem (memIncl J.1 x)
      change s J (memIncl J.1 x) ∈ _
      generalize amalgamPlacement J.1 = N at hmem
      cases N with
      | high => exact mem_sup_left (mem_sup_left hmem)
      | six =>
        have hmem' : s J (memIncl J.1 x) ∈ c₂.E := hmem
        rw [hc₂E] at hmem'
        exact mem_sup_left (mem_sup_right hmem')
      | three =>
        have hmem' : s J (memIncl J.1 x) ∈ c₃.E := hmem
        rw [hc₃E] at hmem'
        exact mem_sup_right hmem'
    · exact sup_le (sup_le hEX hE2) hE3
  have hNX : t ∈ normalizer ((highCover h2 hX.Φ hX.ker_le).E : Set G) := by
    rw [highCover_E, hX.range_eq]
    exact F4Pilot.normalizer_le_normalizer_centralizerPerfectCore _
      (mem_normalizer_modelToG_of_mem_centralizer e htC _)
  have hN2 : t ∈ normalizer ((nbCover e h2 hX.Φ hX.ker_le (triN2 σ)).E : Set G) := by
    rw [nbCover_E_eq_centralizerPerfectCore e h2 hX]
    exact F4Pilot.normalizer_le_normalizer_centralizerPerfectCore _
      (mem_normalizer_modelToG_of_mem_centralizer e htC _)
  have hN3 : t ∈ normalizer ((nbCover e h2 hX.Φ hX.ker_le (triN3 σ)).E : Set G) := by
    rw [nbCover_E_eq_centralizerPerfectCore e h2 hX]
    exact F4Pilot.normalizer_le_normalizer_centralizerPerfectCore _
      (mem_normalizer_modelToG_of_mem_centralizer e htC _)
  have htN : t ∈ normalizer (G₀ : Set G) := by
    rw [hG₀eq]
    exact mem_normalizer_sup_2E6 (mem_normalizer_sup_2E6 hNX hN2) hN3
  refine ⟨φ, hφ, hnt, ?_, htN⟩
  rw [← hX.range_eq]
  exact hEX


theorem twistedE6TwoFieldRowInput_of_rigidity (hR : TwistedE6TwoDiagonalRigidity) :
    TwistedE6TwoFieldRowInput :=
  twistedE6TwoFieldRowInput_of_family hR twistedE6TwoFieldFamilyInput_holds

end Main

end CFSG.SeitzReduction.TwistedE6Pilot
