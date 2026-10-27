module

public import CFSG.Sporadic.HeldB.InnerClass
public import CFSG.Sporadic.SmallOddCore.HeLocalCheck
public import CFSG.Sporadic.SmallOddCore.HeLocalCheck2
public import CFSG.Sporadic.SmallOddCore.LocalTransport

public noncomputable section

namespace CFSG.Sporadic.SmallOddCore

open Subgroup CFSG CFSG.LocalCores CFSG.Blueprint CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier
open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

theorem center_map_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    (center G).map e.toMonoidHom = center H := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_center_iff]
    intro g
    have := congrArg e (mem_center_iff.1 hx (e.symm g))
    simpa using this
  · intro hy
    refine ⟨e.symm y, mem_center_iff.2 fun g => ?_, by simp⟩
    have := congrArg e.symm (mem_center_iff.1 hy (e g))
    simpa using this

theorem card_quotient_center_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    Nat.card (G ⧸ center G) = Nat.card (H ⧸ center H) :=
  Nat.card_congr (QuotientGroup.congr _ _ e (center_map_mulEquiv e)).toEquiv

theorem heInnerGrp0_eq :
    heInnerGrp0 = centralizerIn heP (heGenPerm 0) :=
  (oddCore_eq_bot_of_restrict heInnerGrp0_le heA0_mem_grp0 heA0_ne_one heDelta0_injective
    heInnerGrp0_stab heA0_fix heInnerRes0_range (v := 8) (by rw [card_heX0]; norm_num)
    oddWitness_heX0 (by rw [card_heP_cent0, card_heX0])).1

theorem heOmega0_facts :
    (∀ k < 105, heOmega0[k]! < 8330) ∧ Function.Injective (listPt 8330 heOmega0 (m := 105)) := by
  have h := he_local_basic.1
  simp only [incListOK, Bool.and_eq_true, allLt_iff, decide_eq_true_eq] at h
  exact ⟨h.1.2, listPt_injective_of_inc h.1.2 h.2⟩

@[expose] def heKPerm (j : ℕ) : Equiv.Perm (Fin 105) := permOrId 105 heKGens[j]!

theorem rep_heKPerm
    {j : ℕ} (hj : j < 9) : Rep 105 heKGens[j]! (heKPerm j) :=
  (permChk_spec (he_local_basic.2.1 j hj).1).1

theorem tabRep_heKGens :
    ∀ j < heKGens.size, TabRep heKGens[j]! (heKPerm j) := by
  intro j hj
  have hj9 : j < 9 := by simpa [heKGens] using hj
  exact ⟨(he_local_basic.2.1 j hj9).2.1, rep_heKPerm hj9⟩

theorem heInnerCP0_agree'
    {j : ℕ} (hj : j < 9) (k : Fin 105) :
    heInnerCP0 j (listPt 8330 heOmega0 k) = listPt 8330 heOmega0 (heKPerm j k) :=
  agreeOK_spec_of_lt heOmega0_facts.1 (rep_heInnerC0 hj) (rep_heKPerm hj)
    (he_local_basic.2.1 j hj).2.2 k

theorem heInnerGrp0_stab' :
    heInnerGrp0 ≤
    MulAction.stabilizer (Equiv.Perm (Fin 8330)) (Set.range (listPt 8330 heOmega0 (m := 105))) := by
  rw [heInnerGrp0, Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  exact mem_stabilizer_of_agree (heInnerCP0_agree' hj)

@[expose] def heRho0 :
    heInnerGrp0 →* Equiv.Perm (Fin 105) :=
  restrictHom heOmega0_facts.2 heInnerGrp0 heInnerGrp0_stab'

theorem heRho0_range :
    heRho0.range = genGroup 105 heKGens heKPerm := by
  have hs : heKGens.size = 9 := by simp [heKGens]
  rw [heRho0, restrictHom_range heOmega0_facts.2 heInnerGrp0_stab' rfl, genGroup, hs]
  congr 1
  apply Set.ext
  intro g
  constructor
  · rintro ⟨h, ⟨j, hj, hjh⟩, rfl⟩
    exact ⟨j, hj, (restrictHom_eq_of_agree heOmega0_facts.2 heInnerGrp0_stab' h
      (by rw [← hjh]; exact heInnerCP0_agree' hj)).symm⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨⟨heInnerCP0 j, Subgroup.subset_closure ⟨j, hj, rfl⟩⟩, ⟨j, hj, rfl⟩,
      restrictHom_eq_of_agree heOmega0_facts.2 heInnerGrp0_stab' _ (heInnerCP0_agree' hj)⟩

theorem heK_enumerates :
    Enumerates (genGroup 105 heKGens heKPerm) heKEnum.tabs.toList :=
  enumerates_closure (genGroup_hA tabRep_heKGens) (genGroup_hgens tabRep_heKGens) he_local_K.1

theorem card_heRho0_range :
    Nat.card heRho0.range = 40320 := by
  rw [heRho0_range, heK_enumerates.card, Array.length_toList, he_local_K.2]

theorem card_heInnerGrp0 :
    Nat.card heInnerGrp0 = 161280 := by
  rw [heInnerGrp0_eq, card_heP_cent0]

theorem card_heRho0_ker :
    Nat.card heRho0.ker = 4 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup heRho0.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange heRho0).toEquiv, card_heRho0_range,
    card_heInnerGrp0] at h
  omega

@[expose] def heDPerm (j : ℕ) : Equiv.Perm (Fin 105) := ((heDWords.getD j []).map heKPerm).prod

theorem tabRep_heDGens :
    ∀ j < heDGens.size, TabRep heDGens[j]! (heDPerm j) := by
  intro j hj
  have hj5 : j < 5 := by simpa [heDGens] using hj
  rw [heDGens, getElem!_pos _ j (by simpa using hj5), Array.getElem_ofFn]
  exact tabRep_wordTabS tabRep_heKGens _ fun i hi => by
    have := he_local_basic.2.2 j hj5 i hi
    simpa [heKGens] using this

theorem heD_enumerates :
    Enumerates (genGroup 105 heDGens heDPerm) heDEnum.tabs.toList :=
  enumerates_closure (genGroup_hA tabRep_heDGens) (genGroup_hgens tabRep_heDGens) he_local_D.1

theorem heDPerm_mem
    (j : ℕ) : heDPerm j ∈ genGroup 105 heKGens heKPerm := by
  refine (genGroup 105 heKGens heKPerm).list_prod_mem fun x hx => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
  by_cases hi9 : i < 9
  · exact subset_closure ⟨i, by simpa [heKGens] using hi9, rfl⟩
  · have hq : ∀ j, ∀ i ∈ heDWords.getD j [], i < 9 := by
      intro j i hi
      by_cases hj : j < 5
      · exact he_local_basic.2.2 j hj i hi
      · rw [List.getD_eq_default _ _ (by simp [heDWords]; omega)] at hi
        exact absurd hi (List.not_mem_nil)
    exact absurd (hq j i hi) hi9

theorem heD_cert :
    ClassCert 105 heDGens heDInvs heDEnum 10 heDClassWords heDClassSizes
    heDOrbits where
  enum := he_local_D.1
  words_lt := he_local_classes.2.2.2.2.1
  rep0 := he_local_classes.2.2.2.2.2
  orbit := he_local_classes.2.2.1
  notIn := he_local_classes.2.2.2.1
  cover := by
    intro k hk
    obtain ⟨l, hl, hf⟩ := cover_of_coverAllOK he_local_cover k hk
    exact ⟨l, by rw [he_local_classes.1] at hl; exact hl, hf⟩

theorem heD_facts :
    (IsSimpleGroup (genGroup 105 heDGens heDPerm) ∧
      ∃ a b : genGroup 105 heDGens heDPerm, a * b ≠ b * a) ∧
    Nat.card (genGroup 105 heDGens heDPerm) = 20160 ∧
    genGroup 105 heDGens heDPerm ≤ heRho0.range ∧
    ((genGroup 105 heDGens heDPerm).subgroupOf heRho0.range).index = 2 := by
  have hcard : Nat.card (genGroup 105 heDGens heDPerm) = 20160 := by
    rw [heD_enumerates.card, Array.length_toList, he_local_D.2.1]
  have hle : genGroup 105 heDGens heDPerm ≤ heRho0.range := by
    rw [heRho0_range, genGroup, closure_le]
    rintro _ ⟨j, -, rfl⟩
    exact heDPerm_mem j
  refine ⟨isSimpleGroup_of_classCert tabRep_heDGens heD_cert (by norm_num)
    (by rw [he_local_D.2.1]; norm_num) (by rw [he_local_D.2.1]; exact he_local_sums)
    ⟨1, by decide⟩, hcard, hle, ?_⟩
  have h := ((genGroup 105 heDGens heDPerm).subgroupOf heRho0.range).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv, hcard, card_heRho0_range] at h
  omega

theorem cti_he_first_involution_local_component_simple_quotient_order
    (B : Subgroup (centralizerIn heP (heGenPerm 0))) (hB : IsComponent B) :
    Nat.card (B ⧸ center B) = 20160 := by
  let e : centralizerIn heP (heGenPerm 0) ≃* heInnerGrp0 :=
    MulEquiv.subgroupCongr heInnerGrp0_eq.symm
  have hB' : IsComponent (B.map e.toMonoidHom) := isComponent_map_mulEquiv e hB
  rw [card_quotient_center_mulEquiv (B.equivMapOfInjective e.toMonoidHom e.injective)]
  obtain ⟨⟨hDs, hDnab⟩, hDcard, hDle, hDi⟩ := heD_facts
  have hker : Group.IsSolvable heRho0.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hp : IsPGroup 2 heRho0.ker := IsPGroup.of_card (n := 2) (by rw [card_heRho0_ker]; norm_num)
    have : Group.IsNilpotent heRho0.ker := hp.isNilpotent
    infer_instance
  let eD : (genGroup 105 heDGens heDPerm).subgroupOf heRho0.range ≃* genGroup 105 heDGens heDPerm :=
    subgroupOfEquivOfLe hDle
  have hs : IsSimpleGroup ((genGroup 105 heDGens heDPerm).subgroupOf heRho0.range) :=
    eD.isSimpleGroup
  have hnc : ∃ a b : (genGroup 105 heDGens heDPerm).subgroupOf heRho0.range, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hDnab
    refine ⟨eD.symm a, eD.symm b, fun h => hab ?_⟩
    have := congrArg eD h
    simpa using this
  rw [CFSG.Sporadic.SuzOddCore.card_quotient_center_of_component heRho0.rangeRestrict
    heRho0.rangeRestrict_surjective hker _ hDi hs hnc hB', Nat.card_congr eD.toEquiv, hDcard]

theorem heInnerGrp1_eq :
    heInnerGrp1 = centralizerIn heP heT1P :=
  (oddCore_eq_bot_of_restrict heInnerGrp1_le heT1P_mem_grp1 heT1P_ne_one heDelta1_injective
    heInnerGrp1_stab heT1P_fix heInnerRes1_range (v := 9) (by rw [card_heX1]; norm_num)
    oddWitness_heX1 (by rw [card_heP_cent1, card_heX1])).1

@[expose] def heRho1 :
    heInnerGrp1 →* Equiv.Perm (Fin 42) :=
  restrictHom heDelta1_injective heInnerGrp1 heInnerGrp1_stab

theorem tabRep_heXTabs :
    ∀ j < heXTabs.size, TabRep heXTabs[j]! (heInnerSigmaP1 j) := by
  intro j hj
  have hj9 : j < 9 := by simpa [heXTabs] using hj
  rw [heXTabs, getElem!_pos _ j (by simpa using hj9), Array.getElem_ofFn]
  exact ⟨(he2_basic.1 j hj9).2, (permChk_spec (he2_basic.1 j hj9).1).1⟩

theorem heRho1_range :
    heRho1.range = genGroup 42 heXTabs heInnerSigmaP1 := by
  have hs : heXTabs.size = 9 := by simp [heXTabs]
  rw [heRho1, heInnerRes1_range, heX1_eq, genGroup, hs]

theorem heX_enumerates :
    Enumerates (genGroup 42 heXTabs heInnerSigmaP1) heXEnum.tabs.toList :=
  enumerates_closure (genGroup_hA tabRep_heXTabs) (genGroup_hgens tabRep_heXTabs) he2_X.1

theorem card_heInnerGrp1 :
    Nat.card heInnerGrp1 = 21504 := by
  rw [heInnerGrp1_eq, card_heP_cent1]

theorem card_heRho1_ker :
    Nat.card heRho1.ker = 2 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup heRho1.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange heRho1).toEquiv, heRho1_range,
    heX_enumerates.card, Array.length_toList, he2_X.2.1, card_heInnerGrp1] at h
  omega

@[expose] def heRPerm (j : ℕ) : Equiv.Perm (Fin 42) :=
  ((heRWords.getD j []).map heInnerSigmaP1).prod

theorem tabRep_heRGens :
    ∀ j < heRGens.size, TabRep heRGens[j]! (heRPerm j) := by
  intro j hj
  have hj6 : j < 6 := by simpa [heRGens] using hj
  rw [heRGens, getElem!_pos _ j (by simpa using hj6), Array.getElem_ofFn]
  exact tabRep_wordTabS tabRep_heXTabs _ fun i hi => by
    have := he2_basic.2 j hj6 i hi
    simpa [heXTabs] using this

theorem heR_enumerates :
    Enumerates (genGroup 42 heRGens heRPerm) heREnum.tabs.toList :=
  enumerates_closure (genGroup_hA tabRep_heRGens) (genGroup_hgens tabRep_heRGens) he2_R.1

theorem heRPerm_mem
    (j : ℕ) : heRPerm j ∈ genGroup 42 heXTabs heInnerSigmaP1 := by
  refine (genGroup 42 heXTabs heInnerSigmaP1).list_prod_mem fun x hx => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
  by_cases hi9 : i < 9
  · exact subset_closure ⟨i, by simpa [heXTabs] using hi9, rfl⟩
  · have hq : ∀ j, ∀ i ∈ heRWords.getD j [], i < 9 := by
      intro j i hi
      by_cases hj : j < 6
      · exact he2_basic.2 j hj i hi
      · rw [List.getD_eq_default _ _ (by simp [heRWords]; omega)] at hi
        exact absurd hi (List.not_mem_nil)
    exact absurd (hq j i hi) hi9

theorem heC1_no_component
    (B : Subgroup heInnerGrp1) (hB : IsComponent B) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRX : genGroup 42 heRGens heRPerm ≤ genGroup 42 heXTabs heInnerSigmaP1 := by
    rw [genGroup, closure_le]
    rintro _ ⟨j, -, rfl⟩
    exact heRPerm_mem j
  have hXR : genGroup 42 heXTabs heInnerSigmaP1 ≤
      normalizer (genGroup 42 heRGens heRPerm : Set (Equiv.Perm (Fin 42))) :=
    le_normalizer_of_normalOK tabRep_heXTabs tabRep_heRGens heR_enumerates he2_R.2.2
  have hker : IsPGroup 2 heRho1.ker :=
    IsPGroup.of_card (n := 1) (by rw [card_heRho1_ker]; norm_num)
  have hRp : IsPGroup 2 (genGroup 42 heRGens heRPerm) := IsPGroup.of_card (n := 6) (by
    rw [heR_enumerates.card, Array.length_toList, he2_R.2.1]; norm_num)
  have hmemX : ∀ g : heInnerGrp1, heRho1 g ∈ genGroup 42 heXTabs heInnerSigmaP1 := fun g => by
    rw [← heRho1_range]
    exact ⟨g, rfl⟩
  have hNp : IsPGroup 2 ((genGroup 42 heRGens heRPerm).comap heRho1) :=
    hRp.comap_of_ker_isPGroup heRho1 hker
  have hNn : ((genGroup 42 heRGens heRPerm).comap heRho1).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [mem_comap, map_mul, map_mul, map_inv]
    exact (mem_normalizer_iff.mp (hXR (hmemX g)) _).1 hn
  have hNs : Group.IsSolvable ((genGroup 42 heRGens heRPerm).comap heRho1) := by
    have : Group.IsNilpotent ((genGroup 42 heRGens heRPerm).comap heRho1) := hNp.isNilpotent
    infer_instance
  have hBN := (component_solvable_centralizer hNs hNn.isSubnormal).1 B hB
  have hBle : B ≤ (genGroup 42 heXTabs heInnerSigmaP1 ⊓
      centralizer (genGroup 42 heRGens heRPerm : Set (Equiv.Perm (Fin 42)))).comap heRho1 := by
    intro b hb
    rw [mem_comap, mem_inf]
    refine ⟨hmemX b, ?_⟩
    rw [mem_centralizer_iff]
    intro r hr
    have hrX : r ∈ heRho1.range := by
      rw [heRho1_range]
      exact hRX hr
    obtain ⟨n, rfl⟩ := hrX
    have hn : n ∈ (genGroup 42 heRGens heRPerm).comap heRho1 := hr
    have hc := commutator_eq_bot_iff_le_centralizer.mp hBN hb
    rw [mem_centralizer_iff] at hc
    rw [← map_mul, ← map_mul, hc n hn]
  have hCp : IsPGroup 2 ↥(genGroup 42 heXTabs heInnerSigmaP1 ⊓
      centralizer (genGroup 42 heRGens heRPerm : Set (Equiv.Perm (Fin 42)))) :=
    IsPGroup.of_card (n := 6) (by
      rw [card_inf_centralizer_of_enum heX_enumerates tabRep_heRGens, he2_X.2.2]; norm_num)
  exact CFSG.Sporadic.SuzOddCore.not_isComponent_of_le_pgroup
    (hCp.comap_of_ker_isPGroup heRho1 hker) hBle hB

theorem cti_he_second_involution_centralizers_have_no_components
    {a : Equiv.Perm (Fin 8330)}
    (ha : a ∈ heP) (ha2 : orderOf a = 2) (hna : ¬ ∃ c ∈ heP, a = c * heGenPerm 0 * c⁻¹)
    (B : Subgroup (centralizerIn heP a)) : ¬ IsComponent B := by
  intro hB
  rcases involution_conj_cases ha ha2 with h0 | h1
  · exact hna h0
  · obtain ⟨c, hc, rfl⟩ := h1
    have hmap : (centralizerIn heP (c * heT1P * c⁻¹)).map (MulAut.conj c⁻¹).toMonoidHom =
        heInnerGrp1 := by
      rw [heInnerGrp1_eq, centralizerIn, centralizerIn, Subgroup.map_inf _ _ _
        (MulAut.conj c⁻¹).injective, map_conj_self (heP.inv_mem hc), map_conj_centralizer,
        Set.image_singleton, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        show c⁻¹ * (c * heT1P * c⁻¹) * c⁻¹⁻¹ = heT1P by group]
    let e : centralizerIn heP (c * heT1P * c⁻¹) ≃* heInnerGrp1 :=
      ((centralizerIn heP (c * heT1P * c⁻¹)).equivMapOfInjective _
        (MulAut.conj c⁻¹).injective).trans (MulEquiv.subgroupCongr hmap)
    exact heC1_no_component _ (isComponent_map_mulEquiv e hB)


theorem cti_he_involution_local_components_simple_quotient_order
    {T : Type*} [Group T]
    (hT : Nonempty (T ≃* NativeSporadic.He)) {a : T} (ha : orderOf a = 2) {B : Subgroup T}
    (hB : CFSG.Assembly.IsComponentOf B (centralizer ({a} : Set T))) :
    Nat.card (B ⧸ center B) = 20160 := by
  obtain ⟨e⟩ := hT
  set ι : T →* Equiv.Perm (Fin 8330) := heP.subtype.comp (e.trans heEquivP).toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp (e.trans heEquivP).injective
  have hrange : ι.range = heP := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (e.trans heEquivP).surjective,
      ← MonoidHom.range_eq_map, range_subtype]
  have hτP : ι a ∈ heP := hrange ▸ ⟨a, rfl⟩
  have hτ : orderOf (ι a) = 2 := by rw [orderOf_injective ι hι, ha]
  have hB1 : CFSG.Assembly.IsComponentOf (B.map ι) (centralizerIn heP (ι a)) := by
    have := (isComponentOf_map_iff hι).2 hB
    rwa [map_centralizer_eq_inf hι, hrange, Set.image_singleton] at this
  rw [card_quotient_center_mulEquiv (B.equivMapOfInjective ι hι)]
  rcases involution_conj_cases hτP hτ with h0 | h1
  · obtain ⟨c, hc, hca⟩ := h0
    have hmap : (centralizerIn heP (ι a)).map (MulAut.conj c⁻¹).toMonoidHom =
        centralizerIn heP (heGenPerm 0) := by
      rw [hca, centralizerIn, centralizerIn, Subgroup.map_inf _ _ _ (MulAut.conj c⁻¹).injective,
        map_conj_self (heP.inv_mem hc), map_conj_centralizer, Set.image_singleton,
        MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        show c⁻¹ * (c * heGenPerm 0 * c⁻¹) * c⁻¹⁻¹ = heGenPerm 0 by group]
    have hfinj : Function.Injective (MulAut.conj c⁻¹).toMonoidHom := (MulAut.conj c⁻¹).injective
    have hB2 : CFSG.Assembly.IsComponentOf ((B.map ι).map (MulAut.conj c⁻¹).toMonoidHom)
        (centralizerIn heP (heGenPerm 0)) := by
      rw [← hmap]
      exact (isComponentOf_map_iff hfinj).2 hB1
    rw [card_quotient_center_mulEquiv ((B.map ι).equivMapOfInjective _ hfinj)]
    have hB3 := (isComponentOf_iff_isComponent_subgroupOf hB2.1).1 hB2
    have h := cti_he_first_involution_local_component_simple_quotient_order _ hB3
    rw [← h]
    exact card_quotient_center_mulEquiv (subgroupOfEquivOfLe hB2.1).symm
  · exfalso
    have hB3 := (isComponentOf_iff_isComponent_subgroupOf hB1.1).1 hB1
    refine cti_he_second_involution_centralizers_have_no_components hτP hτ ?_ _ hB3
    rintro ⟨c, hc, hca⟩
    have h0 : ι a ∈ CFSG.Sporadic.Schreier.conjClass heP (heGenPerm 0) := ⟨c, hc, hca⟩
    obtain ⟨d, hd, hda⟩ := h1
    have ht1 : heT1P ∈ CFSG.Sporadic.Schreier.conjClass heP (ι a) :=
      ⟨d⁻¹, heP.inv_mem hd, by rw [hda]; group⟩
    have hsub := (conjClass_subset_of_mem ht1).trans (conjClass_subset_of_mem h0)
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [ncard_conjClass_heT1, ncard_conjClass_heA0] at hle
    norm_num at hle

end CFSG.Sporadic.SmallOddCore
