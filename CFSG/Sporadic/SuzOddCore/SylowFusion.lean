module

public import CFSG.Sporadic.SuzOddCore.SylowCheck
public import CFSG.Sporadic.SuzOddCore.FourCentralizers
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourEnumSpec

public noncomputable section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.PSL3Four.Native
  CFSG.ComponentClassification.PSL3Four
open scoped Pointwise

theorem orderOf_conj' {G : Type*} [Group G] (c x : G) : orderOf (c * x * c⁻¹) = orderOf x := by
  rw [← MulAut.conj_apply]
  exact orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective x

theorem exists_conj_mem_sylow {G : Type*} [Group G] [Finite G] {T S : Subgroup G}
    (P : Sylow 2 T) (hP : (P : Subgroup T) = S.subgroupOf T) {g : G} (hg : g ∈ T)
    (h2 : orderOf g = 2) : ∃ c ∈ T, c * g * c⁻¹ ∈ S := by
  let g' : T := ⟨g, hg⟩
  have hcard : Nat.card (Subgroup.zpowers g') = 2 ^ 1 := by
    rw [Nat.card_zpowers, ← Subgroup.orderOf_coe, pow_one]
    exact h2
  obtain ⟨Q, hQ⟩ := (IsPGroup.of_card hcard).exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq T Q P
  refine ⟨c, c.2, ?_⟩
  have hmem : g' ∈ (Q : Subgroup T) := hQ (Subgroup.mem_zpowers g')
  have h1 : MulAut.conj c • g' ∈ MulAut.conj c • (Q : Subgroup T) :=
    Subgroup.smul_mem_pointwise_smul _ _ _ hmem
  rw [← Sylow.coe_subgroup_smul, hc, hP, Subgroup.mem_subgroupOf, MulAut.smul_def,
    MulAut.conj_apply] at h1
  simpa [g'] using h1

theorem conj_fixed_card (c t : Equiv.Perm (Fin 1782)) :
    (Finset.univ.filter fun x : Fin 1782 => (c * t * c⁻¹) x = x).card =
      (Finset.univ.filter fun x : Fin 1782 => t x = x).card := by
  refine Finset.card_bij (fun x _ => c⁻¹ x) (fun x hx => ?_)
    (fun x _ y _ h => (c⁻¹).injective h) (fun y hy => ⟨c y, ?_, perm_inv_apply_self c y⟩)
  · rw [Finset.mem_filter] at hx ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    have h := congrArg (⇑c⁻¹) hx.2
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, perm_inv_apply_self] at h
    exact h
  · rw [Finset.mem_filter] at hy ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, perm_inv_apply_self, hy.2]

theorem fusionEnums_get {r : ℕ} (hr : r < 21) : fusionEnums[r]! = fusionEnum r := by
  rw [fusionEnums, getElem!_pos _ r (by simpa using hr), Array.getElem_ofFn]

theorem sylowAll_facts :
    (∀ k < 11, permOK 1782 invSylowArrs[k]! = true ∧ inT invSylowArrs[k]! = true) ∧
    enumOK 1782 invSylowArrs sylowEnum = true ∧ sylowEnum.tabs.size = 16384 ∧
    (sylowEnum.tabs.toList.filter isInvTab).length = 911 ∧
    (∀ r < 21, fusionRecOK r (fusionEnum r) sylowEnum (indexOf sylowEnum.tabs) = true) ∧
    (∀ r < 21, ∀ r' < 21, r ≠ r' → notInOK (fusionEnum r).tabs (invFusionRepArr r') = true) ∧
    coverOK 1782 sylowEnum.tabs (fusionEnums.map Enum.tabs) = true ∧
    (∀ i < 4, (caseTabs fusionEnums i).Nodup ∧
      (caseTabs fusionEnums i).length = caseCounts.getD i 0) := by
  have h := sylowAll_check
  simp only [sylowChecks, Bool.and_eq_true, beq_iff_eq, allBelow_eq_true, decide_eq_true_eq,
    and_assoc] at h
  obtain ⟨h1, h2, h3, h4, -, h6, h7, h8, h9⟩ := h
  refine ⟨h1, h2, h3, h4, fun r hr => ?_, fun r hr r' hr' hne => ?_, h8, h9⟩
  · rw [← fusionEnums_get hr]
    exact h6 r hr
  · have := h7 r hr r' hr'
    rw [Bool.or_eq_true, beq_iff_eq] at this
    rw [← fusionEnums_get hr]
    exact this.resolve_left hne

theorem fusion_facts {r : ℕ} (hr : r < 21) :
    orbitOK 1782 invSylowArrs sylowInvs (invFusionRepArr r) (fusionEnum r) = true ∧
    (fusionEnum r).tabs.size = invFusionSizes.getD r 0 ∧
    permOK 1782 (invFusionRepArr r) = true ∧ isInvTab (invFusionRepArr r) = true ∧
    found (indexOf sylowEnum.tabs) sylowEnum.tabs (invFusionRepArr r) = true ∧
    permOK 1782 (invFusionConjArr r) = true ∧ (invCand 1782 (invFusionConjArr r)).size = 1782 ∧
    inT (invFusionConjArr r) = true ∧ fusionCase r < 4 ∧ (tArr (fusionCase r)).size = 1782 ∧
    conjTab 1782 (invFusionConjArr r) (invCand 1782 (invFusionConjArr r))
      (tArr (fusionCase r)) = invFusionRepArr r := by
  have h := sylowAll_facts.2.2.2.2.1 r hr
  simp only [fusionRecOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at h
  exact h

theorem invSylowArrs_size : invSylowArrs.size = 11 := by simp [invSylowArrs]

theorem tabRep_of_permOK {t : Array ℕ} (h : permOK 1782 t = true) :
    TabRep t (permC 1782 t) := by
  simp only [permOK, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1, (rep_permC h.2).1⟩

theorem tabRep_invCand {t : Array ℕ} (h : permOK 1782 t = true)
    (hs : (invCand 1782 t).size = 1782) : TabRep (invCand 1782 t) (permC 1782 t)⁻¹ := by
  simp only [permOK, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨hs, (rep_permC h.2).2⟩

theorem mem_suzT_of_inT
    {t : Array ℕ} {g : Equiv.Perm (Fin 1782)} (ht : Rep 1782 t g)
    (h : inT t = true) : g ∈ suzT := by
  rw [inT, Bool.or_eq_true] at h
  rw [mem_suzT_iff]
  rcases h with h | h
  · exact Or.inl ((inM_iff ht).1 h)
  · exact Or.inr ((inM_iff (rep_compA rep_v ht)).1 h)

theorem isInvTab_iff {t : Tab} {g : Equiv.Perm (Fin 1782)} (ht : TabRep t g) :
    isInvTab t = true ↔ orderOf g = 2 := by
  rw [isInvTab, Bool.and_eq_true, (ht.comp ht).beq_iff TabRep.idTab, Bool.not_eq_true',
    ← Bool.not_eq_true, ht.beq_iff TabRep.idTab, orderOf_eq_prime_iff, pow_two]

theorem suzT_conj_mem_suzM
    {c m : Equiv.Perm (Fin 1782)} (hc : c ∈ suzT) (hm : m ∈ suzM) :
    c * m * c⁻¹ ∈ suzM := by
  have := suzM_normal_T.conj_mem ⟨m, suzM_le_suzT hm⟩ (by rw [Subgroup.mem_subgroupOf]; exact hm)
    ⟨c, hc⟩
  rw [Subgroup.mem_subgroupOf] at this
  simpa using this

@[expose] def sylowGens : Set (Equiv.Perm (Fin 1782)) :=
  {g | ∃ k < 11, permC 1782 invSylowArrs[k]! = g}

theorem sylow_hA :
    ∀ a ∈ sylowGens, ∃ j < invSylowArrs.size, TabRep invSylowArrs[j]! a := by
  rintro _ ⟨k, hk, rfl⟩
  exact ⟨k, by rw [invSylowArrs_size]; exact hk, tabRep_of_permOK (sylowAll_facts.1 k hk).1⟩

theorem sylow_hgens :
    ∀ j < invSylowArrs.size, ∃ a ∈ sylowGens, TabRep invSylowArrs[j]! a := by
  intro j hj
  rw [invSylowArrs_size] at hj
  exact ⟨_, ⟨j, hj, rfl⟩, tabRep_of_permOK (sylowAll_facts.1 j hj).1⟩

theorem sylow_enumerates :
    Enumerates invSylow sylowEnum.tabs.toList :=
  enumerates_closure sylow_hA sylow_hgens sylowAll_facts.2.1

theorem card_invSylow : Nat.card invSylow = 16384 := by
  rw [sylow_enumerates.card, Array.length_toList, sylowAll_facts.2.2.1]

theorem invSylow_le_suzT :
    invSylow ≤ suzT := by
  rw [invSylow, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  have h := sylowAll_facts.1 k hk
  exact mem_suzT_of_inT (tabRep_of_permOK h.1).2 h.2

theorem suzT_card_factorization :
    (Nat.card suzT).factorization 2 = 14 := by
  rw [suzT_card, show (896690995200 : ℕ) = 2 ^ 14 * 54729675 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

@[expose] def suzSylowTwo :
    Sylow 2 suzT :=
  Sylow.ofCard (invSylow.subgroupOf suzT) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe invSylow_le_suzT).toEquiv, card_invSylow,
      suzT_card_factorization]
    norm_num)

theorem suzSylowTwo_coe :
    (suzSylowTwo : Subgroup suzT) = invSylow.subgroupOf suzT := rfl

theorem ncard_sylowInvolutions :
    {g | g ∈ invSylow ∧ orderOf g = 2}.ncard = 911 := by
  rw [← Nat.card_coe_set_eq, card_set_of_tabs (L := sylowEnum.tabs.toList.filter isInvTab) ?_ ?_
    (sylow_enumerates.nodup.filter _), sylowAll_facts.2.2.2.1]
  · intro t ht
    rw [List.mem_filter] at ht
    obtain ⟨g, hg, hrep⟩ := sylow_enumerates.sound t ht.1
    exact ⟨g, ⟨hg, (isInvTab_iff hrep).1 ht.2⟩, hrep⟩
  · rintro g ⟨hg, h2⟩
    obtain ⟨t, ht, hrep⟩ := sylow_enumerates.complete g hg
    exact ⟨t, List.mem_filter.2 ⟨ht, (isInvTab_iff hrep).2 h2⟩, hrep⟩

theorem tabRep_fusionRep
    {r : ℕ} (hr : r < 21) : TabRep (invFusionRepArr r) (invFusionRep r) :=
  tabRep_of_permOK (fusion_facts hr).2.2.1

theorem fusionRep_mem
    {r : ℕ} (hr : r < 21) : invFusionRep r ∈ invSylow := by
  obtain ⟨g, hg, hrep⟩ := sylow_enumerates.sound _ (mem_of_found (fusion_facts hr).2.2.2.2.1)
  rwa [(tabRep_fusionRep hr).perm_eq hrep]

theorem orderOf_fusionRep
    {r : ℕ} (hr : r < 21) : orderOf (invFusionRep r) = 2 :=
  (isInvTab_iff (tabRep_fusionRep hr)).1 (fusion_facts hr).2.2.2.1

theorem fusionCase_lt {r : ℕ} (hr : r < 21) : fusionCase r < 4 :=
  (fusion_facts hr).2.2.2.2.2.2.2.2.1

theorem fusionConj_mem
    {r : ℕ} (hr : r < 21) : invFusionConj r ∈ suzT :=
  mem_suzT_of_inT (tabRep_of_permOK (fusion_facts hr).2.2.2.2.2.1).2
    (fusion_facts hr).2.2.2.2.2.2.2.1

theorem fusionConj_conj
    {r : ℕ} (hr : r < 21) :
    invFusionConj r * suzInv (fusionCase r) * (invFusionConj r)⁻¹ = invFusionRep r := by
  obtain ⟨-, -, -, -, -, hc, hcs, -, hcase, hts, heq⟩ := fusion_facts hr
  have h := (tabRep_of_permOK hc).conjTab ⟨hts, rep_suzInv hcase⟩ (tabRep_invCand hc hcs)
  rw [heq] at h
  exact h.perm_eq (tabRep_fusionRep hr)

@[expose] def sClass (x : Equiv.Perm (Fin 1782)) : Set (Equiv.Perm (Fin 1782)) :=
  {y | ∃ c ∈ invSylow, c * x * c⁻¹ = y}

theorem fusion_orbit {r : ℕ} (hr : r < 21) :
    (∀ t ∈ (fusionEnum r).tabs.toList, ∃ c ∈ invSylow, TabRep t (c * invFusionRep r * c⁻¹)) ∧
      (∀ c ∈ invSylow, ∃ t ∈ (fusionEnum r).tabs.toList, TabRep t (c * invFusionRep r * c⁻¹)) ∧
      (fusionEnum r).tabs.toList.Nodup :=
  conj_orbit sylow_hA sylow_hgens (tabRep_fusionRep hr) (fusion_facts hr).1

theorem ncard_sClass {r : ℕ} (hr : r < 21) :
    (sClass (invFusionRep r)).ncard = invFusionSizes.getD r 0 := by
  obtain ⟨hs, hc, hn⟩ := fusion_orbit hr
  rw [← Nat.card_coe_set_eq, card_set_of_tabs (L := (fusionEnum r).tabs.toList) ?_ ?_ hn,
    Array.length_toList, (fusion_facts hr).2.1]
  · intro t ht
    obtain ⟨c, hc', hrep⟩ := hs t ht
    exact ⟨_, ⟨c, hc', rfl⟩, hrep⟩
  · rintro _ ⟨c, hc', rfl⟩
    exact hc c hc'

theorem fusion_not_conj
    {r r' : ℕ} (hr : r < 21) (hr' : r' < 21) (hne : r ≠ r')
    {c : Equiv.Perm (Fin 1782)} (hc : c ∈ invSylow) :
    c * invFusionRep r * c⁻¹ ≠ invFusionRep r' := by
  intro h
  obtain ⟨t, ht, hrep⟩ := (fusion_orbit hr).2.1 c hc
  rw [h] at hrep
  exact notInOK_spec (sylowAll_facts.2.2.2.2.2.1 r hr r' hr' hne) (tabRep_fusionRep hr') t ht hrep

theorem exists_fusion_of_inv
    {g : Equiv.Perm (Fin 1782)} (hg : g ∈ invSylow)
    (h2 : orderOf g = 2) : ∃ r < 21, ∃ c ∈ invSylow, g = c * invFusionRep r * c⁻¹ := by
  have hg1 : g ≠ 1 := fun h => by rw [h, orderOf_one] at h2; exact absurd h2 (by norm_num)
  have hgg : g * g = 1 := by rw [← pow_two, ← h2, pow_orderOf_eq_one]
  obtain ⟨i, hi, t, ht, hrep⟩ :=
    exists_of_coverOK sylow_enumerates sylowAll_facts.2.2.2.2.2.2.1 hg hg1 hgg
  have hsz : (fusionEnums.map Enum.tabs).size = 21 := by simp [fusionEnums]
  have hi' : i < 21 := hsz ▸ hi
  have hi'' : i < fusionEnums.size := by simpa [fusionEnums] using hi'
  have e : (fusionEnums.map Enum.tabs)[i]! = (fusionEnum i).tabs := by
    rw [getElem!_pos _ i hi, Array.getElem_map, ← getElem!_pos fusionEnums i hi'',
      fusionEnums_get hi']
  rw [e] at ht
  obtain ⟨c, hc, hrep'⟩ := (fusion_orbit hi').1 t ht
  exact ⟨i, hi', c, hc, hrep.perm_eq hrep'⟩

theorem ncard_sylowClasses :
    {C : ConjClasses invSylow | ∃ x : invSylow, ConjClasses.mk x = C ∧ orderOf x = 2}.ncard =
      21 := by
  let f : Fin 21 → ConjClasses invSylow := fun r =>
    ConjClasses.mk ⟨invFusionRep r, fusionRep_mem r.2⟩
  have hf : Function.Injective f := by
    intro r r' h
    rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_iff] at h
    obtain ⟨c, hc⟩ := h
    by_contra hne
    apply fusion_not_conj r.2 r'.2 (fun e => hne (Fin.ext e)) c.2
    have := congrArg Subtype.val hc
    simpa using this
  have hrange : {C : ConjClasses invSylow | ∃ x : invSylow, ConjClasses.mk x = C ∧
      orderOf x = 2} = Set.range f := by
    ext C
    constructor
    · rintro ⟨x, rfl, hx⟩
      rw [← Subgroup.orderOf_coe] at hx
      obtain ⟨r, hr, c, hc, hxe⟩ := exists_fusion_of_inv x.2 hx
      refine ⟨⟨r, hr⟩, ?_⟩
      rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
      refine ⟨⟨c, hc⟩, Subtype.ext ?_⟩
      simp [hxe]
    · rintro ⟨r, rfl⟩
      exact ⟨_, rfl, by rw [← Subgroup.orderOf_coe]; exact orderOf_fusionRep r.2⟩
  rw [hrange, Set.ncard_range_of_injective hf, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem invFixedCounts_inj : ∀ i < 4, ∀ j < 4,
    invFixedCounts.getD i 0 = invFixedCounts.getD j 0 → i = j := by decide

theorem suzInv_conj_unique
    {i j : ℕ} (hi : i < 4) (hj : j < 4) {c : Equiv.Perm (Fin 1782)}
    (h : c * suzInv i * c⁻¹ = suzInv j) : i = j := by
  apply invFixedCounts_inj i hi j hj
  rw [← suzInv_fixed hi, ← suzInv_fixed hj, ← h, conj_fixed_card]

theorem suzInv_conj_of_fusion
    {r : ℕ} (hr : r < 21) {c d g : Equiv.Perm (Fin 1782)} {i : ℕ}
    (hgr : g = c * invFusionRep r * c⁻¹) (hdg : d * suzInv i * d⁻¹ = g) :
    ((invFusionConj r)⁻¹ * c⁻¹ * d) * suzInv i * ((invFusionConj r)⁻¹ * c⁻¹ * d)⁻¹ =
      suzInv (fusionCase r) := by
  have h1 := fusionConj_conj hr
  calc ((invFusionConj r)⁻¹ * c⁻¹ * d) * suzInv i * ((invFusionConj r)⁻¹ * c⁻¹ * d)⁻¹
      = (invFusionConj r)⁻¹ * c⁻¹ * (d * suzInv i * d⁻¹) * c * invFusionConj r := by group
    _ = (invFusionConj r)⁻¹ * c⁻¹ * (c * invFusionRep r * c⁻¹) * c * invFusionConj r := by
      rw [hdg, hgr]
    _ = (invFusionConj r)⁻¹ * invFusionRep r * invFusionConj r := by group
    _ = suzInv (fusionCase r) := by rw [← h1]; group

theorem mem_caseTabs {i : ℕ} {t : Tab} :
    t ∈ caseTabs fusionEnums i ↔ ∃ r < 21, fusionCase r = i ∧ t ∈ (fusionEnum r).tabs.toList := by
  simp only [caseTabs, List.mem_flatMap, List.mem_filter, List.mem_range, beq_iff_eq]
  constructor
  · rintro ⟨r, ⟨hr, hc⟩, ht⟩
    exact ⟨r, hr, hc, by rwa [fusionEnums_get hr] at ht⟩
  · rintro ⟨r, hr, hc, ht⟩
    exact ⟨r, ⟨hr, hc⟩, by rwa [fusionEnums_get hr]⟩

theorem ncard_case
    {i : ℕ} (hi : i < 4) :
    {g | g ∈ invSylow ∧ orderOf g = 2 ∧ ∃ c ∈ suzT, c * suzInv i * c⁻¹ = g}.ncard =
      caseCounts.getD i 0 := by
  obtain ⟨hnd, hlen⟩ := sylowAll_facts.2.2.2.2.2.2.2 i hi
  rw [← Nat.card_coe_set_eq, card_set_of_tabs (L := caseTabs fusionEnums i) ?_ ?_ hnd, hlen]
  · intro t ht
    obtain ⟨r, hr, hcase, ht⟩ := mem_caseTabs.1 ht
    obtain ⟨c, hc, hrep⟩ := (fusion_orbit hr).1 t ht
    refine ⟨_, ⟨invSylow.mul_mem (invSylow.mul_mem hc (fusionRep_mem hr)) (invSylow.inv_mem hc),
      by rw [orderOf_conj']; exact orderOf_fusionRep hr, c * invFusionConj r,
      suzT.mul_mem (invSylow_le_suzT hc) (fusionConj_mem hr), ?_⟩, hrep⟩
    rw [← hcase, ← fusionConj_conj hr]
    group
  · rintro g ⟨hg, h2, d, -, hdg⟩
    obtain ⟨r, hr, c, hc, hgr⟩ := exists_fusion_of_inv hg h2
    obtain ⟨t, ht, hrep⟩ := (fusion_orbit hr).2.1 c hc
    refine ⟨t, mem_caseTabs.2 ⟨r, hr, ?_, ht⟩, hgr ▸ hrep⟩
    exact (suzInv_conj_unique hi (fusionCase_lt hr) (suzInv_conj_of_fusion hr hgr hdg)).symm

theorem suzT_involution_class
    {g : Equiv.Perm (Fin 1782)} (hg : g ∈ suzT) (h2 : orderOf g = 2) :
    ∃! i, i < 4 ∧ ∃ c ∈ suzT, c * suzInv i * c⁻¹ = g := by
  obtain ⟨c, hcT, hcS⟩ := exists_conj_mem_sylow suzSylowTwo suzSylowTwo_coe hg h2
  obtain ⟨r, hr, d, hd, hdr⟩ := exists_fusion_of_inv hcS (by rw [orderOf_conj']; exact h2)
  refine ⟨fusionCase r, ⟨fusionCase_lt hr, c⁻¹ * d * invFusionConj r,
    suzT.mul_mem (suzT.mul_mem (suzT.inv_mem hcT) (invSylow_le_suzT hd)) (fusionConj_mem hr),
    ?_⟩, ?_⟩
  · have e : g = c⁻¹ * (c * g * c⁻¹) * c := by group
    rw [e, hdr, ← fusionConj_conj hr]
    group
  · rintro j ⟨hj, e, -, he⟩
    have hgr : g = (c⁻¹ * d) * invFusionRep r * (c⁻¹ * d)⁻¹ := by
      have e' : g = c⁻¹ * (c * g * c⁻¹) * c := by group
      rw [e', hdr]
      group
    exact suzInv_conj_unique hj (fusionCase_lt hr) (suzInv_conj_of_fusion hr hgr he)

theorem suzM_involution_class
    {g : Equiv.Perm (Fin 1782)} (hg : g ∈ suzM) (h2 : orderOf g = 2) :
    ∃ c ∈ suzT, c * suzInv 0 * c⁻¹ = g ∨ c * suzInv 1 * c⁻¹ = g := by
  obtain ⟨i, ⟨hi, c, hc, hcg⟩, -⟩ := suzT_involution_class (suzM_le_suzT hg) h2
  have hmem : suzInv i ∈ suzM := by
    have := suzT_conj_mem_suzM (suzT.inv_mem hc) hg
    rwa [← hcg, show c⁻¹ * (c * suzInv i * c⁻¹) * c⁻¹⁻¹ = suzInv i by group] at this
  obtain ⟨-, -, -, -, -, -, -, h2', h3', -⟩ := CTUC_Suz_four_exact_involution_centralizers
  refine ⟨c, hc, ?_⟩
  interval_cases i
  · exact Or.inl hcg
  · exact Or.inr hcg
  · exact absurd hmem h2'
  · exact absurd hmem h3'

theorem CTUC_Suz_Sylow_two_exhaustive_involution_fusion :
    invSylow ≤ suzT ∧ Nat.card invSylow = 16384 ∧
    (∃ P : Sylow 2 suzT, (P : Subgroup suzT) = invSylow.subgroupOf suzT) ∧
    {g | g ∈ invSylow ∧ orderOf g = 2}.ncard = 911 ∧
    {C : ConjClasses invSylow | ∃ x : invSylow, ConjClasses.mk x = C ∧ orderOf x = 2}.ncard =
      21 ∧
    (∀ r < 21, invFusionRep r ∈ invSylow ∧ orderOf (invFusionRep r) = 2 ∧
      (sClass (invFusionRep r)).ncard = invFusionSizes.getD r 0 ∧
      (∀ r' < 21, r' ≠ r → invFusionRep r' ∉ sClass (invFusionRep r)) ∧
      fusionCase r < 4 ∧ invFusionConj r ∈ suzT ∧
      invFusionConj r * suzInv (fusionCase r) * (invFusionConj r)⁻¹ = invFusionRep r) ∧
    (∀ g ∈ invSylow, orderOf g = 2 → ∃ r < 21, g ∈ sClass (invFusionRep r)) ∧
    (∀ i < 4, {g | g ∈ invSylow ∧ orderOf g = 2 ∧ ∃ c ∈ suzT, c * suzInv i * c⁻¹ = g}.ncard =
      caseCounts.getD i 0) ∧
    caseCounts = [528, 95, 192, 96] ∧
    (∀ g ∈ suzT, orderOf g = 2 → ∃! i, i < 4 ∧ ∃ c ∈ suzT, c * suzInv i * c⁻¹ = g) ∧
    (∀ g ∈ suzM, orderOf g = 2 →
      ∃ c ∈ suzT, c * suzInv 0 * c⁻¹ = g ∨ c * suzInv 1 * c⁻¹ = g) := by
  refine ⟨invSylow_le_suzT, card_invSylow, ⟨suzSylowTwo, suzSylowTwo_coe⟩,
    ncard_sylowInvolutions, ncard_sylowClasses, fun r hr => ⟨fusionRep_mem hr,
      orderOf_fusionRep hr, ncard_sClass hr, fun r' hr' hne ⟨c, hc, h⟩ =>
        fusion_not_conj hr hr' (Ne.symm hne) hc h, fusionCase_lt hr, fusionConj_mem hr,
      fusionConj_conj hr⟩, fun g hg h2 => ?_, fun i hi => ncard_case hi, rfl,
    fun g hg h2 => suzT_involution_class hg h2, fun g hg h2 => suzM_involution_class hg h2⟩
  obtain ⟨r, hr, c, hc, e⟩ := exists_fusion_of_inv hg h2
  exact ⟨r, hr, c, hc, e.symm⟩

end CFSG.Sporadic.SuzOddCore
