module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K49CoreDefs
public import CFSG.GroupTheory.CoprimeSectionStability
public import CFSG.Quasithin.EmptyFaithful.S1421QA16Cnt

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49

open scoped commutatorElement
open CFSG.GH74.Uniqueness.SU.SU5 (IsQ8D8)

variable {G : Type} [Group G] [Finite G]

theorem isQ8D8_card_inf_centralizer {N : Subgroup G} (h : IsQ8D8 N) :
    Nat.card ↥(N ⊓ Subgroup.centralizer (N : Set G)) = 2 := by
  obtain ⟨-, ζ, hζN, hζ1, hcen, -⟩ := h.facts
  have hset : (N ⊓ Subgroup.centralizer (N : Set G) : Set G) = {1, ζ} := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Subgroup.mem_centralizer_iff,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hxN, hx⟩
      exact (hcen x hxN).mp fun m hm => (hx m hm).symm
    · rintro (h1 | hζ)
      · rw [h1]
        exact ⟨N.one_mem, fun m _ => by simp⟩
      · rw [hζ]
        exact ⟨hζN, fun m hm => ((hcen ζ hζN).mpr (Or.inr rfl) m hm).symm⟩
  change Nat.card ↥(N ⊓ Subgroup.centralizer (N : Set G) : Set G) = 2
  rw [hset, Nat.card_coe_set_eq, Set.ncard_pair hζ1.symm]

theorem isQ8D8_not_isMulCommutative {N : Subgroup G} (h : IsQ8D8 N) :
    ¬ IsMulCommutative ↥N := by
  intro hcomm
  have hcard : Nat.card N = 32 := h.facts.1
  have hcenter : Nat.card ↥(N ⊓ Subgroup.centralizer (N : Set G)) = 2 :=
    isQ8D8_card_inf_centralizer h
  have hle : N ≤ Subgroup.centralizer (N : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    simpa using congrArg Subtype.val (hcomm.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
  have hinf : N ⊓ Subgroup.centralizer (N : Set G) = N := inf_eq_left.mpr hle
  rw [hinf, hcard] at hcenter
  exact absurd hcenter (by norm_num)

theorem isQ8D8_commutator_le_inf_centralizer {N : Subgroup G} (h : IsQ8D8 N) :
    ⁅N, N⁆ ≤ N ⊓ Subgroup.centralizer (N : Set G) := by
  obtain ⟨-, ζ, hζN, hζ1, hcen, hsq⟩ := h.facts
  set Z : Subgroup G := N ⊓ Subgroup.centralizer (N : Set G) with hZdef
  have hZmem : ∀ z : G, z ∈ Z ↔ z = 1 ∨ z = ζ := by
    intro z
    rw [hZdef, Subgroup.mem_inf]
    constructor
    · rintro ⟨hzW, hz⟩
      exact (hcen z hzW).mp fun m hm => (Subgroup.mem_centralizer_iff.mp hz m hm).symm
    · rintro (h1 | hζ)
      · rw [h1]
        exact ⟨N.one_mem, fun m _ => by simp⟩
      · rw [hζ]
        refine ⟨hζN, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro m hm
        exact ((hcen ζ hζN).mpr (Or.inr rfl) m hm).symm
  have hsqZ : ∀ n ∈ N, n * n ∈ Z := by
    intro n hn
    rcases hsq n hn with h1 | h1
    · rw [h1]; exact Z.one_mem
    · rw [h1]; exact (hZmem ζ).mpr (Or.inr rfl)
  have hcentral : ∀ z ∈ Z, ∀ n ∈ N, z * n = n * z :=
    fun z hz n hn => (Subgroup.mem_centralizer_iff.mp hz.2 n hn).symm
  refine Subgroup.commutator_le.mpr ?_
  intro a ha b hb
  have ha2 : (a * a)⁻¹ ∈ Z := Z.inv_mem (hsqZ a ha)
  have hb2 : (b * b)⁻¹ ∈ Z := Z.inv_mem (hsqZ b hb)
  have hab2 : (a * b) * (a * b) ∈ Z := hsqZ (a * b) (N.mul_mem ha hb)
  have hcalc : ⁅a, b⁆ = (a * b) * (a * b) * (a * a)⁻¹ * (b * b)⁻¹ := by
    rw [commutatorElement_def]
    calc a * b * a⁻¹ * b⁻¹
        = a * b * (a * (a * a)⁻¹) * (b * (b * b)⁻¹) := by
          rw [show a⁻¹ = a * (a * a)⁻¹ by group, show b⁻¹ = b * (b * b)⁻¹ by group]
      _ = a * b * a * (a * a)⁻¹ * b * (b * b)⁻¹ := by group
      _ = a * b * a * b * (a * a)⁻¹ * (b * b)⁻¹ := by
          have hh : a * b * a * (a * a)⁻¹ * b = a * b * a * b * (a * a)⁻¹ := by
            rw [show a * b * a * (a * a)⁻¹ * b = a * b * a * ((a * a)⁻¹ * b) by group,
              hcentral (a * a)⁻¹ ha2 b hb]
            group
          rw [hh]
      _ = (a * b) * (a * b) * (a * a)⁻¹ * (b * b)⁻¹ := by group
  rw [hcalc]
  exact Z.mul_mem (Z.mul_mem hab2 ha2) hb2

theorem pCore_alt5_eq_bot : CFSG.pCore 2 (alternatingGroup (Fin 5)) = ⊥ := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  haveI : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    Group.isPerfect_def.mpr (commutator_alternatingGroup_eq_top (α := Fin 5) (by simp))
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (CFSG.pCore 2 (alternatingGroup (Fin 5))) with h | h
  · exact h
  · exfalso
    have hP : IsPGroup 2 (alternatingGroup (Fin 5)) := by
      have hpc := CFSG.pCore_isPGroup (p := 2) (G := alternatingGroup (Fin 5))
      rw [h] at hpc
      exact hpc.of_equiv Subgroup.topEquiv
    haveI : Group.IsNilpotent (alternatingGroup (Fin 5)) := hP.isNilpotent
    exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 5)) inferInstance

theorem pCore_quotient_alt5_eq_bot {Q : Type*} [Group Q] [Finite Q]
    (hQ : Nonempty (Q ≃* alternatingGroup (Fin 5))) : CFSG.pCore 2 Q = ⊥ := by
  obtain ⟨e⟩ := hQ
  have hmap := CFSG.pCore_map_iso 2 e
  rw [pCore_alt5_eq_bot] at hmap
  exact (Subgroup.map_eq_bot_iff_of_injective (CFSG.pCore 2 Q) e.injective).mp hmap

theorem pCore_eq_of_q8d8_alt5 {K : Subgroup G} {V₀ : Subgroup ↥K} (hV₀n : V₀.Normal)
    (hV₀q8 : IsQ8D8 (⊤ : Subgroup V₀)) (hV₀alt : CFSG.Quasithin.IsAlt 5 (↥K ⧸ V₀)) :
    V₀ = CFSG.pCore 2 ↥K := by
  haveI : V₀.Normal := hV₀n
  have hcard : Nat.card V₀ = 32 := by
    have h := hV₀q8.facts.1
    rwa [Nat.card_congr Subgroup.topEquiv.toEquiv] at h
  have hV₀p : IsPGroup 2 V₀ := IsPGroup.of_card (n := 5) (by rw [hcard]; norm_num)
  refine le_antisymm ?_ ?_
  · exact CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCore 2 V₀ hV₀n hV₀p
  · rw [CFSG.pCore_eq_iSup]
    refine iSup_le fun N => iSup_le fun hNn => iSup_le fun hNp => ?_
    let π : ↥K →* (↥K ⧸ V₀) := QuotientGroup.mk' V₀
    have hNmap_le : N.map π ≤ CFSG.pCore 2 (↥K ⧸ V₀) :=
      CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCore 2 (N.map π)
        (hNn.map π (QuotientGroup.mk'_surjective V₀)) (hNp.map π)
    rw [pCore_quotient_alt5_eq_bot hV₀alt] at hNmap_le
    have hle : N ≤ π.ker := (Subgroup.map_eq_bot_iff N).mp (le_bot_iff.mp hNmap_le)
    rwa [QuotientGroup.ker_mk'] at hle

private theorem kmodel_zeta_mem_inf_centralizer_iff {W : Subgroup G} {ζ : G} (hζW : ζ ∈ W)
    (hcen : ∀ n ∈ W, (∀ m ∈ W, n * m = m * n) ↔ (n = 1 ∨ n = ζ)) :
    ∀ z : G, z ∈ W ⊓ Subgroup.centralizer (W : Set G) ↔ z = 1 ∨ z = ζ := by
  intro z
  rw [Subgroup.mem_inf]
  constructor
  · rintro ⟨hzW, hz⟩
    exact (hcen z hzW).mp fun m hm => (Subgroup.mem_centralizer_iff.mp hz m hm).symm
  · rintro (h1 | hζ)
    · rw [h1]
      exact ⟨W.one_mem, fun m _ => by simp⟩
    · rw [hζ]
      refine ⟨hζW, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      exact ((hcen ζ hζW).mpr (Or.inr rfl) m hm).symm

private theorem kmodel_conj_mem_inf_centralizer_of_normalizer {K W : Subgroup G}
    (hWn : K ≤ Subgroup.normalizer (W : Set G)) :
    ∀ k ∈ K, ∀ z ∈ W ⊓ Subgroup.centralizer (W : Set G),
      k * z * k⁻¹ ∈ W ⊓ Subgroup.centralizer (W : Set G) := by
  intro k hk z hz
  obtain ⟨hzW, hzC⟩ := Subgroup.mem_inf.mp hz
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp (hWn hk) z).mp hzW
  · rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hw' : k⁻¹ * w * k ∈ W := by
      have hh := (Subgroup.mem_normalizer_iff.mp (hWn (K.inv_mem hk)) w).mp hw
      simpa using hh
    have hzc := Subgroup.mem_centralizer_iff.mp hzC (k⁻¹ * w * k) hw'
    have hzc' : z * (k⁻¹ * w * k) = (k⁻¹ * w * k) * z := hzc.symm
    exact (show k * z * k⁻¹ * w = w * (k * z * k⁻¹) by
      calc k * z * k⁻¹ * w = k * z * (k⁻¹ * w * k) * k⁻¹ := by group
        _ = k * (z * (k⁻¹ * w * k)) * k⁻¹ := by group
        _ = k * ((k⁻¹ * w * k) * z) * k⁻¹ := by rw [hzc']
        _ = w * (k * z * k⁻¹) := by group).symm

theorem commutator_eq_bot_of_isQ8D8_normal {K W : Subgroup G}
    (hWn : K ≤ Subgroup.normalizer (W : Set G)) (hWq8 : IsQ8D8 W) :
    ⁅K, W ⊓ Subgroup.centralizer (W : Set G)⁆ = ⊥ := by
  obtain ⟨-, ζ, hζW, hζ1, hcen, -⟩ := hWq8.facts
  have hZmem := kmodel_zeta_mem_inf_centralizer_iff hζW hcen
  have hconj := kmodel_conj_mem_inf_centralizer_of_normalizer hWn
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hcases := (hZmem (k * z * k⁻¹)).mp (hconj k hk z hz)
  rcases (hZmem z).mp hz with hz1 | hzζ
  · simp [hz1]
  · have hfix : k * z * k⁻¹ = z := by
      rcases hcases with hk1 | hkζ
      · exfalso
        have hζeq : ζ = 1 := by
          have h : k * ζ * k⁻¹ = 1 := by rw [← hzζ]; exact hk1
          have h2 : k⁻¹ * (k * ζ * k⁻¹) * k = k⁻¹ * (1 : G) * k :=
            congrArg (fun t => k⁻¹ * t * k) h
          calc ζ = k⁻¹ * (k * ζ * k⁻¹) * k := by group
            _ = k⁻¹ * (1 : G) * k := h2
            _ = 1 := by group
        exact hζ1 hζeq
      · rw [hkζ, ← hzζ]
    calc z * k = (k * z * k⁻¹) * k := by rw [hfix]
      _ = k * z := by group

private def kmodel_fixingSubgroup (K W Z : Subgroup G)
    (hZcentK : K ≤ Subgroup.centralizer (Z : Set G)) : Subgroup ↥K :=
  { carrier := {x | ∀ w ∈ W, ⁅w, (x : G)⁆ ∈ Z}
    mul_mem' := by
      intro x y hx hy w hw
      change ⁅w, (x : G) * (y : G)⁆ ∈ Z
      rw [commutatorElement_mul_right_eq_mul_conj]
      have h1 : ⁅w, (x : G)⁆ ∈ Z := hx w hw
      have h2 : ⁅w, (y : G)⁆ ∈ Z := hy w hw
      have h3 : (x : G) * ⁅w, (y : G)⁆ * (x : G)⁻¹ = ⁅w, (y : G)⁆ := by
        have hc := Subgroup.mem_centralizer_iff.mp (hZcentK x.2) ⁅w, (y : G)⁆ h2
        rw [← hc]; group
      rw [show ⁅w, (x : G)⁆ * (x : G) * ⁅w, (y : G)⁆ * (x : G)⁻¹
          = ⁅w, (x : G)⁆ * ((x : G) * ⁅w, (y : G)⁆ * (x : G)⁻¹) by group, h3]
      exact Z.mul_mem h1 h2
    one_mem' := by
      intro w hw
      change ⁅w, (1 : G)⁆ ∈ Z
      rw [commutatorElement_one_right]
      exact Z.one_mem
    inv_mem' := by
      intro x hx w hw
      change ⁅w, (x : G)⁻¹⁆ ∈ Z
      rw [commutatorElement_inv_right]
      have h1 : ⁅(x : G), w⁆ ∈ Z := by
        rw [← commutatorElement_inv]
        exact Z.inv_mem (hx w hw)
      have h2 : (x : G)⁻¹ * ⁅(x : G), w⁆ * (x : G) = ⁅(x : G), w⁆ := by
        have hc := Subgroup.mem_centralizer_iff.mp (hZcentK (K.inv_mem x.2)) ⁅(x : G), w⁆ h1
        rw [← hc]; group
      rw [h2]
      exact h1 }

private theorem kmodel_subgroupOf_le_fixingSubgroup {K W Z : Subgroup G}
    (hZcentK : K ≤ Subgroup.centralizer (Z : Set G)) (hWW : ⁅W, W⁆ ≤ Z) :
    W.subgroupOf K ≤ kmodel_fixingSubgroup K W Z hZcentK := by
  intro x hx w hw
  exact hWW (Subgroup.commutator_mem_commutator hw hx)

private theorem kmodel_fixingSubgroup_normal {K W Z : Subgroup G}
    (hWn : K ≤ Subgroup.normalizer (W : Set G))
    (hZcentK : K ≤ Subgroup.centralizer (Z : Set G)) :
    (kmodel_fixingSubgroup K W Z hZcentK).Normal := by
  refine ⟨fun x hx g w hw => ?_⟩
  have hgw : (g : G)⁻¹ * w * g ∈ W := by
    have hh := (Subgroup.mem_normalizer_iff.mp (hWn (K.inv_mem g.2)) w).mp hw
    simpa using hh
  have h1 : ⁅(g : G)⁻¹ * w * g, (x : G)⁆ ∈ Z := hx _ hgw
  have h2 : (g : G) * ⁅(g : G)⁻¹ * w * g, (x : G)⁆ * (g : G)⁻¹ ∈ Z := by
    have hc := Subgroup.mem_centralizer_iff.mp (hZcentK g.2) ⁅(g : G)⁻¹ * w * g, (x : G)⁆ h1
    rw [← hc]
    simpa [mul_assoc] using h1
  rwa [show (g : G) * ⁅(g : G)⁻¹ * w * g, (x : G)⁆ * (g : G)⁻¹ =
      ⁅w, (g : G) * (x : G) * (g : G)⁻¹⁆ by
    simp only [commutatorElement_def]; group] at h2

private theorem kmodel_fixingSubgroup_eq_top_contradiction {K W Z : Subgroup G}
    (hperf : ⁅K, K⁆ = K) (hWle : W ≤ K) (hWq8 : IsQ8D8 W)
    (hKZ : ⁅K, Z⁆ = ⊥) (hZcentK : K ≤ Subgroup.centralizer (Z : Set G))
    (hS_eq : kmodel_fixingSubgroup K W Z hZcentK = ⊤) : False := by
  have hWKZ : ⁅W, K⁆ ≤ Z := by
    rw [Subgroup.commutator_le]
    intro w hw x hx
    exact (show (⟨x, hx⟩ : ↥K) ∈ kmodel_fixingSubgroup K W Z hZcentK from by
      rw [hS_eq]; exact Subgroup.mem_top _) w hw
  have hWKbot : ⁅W, K⁆ = ⊥ :=
    CFSG.GroupTheory.CoprimeSection.commutator_eq_bot_of_two_step hperf hWKZ
      (by rw [Subgroup.commutator_comm]; exact hKZ)
  refine isQ8D8_not_isMulCommutative hWq8 ?_
  rw [← Subgroup.le_centralizer_iff_isMulCommutative]
  intro w hw
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (Subgroup.mem_centralizer_iff.mp
    ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hWKbot) hw) y (hWle hy))

theorem section_centralizer_le_of_perfect {K W : Subgroup G} (hperf : ⁅K, K⁆ = K)
    (hWle : W ≤ K) (hWn : K ≤ Subgroup.normalizer (W : Set G)) (hWq8 : IsQ8D8 W)
    [(W.subgroupOf K).Normal] (hsimple : IsSimpleGroup (↥K ⧸ W.subgroupOf K)) :
    ∀ k ∈ K, (∀ w ∈ W, ⁅w, k⁆ ∈ W ⊓ Subgroup.centralizer (W : Set G)) → k ∈ W := by
  intro k hk hkZ
  by_contra hkW
  set Z : Subgroup G := W ⊓ Subgroup.centralizer (W : Set G) with hZdef
  have hKZ : ⁅K, Z⁆ = ⊥ := commutator_eq_bot_of_isQ8D8_normal hWn hWq8
  have hZcentK : K ≤ Subgroup.centralizer (Z : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hKZ
  have hWW : ⁅W, W⁆ ≤ Z := by
    rw [hZdef]; exact isQ8D8_commutator_le_inf_centralizer hWq8
  let S : Subgroup ↥K := kmodel_fixingSubgroup K W Z hZcentK
  have hV₀S : W.subgroupOf K ≤ S := kmodel_subgroupOf_le_fixingSubgroup hZcentK hWW
  have hkS : (⟨k, hk⟩ : ↥K) ∈ S := hkZ
  have hSnormal : S.Normal := kmodel_fixingSubgroup_normal hWn hZcentK
  have hSmap : (S.map (QuotientGroup.mk' (W.subgroupOf K))).Normal :=
    hSnormal.map _ (QuotientGroup.mk'_surjective _)
  haveI := hsimple
  haveI := hSmap
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (S.map (QuotientGroup.mk' (W.subgroupOf K))) with h | h
  · exfalso
    have hkimg : (QuotientGroup.mk' (W.subgroupOf K)) ⟨k, hk⟩ ∈
        S.map (QuotientGroup.mk' (W.subgroupOf K)) := Subgroup.mem_map_of_mem _ hkS
    rw [h] at hkimg
    have hqk : (QuotientGroup.mk' (W.subgroupOf K)) ⟨k, hk⟩ ≠ 1 := by
      intro h1
      exact hkW ((QuotientGroup.eq_one_iff (⟨k, hk⟩ : ↥K)).mp h1)
    exact hqk (Subgroup.mem_bot.mp hkimg)
  · have hS_eq : S = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hximg : (QuotientGroup.mk' (W.subgroupOf K)) x ∈
          S.map (QuotientGroup.mk' (W.subgroupOf K)) := by
        rw [h]; exact Subgroup.mem_top _
      obtain ⟨s, hs, hsm⟩ := Subgroup.mem_map.mp hximg
      have hker : s⁻¹ * x ∈ W.subgroupOf K := by
        rw [← QuotientGroup.eq_one_iff]
        change (QuotientGroup.mk' (W.subgroupOf K)) (s⁻¹ * x) = 1
        rw [map_mul, map_inv, hsm, inv_mul_cancel]
      simpa using S.mul_mem hs (hV₀S hker)
    exact kmodel_fixingSubgroup_eq_top_contradiction hperf hWle hWq8 hKZ hZcentK hS_eq

theorem isSimpleGroup_of_isAlt5 {Q : Type} [Group Q] (h : CFSG.Quasithin.IsAlt 5 Q) :
    IsSimpleGroup Q := by
  obtain ⟨e⟩ := h
  exact e.isSimpleGroup

theorem exists_orderOf_eq_five_of_alt5 {K W : Subgroup G}
    (hWle : W ≤ K) (hWq8 : IsQ8D8 W) [(W.subgroupOf K).Normal]
    (halt : CFSG.Quasithin.IsAlt 5 (↥K ⧸ W.subgroupOf K)) :
    ∃ b ∈ K, orderOf b = 5 := by
  obtain ⟨e⟩ := halt
  have hcard_quot : Nat.card (↥K ⧸ W.subgroupOf K) = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num
  have hcardW : Nat.card (W.subgroupOf K) = 32 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWle).toEquiv]
    exact hWq8.facts.1
  have hcardK : Nat.card K = 1920 := by
    have h1 := Subgroup.card_mul_index (W.subgroupOf K)
    rw [Subgroup.index_eq_card, hcardW, hcard_quot] at h1
    omega
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 5 (by rw [hcardK]; norm_num)
  exact ⟨(b : G), b.2, by rw [Subgroup.orderOf_coe]; exact hb⟩

theorem exists_orderOf_eq_three_of_alt5 {K W : Subgroup G}
    (hWle : W ≤ K) (hWq8 : IsQ8D8 W) [(W.subgroupOf K).Normal]
    (halt : CFSG.Quasithin.IsAlt 5 (↥K ⧸ W.subgroupOf K)) :
    ∃ b ∈ K, orderOf b = 3 := by
  obtain ⟨e⟩ := halt
  have hcard_quot : Nat.card (↥K ⧸ W.subgroupOf K) = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num
  have hcardW : Nat.card (W.subgroupOf K) = 32 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWle).toEquiv]
    exact hWq8.facts.1
  have hcardK : Nat.card K = 1920 := by
    have h1 := Subgroup.card_mul_index (W.subgroupOf K)
    rw [Subgroup.index_eq_card, hcardW, hcard_quot] at h1
    omega
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 3 (by rw [hcardK]; norm_num)
  exact ⟨(b : G), b.2, by rw [Subgroup.orderOf_coe]; exact hb⟩

private theorem kmodel_inf_centralizer_singleton_eq_inf_centralizer {E K : Subgroup G} {w : G}
    (hZcent : E ⊓ Subgroup.centralizer (E : Set G) ≤ Subgroup.centralizer (K : Set G))
    (hw : w ∈ K) (h2 : Nat.card ↥(E ⊓ Subgroup.centralizer ({w} : Set G)) = 2)
    (hZcard : Nat.card ↥(E ⊓ Subgroup.centralizer (E : Set G)) = 2) :
    E ⊓ Subgroup.centralizer ({w} : Set G) = E ⊓ Subgroup.centralizer (E : Set G) := by
  have hZle : E ⊓ Subgroup.centralizer (E : Set G) ≤
      E ⊓ Subgroup.centralizer ({w} : Set G) := by
    refine le_inf inf_le_left ?_
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact Subgroup.mem_centralizer_iff.mp (hZcent hz) w hw
  exact (Subgroup.eq_of_le_of_card_ge hZle (by rw [h2, hZcard])).symm

private abbrev kmodel_conjEnd (E : Subgroup G) (w : G)
    (hwN : w ∈ Subgroup.normalizer (E : Set G)) :
    Function.End {n : E // n * n = 1} :=
  fun n =>
    ⟨⟨w * (n.1 : G) * w⁻¹,
        (Subgroup.mem_normalizer_iff.mp hwN (n.1 : G)).mp n.1.2⟩, by
      apply Subtype.ext
      have hn : (n.1 : G) * (n.1 : G) = 1 := by
        simpa using congrArg Subtype.val n.2
      calc (w * (n.1 : G) * w⁻¹) * (w * (n.1 : G) * w⁻¹)
          = w * ((n.1 : G) * (n.1 : G)) * w⁻¹ := by group
        _ = 1 := by rw [hn]; group⟩

private theorem kmodel_conjEnd_pow_three (E : Subgroup G) (w : G)
    (hwN : w ∈ Subgroup.normalizer (E : Set G)) (h3 : w ^ 3 = 1) :
    (kmodel_conjEnd E w hwN) ^ 3 = 1 := by
  funext n
  apply Subtype.ext
  apply Subtype.ext
  change w * (w * (w * (n.1 : G) * w⁻¹) * w⁻¹) * w⁻¹ = (n.1 : G)
  calc w * (w * (w * (n.1 : G) * w⁻¹) * w⁻¹) * w⁻¹
      = w * w * w * (n.1 : G) * (w * w * w)⁻¹ := by group
    _ = (n.1 : G) := by
          have hw3 : w * w * w = 1 := by
            calc w * w * w = w ^ 3 := by simp [pow_succ]
              _ = 1 := h3
          rw [hw3]; group

private theorem kmodel_fixedPoints_card_conjEnd {E : Subgroup G} {w : G}
    (hwN : w ∈ Subgroup.normalizer (E : Set G))
    (h2 : Nat.card ↥(E ⊓ Subgroup.centralizer ({w} : Set G)) = 2) :
    Nat.card ↥((kmodel_conjEnd E w hwN).fixedPoints) = 2 := by
  have he : (↥((kmodel_conjEnd E w hwN).fixedPoints)) ≃
      ↥(E ⊓ Subgroup.centralizer ({w} : Set G)) :=
    { toFun := fun n => ⟨(n.1.1 : G), Subgroup.mem_inf.mpr ⟨n.1.1.2, by
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          rw [hy]
          have hfix := congrArg (fun t : {n : E // n * n = 1} => (t.1 : G)) n.2
          have hfix' : w * (n.1.1 : G) * w⁻¹ = (n.1.1 : G) := by
            simpa [kmodel_conjEnd] using hfix
          have hww : w * (n.1.1 : G) = (n.1.1 : G) * w := by
            calc w * (n.1.1 : G) = w * (n.1.1 : G) * w⁻¹ * w := by group
              _ = (n.1.1 : G) * w := by rw [hfix']
          exact hww⟩⟩
      invFun := fun c => ⟨⟨⟨c.1, (Subgroup.mem_inf.mp c.2).1⟩, by
          apply Subtype.ext
          have hdvd' : orderOf c.1 ∣ 2 := h2 ▸ Subgroup.orderOf_dvd_natCard _ c.2
          simpa [pow_two] using (orderOf_dvd_iff_pow_eq_one).mp hdvd'⟩, by
        apply Subtype.ext
        apply Subtype.ext
        show w * c.1 * w⁻¹ = c.1
        have hcomm := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp c.2).2 w
          (Set.mem_singleton w)
        rw [hcomm]; group⟩
      left_inv := fun n => by apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := fun c => by apply Subtype.ext; rfl }
  rw [Nat.card_congr he]
  exact h2

private theorem kmodel_card_inf_centralizer_ne_thirtytwo {K E : Subgroup G}
    (hperf : ⁅K, K⁆ = K) (hEle : E ≤ K) (hEn : K ≤ Subgroup.normalizer (E : Set G))
    (hEq8 : IsQ8D8 E) [(E.subgroupOf K).Normal]
    (hsimple : IsSimpleGroup (↥K ⧸ E.subgroupOf K))
    {w : G} (hw : w ∈ K) (hord : orderOf w = 3) :
    Nat.card ↥(E ⊓ Subgroup.centralizer ({w} : Set G)) ≠ 32 := by
  intro h32
  have hcardE : Nat.card E = 32 := hEq8.facts.1
  have hCE : E ⊓ Subgroup.centralizer ({w} : Set G) = E :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h32, hcardE])
  have hwZ : ∀ e ∈ E, ⁅e, w⁆ ∈ E ⊓ Subgroup.centralizer (E : Set G) := by
    intro e he
    have heC : e ∈ E ⊓ Subgroup.centralizer ({w} : Set G) := by rw [hCE]; exact he
    have hcomm : w * e = e * w :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp heC).2 w (Set.mem_singleton w)
    rw [commutatorElement_eq_one_iff_mul_comm.mpr hcomm.symm]
    exact Subgroup.one_mem _
  have hwE : w ∈ E :=
    section_centralizer_le_of_perfect hperf hEle hEn hEq8 hsimple w hw hwZ
  have hdvd' : orderOf w ∣ Nat.card E := E.orderOf_dvd_natCard hwE
  rw [hord, hcardE] at hdvd'
  omega

private theorem kmodel_card_eq_eight_of_dvd_thirtytwo {n : ℕ} (hdvd : n ∣ 32)
    (hmod : n ≡ 2 [MOD 3]) (hne2 : n ≠ 2) (hne32 : n ≠ 32) : n = 8 := by
  have hdvd2 : n ∣ 2 ^ 5 := by rw [show (2 : ℕ) ^ 5 = 32 from rfl]; exact hdvd
  obtain ⟨k, _hk5, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd2
  interval_cases k
  · rw [hk] at hmod; norm_num at hmod
  · rw [hk] at hne2; norm_num at hne2
  · rw [hk] at hmod; norm_num at hmod
  · rw [hk]; norm_num
  · rw [hk] at hmod; norm_num at hmod
  · rw [hk] at hne32; norm_num at hne32

theorem card_inf_centralizer_singleton_eq_eight (hI : Inputs49) {K E : Subgroup G}
    (hperf : ⁅K, K⁆ = K) (hEle : E ≤ K) (hEn : K ≤ Subgroup.normalizer (E : Set G))
    (hEq8 : IsQ8D8 E) [(E.subgroupOf K).Normal]
    (hsimple : IsSimpleGroup (↥K ⧸ E.subgroupOf K))
    {w : G} (hw : w ∈ K) (hord : orderOf w = 3) :
    Nat.card ↥(E ⊓ Subgroup.centralizer ({w} : Set G)) = 8 := by
  classical
  have h3 : w ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one w
  have hwN : w ∈ Subgroup.normalizer (E : Set G) := hEn hw
  have hcardE : Nat.card E = 32 := hEq8.facts.1
  have hZcard : Nat.card ↥(E ⊓ Subgroup.centralizer (E : Set G)) = 2 :=
    isQ8D8_card_inf_centralizer hEq8
  have hKZ : ⁅K, E ⊓ Subgroup.centralizer (E : Set G)⁆ = ⊥ :=
    commutator_eq_bot_of_isQ8D8_normal hEn hEq8
  have hZcent : E ⊓ Subgroup.centralizer (E : Set G) ≤ Subgroup.centralizer (K : Set G) :=
    Subgroup.le_centralizer_iff.mpr ((Subgroup.commutator_eq_bot_iff_le_centralizer).mp hKZ)
  have hmodE : Nat.card E ≡ Nat.card ↥(E ⊓ Subgroup.centralizer ({w} : Set G)) [MOD 3] :=
    CFSG.Quasithin.Q16.card_modEq_card_inf_centralizer (p := 3) (n := 1) E hwN
      (by simpa using h3)
  have hmod : Nat.card ↥(E ⊓ Subgroup.centralizer ({w} : Set G)) ≡ 2 [MOD 3] :=
    hmodE.symm.trans (by rw [hcardE]; decide)
  have hdvd : Nat.card ↥(E ⊓ Subgroup.centralizer ({w} : Set G)) ∣ 32 := by
    rw [← hcardE]; exact Subgroup.card_dvd_of_le inf_le_left
  have hne32 := kmodel_card_inf_centralizer_ne_thirtytwo hperf hEle hEn hEq8 hsimple hw hord
  have hne2 : Nat.card ↥(E ⊓ Subgroup.centralizer ({w} : Set G)) ≠ 2 := by
    intro h2
    have hZC : E ⊓ Subgroup.centralizer ({w} : Set G) =
        E ⊓ Subgroup.centralizer (E : Set G) :=
      kmodel_inf_centralizer_singleton_eq_inf_centralizer hZcent hw h2 hZcard
    let S : Type := {n : E // n * n = 1}
    haveI : Fintype S := Fintype.ofFinite S
    have hcardS : Nat.card S = 12 := hI.2.1 G E hEq8
    have hf : (kmodel_conjEnd E w hwN) ^ 3 = 1 := kmodel_conjEnd_pow_three E w hwN h3
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hmodS := Equiv.Perm.card_fixedPoints_modEq (p := 3) (n := 1) hf
    have hfixcard : Nat.card ↥((kmodel_conjEnd E w hwN).fixedPoints) = 2 :=
      kmodel_fixedPoints_card_conjEnd hwN h2
    rw [Nat.card_eq_fintype_card] at hfixcard
    rw [show Fintype.card S = 12 from by rw [← Nat.card_eq_fintype_card, hcardS],
      hfixcard] at hmodS
    exact absurd hmodS (by decide)
  exact kmodel_card_eq_eight_of_dvd_thirtytwo hdvd hmod hne2 hne32

theorem isQ8D8_commutator_eq_inf_centralizer {N : Subgroup G} (h : IsQ8D8 N) :
    ⁅N, N⁆ = N ⊓ Subgroup.centralizer (N : Set G) := by
  have hZcard : Nat.card ↥(N ⊓ Subgroup.centralizer (N : Set G)) = 2 :=
    isQ8D8_card_inf_centralizer h
  have hle := isQ8D8_commutator_le_inf_centralizer h
  have hne : ⁅N, N⁆ ≠ ⊥ := by
    intro hbot
    exact isQ8D8_not_isMulCommutative h
      ((Subgroup.commutator_self_eq_bot_iff (H := N)).mp hbot)
  have hcard : Nat.card ↥⁅N, N⁆ = 2 := by
    have hdvd : Nat.card ↥⁅N, N⁆ ∣ 2 := hZcard ▸ Subgroup.card_dvd_of_le hle
    have hle2 : Nat.card ↥⁅N, N⁆ ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < Nat.card ↥⁅N, N⁆ := Nat.card_pos
    have h12 : Nat.card ↥⁅N, N⁆ = 1 ∨ Nat.card ↥⁅N, N⁆ = 2 := by omega
    rcases h12 with h1 | h2
    · exact absurd ((Subgroup.eq_bot_iff_card ⁅N, N⁆).mpr h1) hne
    · exact h2
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hZcard, hcard])

theorem commutator_sup_eq_of_le_centralizer {Y Z : Subgroup G}
    (hZ : Z ≤ Subgroup.centralizer ((Y ⊔ Z : Subgroup G) : Set G)) :
    ⁅Y ⊔ Z, Y ⊔ Z⁆ = ⁅Y, Y⁆ := by
  have hYZ : ∀ a ∈ Y, ∀ b ∈ Z, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.mp (hZ hb) a (Subgroup.mem_sup_left (T := Z) ha)
  refine le_antisymm ?_ (Subgroup.commutator_mono le_sup_left le_sup_left)
  rw [Subgroup.commutator_le]
  intro a ha b hb
  obtain ⟨a1, ha1, a2, ha2, rfl⟩ :=
    CFSG.GH74.Uniqueness.SU.SU5.mem_sup_of_commute hYZ ha
  obtain ⟨b1, hb1, b2, hb2, rfl⟩ :=
    CFSG.GH74.Uniqueness.SU.SU5.mem_sup_of_commute hYZ hb
  have hca2 : ∀ t ∈ Y ⊔ Z, a2 * t = t * a2 := fun t ht =>
    (Subgroup.mem_centralizer_iff.mp (hZ ha2) t ht).symm
  have hcb2 : ∀ t ∈ Y ⊔ Z, b2 * t = t * b2 := fun t ht =>
    (Subgroup.mem_centralizer_iff.mp (hZ hb2) t ht).symm
  have h1 : ⁅a2, b1⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (hca2 b1 (Subgroup.mem_sup_left hb1))
  have h2 : ⁅a2, b2⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (hca2 b2 (Subgroup.mem_sup_right hb2))
  have h3 : ⁅a1, b2⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr
      (hcb2 a1 (Subgroup.mem_sup_left (T := Z) ha1)).symm
  rw [commutatorElement_mul_left_eq_conj_mul, commutatorElement_mul_right_eq_mul_conj,
    commutatorElement_mul_right_eq_mul_conj, h1, h2, h3]
  simpa using Subgroup.commutator_mem_commutator ha1 hb1

private lemma invariant_subgroups_eq_le_center {Z Y : Subgroup G} (hZcard : Nat.card Z = 2)
    (hYZ : Y ≤ Z) : Y = ⊥ ∨ Y = Z := by
  have hdvd : Nat.card Y ∣ 2 := hZcard ▸ Subgroup.card_dvd_of_le hYZ
  have hle2 : Nat.card Y ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have hpos : 0 < Nat.card Y := Nat.card_pos
  have h12 : Nat.card Y = 1 ∨ Nat.card Y = 2 := by omega
  rcases h12 with h1 | h2
  · exact Or.inl ((Subgroup.eq_bot_iff_card Y).mpr h1)
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge hYZ (by rw [hZcard, h2]))

private lemma invariant_subgroups_eq_conj_mem_sup {K Y Z U : Subgroup G}
    (hUdef : U = Y ⊔ Z) (hYZU : ∀ a ∈ Y, ∀ b ∈ Z, a * b = b * a)
    (hYn : K ≤ Subgroup.normalizer (Y : Set G))
    (hZn : K ≤ Subgroup.normalizer (Z : Set G)) :
    ∀ k ∈ K, ∀ u ∈ U, k * u * k⁻¹ ∈ U := by
  intro k hk u hu
  rw [hUdef] at hu ⊢
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    CFSG.GH74.Uniqueness.SU.SU5.mem_sup_of_commute hYZU hu
  have h1 : k * a * k⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp (hYn hk) a).mp ha
  have h2 : k * b * k⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp (hZn hk) b).mp hb
  rw [show k * (a * b) * k⁻¹ = (k * a * k⁻¹) * (k * b * k⁻¹) by group]
  exact Subgroup.mul_mem_sup h1 h2

private lemma invariant_subgroups_eq_normalizer_of_conj_mem {K U : Subgroup G}
    (h : ∀ k ∈ K, ∀ u ∈ U, k * u * k⁻¹ ∈ U) :
    K ≤ Subgroup.normalizer (U : Set G) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro u
  exact ⟨fun hu => h k hk u hu, fun hu => by
    have hh := h k⁻¹ (K.inv_mem hk) (k * u * k⁻¹) hu
    rwa [show k⁻¹ * (k * u * k⁻¹) * k⁻¹⁻¹ = u by group] at hh⟩

private lemma invariant_subgroups_eq_le_of_commutator_sup_eq {Y Z U E : Subgroup G}
    (hUdef : U = Y ⊔ Z) (hUE : U = E) (hEE : ⁅E, E⁆ = Z)
    (hZleU : Z ≤ Subgroup.centralizer (U : Set G)) : Y = E := by
  have hZleY : Z ≤ Y := by
    rw [← hEE, ← hUE, hUdef]
    rw [commutator_sup_eq_of_le_centralizer (hUdef ▸ hZleU)]
    exact Subgroup.commutator_le.mpr fun a ha b hb => by
      rw [commutatorElement_def]
      exact Y.mul_mem (Y.mul_mem (Y.mul_mem ha hb) (Y.inv_mem ha)) (Y.inv_mem hb)
  rw [← hUE, hUdef, sup_eq_left.mpr hZleY]

private lemma invariant_subgroups_eq_T_mul_mem {K E U Z : Subgroup G}
    (hZcent : Z ≤ Subgroup.centralizer (K : Set G))
    (hUn_fwd : ∀ k ∈ K, ∀ u ∈ U, k * u * k⁻¹ ∈ U)
    {a b' : G} (haK : a ∈ K) (haU : ∀ u ∈ U, ⁅u, a⁆ ∈ Z)
    (haE : ∀ e ∈ E, ⁅e, a⁆ ∈ U) (hbK' : b' ∈ K)
    (hbU' : ∀ u ∈ U, ⁅u, b'⁆ ∈ Z) (hbE' : ∀ e ∈ E, ⁅e, b'⁆ ∈ U) :
    a * b' ∈ K ∧ (∀ u ∈ U, ⁅u, a * b'⁆ ∈ Z) ∧ (∀ e ∈ E, ⁅e, a * b'⁆ ∈ U) := by
  refine ⟨K.mul_mem haK hbK', ?_, ?_⟩
  · intro u hu
    rw [commutatorElement_mul_right_eq_mul_conj]
    have h1 : ⁅u, a⁆ ∈ Z := haU u hu
    have h2 : ⁅u, b'⁆ ∈ Z := hbU' u hu
    have h3 : a * ⁅u, b'⁆ * a⁻¹ = ⁅u, b'⁆ := by
      have hc := Subgroup.mem_centralizer_iff.mp (hZcent h2) a haK
      rw [hc]; group
    rw [show ⁅u, a⁆ * a * ⁅u, b'⁆ * a⁻¹ = ⁅u, a⁆ * (a * ⁅u, b'⁆ * a⁻¹) by
      group, h3]
    exact Z.mul_mem h1 h2
  · intro e he
    rw [commutatorElement_mul_right_eq_mul_conj]
    have h1 : ⁅e, a⁆ ∈ U := haE e he
    have h2 : ⁅e, b'⁆ ∈ U := hbE' e he
    have h3 : a * ⁅e, b'⁆ * a⁻¹ ∈ U := hUn_fwd a haK ⁅e, b'⁆ h2
    rw [show ⁅e, a⁆ * a * ⁅e, b'⁆ * a⁻¹ = ⁅e, a⁆ * (a * ⁅e, b'⁆ * a⁻¹) by group]
    exact U.mul_mem h1 h3

private lemma invariant_subgroups_eq_T_inv_mem {K E U Z : Subgroup G}
    (hZcent : Z ≤ Subgroup.centralizer (K : Set G))
    (hUn_fwd : ∀ k ∈ K, ∀ u ∈ U, k * u * k⁻¹ ∈ U)
    {a : G} (haK : a ∈ K) (haU : ∀ u ∈ U, ⁅u, a⁆ ∈ Z)
    (haE : ∀ e ∈ E, ⁅e, a⁆ ∈ U) :
    a⁻¹ ∈ K ∧ (∀ u ∈ U, ⁅u, a⁻¹⁆ ∈ Z) ∧ (∀ e ∈ E, ⁅e, a⁻¹⁆ ∈ U) := by
  refine ⟨K.inv_mem haK, ?_, ?_⟩
  · intro u hu
    rw [commutatorElement_inv_right]
    have h1 : ⁅a, u⁆ ∈ Z := by
      rw [← commutatorElement_inv]; exact Z.inv_mem (haU u hu)
    have h2 : a⁻¹ * ⁅a, u⁆ * a = ⁅a, u⁆ := by
      have hc := Subgroup.mem_centralizer_iff.mp (hZcent h1) a⁻¹ (K.inv_mem haK)
      rw [hc]; group
    rw [h2]; exact h1
  · intro e he
    rw [commutatorElement_inv_right]
    have h1 : ⁅a, e⁆ ∈ U := by
      rw [← commutatorElement_inv]; exact U.inv_mem (haE e he)
    have hh := hUn_fwd a⁻¹ (K.inv_mem haK) ⁅a, e⁆ h1
    simpa using hh

private lemma invariant_subgroups_eq_le_T {K E U Z : Subgroup G}
    (hEle : E ≤ K) (hEE : ⁅E, E⁆ = Z) (hZU : Z ≤ U) (hUle : U ≤ E) :
    ∀ e ∈ E, e ∈ K ∧ (∀ u ∈ U, ⁅u, e⁆ ∈ Z) ∧ (∀ e' ∈ E, ⁅e', e⁆ ∈ U) := by
  intro e he
  refine ⟨hEle he, ?_, ?_⟩
  · intro u hu
    rw [← hEE]
    exact Subgroup.commutator_mem_commutator (hUle hu) he
  · intro e' he'
    have h : ⁅e', e⁆ ∈ ⁅E, E⁆ := Subgroup.commutator_mem_commutator he' he
    rw [hEE] at h
    exact hZU h

private lemma invariant_subgroups_eq_b_mem_T {K E U Z : Subgroup G} {b : G}
    (hbK : b ∈ K) (hUle : U ≤ E) (hEb' : ∀ e ∈ E, e * b = b * e) :
    b ∈ K ∧ (∀ u ∈ U, ⁅u, b⁆ ∈ Z) ∧ (∀ e ∈ E, ⁅e, b⁆ ∈ U) := by
  refine ⟨hbK, ?_, ?_⟩
  · intro u hu
    have : ⁅u, b⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (hEb' u (hUle hu))
    rw [this]; exact Z.one_mem
  · intro e he
    have : ⁅e, b⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hEb' e he)
    rw [this]; exact U.one_mem

private lemma invariant_subgroups_eq_conj_mem_T {K E U Z : Subgroup G}
    (hZcent : Z ≤ Subgroup.centralizer (K : Set G))
    (hEn : K ≤ Subgroup.normalizer (E : Set G))
    (hUn_fwd : ∀ k ∈ K, ∀ u ∈ U, k * u * k⁻¹ ∈ U) :
    ∀ k ∈ K, ∀ t ∈ K, (∀ u ∈ U, ⁅u, t⁆ ∈ Z) → (∀ e ∈ E, ⁅e, t⁆ ∈ U) →
      k * t * k⁻¹ ∈ K ∧ (∀ u ∈ U, ⁅u, k * t * k⁻¹⁆ ∈ Z) ∧
        (∀ e ∈ E, ⁅e, k * t * k⁻¹⁆ ∈ U) := by
  intro k hk t htK htU htE
  refine ⟨K.mul_mem (K.mul_mem hk htK) (K.inv_mem hk), ?_, ?_⟩
  · intro u hu
    have huw : k⁻¹ * u * k ∈ U := by
      have hh := hUn_fwd k⁻¹ (K.inv_mem hk) u hu
      simpa using hh
    have h1 : ⁅k⁻¹ * u * k, t⁆ ∈ Z := htU _ huw
    have h2 : k * ⁅k⁻¹ * u * k, t⁆ * k⁻¹ = ⁅k⁻¹ * u * k, t⁆ := by
      have hc := Subgroup.mem_centralizer_iff.mp (hZcent h1) k hk
      rw [hc]; group
    have hgoal : ⁅u, k * t * k⁻¹⁆ = ⁅k⁻¹ * u * k, t⁆ := by
      rw [show ⁅u, k * t * k⁻¹⁆ = k * ⁅k⁻¹ * u * k, t⁆ * k⁻¹ by
        simp only [commutatorElement_def]; group, h2]
    rw [hgoal]; exact h1
  · intro e he
    have hew : k⁻¹ * e * k ∈ E := by
      have hh := (Subgroup.mem_normalizer_iff.mp (hEn (K.inv_mem hk)) e).mp he
      simpa using hh
    have h1 : ⁅k⁻¹ * e * k, t⁆ ∈ U := htE _ hew
    have h2 : k * ⁅k⁻¹ * e * k, t⁆ * k⁻¹ ∈ U := hUn_fwd k hk _ h1
    have hgoal : ⁅e, k * t * k⁻¹⁆ = k * ⁅k⁻¹ * e * k, t⁆ * k⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [hgoal]; exact h2

private lemma invariant_subgroups_eq_normalizer_T {K T : Subgroup G}
    (h : ∀ k ∈ K, ∀ t ∈ T, k * t * k⁻¹ ∈ T) :
    K ≤ Subgroup.normalizer (T : Set G) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro t
  exact ⟨fun ht => h k hk t ht, fun ht => by
    have hh := h k⁻¹ (K.inv_mem hk) (k * t * k⁻¹) ht
    rwa [show k⁻¹ * (k * t * k⁻¹) * k⁻¹⁻¹ = t by group] at hh⟩

private lemma invariant_subgroups_eq_centralizer_order_five {K E U Z : Subgroup G} {b : G}
    (hEq8 : IsQ8D8 E) (hZcard : Nat.card Z = 2)
    (hZcent : Z ≤ Subgroup.centralizer (K : Set G))
    (hZU : Z ≤ U) (hUle : U ≤ E) (hUZ : U ≠ Z) (hUE : U ≠ E)
    (hUn : K ≤ Subgroup.normalizer (U : Set G))
    (hEn : K ≤ Subgroup.normalizer (E : Set G)) (hbK : b ∈ K) (hbord : orderOf b = 5) :
    ∀ e ∈ E, e * b = b * e := by
  have hb5' : b ^ 5 = 1 := by rw [← hbord]; exact pow_orderOf_eq_one b
  have hbU : b ∈ Subgroup.normalizer (U : Set G) := hUn hbK
  have hbE : b ∈ Subgroup.normalizer (E : Set G) := hEn hbK
  have hZb : Z ≤ Subgroup.centralizer ({b} : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact Subgroup.mem_centralizer_iff.mp (hZcent hz) b hbK
  have hEb : E ≤ Subgroup.centralizer ({b} : Set G) :=
    CFSG.Quasithin.Q16.le_centralizer_of_ne_ne (hEq8.facts.1) hZcard hZU hUle hUZ hUE
      hbU hbE hb5' hZb
  exact fun e he => (Subgroup.mem_centralizer_iff.mp (hEb he) b (Set.mem_singleton b)).symm

private lemma invariant_subgroups_eq_order_five_not_mem {E : Subgroup G} {b : G}
    (hbord : orderOf b = 5) (hEcard : Nat.card E = 32) : b ∉ E := by
  intro hbE
  have hdvd : orderOf b ∣ Nat.card E := E.orderOf_dvd_natCard hbE
  rw [hbord, hEcard] at hdvd
  omega

private theorem invariant_subgroups_eq_T_eq_K {K E T : Subgroup G} {b : G}
    (hTle : T ≤ K) (hEle_T : E ≤ T) (hTn : K ≤ Subgroup.normalizer (T : Set G))
    (hbT : b ∈ T) (hbK : b ∈ K) (hbord : orderOf b = 5) (hEcard : Nat.card E = 32)
    [(E.subgroupOf K).Normal]
    (hsimple : IsSimpleGroup (↥K ⧸ E.subgroupOf K)) : T = K := by
  haveI hTKn : (T.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTle).mpr hTn
  have hb_ne : (QuotientGroup.mk' (E.subgroupOf K)) ⟨b, hbK⟩ ≠ 1 := by
    intro h1
    exact invariant_subgroups_eq_order_five_not_mem hbord hEcard
      ((QuotientGroup.eq_one_iff (⟨b, hbK⟩ : ↥K)).mp h1)
  have hTimg : ((T.subgroupOf K).map (QuotientGroup.mk' (E.subgroupOf K))).Normal :=
    hTKn.map _ (QuotientGroup.mk'_surjective _)
  haveI := hTimg
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    ((T.subgroupOf K).map (QuotientGroup.mk' (E.subgroupOf K))) with h | h
  · exfalso
    have hmem : (QuotientGroup.mk' (E.subgroupOf K)) ⟨b, hbK⟩ ∈
        (T.subgroupOf K).map (QuotientGroup.mk' (E.subgroupOf K)) :=
      Subgroup.mem_map_of_mem _ hbT
    rw [h] at hmem
    exact hb_ne (Subgroup.mem_bot.mp hmem)
  · apply le_antisymm hTle
    intro t ht
    have hmem : (QuotientGroup.mk' (E.subgroupOf K)) ⟨t, ht⟩ ∈
        (T.subgroupOf K).map (QuotientGroup.mk' (E.subgroupOf K)) := by
      rw [h]; exact Subgroup.mem_top _
    obtain ⟨s, hs, hsm⟩ := Subgroup.mem_map.mp hmem
    have hker : s⁻¹ * ⟨t, ht⟩ ∈ E.subgroupOf K := by
      rw [← QuotientGroup.eq_one_iff]
      change (QuotientGroup.mk' (E.subgroupOf K)) (s⁻¹ * ⟨t, ht⟩) = 1
      rw [map_mul, map_inv, hsm, inv_mul_cancel]
    have := T.mul_mem hs (hEle_T hker)
    simpa using this

private lemma invariant_subgroups_eq_bot_of_commutator_le {K E U Z : Subgroup G}
    (hperf : ⁅K, K⁆ = K) (hEle : E ≤ K) (hKZ : ⁅K, Z⁆ = ⊥)
    (hEK_U : ⁅E, K⁆ ≤ U) (hUK_Z : ⁅U, K⁆ ≤ Z)
    (hEE : ⁅E, E⁆ = Z) (hZcard : Nat.card Z = 2) : False := by
  have hZK : ⁅Z, K⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact hKZ
  let Ys : ℕ → Subgroup G := fun i =>
    match i with
    | 0 => E
    | 1 => U
    | 2 => Z
    | _ => ⊥
  have hEKbot : ⁅E, K⁆ = ⊥ := by
    refine CFSG.GroupTheory.CoprimeSection.commutator_eq_bot_of_series hperf Ys 3 ?_ ?_
    · intro i hi
      interval_cases i
      · exact hEK_U
      · exact hUK_Z
      · exact hZK.le
    · rfl
  have hEEbot : ⁅E, E⁆ = ⊥ :=
    le_bot_iff.mp (hEKbot ▸ Subgroup.commutator_mono le_rfl hEle)
  rw [hEE] at hEEbot
  rw [hEEbot] at hZcard
  simp at hZcard

private theorem invariant_subgroups_eq_bot_of_T {K E U Z T : Subgroup G} {b : G}
    (hperf : ⁅K, K⁆ = K) (hEle : E ≤ K) (hKZ : ⁅K, Z⁆ = ⊥)
    (hEE : ⁅E, E⁆ = Z) (hZcard : Nat.card Z = 2)
    (hTmem : ∀ t, t ∈ T → t ∈ K ∧ (∀ u ∈ U, ⁅u, t⁆ ∈ Z) ∧ (∀ e ∈ E, ⁅e, t⁆ ∈ U))
    (hEle_T : E ≤ T) (hTn : K ≤ Subgroup.normalizer (T : Set G)) (hbT : b ∈ T)
    (hbK : b ∈ K) (hbord : orderOf b = 5) (hEcard : Nat.card E = 32)
    [(E.subgroupOf K).Normal]
    (hsimple : IsSimpleGroup (↥K ⧸ E.subgroupOf K)) : False := by
  have hTle : T ≤ K := fun t ht => (hTmem t ht).1
  have hTK : T = K :=
    invariant_subgroups_eq_T_eq_K hTle hEle_T hTn hbT hbK hbord hEcard hsimple
  have hEK_U : ⁅E, K⁆ ≤ U := by
    rw [Subgroup.commutator_le]
    intro e he k hk
    exact (hTmem k (hTK ▸ hk)).2.2 e he
  have hUK_Z : ⁅U, K⁆ ≤ Z := by
    rw [Subgroup.commutator_le]
    intro u hu k hk
    exact (hTmem k (hTK ▸ hk)).2.1 u hu
  exact invariant_subgroups_eq_bot_of_commutator_le hperf hEle hKZ hEK_U hUK_Z hEE hZcard

private theorem invariant_subgroups_eq_contradiction_of_sup_ne {K E U Z : Subgroup G}
    (hperf : ⁅K, K⁆ = K) (hEle : E ≤ K)
    (hEn : K ≤ Subgroup.normalizer (E : Set G)) (hEq8 : IsQ8D8 E)
    [(E.subgroupOf K).Normal]
    (hsimple : IsSimpleGroup (↥K ⧸ E.subgroupOf K))
    (hb5 : ∃ b ∈ K, orderOf b = 5)
    (hZcard : Nat.card Z = 2) (hZcent : Z ≤ Subgroup.centralizer (K : Set G))
    (hKZ : ⁅K, Z⁆ = ⊥) (hEE : ⁅E, E⁆ = Z)
    (hUle : U ≤ E) (hZU : Z ≤ U) (hUZ : U ≠ Z) (hUE : U ≠ E)
    (hUn_fwd : ∀ k ∈ K, ∀ u ∈ U, k * u * k⁻¹ ∈ U)
    (hUn : K ≤ Subgroup.normalizer (U : Set G)) : False := by
  obtain ⟨b, hbK, hbord⟩ := hb5
  have hEb' : ∀ e ∈ E, e * b = b * e :=
    invariant_subgroups_eq_centralizer_order_five hEq8 hZcard hZcent hZU hUle hUZ hUE
      hUn hEn hbK hbord
  let T : Subgroup G :=
    { carrier := {t | t ∈ K ∧ (∀ u ∈ U, ⁅u, t⁆ ∈ Z) ∧ (∀ e ∈ E, ⁅e, t⁆ ∈ U)}
      mul_mem' := by
        rintro a b' ⟨haK, haU, haE⟩ ⟨hbK', hbU', hbE'⟩
        exact invariant_subgroups_eq_T_mul_mem hZcent hUn_fwd haK haU haE hbK' hbU' hbE'
      one_mem' := by
        refine ⟨K.one_mem, ?_, ?_⟩
        · intro u _; rw [commutatorElement_one_right]; exact Z.one_mem
        · intro e _; rw [commutatorElement_one_right]; exact U.one_mem
      inv_mem' := by
        rintro a ⟨haK, haU, haE⟩
        exact invariant_subgroups_eq_T_inv_mem hZcent hUn_fwd haK haU haE }
  have hEle_T : E ≤ T := by
    intro e he
    exact invariant_subgroups_eq_le_T hEle hEE hZU hUle e he
  have hbT : b ∈ T := invariant_subgroups_eq_b_mem_T hbK hUle hEb'
  have hTn_fwd : ∀ k ∈ K, ∀ t ∈ T, k * t * k⁻¹ ∈ T := by
    intro k hk t ht
    change t ∈ K ∧ (∀ u ∈ U, ⁅u, t⁆ ∈ Z) ∧ (∀ e ∈ E, ⁅e, t⁆ ∈ U) at ht
    obtain ⟨htK, htU, htE⟩ := ht
    exact invariant_subgroups_eq_conj_mem_T hZcent hEn hUn_fwd k hk t htK htU htE
  have hTn : K ≤ Subgroup.normalizer (T : Set G) :=
    invariant_subgroups_eq_normalizer_T hTn_fwd
  exact invariant_subgroups_eq_bot_of_T hperf hEle hKZ hEE hZcard (fun t ht => ht) hEle_T
    hTn hbT hbK hbord hEq8.facts.1 hsimple

private theorem invariant_subgroups_eq_of_not_le_center {K E Y Z : Subgroup G}
    (hperf : ⁅K, K⁆ = K) (hEle : E ≤ K)
    (hEn : K ≤ Subgroup.normalizer (E : Set G)) (hEq8 : IsQ8D8 E)
    [(E.subgroupOf K).Normal]
    (hsimple : IsSimpleGroup (↥K ⧸ E.subgroupOf K))
    (hb5 : ∃ b ∈ K, orderOf b = 5)
    (hZcard : Nat.card Z = 2) (hZcent : Z ≤ Subgroup.centralizer (K : Set G))
    (hZn : K ≤ Subgroup.normalizer (Z : Set G)) (hKZ : ⁅K, Z⁆ = ⊥)
    (hEE : ⁅E, E⁆ = Z) (hZE : Z ≤ E)
    (hYle : Y ≤ E) (hYn : K ≤ Subgroup.normalizer (Y : Set G)) (hYZ : ¬ Y ≤ Z) :
    Y = ⊥ ∨ Y = Z ∨ Y = E := by
  rw [SetLike.le_def] at hYZ
  push Not at hYZ
  obtain ⟨y, hyY, hyZ⟩ := hYZ
  set U : Subgroup G := Y ⊔ Z with hUdef
  have hUle : U ≤ E := sup_le hYle hZE
  have hZU : Z ≤ U := le_sup_right
  have hYU : Y ≤ U := le_sup_left
  have hUZ : U ≠ Z := by
    intro h
    exact hyZ (h ▸ Subgroup.mem_sup_left hyY)
  have hZleU : Z ≤ Subgroup.centralizer (U : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact Subgroup.mem_centralizer_iff.mp (hZcent hz) u (hEle (hUle hu))
  have hYZU : ∀ a ∈ Y, ∀ b ∈ Z, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.mp (hZleU hb) a (Subgroup.mem_sup_left ha)
  have hUn_fwd : ∀ k ∈ K, ∀ u ∈ U, k * u * k⁻¹ ∈ U :=
    invariant_subgroups_eq_conj_mem_sup hUdef hYZU hYn hZn
  have hUn : K ≤ Subgroup.normalizer (U : Set G) :=
    invariant_subgroups_eq_normalizer_of_conj_mem hUn_fwd
  by_cases hUE : U = E
  · exact Or.inr (Or.inr (invariant_subgroups_eq_le_of_commutator_sup_eq hUdef hUE hEE hZleU))
  · exfalso
    exact invariant_subgroups_eq_contradiction_of_sup_ne hperf hEle hEn hEq8 hsimple hb5
      hZcard hZcent hKZ hEE hUle hZU hUZ hUE hUn_fwd hUn

theorem invariant_subgroups_eq (hI : Inputs49) {K E : Subgroup G}
    (hperf : ⁅K, K⁆ = K) (hEle : E ≤ K) (hEn : K ≤ Subgroup.normalizer (E : Set G))
    (hEq8 : IsQ8D8 E) [(E.subgroupOf K).Normal]
    (hsimple : IsSimpleGroup (↥K ⧸ E.subgroupOf K))
    (hb5 : ∃ b ∈ K, orderOf b = 5) :
    ∀ Y : Subgroup G, Y ≤ E → K ≤ Subgroup.normalizer (Y : Set G) →
      Y = ⊥ ∨ Y = E ⊓ Subgroup.centralizer (E : Set G) ∨ Y = E := by
  intro Y hYle hYn
  set Z : Subgroup G := E ⊓ Subgroup.centralizer (E : Set G) with hZdef
  have hZcard : Nat.card Z = 2 := isQ8D8_card_inf_centralizer hEq8
  have hZE : Z ≤ E := inf_le_left
  have hKZ : ⁅K, Z⁆ = ⊥ := commutator_eq_bot_of_isQ8D8_normal hEn hEq8
  have hZcent : Z ≤ Subgroup.centralizer (K : Set G) :=
    Subgroup.le_centralizer_iff.mpr ((Subgroup.commutator_eq_bot_iff_le_centralizer).mp hKZ)
  have hZn : K ≤ Subgroup.normalizer (Z : Set G) :=
    (Subgroup.le_centralizer_iff.mp hZcent).trans
      (Subgroup.centralizer_le_normalizer (Z : Set G))
  have hEE : ⁅E, E⁆ = Z := by rw [hZdef]; exact isQ8D8_commutator_eq_inf_centralizer hEq8
  by_cases hYZ : Y ≤ Z
  · rcases invariant_subgroups_eq_le_center hZcard hYZ with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact invariant_subgroups_eq_of_not_le_center hperf hEle hEn hEq8 hsimple hb5
      hZcard hZcent hZn hKZ hEE hZE hYle hYn hYZ

private theorem kmodel49_setup {K : Subgroup G} {V₀ : Subgroup ↥K} (hV₀n : V₀.Normal)
    (hV₀q8 : IsQ8D8 (⊤ : Subgroup V₀))
    (hV₀alt : CFSG.Quasithin.IsAlt 5 (↥K ⧸ V₀)) :
    ∃ W : Subgroup G, W ≤ K ∧ K ≤ Subgroup.normalizer (W : Set G) ∧ IsQ8D8 W ∧
      W = CFSG.Open.pCoreOf 2 K ∧ W.subgroupOf K = V₀ := by
  haveI : V₀.Normal := hV₀n
  set W : Subgroup G := V₀.map K.subtype with hWdef
  have hWq8 : IsQ8D8 W := by
    rw [hWdef]
    refine (CFSG.GH74.Uniqueness.SU.SU5.isQ8D8_map_iff K.subtype_injective).mpr ?_
    have h :=
      (CFSG.GH74.Uniqueness.SU.SU5.isQ8D8_map_iff (Subgroup.subtype_injective V₀)).mpr hV₀q8
    rwa [Subgroup.map_top, Subgroup.range_subtype] at h
  have hWle : W ≤ K := hWdef ▸ Subgroup.map_subtype_le V₀
  have hWsub : W.subgroupOf K = V₀ := by
    rw [hWdef]
    exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective V₀
  have hWnormal : K ≤ Subgroup.normalizer (W : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWle).mp (by rw [hWsub]; exact hV₀n)
  have hWpCore : W = CFSG.Open.pCoreOf 2 K := by
    rw [hWdef, pCore_eq_of_q8d8_alt5 hV₀n hV₀q8 hV₀alt]
    rfl
  exact ⟨W, hWle, hWnormal, hWq8, hWpCore, hWsub⟩

private theorem kmodel49_centre_le_centralizer_singleton {K W : Subgroup G} {d : G}
    (hZcentW : W ⊓ Subgroup.centralizer (W : Set G) ≤ Subgroup.centralizer (K : Set G))
    (hdK : d ∈ K) :
    (W ⊓ Subgroup.centralizer ({d} : Set G)) ⊔ (W ⊓ Subgroup.centralizer (W : Set G)) =
      W ⊓ Subgroup.centralizer ({d} : Set G) := by
  refine sup_eq_left.mpr ?_
  refine le_inf inf_le_left ?_
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  rw [hy]
  exact Subgroup.mem_centralizer_iff.mp (hZcentW hz) d hdK

private theorem kmodel49_exists_phi {K W : Subgroup G}
    (hperf : ⁅K, K⁆ = K) (hWle : W ≤ K) (hWn : K ≤ Subgroup.normalizer (W : Set G))
    (hWq8 : IsQ8D8 W) [(W.subgroupOf K).Normal]
    (hsimple : IsSimpleGroup (↥K ⧸ W.subgroupOf K))
    (hWalt : CFSG.Quasithin.IsAlt 5 (↥K ⧸ W.subgroupOf K)) :
    ∃ φ : ↥K →* alternatingGroup (Fin 5), Function.Surjective φ ∧
      ∀ d : ↥K, φ d = 1 ↔
        ∀ n ∈ W, ⁅n, (d : G)⁆ ∈ W ⊓ Subgroup.centralizer (W : Set G) := by
  have hEEW : ⁅W, W⁆ = W ⊓ Subgroup.centralizer (W : Set G) :=
    isQ8D8_commutator_eq_inf_centralizer hWq8
  obtain ⟨e⟩ := hWalt
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' (W.subgroupOf K)), ?_, ?_⟩
  · exact e.surjective.comp (QuotientGroup.mk'_surjective _)
  · intro d
    change e ((QuotientGroup.mk' (W.subgroupOf K)) d) = 1 ↔
      ∀ n ∈ W, ⁅n, (d : G)⁆ ∈ W ⊓ Subgroup.centralizer (W : Set G)
    rw [e.map_eq_one_iff]
    change (d : ↥K ⧸ W.subgroupOf K) = 1 ↔
      ∀ n ∈ W, ⁅n, (d : G)⁆ ∈ W ⊓ Subgroup.centralizer (W : Set G)
    rw [QuotientGroup.eq_one_iff]
    simp only [Subgroup.mem_subgroupOf]
    constructor
    · intro hd n hn
      rw [← hEEW]
      exact Subgroup.commutator_mem_commutator hn hd
    · intro hd
      exact section_centralizer_le_of_perfect hperf hWle hWn hWq8 hsimple d d.2 hd

private theorem kmodel49_invariant_subgroups_of_centralizer (hI : Inputs49) {K W : Subgroup G}
    (hperf : ⁅K, K⁆ = K) (hWle : W ≤ K) (hWn : K ≤ Subgroup.normalizer (W : Set G))
    (hWq8 : IsQ8D8 W) [(W.subgroupOf K).Normal]
    (hsimple : IsSimpleGroup (↥K ⧸ W.subgroupOf K))
    (hWalt : CFSG.Quasithin.IsAlt 5 (↥K ⧸ W.subgroupOf K))
    (hZcardW : Nat.card ↥(W ⊓ Subgroup.centralizer (W : Set G)) = 2) :
    ∀ Y : Subgroup G, W ⊓ Subgroup.centralizer (W : Set G) ≤ Y → Y ≤ W →
      K ≤ Subgroup.normalizer (Y : Set G) →
      Y = W ⊓ Subgroup.centralizer (W : Set G) ∨ Y = W := by
  intro Y hZY hYW hYn
  rcases invariant_subgroups_eq hI hperf hWle hWn hWq8 hsimple
    (exists_orderOf_eq_five_of_alt5 hWle hWq8 hWalt) Y hYW hYn with h | h | h
  · exfalso
    have hZbot : W ⊓ Subgroup.centralizer (W : Set G) = ⊥ := le_bot_iff.mp (h ▸ hZY)
    rw [hZbot] at hZcardW
    simp at hZcardW
  · exact Or.inl h
  · exact Or.inr h

private theorem kmodel49_natA5Sec (hI : Inputs49) {K W : Subgroup G}
    (hperf : ⁅K, K⁆ = K) (hWle : W ≤ K) (hWn : K ≤ Subgroup.normalizer (W : Set G))
    (hWq8 : IsQ8D8 W) [(W.subgroupOf K).Normal]
    (hsimple : IsSimpleGroup (↥K ⧸ W.subgroupOf K))
    (hWalt : CFSG.Quasithin.IsAlt 5 (↥K ⧸ W.subgroupOf K)) :
    NatA5Sec K W (W ⊓ Subgroup.centralizer (W : Set G)) := by
  have hKZW : ⁅K, W ⊓ Subgroup.centralizer (W : Set G)⁆ = ⊥ :=
    commutator_eq_bot_of_isQ8D8_normal hWn hWq8
  have hZcentW : W ⊓ Subgroup.centralizer (W : Set G) ≤ Subgroup.centralizer (K : Set G) :=
    Subgroup.le_centralizer_iff.mpr ((Subgroup.commutator_eq_bot_iff_le_centralizer).mp hKZW)
  have hZnW : K ≤ Subgroup.normalizer (W ⊓ Subgroup.centralizer (W : Set G) : Set G) :=
    (Subgroup.le_centralizer_iff.mp hZcentW).trans
      (Subgroup.centralizer_le_normalizer (W ⊓ Subgroup.centralizer (W : Set G) : Set G))
  have hφ := kmodel49_exists_phi hperf hWle hWn hWq8 hsimple hWalt
  obtain ⟨d, hdK, hdord⟩ := exists_orderOf_eq_three_of_alt5 hWle hWq8 hWalt
  have hd8 : Nat.card ↥(W ⊓ Subgroup.centralizer ({d} : Set G)) = 8 :=
    card_inf_centralizer_singleton_eq_eight hI hperf hWle hWn hWq8 hsimple hdK hdord
  have hsup_eq := kmodel49_centre_le_centralizer_singleton hZcentW hdK
  obtain ⟨-, ζ, hζW, hζ1, hcen, hsq⟩ := hWq8.facts
  have hZmem : ∀ z : G, z ∈ W ⊓ Subgroup.centralizer (W : Set G) ↔ z = 1 ∨ z = ζ :=
    kmodel_zeta_mem_inf_centralizer_iff hζW hcen
  have hW2 : IsPGroup 2 W := IsPGroup.of_card (n := 5) (hWq8.facts.1.trans (by norm_num))
  have hZcardW : Nat.card ↥(W ⊓ Subgroup.centralizer (W : Set G)) = 2 :=
    isQ8D8_card_inf_centralizer hWq8
  have hcardW : Nat.card W = 32 := hWq8.facts.1
  refine hI.2.2 G K W (W ⊓ Subgroup.centralizer (W : Set G)) inf_le_left hW2 hWn hZnW
    ?_ ?_ ?_ ?_ hφ ⟨d, hdK, hdord, ?_⟩
  · intro x hx y hy
    rw [← isQ8D8_commutator_eq_inf_centralizer hWq8]
    exact Subgroup.commutator_mem_commutator hx hy
  · intro x hx
    rw [pow_two]
    rcases hsq x hx with h | h
    · rw [h]; exact (W ⊓ Subgroup.centralizer (W : Set G)).one_mem
    · rw [h]; exact (hZmem ζ).mpr (Or.inr rfl)
  · have h1 := Subgroup.relIndex_mul_card (H := W ⊓ Subgroup.centralizer (W : Set G)) (K := W)
    rw [inf_eq_left.mpr inf_le_left, hZcardW, hcardW] at h1
    omega
  · exact kmodel49_invariant_subgroups_of_centralizer hI hperf hWle hWn hWq8 hsimple hWalt
      hZcardW
  · rw [hsup_eq]
    have h2 := Subgroup.relIndex_mul_card (H := W ⊓ Subgroup.centralizer ({d} : Set G)) (K := W)
    rw [inf_eq_left.mpr inf_le_left, hd8, hcardW] at h2
    omega

theorem kmodel49 (hI : Inputs49) {K : Subgroup G}
    (hK : CFSG.Quasithin.IsExt ↥K
      (fun V _ => CFSG.GH74.Uniqueness.SU.SU5.IsQ8D8 (⊤ : Subgroup V))
      (fun Y _ => CFSG.Quasithin.IsAlt 5 Y)) (hperf : ⁅K, K⁆ = K) :
    ∃ V : Subgroup G, V ≤ K ∧ K ≤ Subgroup.normalizer (V : Set G) ∧
      CFSG.GH74.Uniqueness.SU.SU5.IsQ8D8 V ∧ V = CFSG.Open.pCoreOf 2 K ∧
      Nat.card ↥(V ⊓ Subgroup.centralizer (V : Set G)) = 2 ∧
      ⁅K, V ⊓ Subgroup.centralizer (V : Set G)⁆ = ⊥ ∧
      (∀ Y : Subgroup G, Y ≤ V → K ≤ Subgroup.normalizer (Y : Set G) →
        Y = ⊥ ∨ Y = V ⊓ Subgroup.centralizer (V : Set G) ∨ Y = V) ∧
      NatA5Sec K V (V ⊓ Subgroup.centralizer (V : Set G)) ∧
      ∀ z ∈ K, orderOf z = 3 → Nat.card ↥(V ⊓ Subgroup.centralizer ({z} : Set G)) = 8 := by
  unfold CFSG.Quasithin.IsExt at hK
  obtain ⟨V₀, hV₀n, hV₀q8, hV₀alt⟩ := hK
  obtain ⟨W, hWle, hWnormal, hWq8, hWpCore, hWsub⟩ := kmodel49_setup hV₀n hV₀q8 hV₀alt
  haveI : (W.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWle).mpr hWnormal
  have hWalt : CFSG.Quasithin.IsAlt 5 (↥K ⧸ W.subgroupOf K) := by
    obtain ⟨e⟩ := hV₀alt
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hWsub).trans e⟩
  have hsimple : IsSimpleGroup (↥K ⧸ W.subgroupOf K) := isSimpleGroup_of_isAlt5 hWalt
  refine ⟨W, hWle, hWnormal, hWq8, hWpCore, ?_, ?_, ?_, ?_, ?_⟩
  · exact isQ8D8_card_inf_centralizer hWq8
  · exact commutator_eq_bot_of_isQ8D8_normal hWnormal hWq8
  · intro Y hYle hYn
    exact invariant_subgroups_eq hI hperf hWle hWnormal hWq8 hsimple
      (exists_orderOf_eq_five_of_alt5 hWle hWq8 hWalt) Y hYle hYn
  · exact kmodel49_natA5Sec hI hperf hWle hWnormal hWq8 hsimple hWalt
  · intro z hz hzord
    exact card_inf_centralizer_singleton_eq_eight hI hperf hWle hWnormal hWq8 hsimple hz hzord

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49
