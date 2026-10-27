module

public import CFSG.OddTranspositions.PartFour.Fourteen.OFour.Statements
import CFSG.OddTranspositions.PartThree.Eleven.Primitive
import CFSG.OddTranspositions.PartThree.Eleven.GroupLemmas
import CFSG.OddTranspositions.PartThree.HalphaCentralizer
import CFSG.OddTranspositions.FusionStep
import CFSG.OddTranspositions.AalphaCommute
import CFSG.Timmesfeld.Bridge.Asc72ElemCompQuot
import CFSG.GroupTheory.ClosureDiffImage

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
  CFSG.Timmesfeld.Bridge.OddTransp


variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem solvableRadical_eq_center_of_le_center {H : Type} [Group H]
    (h : CFSG.solvableRadical H ≤ Subgroup.center H) :
    CFSG.solvableRadical H = Subgroup.center H :=
  le_antisymm h otg2_center_le_solvableRadical

theorem index_commutator_Halpha_le_two (hC : HypothesisC D) :
    (commutator (Halpha D hC.alpha)).index ≤ 2 :=
  (⟨DstarH_isClass hC, DstarH_isOddTransp hC, DstarH_closure_eq_top hC⟩ :
    Setup (Halpha D hC.alpha) (DstarH hC)).index_commutator_le_two

theorem solvableRadical_le_commutator_Halpha (hC : HypothesisC D)
    (hF : O4CaseAFacts
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) (imageClass hC)) :
    CFSG.solvableRadical (Halpha D hC.alpha) ≤ commutator (Halpha D hC.alpha) :=
  CFSG.OddTranspositions.PartThree.le_commutator_of_index_commutator_quotient _
    (index_commutator_Halpha_le_two hC) hF.index_two

theorem commutator_eq_commutator_commutator_sup_solvableRadical (hC : HypothesisC D)
    (hF : O4CaseAFacts
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) (imageClass hC)) :
    commutator (Halpha D hC.alpha) =
      ⁅commutator (Halpha D hC.alpha), commutator (Halpha D hC.alpha)⁆ ⊔
        CFSG.solvableRadical (Halpha D hC.alpha) := by
  classical
  let H := Halpha D hC.alpha
  let K : Subgroup H := CFSG.solvableRadical H
  let π : H →* H ⧸ K := QuotientGroup.mk' K
  let H1 : Subgroup H := commutator H
  let H2 : Subgroup H := ⁅H1, H1⁆
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective K
  have hKle : K ≤ H1 := solvableRadical_le_commutator_Halpha hC hF
  have hker_le : π.ker ≤ H1 := by
    rwa [QuotientGroup.ker_mk']
  have hmapH1 : H1.map π = commutator (H ⧸ K) :=
    TauCeti.Subgroup.map_commutator_eq_commutator hπsurj
  have hmapH2 : H2.map π = commutator (H ⧸ K) := by
    dsimp only [H2]
    rw [Subgroup.map_commutator, hmapH1, hF.perfect]
  calc H1 = (H1.map π).comap π := (Subgroup.comap_map_eq_self hker_le).symm
    _ = (H2.map π).comap π := by rw [hmapH2, hmapH1]
    _ = H2 ⊔ π.ker := Subgroup.comap_map_eq π H2
    _ = H2 ⊔ K := by rw [QuotientGroup.ker_mk']

theorem commutator_commutator_Halpha_eq (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤
      Subgroup.center (Halpha D hC.alpha))
    (hF : O4CaseAFacts
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) (imageClass hC)) :
    ⁅commutator (Halpha D hC.alpha), commutator (Halpha D hC.alpha)⁆ =
      commutator (Halpha D hC.alpha) := by
  classical
  let H := Halpha D hC.alpha
  let K : Subgroup H := CFSG.solvableRadical H
  let H1 : Subgroup H := commutator H
  let H2 : Subgroup H := ⁅H1, H1⁆
  have hH1 : H1 = H2 ⊔ K :=
    commutator_eq_commutator_commutator_sup_solvableRadical hC hF
  let Y := H ⧸ H2
  let π₂ : H →* Y := QuotientGroup.mk' H2
  have hπ₂surj : Function.Surjective π₂ := QuotientGroup.mk'_surjective H2
  have hmapY : commutator Y = H1.map π₂ :=
    (TauCeti.Subgroup.map_commutator_eq_commutator (f := π₂) hπ₂surj).symm
  have hKmap_center : K.map π₂ ≤ Subgroup.center Y := by
    intro y hy
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hy
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨h, rfl⟩ := hπ₂surj z
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subgroup.mem_center_iff.mp (hMZ hk) h
  have hH2map : H2.map π₂ = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have hEq : H1.map π₂ = K.map π₂ := by
    calc H1.map π₂ = (H2 ⊔ K).map π₂ := congrArg (Subgroup.map π₂) hH1
      _ = H2.map π₂ ⊔ K.map π₂ := Subgroup.map_sup H2 K π₂
      _ = ⊥ ⊔ K.map π₂ := by rw [hH2map]
      _ = K.map π₂ := bot_sup_eq _
  have hcommY : commutator Y ≤ Subgroup.center Y := by
    rw [hmapY]
    exact hEq.le.trans hKmap_center
  obtain ⟨d₀, hclass⟩ := DstarH_isClass hC
  obtain ⟨c, hc⟩ := image_isClass_quotient hclass H2
  have hgen : Subgroup.closure {g : Y | IsConj c g} = ⊤ := by
    rw [← hc]
    exact image_closure_eq_top_quotient H2 (DstarH_closure_eq_top hC)
  have hcommYall : ∀ a b : Y, a * b = b * a := fun a b =>
    (CFSG.OddTranspositions.PartThree.commute_of_closure_isConj_of_commutator_le_center
      c hgen hcommY a b).eq
  have hYcomm : IsMulCommutative Y := ⟨⟨hcommYall⟩⟩
  have hYbot : commutator Y = ⊥ := (commutator_eq_bot_iff Y).mpr hYcomm
  have hH1leH2 : H1 ≤ H2 := by
    have hbot : H1.map π₂ = ⊥ := by rw [← hmapY]; exact hYbot
    have hle : H1 ≤ π₂.ker := (Subgroup.map_eq_bot_iff H1).mp hbot
    exact hle.trans (le_of_eq (QuotientGroup.ker_mk' H2))
  exact le_antisymm (Subgroup.commutator_le_left H1 H1) hH1leH2

theorem isPerfect_commutator_Halpha (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤
      Subgroup.center (Halpha D hC.alpha))
    (hF : O4CaseAFacts
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) (imageClass hC)) :
    Group.IsPerfect ↥(commutator (Halpha D hC.alpha)) := by
  rw [Subgroup.isPerfect_iff]
  exact commutator_commutator_Halpha_eq hC hMZ hF

theorem solvableRadical_Halpha_eq_bot (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤
      Subgroup.center (Halpha D hC.alpha))
    (hF : O4CaseAFacts
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) (imageClass hC)) :
    CFSG.solvableRadical (Halpha D hC.alpha) = ⊥ := by
  classical
  let H := Halpha D hC.alpha
  let K : Subgroup H := CFSG.solvableRadical H
  let E : Subgroup H := commutator H
  let π : H →* H ⧸ K := QuotientGroup.mk' K
  have hKle : K ≤ E := solvableRadical_le_commutator_Halpha hC hF
  have hmapE : E.map π = commutator (H ⧸ K) :=
    TauCeti.Subgroup.map_commutator_eq_commutator (QuotientGroup.mk'_surjective K)
  let p : ↥E →* ↥(commutator (H ⧸ K)) :=
    (π.comp E.subtype).codRestrict _ fun x => by
      rw [← hmapE]
      exact Subgroup.mem_map_of_mem π x.2
  have hp_surj : Function.Surjective p := by
    intro y
    have hy : (y : H ⧸ K) ∈ E.map π := by
      rw [hmapE]
      exact y.2
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hp_ker : p.ker ≤ Subgroup.center ↥E := by
    intro x hx
    have hx1 : π (x : H) = 1 := congrArg Subtype.val hx
    have hxK : (x : H) ∈ K := by
      rw [← QuotientGroup.eq_one_iff]
      exact hx1
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hMZ hxK) (y : H))
  have hp_perf : commutator ↥E = ⊤ := by
    rw [← Group.isPerfect_def]
    exact isPerfect_commutator_Halpha hC hMZ hF
  have hker_bot : p.ker = ⊥ := hF.cover ↥E p hp_surj hp_ker hp_perf
  refine le_bot_iff.mp ?_
  intro k hk
  have hkE : k ∈ E := hKle hk
  have hkker : (⟨k, hkE⟩ : ↥E) ∈ p.ker := by
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    show π k = 1
    exact (QuotientGroup.eq_one_iff k).mpr hk
  have hbot : (⟨k, hkE⟩ : ↥E) ∈ (⊥ : Subgroup ↥E) := by
    rw [← hker_bot]
    exact hkker
  simpa using hbot

theorem alpha_eq_singleton_of_o4CaseAFacts (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤
      Subgroup.center (Halpha D hC.alpha))
    (hF : O4CaseAFacts
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) (imageClass hC)) :
    hC.alpha = {hC.d} := by
  classical
  let H := Halpha D hC.alpha
  let K : Subgroup H := CFSG.solvableRadical H
  have hKbot : K = ⊥ := solvableRadical_Halpha_eq_bot hC hMZ hF
  have hinj : Set.InjOn (QuotientGroup.mk' K) (DstarH hC) :=
    ((MonoidHom.ker_eq_bot_iff (QuotientGroup.mk' K)).mp (by
      rw [QuotientGroup.ker_mk', hKbot])).injOn
  exact CFSG.OddTranspositions.PartThree.alpha_eq_singleton hC hinj hF.primitive

theorem d_not_mem_Halpha_of_o4CaseAFacts (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤
      Subgroup.center (Halpha D hC.alpha))
    (hF : O4CaseAFacts
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) (imageClass hC)) :
    hC.d ∉ Halpha D hC.alpha := by
  classical
  let H := Halpha D hC.alpha
  intro hdH
  have hdcenter : (⟨hC.d, hdH⟩ : H) ∈ Subgroup.center H := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext
      (Subgroup.mem_centralizer_singleton_iff.mp
        (CFSG.OddTranspositions.PartThree.Halpha_le_centralizer_d hC y.2))
  have hdK : (⟨hC.d, hdH⟩ : H) ∈ CFSG.solvableRadical H := by
    rw [solvableRadical_eq_center_of_le_center hMZ]
    exact hdcenter
  have hKbot : CFSG.solvableRadical H = ⊥ := solvableRadical_Halpha_eq_bot hC hMZ hF
  rw [hKbot] at hdK
  have hd1 : hC.d = 1 := by simpa using hdK
  have hord : orderOf hC.d = 2 := hC.setup.oddT.1 hC.d hC.hd
  rw [hd1, orderOf_one] at hord
  exact absurd hord (by norm_num)

theorem exists_lift_triple_DstarH (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤
      Subgroup.center (Halpha D hC.alpha))
    (hF : O4CaseAFacts
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) (imageClass hC)) :
    ∃ ΛH : Set (Halpha D hC.alpha), ΛH ⊆ DstarH hC ∧
      (∀ a ∈ ΛH, ∀ b ∈ ΛH, Commute a b) ∧
      ∃ vH ∈ ΛH, vH ∈ Subgroup.closure (ΛH \ {vH}) := by
  classical
  let H := Halpha D hC.alpha
  let K : Subgroup H := CFSG.solvableRadical H
  let π : H →* H ⧸ K := QuotientGroup.mk' K
  have hKbot : K = ⊥ := solvableRadical_Halpha_eq_bot hC hMZ hF
  have hinj : Function.Injective π :=
    (MonoidHom.ker_eq_bot_iff π).mp (by rw [QuotientGroup.ker_mk', hKbot])
  obtain ⟨Λ, hΛsub, hΛcomm, v, hvΛ, hvclos⟩ := hF.triple
  have hΛrange : Λ ⊆ Set.range π := by
    intro y hy
    have hy' : y ∈ imageClass hC := hΛsub hy
    rw [imageClass] at hy'
    obtain ⟨x, _, hxy⟩ := hy'
    exact ⟨x, hxy⟩
  obtain ⟨vH, hvHπ⟩ := hΛrange hvΛ
  let ΛH : Set H := {x | π x ∈ Λ}
  have hΛH_sub : ΛH ⊆ DstarH hC := by
    intro x hx
    have hx' : π x ∈ imageClass hC := hΛsub hx
    rw [imageClass] at hx'
    obtain ⟨y, hy, hxy⟩ := hx'
    rw [← hinj hxy]
    exact hy
  have hΛH_comm : ∀ a ∈ ΛH, ∀ b ∈ ΛH, Commute a b := by
    intro a ha b hb
    exact (commute_map_iff hinj).mp (hΛcomm (π a) ha (π b) hb)
  have hvHΛ : vH ∈ ΛH := by
    show π vH ∈ Λ
    rw [hvHπ]
    exact hvΛ
  have hvHclos : vH ∈ Subgroup.closure (ΛH \ {vH}) :=
    CFSG.GroupTheory.mem_closure_preimage_diff_of_injective hinj hΛrange
      (by rw [hvHπ]; exact hvclos)
  exact ⟨ΛH, hΛH_sub, hΛH_comm, vH, hvHΛ, hvHclos⟩

theorem exists_lift_triple_of_o4CaseAFacts (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤
      Subgroup.center (Halpha D hC.alpha))
    (hF : O4CaseAFacts
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) (imageClass hC)) :
    ∃ Λ' : Set G, Λ' ⊆ DalphaStar D hC.alpha ∧
      (∀ a ∈ Λ', ∀ b ∈ Λ', Commute a b) ∧
      ∃ v' ∈ Λ', v' ∈ Subgroup.closure (Λ' \ {v'}) := by
  obtain ⟨ΛH, hΛH_sub, hΛH_comm, vH, hvHΛ, hvHclos⟩ :=
    exists_lift_triple_DstarH hC hMZ hF
  let Λ' : Set G := (Halpha D hC.alpha).subtype '' ΛH
  let v' : G := (vH : G)
  have hΛ'D : Λ' ⊆ DalphaStar D hC.alpha := by
    rintro x ⟨y, hy, rfl⟩
    exact (mem_DstarH_iff hC).mp (hΛH_sub hy)
  have hΛ'comm : ∀ a ∈ Λ', ∀ b ∈ Λ', Commute a b := by
    rintro a ⟨x, hx, rfl⟩ b ⟨y, hy, rfl⟩
    exact (hΛH_comm x hx y hy).map (Halpha D hC.alpha).subtype
  have hv'clos : v' ∈ Subgroup.closure (Λ' \ {v'}) :=
    (CFSG.GroupTheory.mem_closure_image_diff_iff (S := ΛH) (x := vH)
      (Halpha D hC.alpha).subtype_injective).mpr hvHclos
  exact ⟨Λ', hΛ'D, hΛ'comm, v', ⟨vH, hvHΛ, rfl⟩, hv'clos⟩

theorem sylow_inter_D_diff_subset_DalphaStar (hC : HypothesisC D)
    (hα : hC.alpha = {hC.d}) {S : Sylow 2 G} (huS : hC.d ∈ (S : Subgroup G)) :
    ((S : Set G) ∩ D) \ {hC.d} ⊆ DalphaStar D hC.alpha := by
  rintro x ⟨⟨hxS, hxD⟩, hxu⟩
  have hcomm : Commute x hC.d :=
    hC.setup.oddT.commute_of_isPGroup S.isPGroup' hxD hC.hd hxS huS
  have hxunion : x ∈ hC.alpha ∪ DalphaStar D hC.alpha ∪ AalphaStar D hC.alpha :=
    hC.eq_alpha_union ▸ hxD
  rcases hxunion with (hxα | hxE) | hxA
  · exact absurd (Set.mem_singleton_iff.mp (hα ▸ hxα)) hxu
  · exact hxE
  · exact absurd hcomm (not_commute_of_mem_AalphaStar hC hxA hC.d_mem_alpha)

theorem exists_sylow_containing_d_and_lift (hC : HypothesisC D) {Λ' : Set G}
    (hΛ'D : Λ' ⊆ DalphaStar D hC.alpha)
    (hΛ'comm : ∀ a ∈ Λ', ∀ b ∈ Λ', Commute a b) :
    ∃ S : Sylow 2 G, hC.d ∈ (S : Subgroup G) ∧ Λ' ⊆ (S : Subgroup G) := by
  classical
  have hPpair : ({hC.d} ∪ Λ' : Set G).Pairwise Commute := by
    intro a ha b hb _
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · exact Commute.refl _
      · exact (hC.DalphaStar_subset_commute (hΛ'D hb)).2.symm
    · rcases hb with rfl | hb
      · exact (hC.DalphaStar_subset_commute (hΛ'D ha)).2
      · exact hΛ'comm a ha b hb
  have hPsq : ∀ s ∈ ({hC.d} ∪ Λ' : Set G), s * s = 1 := by
    intro s hs
    have h2 : s ^ 2 = 1 := by
      have hord : orderOf s = 2 := by
        rcases hs with rfl | hs
        · exact hC.setup.oddT.1 hC.d hC.hd
        · exact hC.setup.oddT.1 s (DalphaStar_subset hC.isBlock_alpha (hΛ'D hs))
      have := pow_orderOf_eq_one s
      rwa [hord] at this
    simpa [pow_two] using h2
  let P : Subgroup G := Subgroup.closure ({hC.d} ∪ Λ')
  have hP2 : IsPGroup 2 P := isPGroup_closure_of_pairwise hPpair hPsq
  obtain ⟨S, hPS⟩ := hP2.exists_le_sylow
  exact ⟨S, hPS (Subgroup.subset_closure (Or.inl rfl)),
    fun x hx => hPS (Subgroup.subset_closure (Or.inr hx))⟩

theorem false_of_o4CaseAFacts (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤
      Subgroup.center (Halpha D hC.alpha))
    (hF : O4CaseAFacts
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) (imageClass hC)) :
    False := by
  classical
  let H := Halpha D hC.alpha
  have hα : hC.alpha = {hC.d} := alpha_eq_singleton_of_o4CaseAFacts hC hMZ hF
  have hdH : hC.d ∉ H := d_not_mem_Halpha_of_o4CaseAFacts hC hMZ hF
  obtain ⟨Λ', hΛ'D, hΛ'comm, v', hv'Λ', hv'clos⟩ :=
    exists_lift_triple_of_o4CaseAFacts hC hMZ hF
  obtain ⟨S, huS, hΛ'S⟩ := exists_sylow_containing_d_and_lift hC hΛ'D hΛ'comm
  have hΛ'Δ : Λ' ⊆ (S : Set G) ∩ D := fun x hx =>
    ⟨hΛ'S hx, DalphaStar_subset hC.isBlock_alpha (hΛ'D hx)⟩
  have hΔ_subset : ((S : Set G) ∩ D) \ {hC.d} ⊆ DalphaStar D hC.alpha :=
    sylow_inter_D_diff_subset_DalphaStar hC hα huS
  have huΔ : hC.d ∈ (S : Set G) ∩ D := ⟨huS, hC.hd⟩
  obtain ⟨n, hn, hnv⟩ := sylow_inter_D_transitive hC.setup.isClass hC.setup.oddT S
    (e := v') (f := hC.d) (hΛ'Δ hv'Λ') huΔ
  have hsub : Λ' \ {v'} ⊆ ((S : Set G) ∩ D) \ {v'} := fun x hx =>
    ⟨hΛ'Δ hx.1, hx.2⟩
  have hconj_mem : hC.d ∈ Subgroup.closure (((S : Set G) ∩ D) \ {hC.d}) := by
    have h := CFSG.GroupTheory.conj_mem_closure_diff
      (Subgroup.mem_normalizer_iff_conj_image_eq.mp hn) (Subgroup.closure_mono hsub hv'clos)
    rwa [hnv] at h
  have hclosure_sub_H : Subgroup.closure (((S : Set G) ∩ D) \ {hC.d}) ≤ H := by
    rw [Subgroup.closure_le]
    intro x hx
    exact Subgroup.subset_closure (hΔ_subset hx)
  exact hdH (hclosure_sub_H hconj_mem)

end CFSG.OddTranspositions.PartFour
