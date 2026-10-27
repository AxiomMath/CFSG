module

public import CFSG.OddTranspositions.PartFour.LineVmem
public import CFSG.CGT.T75F.E710Fib
public import CFSG.OddTranspositions.PartFour.LineStabilizer

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem blockImage_cimg (hC : HypothesisC D) (γ : Set G) {x : G}
    (hx : x ∈ Malpha D hC.alpha) : blockImage hC (cimg x γ) = blockImage hC γ := by
  let H := Halpha D hC.alpha
  let R := CFSG.solvableRadical H
  let mk := QuotientGroup.mk' R
  obtain ⟨r, hrR, hrx⟩ := Subgroup.mem_map.mp hx
  have hrx' : (r : G) = x := hrx
  have hxH : x ∈ H := by
    rw [← hrx']
    exact (Subgroup.map_subtype_le R) (Subgroup.mem_map_of_mem H.subtype hrR)
  have hmk : mk r = 1 := (QuotientGroup.eq_one_iff r).mpr hrR
  ext z
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨a, haγ, ha⟩ := hc
    have haH : a ∈ H := by
      have h : a = x⁻¹ * (c : G) * x := by rw [← ha]; group
      rw [h]
      exact H.mul_mem (H.mul_mem (H.inv_mem hxH) c.2) hxH
    refine ⟨⟨a, haH⟩, haγ, ?_⟩
    have hceq : c = r * ⟨a, haH⟩ * r⁻¹ := by
      apply Subtype.ext
      show (c : G) = (r : G) * a * (r : G)⁻¹
      rw [hrx', ← ha]
    rw [hceq, map_mul, map_mul, map_inv, hmk]
    group
  · rintro ⟨c, hc, rfl⟩
    refine ⟨r * c * r⁻¹, ⟨(c : G), hc, ?_⟩, ?_⟩
    · show x * (c : G) * x⁻¹ = (r : G) * (c : G) * (r : G)⁻¹
      rw [hrx']
    · rw [map_mul, map_mul, map_inv, hmk]
      group

theorem exists_cimg_eq_of_blockImage_inter_nonempty (h113 : PartThree.Theorem11_3)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    {γ δ : Set G} (hγ : γ ∈ Dalpha D hC.alpha) (hδ : δ ∈ Dalpha D hC.alpha)
    (h : (blockImage hC γ ∩ blockImage hC δ).Nonempty) :
    ∃ x ∈ Malpha D hC.alpha, cimg x γ = δ := by
  obtain ⟨z, hzγ, hzδ⟩ := h
  obtain ⟨c₁, hc₁, hz₁⟩ := hzγ
  obtain ⟨c₂, hc₂, hz₂⟩ := hzδ
  have hmk : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c₁ =
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c₂ := hz₁.trans hz₂.symm
  have hR : c₁⁻¹ * c₂ ∈ CFSG.solvableRadical (Halpha D hC.alpha) :=
    (QuotientGroup.eq).mp hmk
  have hb : c₁ ∈ DstarH hC := ⟨γ, hγ, hc₁⟩
  have hc : c₂ ∈ DstarH hC := ⟨δ, hδ, hc₂⟩
  obtain ⟨y, hyQ, hye⟩ :=
    exists_pCore_conj_eq_of_inv_mul_mem h113 hC hrad hn3 hHns hb hc hR
  refine ⟨(y : G), ?_, ?_⟩
  · exact Subgroup.mem_map_of_mem (Halpha D hC.alpha).subtype
      (CFSG.pCore_le_solvableRadical 2 (Halpha D hC.alpha) hyQ)
  · have hclass : cimg (y : G) γ ∈ blockClass hC.alpha :=
      cimg_mem_blockClass_iff.mpr hγ.1
    have hmeet : (cimg (y : G) γ ∩ δ).Nonempty := by
      refine ⟨(c₂ : G), ⟨(c₁ : G), hc₁, ?_⟩, hc₂⟩
      simpa using congrArg Subtype.val hye
    exact eq_of_mem_of_mem_blockClass hC.isBlock_alpha hclass hδ.1 hmeet

theorem ncard_blockImage (h89 : PartThree.Lemma8_9) (h113 : PartThree.Theorem11_3)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    {γ : Set G} (hγ : γ ∈ Dalpha D hC.alpha) :
    (blockImage hC γ).ncard = γ.ncard := by
  let H := Halpha D hC.alpha
  let R := CFSG.solvableRadical H
  let mk := QuotientGroup.mk' R
  let S : Set H := {c : H | (c : G) ∈ γ}
  have hS : S = Subtype.val ⁻¹' γ := by
    ext c
    rfl
  have hinj : Set.InjOn mk S := by
    intro c hc c' hc' hEq
    have hR : c⁻¹ * c' ∈ R := (QuotientGroup.eq).mp hEq
    have hM : (c : G)⁻¹ * (c' : G) ∈ Malpha D hC.alpha := by
      change (c : G)⁻¹ * (c' : G) ∈ (CFSG.solvableRadical H).map H.subtype
      simpa using Subgroup.mem_map_of_mem H.subtype hR
    exact Subtype.ext
      (eq_of_mem_of_inv_mul_mem_Malpha h89 h113 hC hrad hW hn3 hHns hγ hc hc' hM)
  have hsub : γ ⊆ Set.range (Subtype.val : H → G) := by
    intro x hx
    exact ⟨⟨x, Subgroup.subset_closure (show x ∈ DalphaStar D hC.alpha from ⟨γ, hγ, hx⟩)⟩, rfl⟩
  calc (blockImage hC γ).ncard = S.ncard := Set.InjOn.ncard_image hinj
    _ = (Subtype.val ⁻¹' γ).ncard := by rw [hS]
    _ = γ.ncard :=
      Set.ncard_preimage_of_injective_subset_range
        (f := (Subtype.val : H → G)) Subtype.val_injective hsub

theorem blockImage_eq_of_inter_nonempty (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    {β γ δ : Set G} (hβ : β ∈ Dalpha D hC.alpha)
    (hγ : γ ∈ blockLine D hC.alpha β \ {hC.alpha})
    (hδ : δ ∈ blockLine D hC.alpha β \ {hC.alpha})
    (h : (blockImage hC γ ∩ blockImage hC δ).Nonempty) :
    blockImage hC γ = blockImage hC δ := by
  have hγD : γ ∈ Dalpha D hC.alpha :=
    mem_Dalpha_of_mem_blockLine hC.isBlock_alpha.subset hβ hγ.1 (by simpa using hγ.2)
  have hδD : δ ∈ Dalpha D hC.alpha :=
    mem_Dalpha_of_mem_blockLine hC.isBlock_alpha.subset hβ hδ.1 (by simpa using hδ.2)
  obtain ⟨x, hx, hxδ⟩ :=
    exists_cimg_eq_of_blockImage_inter_nonempty h113 hC hrad hn3 hHns hγD hδD h
  rw [← hxδ]
  exact (blockImage_cimg hC γ hx).symm

theorem ncard_blockImage_eq_ncard_of_mem_blockLine_diff (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    {β γ : Set G} (hβ : β ∈ Dalpha D hC.alpha)
    (hγ : γ ∈ blockLine D hC.alpha β \ {hC.alpha}) :
    (blockImage hC γ).ncard = β.ncard := by
  have hγD : γ ∈ Dalpha D hC.alpha :=
    mem_Dalpha_of_mem_blockLine hC.isBlock_alpha.subset hβ hγ.1 (by simpa using hγ.2)
  rw [ncard_blockImage h89 h113 hC hrad hW hn3 hHns hγD]
  obtain ⟨g, hg⟩ := mem_blockClass_iff.mp hγD.1
  obtain ⟨k, hk⟩ := mem_blockClass_iff.mp hβ.1
  rw [hg, hk, ncard_cimg, ncard_cimg]

theorem setOf_blockImage_eq_eq_orbit (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    {β γ : Set G} (hβ : β ∈ Dalpha D hC.alpha) (hγ : γ ∈ blockLine D hC.alpha β \ {hC.alpha}) :
    {δ | δ ∈ blockLine D hC.alpha β \ {hC.alpha} ∧ blockImage hC δ = blockImage hC γ} =
      (fun x => cimg x γ) '' (Malpha D hC.alpha : Set G) := by
  have hγD : γ ∈ Dalpha D hC.alpha :=
    mem_Dalpha_of_mem_blockLine hC.isBlock_alpha.subset hβ hγ.1 (by simpa using hγ.2)
  ext δ
  constructor
  · intro hδ
    have hδD : δ ∈ Dalpha D hC.alpha :=
      mem_Dalpha_of_mem_blockLine hC.isBlock_alpha.subset hβ hδ.1.1 (by simpa using hδ.1.2)
    have hne : (blockImage hC γ).Nonempty := by
      obtain ⟨c, hc⟩ := nonempty_of_mem_blockClass hC.isBlock_alpha.nonempty hγD.1
      let cH : Halpha D hC.alpha :=
        ⟨c, Subgroup.subset_closure (show c ∈ DalphaStar D hC.alpha from ⟨γ, hγD, hc⟩)⟩
      exact ⟨QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) cH, cH, hc, rfl⟩
    have hinter : (blockImage hC γ ∩ blockImage hC δ).Nonempty := by
      rw [hδ.2, Set.inter_self]
      exact hne
    obtain ⟨x, hx, hxδ⟩ :=
      exists_cimg_eq_of_blockImage_inter_nonempty h113 hC hrad hn3 hHns hγD hδD hinter
    exact ⟨x, hx, hxδ⟩
  · rintro ⟨x, hx, hxγ⟩
    rw [← hxγ]
    refine ⟨⟨cimg_mem_blockLine_of_mem_Malpha h113 hC hrad hn3 hβ hγ.1 hx, ?_⟩,
      blockImage_cimg hC γ hx⟩
    intro hEq
    have hxinvM : x⁻¹ ∈ Malpha D hC.alpha := (Malpha D hC.alpha).inv_mem hx
    have hxinvH : x⁻¹ ∈ Halpha D hC.alpha :=
      Subgroup.map_subtype_le (CFSG.solvableRadical (Halpha D hC.alpha)) hxinvM
    have hfix : cimg x⁻¹ hC.alpha = hC.alpha :=
      cimg_eq_self_of_mem_normalizer (Halpha_le_normalizer_block D hC.alpha hxinvH)
    have hEq' : cimg x γ = hC.alpha := hEq
    have hα : γ = hC.alpha := by
      rw [← cimg_inv_cimg x γ, hEq', hfix]
    exact hγ.2 (by simpa using hα)

theorem ncard_blockLine_diff_eq (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) :
    (blockLine D hC.alpha β \ {hC.alpha}).ncard =
      (blockImage hC '' (blockLine D hC.alpha β \ {hC.alpha})).ncard *
        ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)).ncard := by
  have hmaps : ∀ a ∈ blockLine D hC.alpha β \ {hC.alpha},
      blockImage hC a ∈ blockImage hC '' (blockLine D hC.alpha β \ {hC.alpha}) :=
    fun a ha => ⟨a, ha, rfl⟩
  have hfib : ∀ b ∈ blockImage hC '' (blockLine D hC.alpha β \ {hC.alpha}),
      {a | a ∈ blockLine D hC.alpha β \ {hC.alpha} ∧ blockImage hC a = b}.ncard =
        ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)).ncard := by
    rintro b ⟨γ, hγ, rfl⟩
    have hγD : γ ∈ Dalpha D hC.alpha :=
      mem_Dalpha_of_mem_blockLine hC.isBlock_alpha.subset hβ hγ.1 (by simpa using hγ.2)
    rw [setOf_blockImage_eq_eq_orbit h113 hC hrad hn3 hHns hβ hγ,
      ncard_orbit_Malpha_eq hC hβ hγD]
  exact CFSG.CGT.T75F.ncard_eq_mul_of_fibres
    (blockLine D hC.alpha β \ {hC.alpha})
    (blockImage hC '' (blockLine D hC.alpha β \ {hC.alpha}))
    (blockImage hC) hmaps
    ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)).ncard hfib

theorem blockImage_exists_unique (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) {Δ : Set (Set G)}
    (hΔ : ∀ γ ∈ Δ, γ ∈ blockLine D hC.alpha β \ {hC.alpha})
    {z : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hz : z ∈ ⋃ γ ∈ Δ, blockImage hC γ) :
    ∃ T ∈ blockImage hC '' Δ, z ∈ T ∧
      ∀ T' ∈ blockImage hC '' Δ, z ∈ T' → T' = T := by
  obtain ⟨γ, hzγ⟩ := Set.mem_iUnion.mp hz
  obtain ⟨hγ, hzγ'⟩ := Set.mem_iUnion.mp hzγ
  refine ⟨blockImage hC γ, ⟨γ, hγ, rfl⟩, hzγ', ?_⟩
  rintro T' ⟨δ, hδ, rfl⟩ hzT'
  exact (blockImage_eq_of_inter_nonempty h113 hC hrad hn3 hHns
    (β := β) (γ := γ) (δ := δ) hβ (hΔ γ hγ) (hΔ δ hδ) ⟨z, hzγ', hzT'⟩).symm

theorem blockImage_iUnion_unique (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) {Δ : Set (Set G)}
    (hΔ : ∀ γ ∈ Δ, γ ∈ blockLine D hC.alpha β \ {hC.alpha})
    {z : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hz : z ∈ ⋃ γ ∈ Δ, blockImage hC γ) :
    ∃ T ∈ blockImage hC '' Δ, z ∈ T ∧
      (⋃₀ {T' | T' ∈ blockImage hC '' Δ ∧ z ∈ T'}) = T := by
  obtain ⟨T0, hT0, hzT0, huniq⟩ :=
    blockImage_exists_unique h113 hC hrad hn3 hHns hβ hΔ hz
  refine ⟨T0, hT0, hzT0, ?_⟩
  have hset : {T' | T' ∈ blockImage hC '' Δ ∧ z ∈ T'} = {T0} := by
    ext T'
    constructor
    · rintro ⟨hT', hzT'⟩
      exact Set.mem_singleton_iff.mpr (huniq T' hT' hzT')
    · intro h
      rw [Set.mem_singleton_iff] at h
      rw [h]
      exact ⟨hT0, hzT0⟩
  show (⋃₀ {T' | T' ∈ blockImage hC '' Δ ∧ z ∈ T'}) = T0
  rw [hset]
  exact Set.sUnion_singleton _

theorem blockImage_fibre_ncard (h89 : PartThree.Lemma8_9) (h113 : PartThree.Theorem11_3)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) {Δ : Set (Set G)}
    (hΔ : ∀ γ ∈ Δ, γ ∈ blockLine D hC.alpha β \ {hC.alpha})
    {T : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))}
    (hT : T ∈ blockImage hC '' Δ) :
    {z | z ∈ ⋃ γ ∈ Δ, blockImage hC γ ∧
      (⋃₀ {T' | T' ∈ blockImage hC '' Δ ∧ z ∈ T'}) = T}.ncard = β.ncard := by
  obtain ⟨γ, hγ, rfl⟩ := hT
  have hcard : (blockImage hC γ).ncard = β.ncard :=
    ncard_blockImage_eq_ncard_of_mem_blockLine_diff h89 h113 hC hrad hW hn3 hHns hβ (hΔ γ hγ)
  have hEq : {z | z ∈ ⋃ γ ∈ Δ, blockImage hC γ ∧
      (⋃₀ {T' | T' ∈ blockImage hC '' Δ ∧ z ∈ T'}) = blockImage hC γ} =
        blockImage hC γ := by
    ext z
    constructor
    · rintro ⟨hzV, hfz⟩
      obtain ⟨T0, -, hzT0, hfT0⟩ :=
        blockImage_iUnion_unique h113 hC hrad hn3 hHns hβ hΔ hzV
      rw [hfz] at hfT0
      rw [hfT0]
      exact hzT0
    · intro hzγ
      have hzV : z ∈ ⋃ γ ∈ Δ, blockImage hC γ :=
        Set.mem_iUnion.mpr ⟨γ, Set.mem_iUnion.mpr ⟨hγ, hzγ⟩⟩
      refine ⟨hzV, ?_⟩
      obtain ⟨T0, hT0, hzT0, hfT0⟩ :=
        blockImage_iUnion_unique h113 hC hrad hn3 hHns hβ hΔ hzV
      obtain ⟨T1, -, -, huniq⟩ :=
        blockImage_exists_unique h113 hC hrad hn3 hHns hβ hΔ hzV
      have hT0eq : T0 = T1 := huniq T0 hT0 hzT0
      have hblockeq : blockImage hC γ = T1 := huniq _ ⟨γ, hγ, rfl⟩ hzγ
      rw [hfT0, hT0eq, hblockeq]
  rw [hEq]
  exact hcard

theorem ncard_iUnion_blockImage (h89 : PartThree.Lemma8_9) (h113 : PartThree.Theorem11_3)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) :
    (⋃ γ ∈ blockLine D hC.alpha β \ {hC.alpha}, blockImage hC γ).ncard =
      (blockImage hC '' (blockLine D hC.alpha β \ {hC.alpha})).ncard * β.ncard := by
  let H := Halpha D hC.alpha
  let R := CFSG.solvableRadical H
  let Δ : Set (Set G) := blockLine D hC.alpha β \ {hC.alpha}
  let P : Set (Set (H ⧸ R)) := blockImage hC '' Δ
  let f : H ⧸ R → Set (H ⧸ R) := fun z => ⋃₀ {T | T ∈ P ∧ z ∈ T}
  have hΔ : ∀ γ ∈ Δ, γ ∈ blockLine D hC.alpha β \ {hC.alpha} := fun _ hγ => hγ
  have hmaps : ∀ z ∈ ⋃ γ ∈ Δ, blockImage hC γ, f z ∈ P := by
    intro z hz
    obtain ⟨T, hT, -, hfT⟩ :=
      blockImage_iUnion_unique h113 hC hrad hn3 hHns hβ hΔ hz
    change (⋃₀ {T' | T' ∈ P ∧ z ∈ T'}) ∈ P
    rw [hfT]
    exact hT
  have hfib : ∀ T ∈ P, {z | z ∈ ⋃ γ ∈ Δ, blockImage hC γ ∧ f z = T}.ncard = β.ncard := by
    intro T hT
    simpa only [f] using
      blockImage_fibre_ncard h89 h113 hC hrad hW hn3 hHns hβ hΔ hT
  have hcount := CFSG.CGT.T75F.ncard_eq_mul_of_fibres
    (⋃ γ ∈ Δ, blockImage hC γ) P f hmaps β.ncard hfib
  simpa only [Δ, P] using hcount

theorem ncard_Vmem_eq (h89 : PartThree.Lemma8_9) (h113 : PartThree.Theorem11_3)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) {b : Halpha D hC.alpha} (hb : (b : G) ∈ β) :
    (Vmem (imageClass hC) (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b)).ncard =
      (blockImage hC '' (blockLine D hC.alpha β \ {hC.alpha})).ncard * β.ncard := by
  rw [← iUnion_blockImage_eq_Vmem h89 h113 hC hrad hW hn3 hMZ hβ hb]
  exact ncard_iUnion_blockImage h89 h113 hC hrad hW hn3 hHns hβ

theorem blockLine_diff_eq_orbit_of_singleton (h113 : PartThree.Theorem11_3)
    (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha)
    (hP : blockImage hC '' (blockLine D hC.alpha β \ {hC.alpha}) = {blockImage hC β}) :
    blockLine D hC.alpha β \ {hC.alpha} =
      (fun x => cimg x β) '' (Malpha D hC.alpha : Set G) := by
  have hβℓ : β ∈ blockLine D hC.alpha β := right_mem_blockLine hβ.1 hβ.2.1
  have hβΔ : β ∈ blockLine D hC.alpha β \ {hC.alpha} := ⟨hβℓ, by simpa using hβ.2.2.1⟩
  have hset := setOf_blockImage_eq_eq_orbit h113 hC hrad hn3 hHns hβ hβΔ
  apply Set.Subset.antisymm
  · intro γ hγ
    have hImg : blockImage hC γ = blockImage hC β := by
      have hmem : blockImage hC γ ∈ blockImage hC '' (blockLine D hC.alpha β \ {hC.alpha}) :=
        ⟨γ, hγ, rfl⟩
      rw [hP] at hmem
      simpa using hmem
    have hmem : γ ∈ {δ | δ ∈ blockLine D hC.alpha β \ {hC.alpha} ∧
        blockImage hC δ = blockImage hC β} := ⟨hγ, hImg⟩
    rwa [hset] at hmem
  · intro γ hγ
    have hmem : γ ∈ {δ | δ ∈ blockLine D hC.alpha β \ {hC.alpha} ∧
        blockImage hC δ = blockImage hC β} := by
      rwa [hset]
    exact hmem.1

theorem ncard_blockImage_quotient_eq_one (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    (hV : ∀ v ∈ imageClass hC, Odd (Vmem (imageClass hC) v).ncard)
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) {b : Halpha D hC.alpha} (hb : (b : G) ∈ β)
    {e : ℕ} (he : (blockLine D hC.alpha β).ncard = 2 ^ e + 1) :
    (blockImage hC '' (blockLine D hC.alpha β \ {hC.alpha})).ncard = 1 := by
  let Δ : Set (Set G) := blockLine D hC.alpha β \ {hC.alpha}
  set r : ℕ := (blockImage hC '' Δ).ncard with hrdef
  have hαℓ : hC.alpha ∈ blockLine D hC.alpha β := left_mem_blockLine hC.isBlock_alpha.subset
  have hΔcard : Δ.ncard = 2 ^ e := by
    change (blockLine D hC.alpha β \ {hC.alpha}).ncard = 2 ^ e
    rw [Set.ncard_diff_singleton_of_mem (s := blockLine D hC.alpha β) hαℓ, he]
    exact Nat.add_sub_cancel _ 1
  have hVodd : Odd (Vmem (imageClass hC)
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b)).ncard :=
    hV _ ⟨b, ⟨β, hβ, hb⟩, rfl⟩
  have hitem6 := ncard_Vmem_eq h89 h113 hC hrad hW hn3 hMZ hHns hβ hb
  have hrodd : Odd r := by
    have h' : Odd ((blockImage hC '' Δ).ncard * β.ncard) := by
      rw [← hitem6]
      exact hVodd
    exact Nat.Odd.of_mul_left h'
  have hitem5 := ncard_blockLine_diff_eq h113 hC hrad hn3 hHns hβ
  have hΔeq : Δ.ncard = r * ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)).ncard := by
    rw [hrdef]
    exact hitem5
  have hdvd : r ∣ 2 ^ e := by
    refine ⟨((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)).ncard, ?_⟩
    rw [← hΔcard, hΔeq]
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hi0 : i = 0 := by
    by_contra hne
    have h2 : 2 ∣ 2 ^ i := by
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hne
      exact ⟨2 ^ j, by rw [pow_succ]; ring⟩
    exact (hi ▸ hrodd).not_two_dvd_nat h2
  have hr1 : r = 1 := by rw [hi, hi0, pow_zero]
  rw [hrdef]
  exact hr1

theorem blockLine_eq_insert_orbit (h89 : PartThree.Lemma8_9) (h113 : PartThree.Theorem11_3)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    (hV : ∀ v ∈ imageClass hC, Odd (Vmem (imageClass hC) v).ncard)
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) {e : ℕ}
    (he : (blockLine D hC.alpha β).ncard = 2 ^ e + 1) :
    blockLine D hC.alpha β =
      insert hC.alpha ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)) := by
  let H := Halpha D hC.alpha
  let R := CFSG.solvableRadical H
  let Δ : Set (Set G) := blockLine D hC.alpha β \ {hC.alpha}
  have hαℓ : hC.alpha ∈ blockLine D hC.alpha β := left_mem_blockLine hC.isBlock_alpha.subset
  have hβℓ : β ∈ blockLine D hC.alpha β := right_mem_blockLine hβ.1 hβ.2.1
  have hβΔ : β ∈ Δ := ⟨hβℓ, by simpa using hβ.2.2.1⟩
  obtain ⟨b0, hb0⟩ := nonempty_of_mem_blockClass hC.isBlock_alpha.nonempty hβ.1
  let b : H := ⟨b0, Subgroup.subset_closure
    (show b0 ∈ DalphaStar D hC.alpha from ⟨β, hβ, hb0⟩)⟩
  have hr1 : (blockImage hC '' Δ).ncard = 1 :=
    ncard_blockImage_quotient_eq_one h89 h113 hC hrad hW hn3 hMZ hHns hV
      (b := b) hβ hb0 he
  have hPsingle : blockImage hC '' Δ = {blockImage hC β} := by
    obtain ⟨T, hT⟩ := Set.ncard_eq_one.mp hr1
    have hmem : blockImage hC β ∈ ({T} : Set (Set (H ⧸ R))) := hT ▸ ⟨β, hβΔ, rfl⟩
    rw [Set.mem_singleton_iff] at hmem
    rw [← hmem] at hT
    exact hT
  have hΔEq : Δ = (fun x => cimg x β) '' (Malpha D hC.alpha : Set G) :=
    blockLine_diff_eq_orbit_of_singleton h113 hC hrad hn3 hHns hβ hPsingle
  rw [hΔEq.symm]
  change blockLine D hC.alpha β = insert hC.alpha (blockLine D hC.alpha β \ {hC.alpha})
  rw [Set.insert_diff_singleton, Set.insert_eq_of_mem hαℓ]

theorem ncard_orbit_eq_two_pow (h89 : PartThree.Lemma8_9) (h113 : PartThree.Theorem11_3)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    (hV : ∀ v ∈ imageClass hC, Odd (Vmem (imageClass hC) v).ncard)
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) {e : ℕ}
    (he : (blockLine D hC.alpha β).ncard = 2 ^ e + 1) :
    ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)).ncard = 2 ^ e := by
  have hitem7 := blockLine_eq_insert_orbit h89 h113 hC hrad hW hn3 hMZ hHns hV hβ he
  have hnot : hC.alpha ∉ (fun x => cimg x β) '' (Malpha D hC.alpha : Set G) := by
    rintro ⟨x, hx, hxα⟩
    have hxα' : cimg x β = hC.alpha := hxα
    have hxinvM : x⁻¹ ∈ Malpha D hC.alpha := (Malpha D hC.alpha).inv_mem hx
    have hxinvH : x⁻¹ ∈ Halpha D hC.alpha :=
      Subgroup.map_subtype_le (CFSG.solvableRadical (Halpha D hC.alpha)) hxinvM
    have hfix : cimg x⁻¹ hC.alpha = hC.alpha :=
      cimg_eq_self_of_mem_normalizer (Halpha_le_normalizer_block D hC.alpha hxinvH)
    have hβeq : β = hC.alpha := by
      calc β = cimg x⁻¹ (cimg x β) := (cimg_inv_cimg x β).symm
        _ = cimg x⁻¹ hC.alpha := by rw [hxα']
        _ = hC.alpha := hfix
    exact hβ.2.2.1 hβeq
  have h1 : ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)).ncard + 1 = 2 ^ e + 1 := by
    rw [← Set.ncard_insert_of_notMem hnot, ← hitem7, he]
  exact Nat.add_right_cancel h1

end CFSG.OddTranspositions.PartFour
