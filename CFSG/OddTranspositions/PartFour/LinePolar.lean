module

public import CFSG.OddTranspositions.PartFour.LineVmem

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity

@[expose] def lineMem {X : Type*} [Group X] (S : Set X) (v w : X) : Set X :=
  {x | x ∈ S ∧ perpMem S v ∩ perpMem S w ⊆ perpMem S x}

theorem mem_lineMem {X : Type*} [Group X] {S : Set X} {v w x : X} :
    x ∈ lineMem S v w ↔ x ∈ S ∧ perpMem S v ∩ perpMem S w ⊆ perpMem S x := Iff.rfl

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem perpMem_mk_eq_of_mem (h89 : PartThree.Lemma8_9) (h113 : PartThree.Theorem11_3)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {δ : Set G} (hδ : δ ∈ Dalpha D hC.alpha) {d d' : Halpha D hC.alpha} (hd : (d : G) ∈ δ)
    (hd' : (d' : G) ∈ δ) :
    perpMem (imageClass hC) (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) d) =
      perpMem (imageClass hC) (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) d') := by
  have hline : δ ∈ blockLine D hC.alpha δ := right_mem_blockLine hδ.1 hδ.2.1
  have hV := blockImage_subset_Vmem h89 h113 hC hrad hW hn3 hMZ hδ hline hδ.2.2.1
    (b := d) hd
  have hmk : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) d' ∈
      Vmem (imageClass hC) (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) d) :=
    hV ⟨d', hd', rfl⟩
  exact (mem_Vmem.mp hmk).2.symm

theorem mem_Dalpha_of_commute_mk (h89 : PartThree.Lemma8_9) (h113 : PartThree.Theorem11_3)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {β γ : Set G} (hβ : β ∈ Dalpha D hC.alpha) (hγ : γ ∈ Dalpha D hC.alpha)
    {b c : Halpha D hC.alpha} (hb : (b : G) ∈ β) (hc : (c : G) ∈ γ)
    (hbc : Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b)
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c))
    (hne : perpMem (imageClass hC) (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b) ≠
      perpMem (imageClass hC) (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c)) :
    γ ∈ Dalpha D β := by
  have hbStar : b ∈ DstarH hC := ⟨β, hβ, hb⟩
  have hcStar : c ∈ DstarH hC := ⟨γ, hγ, hc⟩
  have hcommH : Commute b c := commute_of_commute_mk h113 hC hrad hn3 hbStar hcStar hbc
  have hcommG : Commute (b : G) (c : G) := hcommH.map (Subgroup.subtype _)
  have hperp : γ ∈ perp D β := mem_perp_of_commute hC hβ.1 hγ.1 hb hc hcommG
  rcases mem_perp_iff.mp hperp with h | h
  · exact h
  · exfalso
    apply hne
    exact perpMem_mk_eq_of_mem h89 h113 hC hrad hW hn3 hMZ hβ hb (h ▸ hc)

theorem alpha_not_mem_blockLine (h89 : PartThree.Lemma8_9) (h113 : PartThree.Theorem11_3)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {β γ : Set G} (hβ : β ∈ Dalpha D hC.alpha) (hγ : γ ∈ Dalpha D hC.alpha)
    {b c : Halpha D hC.alpha} (hb : (b : G) ∈ β) (hc : (c : G) ∈ γ)
    (hbc : Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b)
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c))
    (hne : perpMem (imageClass hC) (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b) ≠
      perpMem (imageClass hC) (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c)) :
    hC.alpha ∉ blockLine D β γ := by
  by_contra hαΛ
  have hγDβ : γ ∈ Dalpha D β :=
    mem_Dalpha_of_commute_mk h89 h113 hC hrad hW hn3 hMZ hβ hγ hb hc hbc hne
  obtain ⟨k, hk⟩ := mem_blockClass_iff.mp hβ.1
  have hα' : (hC.conj k).alpha = β := (HypothesisC.conj_alpha hC k).trans hk.symm
  have hγ' : γ ∈ Dalpha D (hC.conj k).alpha := by rwa [hα']
  have hγline : γ ∈ blockLine D β γ :=
    right_mem_blockLine (mem_blockClass_of_mem_blockClass hβ.1 hγ.1) hγ.2.1
  have hαΛ' : hC.alpha ∈ blockLine D (hC.conj k).alpha γ := by rwa [hα']
  have hγline' : γ ∈ blockLine D (hC.conj k).alpha γ := by rwa [hα']
  have hline := blockLine_eq_of_mem_of_mem (hC.conj k) hγ' hαΛ' hγline'
    (Ne.symm hγ.2.2.1)
  rw [hα'] at hline
  have hβline : β ∈ blockLine D hC.alpha γ := by
    rw [hline]
    exact left_mem_blockLine hβ.2.1
  have hV := blockImage_subset_Vmem h89 h113 hC hrad hW hn3 hMZ hγ hβline hβ.2.2.1
    (b := c) hc
  exact hne (mem_Vmem.mp (hV ⟨b, hb, rfl⟩)).2

theorem mem_Dalpha_of_mem_blockLine_of_ne (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {β γ : Set G} (hβ : β ∈ Dalpha D hC.alpha) (hγ : γ ∈ Dalpha D hC.alpha)
    {b c : Halpha D hC.alpha} (hb : (b : G) ∈ β) (hc : (c : G) ∈ γ)
    (hbc : Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b)
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c))
    (hne : perpMem (imageClass hC) (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b) ≠
      perpMem (imageClass hC) (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c))
    {δ : Set G} (hδ : δ ∈ blockLine D β γ) : δ ∈ Dalpha D hC.alpha := by
  have hαβ : hC.alpha ∈ perp D β :=
    mem_perp_iff.mpr (Or.inl (mem_Dalpha_symm hβ hC.isBlock_alpha.subset))
  have hαγ : hC.alpha ∈ perp D γ :=
    mem_perp_iff.mpr (Or.inl (mem_Dalpha_symm hγ hC.isBlock_alpha.subset))
  have hδperp : δ ∈ perp D hC.alpha := hδ.2 hC.alpha ⟨hαβ, hαγ⟩
  rcases mem_perp_iff.mp hδperp with h | h
  · exact h
  · exact absurd (h ▸ hδ)
      (alpha_not_mem_blockLine h89 h113 hC hrad hW hn3 hMZ hβ hγ hb hc hbc hne)

theorem eq_of_perpMem_mk_eq (h89 : PartThree.Lemma8_9) (h113 : PartThree.Theorem11_3)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {β γ : Set G} (hβ : β ∈ Dalpha D hC.alpha) (hγ : γ ∈ Dalpha D hC.alpha)
    {b c : Halpha D hC.alpha} (hb : (b : G) ∈ β) (hc : (c : G) ∈ γ)
    (hbc : Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b)
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c))
    (hne : perpMem (imageClass hC) (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b) ≠
      perpMem (imageClass hC) (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c))
    {δ ε : Set G} (hδ : δ ∈ blockLine D β γ) (hε : ε ∈ blockLine D β γ)
    {d e : Halpha D hC.alpha} (hd : (d : G) ∈ δ) (he : (e : G) ∈ ε)
    (hde : perpMem (imageClass hC) (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) d) =
      perpMem (imageClass hC) (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) e)) :
    δ = ε := by
  by_contra hδεne
  have hδD : δ ∈ Dalpha D hC.alpha :=
    mem_Dalpha_of_mem_blockLine_of_ne h89 h113 hC hrad hW hn3 hMZ hβ hγ hb hc hbc hne hδ
  have hεD : ε ∈ Dalpha D hC.alpha :=
    mem_Dalpha_of_mem_blockLine_of_ne h89 h113 hC hrad hW hn3 hMZ hβ hγ hb hc hbc hne hε
  have heStar : e ∈ DstarH hC := ⟨ε, hεD, he⟩
  have hV : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) e ∈
      Vmem (imageClass hC) (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) d) :=
    mem_Vmem.mpr ⟨⟨e, heStar, rfl⟩, hde.symm⟩
  have hεline : ε ∈ blockLine D hC.alpha δ :=
    mem_blockLine_of_mk_mem_Vmem h89 h113 hC hrad hW hn3 hMZ hδD hεD hd he hV
  have hline1 : blockLine D δ ε = blockLine D hC.alpha δ :=
    blockLine_eq_of_mem_of_mem hC hδD (right_mem_blockLine hδD.1 hδD.2.1) hεline hδεne
  obtain ⟨k, hk⟩ := mem_blockClass_iff.mp hβ.1
  have hα' : (hC.conj k).alpha = β := (HypothesisC.conj_alpha hC k).trans hk.symm
  have hγDβ : γ ∈ Dalpha D β :=
    mem_Dalpha_of_commute_mk h89 h113 hC hrad hW hn3 hMZ hβ hγ hb hc hbc hne
  have hγ' : γ ∈ Dalpha D (hC.conj k).alpha := by rwa [hα']
  have hδ' : δ ∈ blockLine D (hC.conj k).alpha γ := by rwa [hα']
  have hε' : ε ∈ blockLine D (hC.conj k).alpha γ := by rwa [hα']
  have hline2 : blockLine D δ ε = blockLine D β γ := by
    have h := blockLine_eq_of_mem_of_mem (hC.conj k) hγ' hδ' hε' hδεne
    rwa [hα'] at h
  have hαline : hC.alpha ∈ blockLine D hC.alpha δ := left_mem_blockLine hC.isBlock_alpha.subset
  rw [← hline1, hline2] at hαline
  exact alpha_not_mem_blockLine h89 h113 hC hrad hW hn3 hMZ hβ hγ hb hc hbc hne hαline

theorem mk_mem_lineMem (h89 : PartThree.Lemma8_9) (h113 : PartThree.Theorem11_3)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {β γ : Set G} (hβ : β ∈ Dalpha D hC.alpha) (hγ : γ ∈ Dalpha D hC.alpha)
    {b c : Halpha D hC.alpha} (hb : (b : G) ∈ β) (hc : (c : G) ∈ γ)
    (hbc : Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b)
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c))
    (hne : perpMem (imageClass hC) (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b) ≠
      perpMem (imageClass hC) (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c))
    {δ : Set G} (hδ : δ ∈ blockLine D β γ) {d : Halpha D hC.alpha} (hd : (d : G) ∈ δ) :
    QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) d ∈
      lineMem (imageClass hC) (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b)
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c) := by
  have hδD : δ ∈ Dalpha D hC.alpha :=
    mem_Dalpha_of_mem_blockLine_of_ne h89 h113 hC hrad hW hn3 hMZ hβ hγ hb hc hbc hne hδ
  refine mem_lineMem.mpr ⟨⟨d, ⟨δ, hδD, hd⟩, rfl⟩, ?_⟩
  rintro y ⟨hyb, hyc⟩
  obtain ⟨e, heStar, rfl⟩ := (mem_perpMem.mp hyb).1
  obtain ⟨ε, hεD, heε⟩ := mem_DalphaStar_iff.mp ((mem_DstarH_iff hC).mp heStar)
  have hbStar : b ∈ DstarH hC := ⟨β, hβ, hb⟩
  have hcStar : c ∈ DstarH hC := ⟨γ, hγ, hc⟩
  have hεβ : ε ∈ perp D β :=
    mem_perp_of_commute hC hβ.1 hεD.1 hb heε
      ((commute_of_commute_mk h113 hC hrad hn3 heStar hbStar (mem_perpMem.mp hyb).2).map
        (Subgroup.subtype _)).symm
  have hεγ : ε ∈ perp D γ :=
    mem_perp_of_commute hC hγ.1 hεD.1 hc heε
      ((commute_of_commute_mk h113 hC hrad hn3 heStar hcStar (mem_perpMem.mp hyc).2).map
        (Subgroup.subtype _)).symm
  have hδperp : δ ∈ perp D ε := hδ.2 ε ⟨hεβ, hεγ⟩
  have hde : Commute e d := by
    rcases mem_perp_iff.mp hδperp with hδε | hδε
    · exact Subtype.ext ((mem_Dalpha_iff.mp hδε).2.2.2 (e : G) heε (d : G) hd).eq
    · exact Subtype.ext
        (commute_of_mem_Dalpha h89 h113 hC hrad hW hn3 hMZ hεD heε (hδε ▸ hd)).eq
  exact ⟨⟨e, heStar, rfl⟩, hde.map (QuotientGroup.mk' _)⟩

theorem ncard_blockLine_eq (hC : HypothesisC D) {β γ δ : Set G} (hβ : β ∈ blockClass hC.alpha)
    (hγ : γ ∈ Dalpha D β) (hδ : δ ∈ Dalpha D hC.alpha) :
    (blockLine D β γ).ncard = (blockLine D hC.alpha δ).ncard := by
  obtain ⟨k, hk⟩ := mem_blockClass_iff.mp hβ
  have hk' : β = cimg k hC.alpha := hk
  have hγc : γ ∈ Dalpha D (cimg k hC.alpha) := hk' ▸ hγ
  have hγ' : cimg k⁻¹ γ ∈ Dalpha D hC.alpha := by
    have hD : cimg k⁻¹ '' Dalpha D (cimg k hC.alpha) =
        Dalpha D (cimg k⁻¹ (cimg k hC.alpha)) :=
      Dalpha_conj_image hC.setup.normal k⁻¹
    have hm : cimg k⁻¹ γ ∈ cimg k⁻¹ '' Dalpha D (cimg k hC.alpha) := ⟨γ, hγc, rfl⟩
    rwa [hD, cimg_inv_cimg] at hm
  have hline : blockLine D β γ = cimg k '' blockLine D hC.alpha (cimg k⁻¹ γ) := by
    have h := blockLine_cimg hC.setup.normal k hC.alpha (cimg k⁻¹ γ)
    rwa [cimg_cimg_inv, ← hk'] at h
  have hcard : (blockLine D β γ).ncard = (blockLine D hC.alpha (cimg k⁻¹ γ)).ncard := by
    rw [hline, Set.ncard_image_of_injective _ (cimg_injective k)]
  obtain ⟨g, hg, hgγ⟩ := hC.normalizer_transitive (cimg k⁻¹ γ) hγ' δ hδ
  have hgγ' : cimg g (cimg k⁻¹ γ) = δ := hgγ
  have hline2 : blockLine D hC.alpha δ = cimg g '' blockLine D hC.alpha (cimg k⁻¹ γ) := by
    have h := blockLine_cimg hC.setup.normal g hC.alpha (cimg k⁻¹ γ)
    rwa [cimg_eq_self_of_mem_normalizer hg, hgγ'] at h
  calc (blockLine D β γ).ncard
      = (blockLine D hC.alpha (cimg k⁻¹ γ)).ncard := hcard
    _ = (blockLine D hC.alpha δ).ncard := by
        rw [hline2, Set.ncard_image_of_injective _ (cimg_injective g)]

theorem ncard_blockLine_le (h89 : PartThree.Lemma8_9) (h113 : PartThree.Theorem11_3)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {v w : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hv : v ∈ imageClass hC) (hw : w ∈ imageClass hC) (hvw : Commute v w)
    (hne : perpMem (imageClass hC) v ≠ perpMem (imageClass hC) w)
    {δ : Set G} (hδ : δ ∈ Dalpha D hC.alpha) :
    (blockLine D hC.alpha δ).ncard ≤
      (perpMem (imageClass hC) '' lineMem (imageClass hC) v w).ncard := by
  classical
  obtain ⟨b, hbStar, rfl⟩ := hv
  obtain ⟨c, hcStar, rfl⟩ := hw
  obtain ⟨β, hβ, hbβ⟩ := mem_DalphaStar_iff.mp ((mem_DstarH_iff hC).mp hbStar)
  obtain ⟨γ, hγ, hcγ⟩ := mem_DalphaStar_iff.mp ((mem_DstarH_iff hC).mp hcStar)
  have hγDβ : γ ∈ Dalpha D β :=
    mem_Dalpha_of_commute_mk h89 h113 hC hrad hW hn3 hMZ hβ hγ hbβ hcγ hvw hne
  let rep : Set G → Halpha D hC.alpha := fun ε =>
    if h : ∃ e : Halpha D hC.alpha, (e : G) ∈ ε then Classical.choose h else 1
  have rep_mem : ∀ ε ∈ blockLine D β γ, (rep ε : G) ∈ ε := by
    intro ε hε
    have hεD : ε ∈ Dalpha D hC.alpha :=
      mem_Dalpha_of_mem_blockLine_of_ne h89 h113 hC hrad hW hn3 hMZ hβ hγ hbβ hcγ hvw hne hε
    obtain ⟨e, he⟩ := nonempty_of_mem_blockClass hC.isBlock_alpha.nonempty hεD.1
    have hex : ∃ e : Halpha D hC.alpha, (e : G) ∈ ε :=
      ⟨⟨e, Subgroup.subset_closure ⟨ε, hεD, he⟩⟩, he⟩
    simp only [rep, dif_pos hex]
    exact Classical.choose_spec hex
  let f : Set G → Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha) :=
    fun ε => QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) (rep ε)
  have hmaps : Set.MapsTo (fun ε => perpMem (imageClass hC) (f ε))
      (blockLine D β γ) (perpMem (imageClass hC) '' lineMem (imageClass hC)
        (QuotientGroup.mk' _ b) (QuotientGroup.mk' _ c)) := by
    intro ε hε
    exact ⟨f ε, mk_mem_lineMem h89 h113 hC hrad hW hn3 hMZ hβ hγ hbβ hcγ hvw hne hε
      (rep_mem ε hε), rfl⟩
  have hinj : Set.InjOn (fun ε => perpMem (imageClass hC) (f ε)) (blockLine D β γ) := by
    intro ε₁ hε₁ ε₂ hε₂ heq
    exact eq_of_perpMem_mk_eq h89 h113 hC hrad hW hn3 hMZ hβ hγ hbβ hcγ hvw hne
      hε₁ hε₂ (rep_mem ε₁ hε₁) (rep_mem ε₂ hε₂) heq
  have hle := Set.ncard_le_ncard_of_injOn _ hmaps hinj (Set.toFinite _)
  rwa [ncard_blockLine_eq hC hβ.1 hγDβ hδ] at hle

end CFSG.OddTranspositions.PartFour
