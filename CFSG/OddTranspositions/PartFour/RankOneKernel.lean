module

public import CFSG.OddTranspositions.PartFour.LineCount
public import CFSG.OddTranspositions.PartFour.RankOneSRG
public import CFSG.OddTranspositions.PartFour.RootWitness
import CFSG.OddTranspositions.PartThree.EightNine.O4

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem Dalpha_inter_subset_blockLine (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hTI : ∀ x ∈ imageClass hC, ∀ y ∈ imageClass hC, Commute x y →
      y ∈ Vmem (imageClass hC) x)
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) :
    Dalpha D hC.alpha ∩ Dalpha D β ⊆ blockLine D hC.alpha β := by
  rintro ε ⟨hεα, hεβ⟩
  obtain ⟨b, hb⟩ := nonempty_of_mem_blockClass hC.isBlock_alpha.nonempty hβ.1
  obtain ⟨e, he⟩ := nonempty_of_mem_blockClass hC.isBlock_alpha.nonempty hεα.1
  let bH : Halpha D hC.alpha := ⟨b, Subgroup.subset_closure ⟨β, hβ, hb⟩⟩
  let eH : Halpha D hC.alpha := ⟨e, Subgroup.subset_closure ⟨ε, hεα, he⟩⟩
  have hcomm : Commute b e := (mem_Dalpha_iff.mp hεβ).2.2.2 b hb e he
  have hcommH : Commute bH eH := Subtype.ext hcomm.eq
  have hbImg : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) bH ∈
      imageClass hC := ⟨bH, ⟨β, hβ, hb⟩, rfl⟩
  have heImg : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) eH ∈
      imageClass hC := ⟨eH, ⟨ε, hεα, he⟩, rfl⟩
  have hv := hTI _ hbImg _ heImg (hcommH.map (QuotientGroup.mk' _))
  exact mem_blockLine_of_mk_mem_Vmem h89 h113 hC hrad hW hn3 hMZ hβ hεα
    (b := bH) (e := eH) hb he hv

theorem exists_kernel_config_of_mem_Dalpha (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hTI : ∀ x ∈ imageClass hC, ∀ y ∈ imageClass hC, Commute x y →
      y ∈ Vmem (imageClass hC) x)
    {x y ε : Set G} (hx : x ∈ Dalpha D hC.alpha) (hy : y ∈ Dalpha D hC.alpha)
    (hxy : y ∉ perp D x) (hε : ε ∈ Dalpha D x ∩ Dalpha D y) (hεα : ε ≠ hC.alpha) :
    ∃ α' ∈ Dalpha D hC.alpha, ∃ γ ∈ Dalpha D hC.alpha,
      γ ∉ perp D α' ∧ hC.alpha ∉ blockLine D α' γ := by
  have hεnotDα : ε ∉ Dalpha D hC.alpha := by
    intro hεDα
    have hxDε : x ∈ Dalpha D ε := mem_Dalpha_symm hε.1 hx.2.1
    have hyDε : y ∈ Dalpha D ε := mem_Dalpha_symm hε.2 hy.2.1
    have hxline : x ∈ blockLine D hC.alpha ε :=
      Dalpha_inter_subset_blockLine h89 h113 hC hrad hW hn3 hMZ hTI hεDα ⟨hx, hxDε⟩
    have hyline : y ∈ blockLine D hC.alpha ε :=
      Dalpha_inter_subset_blockLine h89 h113 hC hrad hW hn3 hMZ hTI hεDα ⟨hy, hyDε⟩
    exact hxy (mem_perp_of_mem_blockLine hC.isBlock_alpha.subset hεDα hxline hyline)
  have hεnotperp : ε ∉ perp D hC.alpha := by
    rw [mem_perp_iff]
    rintro (h | h)
    · exact hεnotDα h
    · exact hεα h
  have hαnotperp : hC.alpha ∉ perp D ε := by
    intro h
    exact hεnotperp (mem_perp_symm h hε.1.2.1)
  exact ⟨x, hx, y, hy, hxy,
    not_mem_blockLine_of_not_mem_perp
      (α' := x) (γ := y) (η := hC.alpha) (η' := ε)
      ⟨mem_perp_iff.mpr (Or.inl hε.1), mem_perp_iff.mpr (Or.inl hε.2)⟩ hαnotperp⟩

theorem exists_kernel_config_of_two_common (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hTI : ∀ x ∈ imageClass hC, ∀ y ∈ imageClass hC, Commute x y →
      y ∈ Vmem (imageClass hC) x)
    {x y ε₁ ε₂ : Set G} (hx : x ∈ blockClass hC.alpha) (hy : y ∈ blockClass hC.alpha)
    (hxy : y ∉ perp D x) (h₁ : ε₁ ∈ Dalpha D x ∩ Dalpha D y)
    (h₂ : ε₂ ∈ Dalpha D x ∩ Dalpha D y) (h₁₂ : ε₁ ≠ ε₂) :
    ∃ α' ∈ Dalpha D hC.alpha, ∃ γ ∈ Dalpha D hC.alpha,
      γ ∉ perp D α' ∧ hC.alpha ∉ blockLine D α' γ := by
  have hxsub : x ⊆ D := subset_of_mem_blockClass hC.setup.normal hC.isBlock_alpha hx
  have hysub : y ⊆ D := subset_of_mem_blockClass hC.setup.normal hC.isBlock_alpha hy
  have hε₁class : ε₁ ∈ blockClass hC.alpha := by
    have h := (mem_Dalpha_iff.mp h₁.1).1
    rwa [blockClass_eq_of_mem hx] at h
  obtain ⟨g, hg⟩ := mem_blockClass_iff.mp hε₁class
  let hinv : G := g⁻¹
  have hα : (fun x => hinv * x * hinv⁻¹) '' ε₁ = hC.alpha := by
    change cimg g⁻¹ ε₁ = hC.alpha
    rw [hg, cimg_inv_cimg]
  have hxDε₁ : x ∈ Dalpha D ε₁ := mem_Dalpha_symm h₁.1 hxsub
  have hyDε₁ : y ∈ Dalpha D ε₁ := mem_Dalpha_symm h₁.2 hysub
  have hx' : cimg hinv x ∈ Dalpha D hC.alpha := by
    have h := Dalpha.conj hC.setup.normal hxDε₁ hinv
    rwa [hα] at h
  have hy' : cimg hinv y ∈ Dalpha D hC.alpha := by
    have h := Dalpha.conj hC.setup.normal hyDε₁ hinv
    rwa [hα] at h
  have hxy' : cimg hinv y ∉ perp D (cimg hinv x) := by
    intro hmem
    exact hxy ((perp_cimg_mem hC.setup.normal hinv (α := x) (γ := y)).mp hmem)
  have hε' : cimg hinv ε₂ ∈ Dalpha D (cimg hinv x) ∩ Dalpha D (cimg hinv y) :=
    ⟨Dalpha.conj hC.setup.normal h₂.1 hinv, Dalpha.conj hC.setup.normal h₂.2 hinv⟩
  have hε'ne : cimg hinv ε₂ ≠ hC.alpha := by
    intro heq
    have h₁₂' : cimg hinv ε₂ = cimg hinv ε₁ := by
      rw [heq]
      exact hα.symm
    exact h₁₂ (cimg_injective hinv h₁₂').symm
  exact exists_kernel_config_of_mem_Dalpha h89 h113 hC hrad hW hn3 hMZ hTI
    hx' hy' hxy' hε' hε'ne

theorem not_o4PairData_of_one_lt (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha)
    (hm : 1 < ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)).ncard) :
    ¬ O4PairData G D := by
  intro hO4
  have hcenter := PartThree.pCore_two_le_center_Halpha_of_o4PairData hC hO4
  have hfix : ∀ y : Halpha D hC.alpha, y ∈ CFSG.pCore 2 (Halpha D hC.alpha) →
      ∀ c ∈ β, (y : G) * c * (y : G)⁻¹ = c := by
    intro y hy c hc
    let cH : Halpha D hC.alpha := ⟨c, Subgroup.subset_closure ⟨β, hβ, hc⟩⟩
    have hyc : y ∈ Subgroup.center (Halpha D hC.alpha) := hcenter hy
    have hcomm : Commute y cH := (Subgroup.mem_center_iff.mp hyc cH).symm
    have h : y * cH * y⁻¹ = cH := by
      rw [hcomm.eq, mul_assoc, mul_inv_cancel, mul_one]
    exact congrArg Subtype.val h
  have himg : ∀ x ∈ Malpha D hC.alpha, cimg x β = β := by
    intro x hx
    obtain ⟨y, hy, hye⟩ := exists_mem_pCore_cimg_eq h113 hC hrad hn3 hHns hβ hx
    rw [← hye]
    ext c
    constructor
    · rintro ⟨d, hd, rfl⟩
      simpa only [hfix y hy d hd] using hd
    · intro hc
      exact ⟨c, hc, hfix y hy c hc⟩
  have hset : (fun x => cimg x β) '' (Malpha D hC.alpha : Set G) = {β} := by
    apply Set.Subset.antisymm
    · rintro S ⟨x, hx, rfl⟩
      exact Set.mem_singleton_iff.mpr (himg x hx)
    · intro S hS
      rw [Set.mem_singleton_iff] at hS
      refine ⟨1, (Malpha D hC.alpha).one_mem, ?_⟩
      simpa only [hS] using cimg_one β
  rw [hset, Set.ncard_singleton] at hm
  exact Nat.lt_irrefl 1 hm

theorem ncard_Dalpha_inter_eq_one (h87 : PartThree.Theorem8_7) (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    (hTI : ∀ x ∈ imageClass hC, ∀ y ∈ imageClass hC, Commute x y →
      y ∈ Vmem (imageClass hC) x)
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha)
    (hm : 1 < ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)).ncard)
    (hker : ¬ ∃ α' ∈ Dalpha D hC.alpha, ∃ γ ∈ Dalpha D hC.alpha,
      γ ∉ perp D α' ∧ hC.alpha ∉ blockLine D α' γ)
    {x y : Set G} (hx : x ∈ blockClass hC.alpha) (hy : y ∈ blockClass hC.alpha)
    (hxy : y ∉ perp D x) :
    (Dalpha D x ∩ Dalpha D y).ncard = 1 := by
  have hnoO4 : ¬ O4PairData G D :=
    not_o4PairData_of_one_lt h113 hC hrad hn3 hHns hβ hm
  have hne : (Dalpha D x ∩ Dalpha D y).Nonempty := by
    rcases h87 (G := G) (D := D) hC hrad hnoO4 x hx y hy with h | hyx | ⟨δ, hδx, hδy⟩
    · exact absurd (mem_perp_iff.mpr (Or.inr h.symm)) hxy
    · exact absurd (mem_perp_iff.mpr (Or.inl hyx)) hxy
    · exact ⟨δ, hδx, hδy⟩
  have hle : (Dalpha D x ∩ Dalpha D y).ncard ≤ 1 := by
    rw [Set.ncard_le_one]
    intro a ha b hb
    by_contra hab
    exact hker (exists_kernel_config_of_two_common h89 h113 hC hrad hW hn3 hMZ hTI
      hx hy hxy ha hb hab)
  have hpos : 0 < (Dalpha D x ∩ Dalpha D y).ncard :=
    (Set.ncard_pos (Set.toFinite _)).2 hne
  omega

private noncomputable def rankOneKernel_fibreMap (hC : HypothesisC D) (γ : Set G) :
    Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) :=
  ⋃ δ ∈ blockLine D hC.alpha γ \ {hC.alpha}, blockImage hC δ

private theorem rankOneKernel_fibreMap_eq_Vmem (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {γ : Set G} (hγ : γ ∈ Dalpha D hC.alpha) {c : Halpha D hC.alpha}
    (hc : (c : G) ∈ γ) :
    rankOneKernel_fibreMap hC γ =
      Vmem (imageClass hC) (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c) :=
  iUnion_blockImage_eq_Vmem h89 h113 hC hrad hW hn3 hMZ hγ hc

private theorem rankOneKernel_fibreSet (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {δ : Set G} (hδ : δ ∈ Dalpha D hC.alpha) {d : Halpha D hC.alpha} (hd : (d : G) ∈ δ) :
    {γ | γ ∈ Dalpha D hC.alpha ∧ rankOneKernel_fibreMap hC γ =
      Vmem (imageClass hC) (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) d)} =
      blockLine D hC.alpha δ \ {hC.alpha} := by
  ext γ
  constructor
  · rintro ⟨hγ, hγeq⟩
    obtain ⟨c, hc⟩ := nonempty_of_mem_blockClass hC.isBlock_alpha.nonempty hγ.1
    let cH : Halpha D hC.alpha :=
      ⟨c, Subgroup.subset_closure ⟨γ, hγ, hc⟩⟩
    have hcImg : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) cH ∈
        imageClass hC := ⟨cH, ⟨γ, hγ, hc⟩, rfl⟩
    have hfγ : rankOneKernel_fibreMap hC γ =
        Vmem (imageClass hC)
          (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) cH) :=
      rankOneKernel_fibreMap_eq_Vmem h89 h113 hC hrad hW hn3 hMZ hγ hc
    have hv : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) cH ∈
        Vmem (imageClass hC)
          (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) d) := by
      rw [← hγeq, hfγ]
      exact mem_Vmem_self hcImg
    exact ⟨mem_blockLine_of_mk_mem_Vmem h89 h113 hC hrad hW hn3 hMZ hδ hγ
      (b := d) (e := cH) hd hc hv, by simpa using hγ.2.2.1⟩
  · rintro ⟨hγline, hγα⟩
    have hγ : γ ∈ Dalpha D hC.alpha :=
      mem_Dalpha_of_mem_blockLine hC.isBlock_alpha.subset hδ hγline (by simpa using hγα)
    refine ⟨hγ, ?_⟩
    have hline : blockLine D hC.alpha γ = blockLine D hC.alpha δ :=
      blockLine_eq_of_mem hC hδ hγ hγline
    have hfγδ : rankOneKernel_fibreMap hC γ = rankOneKernel_fibreMap hC δ := by
      simp only [rankOneKernel_fibreMap, hline]
    rw [hfγδ, rankOneKernel_fibreMap_eq_Vmem h89 h113 hC hrad hW hn3 hMZ hδ hd]

theorem ncard_Dalpha_alpha_eq (h89 : PartThree.Lemma8_9) (h113 : PartThree.Theorem11_3)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    (hr1 : ∀ β ∈ Dalpha D hC.alpha,
      (blockImage hC '' (blockLine D hC.alpha β \ {hC.alpha})).ncard = 1)
    {s : ℕ} (hm : ∀ β ∈ Dalpha D hC.alpha,
      ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)).ncard = 2 ^ s) :
    (Dalpha D hC.alpha).ncard = (Vmem (imageClass hC) '' imageClass hC).ncard * 2 ^ s := by
  have hmaps : ∀ γ ∈ Dalpha D hC.alpha,
      rankOneKernel_fibreMap hC γ ∈ Vmem (imageClass hC) '' imageClass hC := by
    intro γ hγ
    obtain ⟨c, hc⟩ := nonempty_of_mem_blockClass hC.isBlock_alpha.nonempty hγ.1
    let cH : Halpha D hC.alpha := ⟨c, Subgroup.subset_closure ⟨γ, hγ, hc⟩⟩
    have hcImg : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) cH ∈
        imageClass hC := ⟨cH, ⟨γ, hγ, hc⟩, rfl⟩
    exact ⟨QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) cH, hcImg,
      (rankOneKernel_fibreMap_eq_Vmem h89 h113 hC hrad hW hn3 hMZ hγ hc).symm⟩
  have hfib : ∀ v ∈ Vmem (imageClass hC) '' imageClass hC,
      {γ | γ ∈ Dalpha D hC.alpha ∧ rankOneKernel_fibreMap hC γ = v}.ncard = 2 ^ s := by
    rintro v ⟨u, hu, rfl⟩
    obtain ⟨dH, hdStar, rfl⟩ := hu
    obtain ⟨δ, hδ, hdδ⟩ := mem_DalphaStar_iff.mp ((mem_DstarH_iff hC).mp hdStar)
    have hset := rankOneKernel_fibreSet h89 h113 hC hrad hW hn3 hMZ hδ hdδ
    have hcard := ncard_blockLine_diff_eq h113 hC hrad hn3 hHns hδ
    rw [hr1 δ hδ, hm δ hδ, one_mul] at hcard
    rw [hset]
    exact hcard
  exact CFSG.CGT.T75F.ncard_eq_mul_of_fibres (Dalpha D hC.alpha)
    (Vmem (imageClass hC) '' imageClass hC) (rankOneKernel_fibreMap hC) hmaps (2 ^ s) hfib

theorem ncard_Dalpha_inter_alpha_eq (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    (hTI : ∀ x ∈ imageClass hC, ∀ y ∈ imageClass hC, Commute x y →
      y ∈ Vmem (imageClass hC) x)
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha)
    (hr1 : (blockImage hC '' (blockLine D hC.alpha β \ {hC.alpha})).ncard = 1) {s : ℕ}
    (hm : ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)).ncard = 2 ^ s) :
    (Dalpha D hC.alpha ∩ Dalpha D β).ncard = 2 ^ s - 1 := by
  have hset : Dalpha D hC.alpha ∩ Dalpha D β =
      (blockLine D hC.alpha β \ {hC.alpha}) \ {β} := by
    ext γ
    constructor
    · rintro ⟨hγα, hγβ⟩
      refine ⟨⟨?_, by simpa using hγα.2.2.1⟩, by simpa using hγβ.2.2.1⟩
      exact Dalpha_inter_subset_blockLine h89 h113 hC hrad hW hn3 hMZ hTI hβ ⟨hγα, hγβ⟩
    · rintro ⟨⟨hγline, hγα⟩, hγβ⟩
      have hγDα : γ ∈ Dalpha D hC.alpha :=
        mem_Dalpha_of_mem_blockLine hC.isBlock_alpha.subset hβ hγline (by simpa using hγα)
      refine ⟨hγDα, ?_⟩
      have hβline : β ∈ blockLine D hC.alpha β := right_mem_blockLine hβ.1 hβ.2.1
      rcases mem_perp_iff.mp
        (mem_perp_of_mem_blockLine hC.isBlock_alpha.subset hβ hβline hγline) with h | h
      · exact h
      · exact absurd h (by simpa using hγβ)
  rw [hset]
  have hβline : β ∈ blockLine D hC.alpha β := right_mem_blockLine hβ.1 hβ.2.1
  have hβmem : β ∈ blockLine D hC.alpha β \ {hC.alpha} :=
    ⟨hβline, by simpa using hβ.2.2.1⟩
  have hcard := ncard_blockLine_diff_eq h113 hC hrad hn3 hHns hβ
  rw [hr1, hm, one_mul] at hcard
  rw [Set.ncard_diff_singleton_of_mem hβmem, hcard]

theorem ncard_Dalpha_eq_of_mem_blockClass (hC : HypothesisC D) {x : Set G}
    (hx : x ∈ blockClass hC.alpha) : (Dalpha D x).ncard = (Dalpha D hC.alpha).ncard := by
  obtain ⟨g, hg⟩ := mem_blockClass_iff.mp hx
  have hset : Dalpha D x = (cimg g) '' Dalpha D hC.alpha := by
    rw [hg]
    exact (Dalpha_conj_image hC.setup.normal g).symm
  rw [hset]
  exact Set.ncard_image_of_injective _ (cimg_injective g)

theorem exists_ncard_Dalpha_inter_eq (hC : HypothesisC D) {x y : Set G}
    (hx : x ∈ blockClass hC.alpha) (hy : y ∈ Dalpha D x) :
    ∃ β ∈ Dalpha D hC.alpha,
      (Dalpha D x ∩ Dalpha D y).ncard = (Dalpha D hC.alpha ∩ Dalpha D β).ncard := by
  obtain ⟨g, hg⟩ := mem_blockClass_iff.mp hx
  have hβ : cimg g⁻¹ y ∈ Dalpha D hC.alpha := by
    have h := Dalpha.conj hC.setup.normal hy g⁻¹
    have h' : (fun x => g⁻¹ * x * (g⁻¹)⁻¹) '' ((fun x => g * x * g⁻¹) '' hC.alpha) =
        hC.alpha := cimg_inv_cimg g hC.alpha
    rw [hg, h'] at h
    exact h
  have hset : cimg g '' (Dalpha D hC.alpha ∩ Dalpha D (cimg g⁻¹ y)) =
      Dalpha D x ∩ Dalpha D y := by
    rw [Set.image_inter (cimg_injective g)]
    change (fun γ : Set G => (fun x => g * x * g⁻¹) '' γ) '' Dalpha D hC.alpha ∩
      (fun γ : Set G => (fun x => g * x * g⁻¹) '' γ) '' Dalpha D (cimg g⁻¹ y) =
      Dalpha D x ∩ Dalpha D y
    rw [Dalpha_conj_image hC.setup.normal g, Dalpha_conj_image hC.setup.normal g]
    change Dalpha D ((fun x => g * x * g⁻¹) '' hC.alpha) ∩
      Dalpha D ((fun x => g * x * g⁻¹) '' ((fun x => g⁻¹ * x * (g⁻¹)⁻¹) '' y)) =
      Dalpha D x ∩ Dalpha D y
    rw [show (fun x => g * x * g⁻¹) '' hC.alpha = x from hg.symm,
      show (fun x => g * x * g⁻¹) '' ((fun x => g⁻¹ * x * (g⁻¹)⁻¹) '' y) = y from
        cimg_cimg_inv g y]
  refine ⟨cimg g⁻¹ y, hβ, ?_⟩
  rw [← hset]
  exact Set.ncard_image_of_injective _ (cimg_injective g)

private noncomputable def rankOneKernel_graph (hC : HypothesisC D) :
    SimpleGraph ↥(blockClass hC.alpha) :=
  SimpleGraph.fromRel fun u v : ↥(blockClass hC.alpha) => (v : Set G) ∈ Dalpha D u

private theorem rankOneKernel_graph_adj (hC : HypothesisC D)
    {u v : ↥(blockClass hC.alpha)} :
    (rankOneKernel_graph hC).Adj u v ↔ (v : Set G) ∈ Dalpha D u := by
  rw [rankOneKernel_graph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, h | h⟩
    · exact h
    · exact mem_Dalpha_symm h
        (subset_of_mem_blockClass hC.setup.normal hC.isBlock_alpha v.2)
  · intro h
    have hne : (v : Set G) ≠ (u : Set G) := (mem_Dalpha_iff.mp h).2.2.1
    exact ⟨fun huv => hne (congrArg Subtype.val huv).symm, Or.inl h⟩

private theorem rankOneKernel_image_neighborSet (hC : HypothesisC D)
    (u : ↥(blockClass hC.alpha)) :
    Subtype.val '' (rankOneKernel_graph hC).neighborSet u = Dalpha D (u : Set G) := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    rwa [SimpleGraph.mem_neighborSet, rankOneKernel_graph_adj hC] at hw
  · intro hv
    have hvclass : v ∈ blockClass hC.alpha := by
      have h := (mem_Dalpha_iff.mp hv).1
      rwa [blockClass_eq_of_mem u.2] at h
    refine ⟨⟨v, hvclass⟩, ?_, rfl⟩
    rwa [SimpleGraph.mem_neighborSet, rankOneKernel_graph_adj hC]

private theorem rankOneKernel_ncard_neighborSet (hC : HypothesisC D)
    (u : ↥(blockClass hC.alpha)) :
    ((rankOneKernel_graph hC).neighborSet u).ncard = (Dalpha D (u : Set G)).ncard := by
  rw [← Set.ncard_image_of_injective ((rankOneKernel_graph hC).neighborSet u)
      Subtype.val_injective, rankOneKernel_image_neighborSet hC u]

private theorem rankOneKernel_ncard_commonNeighbors (hC : HypothesisC D)
    (u v : ↥(blockClass hC.alpha)) :
    ((rankOneKernel_graph hC).commonNeighbors u v).ncard =
      (Dalpha D (u : Set G) ∩ Dalpha D (v : Set G)).ncard := by
  rw [SimpleGraph.commonNeighbors,
    ← Set.ncard_image_of_injective
      ((rankOneKernel_graph hC).neighborSet u ∩ (rankOneKernel_graph hC).neighborSet v)
      Subtype.val_injective,
    Set.image_inter Subtype.val_injective, rankOneKernel_image_neighborSet hC u,
    rankOneKernel_image_neighborSet hC v]

private theorem rankOneKernel_exists_one_lt (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    (hr1 : ∀ β ∈ Dalpha D hC.alpha,
      (blockImage hC '' (blockLine D hC.alpha β \ {hC.alpha})).ncard = 1)
    {a s : ℕ} (hS : (Vmem (imageClass hC) '' imageClass hC).ncard = 2 ^ a + 1)
    (hm : ∀ β ∈ Dalpha D hC.alpha,
      ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)).ncard = 2 ^ s)
    (hs : 1 ≤ s) :
    ∃ β ∈ Dalpha D hC.alpha,
      1 < ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)).ncard := by
  have hDcard := ncard_Dalpha_alpha_eq h89 h113 hC hrad hW hn3 hMZ hHns hr1 hm
  have hDpos : 0 < (Dalpha D hC.alpha).ncard := by
    rw [hDcard, hS]
    positivity
  obtain ⟨β, hβ⟩ := (Set.ncard_pos (Set.toFinite _)).1 hDpos
  refine ⟨β, hβ, ?_⟩
  rw [hm β hβ]
  exact Nat.one_lt_two_pow (by omega)

private theorem rankOneKernel_ncard_commonNeighbors_adj (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    (hTI : ∀ x ∈ imageClass hC, ∀ y ∈ imageClass hC, Commute x y →
      y ∈ Vmem (imageClass hC) x)
    (hr1 : ∀ β ∈ Dalpha D hC.alpha,
      (blockImage hC '' (blockLine D hC.alpha β \ {hC.alpha})).ncard = 1)
    {s : ℕ} (hm : ∀ β ∈ Dalpha D hC.alpha,
      ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)).ncard = 2 ^ s)
    {u v : ↥(blockClass hC.alpha)}
    (huv : (rankOneKernel_graph hC).Adj u v) :
    ((rankOneKernel_graph hC).commonNeighbors u v).ncard = 2 ^ s - 1 := by
  obtain ⟨β, hβ, hcard⟩ :=
    exists_ncard_Dalpha_inter_eq hC u.2 ((rankOneKernel_graph_adj hC).mp huv)
  rw [rankOneKernel_ncard_commonNeighbors hC u v, hcard,
    ncard_Dalpha_inter_alpha_eq h89 h113 hC hrad hW hn3 hMZ hHns hTI hβ
      (hr1 β hβ) (hm β hβ)]

private theorem rankOneKernel_ncard_commonNeighbors_not_adj (h87 : PartThree.Theorem8_7)
    (h89 : PartThree.Lemma8_9) (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    (hTI : ∀ x ∈ imageClass hC, ∀ y ∈ imageClass hC, Commute x y →
      y ∈ Vmem (imageClass hC) x)
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha)
    (hmβ : 1 < ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)).ncard)
    (hker : ¬ ∃ α' ∈ Dalpha D hC.alpha, ∃ γ ∈ Dalpha D hC.alpha,
      γ ∉ perp D α' ∧ hC.alpha ∉ blockLine D α' γ)
    {u v : ↥(blockClass hC.alpha)} (huv : u ≠ v)
    (hnot : ¬ (rankOneKernel_graph hC).Adj u v) :
    ((rankOneKernel_graph hC).commonNeighbors u v).ncard = 1 := by
  have hvnot : (v : Set G) ∉ Dalpha D u := fun h =>
    hnot ((rankOneKernel_graph_adj hC).mpr h)
  have hnotperp : (v : Set G) ∉ perp D (u : Set G) := by
    rw [mem_perp_iff]
    rintro (h | h)
    · exact hvnot h
    · exact huv (Subtype.ext h).symm
  rw [rankOneKernel_ncard_commonNeighbors hC u v]
  exact ncard_Dalpha_inter_eq_one h87 h89 h113 hC hrad hW hn3 hMZ hHns hTI hβ hmβ
    hker u.2 v.2 hnotperp

theorem exists_kernel_config_of_rankOne (h87 : PartThree.Theorem8_7)
    (h89 : PartThree.Lemma8_9) (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    (hTI : ∀ x ∈ imageClass hC, ∀ y ∈ imageClass hC, Commute x y →
      y ∈ Vmem (imageClass hC) x)
    (hr1 : ∀ β ∈ Dalpha D hC.alpha,
      (blockImage hC '' (blockLine D hC.alpha β \ {hC.alpha})).ncard = 1)
    {a s : ℕ} (hS : (Vmem (imageClass hC) '' imageClass hC).ncard = 2 ^ a + 1)
    (hm : ∀ β ∈ Dalpha D hC.alpha,
      ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)).ncard = 2 ^ s)
    (hs : 1 ≤ s) (has : a ≠ s + 1) :
    ∃ α' ∈ Dalpha D hC.alpha, ∃ γ ∈ Dalpha D hC.alpha,
      γ ∉ perp D α' ∧ hC.alpha ∉ blockLine D α' γ := by
  by_contra hker
  classical
  letI : Fintype ↥(blockClass hC.alpha) := Fintype.ofFinite _
  obtain ⟨β, hβ, hmβ⟩ :=
    rankOneKernel_exists_one_lt h89 h113 hC hrad hW hn3 hMZ hHns hr1 hS hm hs
  have hDcard : (Dalpha D hC.alpha).ncard =
      (Vmem (imageClass hC) '' imageClass hC).ncard * 2 ^ s :=
    ncard_Dalpha_alpha_eq h89 h113 hC hrad hW hn3 hMZ hHns hr1 hm
  have hdeg : (rankOneKernel_graph hC).IsRegularOfDegree ((2 ^ a + 1) * 2 ^ s) := by
    intro u
    rw [← SimpleGraph.ncard_neighborSet]
    rw [rankOneKernel_ncard_neighborSet hC u,
      ncard_Dalpha_eq_of_mem_blockClass hC u.2, hDcard, hS]
  have hsrg : (rankOneKernel_graph hC).IsSRGWith
      (Fintype.card ↥(blockClass hC.alpha)) ((2 ^ a + 1) * 2 ^ s) (2 ^ s - 1) 1 := by
    refine ⟨rfl, hdeg, ?_, ?_⟩
    · intro u v huv
      rw [Set.fintypeCard_eq_ncard]
      exact rankOneKernel_ncard_commonNeighbors_adj h89 h113 hC hrad hW hn3 hMZ hHns hTI
        hr1 hm huv
    · intro u v huv hnot
      rw [Set.fintypeCard_eq_ncard]
      exact rankOneKernel_ncard_commonNeighbors_not_adj h87 h89 h113 hC hrad hW hn3 hMZ
        hHns hTI hβ hmβ hker huv hnot
  have hn : 0 < Fintype.card ↥(blockClass hC.alpha) := by
    rw [Fintype.card_pos_iff]
    exact ⟨⟨hC.alpha, mem_blockClass_self hC.alpha⟩⟩
  exact has (eq_add_one_of_isSRGWith_two_pow hsrg hn hs)

end CFSG.OddTranspositions.PartFour
