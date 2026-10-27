module

public import CFSG.OddTranspositions.PartFour.RootKernel
public import CFSG.OddTranspositions.PartFour.RootCount
public import CFSG.OddTranspositions.PartFour.RootWitness
public import CFSG.OddTranspositions.PartFour.MeetsSqAlpha
public import CFSG.OddTranspositions.PartFour.SideConditions
public import CFSG.OddTranspositions.PartFour.SeventeenFourSpD2
public import CFSG.OddTranspositions.PartFour.RootGroupSp
import CFSG.OddTranspositions.PartFour.Fourteen.TableSp

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Bridge.OddTransp CFSG.Timmesfeld.Connectivity
open CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem card_closure_alpha_le_of_kernel (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    (hker : ∃ α' ∈ Dalpha D hC.alpha, ∃ γ ∈ Dalpha D hC.alpha,
      γ ∉ perp D α' ∧ hC.alpha ∉ blockLine D α' γ)
    (hroot : ∀ x ∈ imageClass hC,
      ∃ R₀ : Subgroup (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)),
        (R₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))) =
          insert 1 (Vmem (imageClass hC) x))
    (h2 : ∀ x ∈ imageClass hC, 2 ≤ (Vmem (imageClass hC) x).ncard)
    (hr1 : ∀ β ∈ Dalpha D hC.alpha,
      (blockImage hC '' (blockLine D hC.alpha β \ {hC.alpha})).ncard = 1) :
    Nat.card (Subgroup.closure hC.alpha) ≤ hC.alpha.ncard + 1 ∧ 2 ≤ hC.alpha.ncard := by
  obtain ⟨α', hα', γ, hγ, hγα', hαℓ⟩ := hker
  have hcard : Nat.card (Subgroup.closure α') ≤ α'.ncard + 1 :=
    card_closure_le_of_root h89 h113 hC hrad hW hn3 hMZ hHns hroot hα' (hr1 α' hα')
      fun z hz hzM =>
        eq_one_of_mem_closure_of_mem_Malpha h89 h113 hC hrad hW hn3 hMZ hHns hα' hγ hγα' hαℓ
          hz hzM
  obtain ⟨a, ha⟩ := nonempty_of_mem_blockClass hC.isBlock_alpha.nonempty hα'.1
  let b : Halpha D hC.alpha :=
    ⟨a, Subgroup.subset_closure (mem_DalphaStar_iff.mpr ⟨α', hα', ha⟩)⟩
  have hV := ncard_Vmem_eq h89 h113 hC hrad hW hn3 hMZ hHns hα' (b := b) ha
  rw [hr1 α' hα', one_mul] at hV
  have hV2 := h2 (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b)
    ⟨b, ⟨α', hα', ha⟩, rfl⟩
  obtain ⟨g, hg⟩ := mem_blockClass_iff.mp hα'.1
  have hg' : α' = cimg g hC.alpha := hg
  have hcl : Nat.card (Subgroup.closure α') = Nat.card (Subgroup.closure hC.alpha) := by
    rw [hg', closure_cimg, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hnc : α'.ncard = hC.alpha.ncard := by rw [hg', ncard_cimg]
  refine ⟨?_, ?_⟩
  · rw [← hcl, ← hnc]
    exact hcard
  · rw [← hnc, ← hV]
    exact hV2

theorem meetsSq_of_kernel (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hsq : MeetsSq (imageClass hC))
    (hker : ∃ α' ∈ Dalpha D hC.alpha, ∃ γ ∈ Dalpha D hC.alpha,
      γ ∉ perp D α' ∧ hC.alpha ∉ blockLine D α' γ)
    (hroot : ∀ x ∈ imageClass hC,
      ∃ R₀ : Subgroup (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)),
        (R₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))) =
          insert 1 (Vmem (imageClass hC) x))
    (h2 : ∀ x ∈ imageClass hC, 2 ≤ (Vmem (imageClass hC) x).ncard)
    (hr1 : ∀ β ∈ Dalpha D hC.alpha,
      (blockImage hC '' (blockLine D hC.alpha β \ {hC.alpha})).ncard = 1) :
    MeetsSq D := by
  have hHns := not_isSolvable_Halpha_of_meetsSq hC hsq
  have hn3 := not_threeTransp_of_meetsSq hC hsq
  obtain ⟨hcard, h2α⟩ :=
    card_closure_alpha_le_of_kernel h89 h113 hC hrad hW hn3 hMZ hHns hker hroot h2 hr1
  exact meetsSq_of_card_closure_alpha hC
    (fun a ha b hb => commute_of_mem_alpha h89 h113 hC hrad hW hn3 hMZ ha hb) hcard h2α

theorem meetsSq_of_root (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hsq : MeetsSq (imageClass hC))
    (hfour : ∃ t ∈ imageClass hC, ∃ u ∈ imageClass hC, ∃ v ∈ imageClass hC,
      ∃ w ∈ imageClass hC, ¬ Commute t u ∧ ¬ Commute v w ∧
        Commute v t ∧ Commute v u ∧ Commute w t ∧ Commute w u)
    (hroot : ∀ x ∈ imageClass hC,
      ∃ R₀ : Subgroup (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)),
        (R₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))) =
          insert 1 (Vmem (imageClass hC) x))
    (h2 : ∀ x ∈ imageClass hC, 2 ≤ (Vmem (imageClass hC) x).ncard)
    (hr1 : ∀ β ∈ Dalpha D hC.alpha,
      (blockImage hC '' (blockLine D hC.alpha β \ {hC.alpha})).ncard = 1) :
    MeetsSq D :=
  meetsSq_of_kernel h89 h113 hC hrad hW hMZ hsq
    (exists_kernel_config_of_four h89 h113 hC hrad hW (not_threeTransp_of_meetsSq hC hsq) hMZ
      hfour) hroot h2 hr1

theorem meetsSq_of_isSymplecticTransvection_imageClass (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC)
    {k f : ℕ} (hk : 2 ≤ k) (hf : 2 ≤ f)
    (hsp : IsSymplecticTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) (2 * k) f s) :
    MeetsSq D := by
  have hZ := center_eq_bot_quotient_H hC
  have hcls := imageClass_eq_setOf_isConj hC hs
  have hsq : MeetsSq (imageClass hC) :=
    Fourteen.meetsSq_of_isSymplecticTransvection (imageClass_isClass hC) hZ hs hf hsp
  have hHns := not_isSolvable_Halpha_of_meetsSq hC hsq
  have hn3 := not_threeTransp_of_meetsSq hC hsq
  have hfour := exists_four_of_isSymplecticTransvection hZ hk hsp
  rw [← hcls] at hfour
  refine meetsSq_of_root h89 h113 hC hrad hW hMZ hsq hfour (fun x hx => ?_) (fun x hx => ?_)
    fun β hβ => ncard_blockImage_blockLine_diff_eq_one_of_eq_insert hC hβ
      (blockLine_eq_insert_orbit_of_isSymplecticTransvection_of_two_le h89 h113 hC hrad hW hn3
        hMZ hHns hs hk hsp hβ).1
  · have h := exists_subgroup_eq_insert_Vmem_of_isSymplecticTransvection hZ hsp (x := x)
      (by rw [← hcls]; exact hx)
    rwa [← hcls] at h
  · have h := two_le_ncard_Vmem_of_isSymplecticTransvection hZ hf hsp (x := x)
      (by rw [← hcls]; exact hx)
    rwa [← hcls] at h

end CFSG.OddTranspositions.PartFour
