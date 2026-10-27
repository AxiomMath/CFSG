module

public import CFSG.OddTranspositions.PartFour.LineCount
public import CFSG.OddTranspositions.PartFour.LinePolar

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem blockLine_eq_insert_orbit_of_ncard_le (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    {v w : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hv : v ∈ imageClass hC) (hw : w ∈ imageClass hC) (hvw : Commute v w)
    (hne : perpMem (imageClass hC) v ≠ perpMem (imageClass hC) w) {q : ℕ}
    (hq : (perpMem (imageClass hC) '' lineMem (imageClass hC) v w).ncard ≤ q + 1)
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha)
    (hm : q ≤ ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)).ncard) :
    blockLine D hC.alpha β =
        insert hC.alpha ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)) ∧
      ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)).ncard = q := by
  set O := (fun x => cimg x β) '' (Malpha D hC.alpha : Set G) with hO
  set Δ := blockLine D hC.alpha β \ {hC.alpha} with hΔdef
  have hline := ncard_blockLine_le h89 h113 hC hrad hW hn3 hMZ hv hw hvw hne hβ
  have hΔ : Δ.ncard = (blockImage hC '' Δ).ncard * O.ncard :=
    ncard_blockLine_diff_eq h113 hC hrad hn3 hHns hβ
  have hαℓ : hC.alpha ∈ blockLine D hC.alpha β := left_mem_blockLine hC.isBlock_alpha.subset
  have hℓ : (blockLine D hC.alpha β).ncard = Δ.ncard + 1 :=
    (Set.ncard_diff_singleton_add_one hαℓ (Set.toFinite _)).symm
  have hβΔ : β ∈ Δ :=
    ⟨right_mem_blockLine hβ.1 hβ.2.1, fun h => hβ.2.2.1 (Set.mem_singleton_iff.mp h)⟩
  have hr : 0 < (blockImage hC '' Δ).ncard :=
    (Set.ncard_pos (Set.toFinite _)).mpr ⟨_, Set.mem_image_of_mem _ hβΔ⟩
  have hm1 : 0 < O.ncard :=
    (Set.ncard_pos (Set.toFinite _)).mpr ⟨β, 1, (Malpha D hC.alpha).one_mem, cimg_one β⟩
  generalize hr' : (blockImage hC '' Δ).ncard = r at hΔ hr
  generalize hk : O.ncard = k at hm hm1 hΔ ⊢
  have hrk : r * k ≤ 1 * k := by
    have : r * k ≤ q := by omega
    omega
  have hr1 : r = 1 := le_antisymm (Nat.le_of_mul_le_mul_right hrk hm1) hr
  subst hr1
  refine ⟨?_, by omega⟩
  have hP : blockImage hC '' Δ = {blockImage hC β} := by
    obtain ⟨T, hT⟩ := Set.ncard_eq_one.mp hr'
    have hmem : blockImage hC β ∈ blockImage hC '' Δ := Set.mem_image_of_mem _ hβΔ
    rw [hT, Set.mem_singleton_iff] at hmem
    rw [hT, hmem]
  have hΔO : Δ = O := blockLine_diff_eq_orbit_of_singleton h113 hC hrad hn3 hHns hβ hP
  rw [← hΔO, hΔdef, Set.insert_diff_singleton, Set.insert_eq_of_mem hαℓ]

end CFSG.OddTranspositions.PartFour
