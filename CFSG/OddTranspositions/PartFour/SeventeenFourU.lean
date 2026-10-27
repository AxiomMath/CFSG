module

public import CFSG.OddTranspositions.PartFour.RootLift
public import CFSG.OddTranspositions.PartFour.RootGroupU
public import CFSG.OddTranspositions.PartFour.SeventeenFourTorus
public import CFSG.OddTranspositions.PartFour.UnitaryLine
public import CFSG.OddTranspositions.PartFour.UnitaryPlaneSL2

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity CFSG.LocalAnalysis.WeakClosure81.SevenK

theorem pos_of_isUnitaryTransvection {X : Type} [Group X] {s : X} {d f : ℕ}
    (hs : IsUnitaryTransvection X d f s) : 0 < f := by
  obtain ⟨F, hF, hFfin, hFcard, -⟩ := hs
  letI : Finite F := hFfin
  letI : Field F := hF
  have h2 : 1 < Nat.card F := Finite.one_lt_card
  rw [hFcard] at h2
  rcases Nat.eq_zero_or_pos f with rfl | h
  · simp at h2
  · exact h

private theorem seventeenFourU_arith {q r j : ℕ} (hq : 2 ≤ q) (hr : 1 ≤ r) (hrq : r ≤ q - 1)
    (hj : 0 < j) (hle : r * q ^ j ≤ q ^ 2) (hdvd : q + 1 ∣ r * q ^ j - 1) : r = 1 ∧ j = 2 := by
  have hj2 : j ≤ 2 :=
    (Nat.pow_le_pow_iff_right hq).mp (le_trans (Nat.le_mul_of_pos_left _ hr) hle)
  interval_cases j
  · rw [pow_one] at hle hdvd
    have hrq1 : 0 < r * q := Nat.mul_pos (by omega) (by omega)
    have heq : r * q - 1 + (r + 1) = r * (q + 1) := by rw [mul_add, mul_one]; omega
    have h1 : q + 1 ∣ r + 1 := (Nat.dvd_add_right hdvd).mp (heq ▸ dvd_mul_left _ _)
    have := Nat.le_of_dvd (by omega) h1
    omega
  · refine ⟨le_antisymm ?_ hr, rfl⟩
    exact Nat.le_of_mul_le_mul_right (by simpa using hle) (by positivity)

variable {G : Type} [Group G] [Finite G] {D : Set G}

private theorem seventeenFourU_ncard_blockImage_le (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC)
    {d f : ℕ} (hd : 3 ≤ d)
    (hut : IsUnitaryTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) d f s)
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) :
    (blockImage hC '' (blockLine D hC.alpha β \ {hC.alpha})).ncard ≤ 2 ^ f - 1 := by
  obtain ⟨b0, hb0⟩ := nonempty_of_mem_blockClass hC.isBlock_alpha.nonempty hβ.1
  let b : Halpha D hC.alpha := ⟨b0, Subgroup.subset_closure
    (show b0 ∈ DalphaStar D hC.alpha from ⟨β, hβ, hb0⟩)⟩
  have hbD : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b ∈ imageClass hC :=
    ⟨b, (mem_DstarH_iff hC).mpr ⟨β, hβ, hb0⟩, rfl⟩
  have hcls := imageClass_eq_setOf_isConj hC hs
  have hVq := ncard_Vmem_of_isUnitaryTransvection (center_eq_bot_quotient_H hC) hd hut
    (show _ ∈ {y | IsConj s y} by rw [← hcls]; exact hbD)
  rw [← hcls, ncard_Vmem_eq h89 h113 hC hrad hW hn3 hMZ hHns hβ (b := b) hb0] at hVq
  have hβpos : 0 < β.ncard := (Set.ncard_pos (Set.toFinite _)).mpr ⟨b0, hb0⟩
  rw [← hVq]
  exact Nat.le_mul_of_pos_right _ hβpos

theorem blockLine_eq_insert_orbit_of_isUnitaryTransvection
    (h89 : PartThree.Lemma8_9) (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC)
    {d f : ℕ} (hd : 4 ≤ d)
    (hut : IsUnitaryTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) d f s)
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) :
    blockLine D hC.alpha β =
        insert hC.alpha ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)) ∧
      ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)).ncard = (2 ^ f) ^ 2 := by
  have hZ := center_eq_bot_quotient_H hC
  have hf := pos_of_isUnitaryTransvection hut
  have hcls := imageClass_eq_setOf_isConj hC hs
  obtain ⟨K0, hgen, hconj, hord⟩ := exists_subgroup_of_isUnitaryTransvection hZ (by omega) hut
  rw [← hcls] at hgen hconj hord
  obtain ⟨j, hj, hm⟩ := exists_ncard_orbit_Malpha_eq_two_pow_mul h89 h113 hC hrad hW hn3 hMZ
    hHns K0 hf hgen hconj hord hβ
  obtain ⟨v, hv, w, hw, hvw, hne, hcount, g, hgo, hgv, hgw, hsemi⟩ :=
    exists_lineMem_torus_of_isUnitaryTransvection hZ hd hut
  rw [← hcls] at hv hw hne hcount hgv hgw hsemi
  have hodd : Odd (orderOf g) := by
    rw [hgo]
    exact (Nat.even_pow.mpr ⟨even_two, hf.ne'⟩).add_one
  have hdvd := dvd_ncard_blockLine_sub_two_of_torus h89 h113 hC hrad hW hn3 hMZ hHns hv hw hvw
    hne hodd hgv hgw hsemi hβ
  have hle := ncard_blockLine_le h89 h113 hC hrad hW hn3 hMZ hv hw hvw hne hβ
  have hΔ := ncard_blockLine_diff_eq h113 hC hrad hn3 hHns hβ
  have hαℓ : hC.alpha ∈ blockLine D hC.alpha β := left_mem_blockLine hC.isBlock_alpha.subset
  have hℓ := Set.ncard_diff_singleton_add_one hαℓ (Set.toFinite _)
  have hβΔ : β ∈ blockLine D hC.alpha β \ {hC.alpha} :=
    ⟨right_mem_blockLine hβ.1 hβ.2.1, fun h => hβ.2.2.1 (Set.mem_singleton_iff.mp h)⟩
  have hr : 0 < (blockImage hC '' (blockLine D hC.alpha β \ {hC.alpha})).ncard :=
    (Set.ncard_pos (Set.toFinite _)).mpr ⟨_, Set.mem_image_of_mem _ hβΔ⟩
  have hrq := seventeenFourU_ncard_blockImage_le h89 h113 hC hrad hW hn3 hMZ hHns hs (by omega)
    hut hβ
  rw [hgo] at hdvd
  rw [pow_mul] at hm
  generalize (blockImage hC '' (blockLine D hC.alpha β \ {hC.alpha})).ncard = r at hΔ hr hrq
  generalize hO : ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)).ncard = k at hΔ hm
  subst hm
  obtain ⟨-, rfl⟩ := seventeenFourU_arith (Nat.one_lt_two_pow hf.ne') hr hrq hj (by omega)
    (by rw [← hΔ]; convert hdvd using 1; omega)
  exact ⟨(blockLine_eq_insert_orbit_of_ncard_le h89 h113 hC hrad hW hn3 hMZ hHns hv hw hvw hne
    hcount hβ hO.ge).1, rfl⟩

end CFSG.OddTranspositions.PartFour
