module

public import CFSG.OddTranspositions.PartFour.Fourteen.Statements
public import CFSG.OddTranspositions.AscTheoremTwo
public import CFSG.OddTranspositions.HalphaQuotient
import CFSG.OddTranspositions.PartFour.Fourteen.BraidSolvable
import CFSG.OddTranspositions.PartThree.SixThreeGlobal
import CFSG.OddTranspositions.LocalSecondSolvable
import CFSG.OddTranspositions.HalphaCard
import CFSG.OddTranspositions.WidthOne
public import CFSG.Milestones.OO_odd_order_solvable
public import CFSG.Timmesfeld.Bridge.RootSetsConn3

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Bridge.OddTransp

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem not_almostSimpleCase_of_derivedSeries (hS : Setup G D)
    (hder : derivedSeries G 1 = derivedSeries G 2) : ¬ AlmostSimpleCase G D := by
  rintro ⟨M, hMn, -, -, -, -, hidx, hW, -⟩
  have := hMn
  have hne : ∀ x ∈ D, QuotientGroup.mk' M x ≠ 1 := by
    intro x hx h1
    have hxM : x ∈ M := (QuotientGroup.eq_one_iff x).mp h1
    have hDM : D ⊆ M := fun y hy => by
      obtain ⟨g, rfl⟩ := isConj_iff.mp (hS.isConj hx hy)
      exact hMn.conj_mem x hxM g
    have hMtop : M = ⊤ := by
      rw [eq_top_iff, ← hS.gen]
      exact (Subgroup.closure_le M).mpr hDM
    rw [hMtop, Subgroup.index_top] at hidx
    omega
  obtain ⟨d₀, hd₀⟩ := hS.isClass
  have hd₀D : d₀ ∈ D := hd₀ ▸ IsConj.refl d₀
  have hSQ : Setup (G ⧸ M) (QuotientGroup.mk' M '' D) :=
    ⟨image_isClass_quotient hd₀ M, image_isOddTransp_quotient M hS.oddT hne,
      image_closure_eq_top_quotient M hS.gen⟩
  have h2 : Nat.card ((G ⧸ M) ⧸ CFSG.oddCore (G ⧸ M)) = 2 :=
    index_oddCore_eq_two_of_widthOne hSQ hW
  have hOodd : Odd (Nat.card (CFSG.oddCore (G ⧸ M))) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [(CFSG.oddCore_eq_piCore (G ⧸ M)).trans (CFSG.pPrimeCore_eq_piCore (G ⧸ M) 2).symm]
    exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  have : Group.IsSolvable (CFSG.oddCore (G ⧸ M)) := CFSG.Milestones.odd_order_solvable hOodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsCyclic ((G ⧸ M) ⧸ CFSG.oddCore (G ⧸ M)) := isCyclic_of_prime_card h2
  have : Group.IsSolvable ((G ⧸ M) ⧸ CFSG.oddCore (G ⧸ M)) := by
    let := IsCyclic.commGroup (α := (G ⧸ M) ⧸ CFSG.oddCore (G ⧸ M))
    exact isSolvable_of_comm mul_comm
  have hQsolv : Group.IsSolvable (G ⧸ M) :=
    solvable_of_ker_le_range (CFSG.oddCore (G ⧸ M)).subtype
      (QuotientGroup.mk' (CFSG.oddCore (G ⧸ M)))
      (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
  have hQder : derivedSeries (G ⧸ M) 1 = derivedSeries (G ⧸ M) 2 := by
    rw [← map_derivedSeries_eq (QuotientGroup.mk'_surjective M) 1,
      ← map_derivedSeries_eq (QuotientGroup.mk'_surjective M) 2, hder]
  have hbot : derivedSeries (G ⧸ M) 1 = ⊥ := by
    obtain ⟨n, hn⟩ := hQsolv.solvable
    have key : ∀ k, derivedSeries (G ⧸ M) (k + 1) = derivedSeries (G ⧸ M) 1 := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [derivedSeries_succ (G ⧸ M) (k + 1), ih]
        exact hQder.symm
    rw [← key n, derivedSeries_succ, hn, Subgroup.commutator_bot_left]
  have hcomm : ∀ x y : G ⧸ M, x * y = y * x := by
    intro x y
    have h : (⊤ : Subgroup (G ⧸ M)) ≤ Subgroup.centralizer (⊤ : Subgroup (G ⧸ M)) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, ← commutator_def, ← derivedSeries_one,
        hbot]
    exact Subgroup.mem_centralizer_iff.mp (h (Subgroup.mem_top y)) x (Subgroup.mem_top x)
  have hsub : QuotientGroup.mk' M '' D ⊆ {QuotientGroup.mk' M d₀} := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨g, rfl⟩ := isConj_iff.mp (hS.isConj hd₀D hy)
    rw [Set.mem_singleton_iff, map_mul, map_mul, map_inv,
      hcomm (QuotientGroup.mk' M g) (QuotientGroup.mk' M d₀), mul_inv_cancel_right]
  have htop : (⊤ : Subgroup (G ⧸ M)) ≤ Subgroup.zpowers (QuotientGroup.mk' M d₀) := by
    rw [← hSQ.gen, Subgroup.zpowers_eq_closure]
    exact Subgroup.closure_mono hsub
  have hle : Nat.card (G ⧸ M) ≤ orderOf (QuotientGroup.mk' M d₀) := by
    rw [← Nat.card_zpowers, ← Subgroup.card_top (G := G ⧸ M)]
    exact Subgroup.card_le_of_le htop
  have hdvd : orderOf (QuotientGroup.mk' M d₀) ∣ 2 := orderOf_dvd_of_pow_eq_one (by
    rw [pow_two, ← map_mul, hS.oddT.mul_self_eq_one hd₀D, map_one])
  have hidx' : M.index = Nat.card (G ⧸ M) := rfl
  have := Nat.le_of_dvd two_pos hdvd
  omega

theorem ascList_of_disconnected (h1 : TheoremOne) (hS : Setup G D)
    (hdis : CFSG.Timmesfeld.Connectivity.Disconnected D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hder : derivedSeries G 1 = derivedSeries G 2) : AscList G D := by
  rcases h1 G D hS.isClass hS.oddT.1 hS.oddT.2 hS.gen hrad
      (exists_subgroup_of_disconnected hS hdis) with hB | ⟨f, n, hf, -, he⟩ | hA
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hB)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨f, n, hf, he⟩)))
  · exact (not_almostSimpleCase_of_derivedSeries hS hder hA).elim

theorem ascList_of_isSolvable_Halpha (h2 : AschbacherTheoremTwo) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hsolv : Group.IsSolvable (Halpha D hC.alpha)) : AscList G D := by
  have hL : LocalSecond D := localSecond_of_isSolvable_Halpha hC hsolv
  rcases h2 G D hC.setup hC hL hrad with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

theorem natCard_quotient_Halpha_lt (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) :
    Nat.card (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) < Nat.card G := by
  have h1 : Nat.card (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≤
      Nat.card (Halpha D hC.alpha) :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
  have h2 : Nat.card (Halpha D hC.alpha) < Nat.card G := by
    rw [← Subgroup.card_top (G := G)]
    exact Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr (Halpha_ne_top hC hrad))
  exact lt_of_le_of_lt h1 h2

theorem localSecond_of_threeTransp_imageClass (hC : HypothesisC D)
    (h3 : ∀ d ∈ imageClass hC, ∀ e ∈ imageClass hC, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)) :
    LocalSecond D := by
  have hS := hC.setup
  refine localSecond_of_DalphaStar_triangles hC fun x hx y hy t ht htri => ?_
  set H := Halpha D hC.alpha with hHdef
  set π := QuotientGroup.mk' (CFSG.solvableRadical H) with hπ
  let x' : H := ⟨x, Subgroup.subset_closure hx⟩
  let y' : H := ⟨y, Subgroup.subset_closure hy⟩
  let t' : H := ⟨t, Subgroup.subset_closure ht⟩
  have hxI : π x' ∈ imageClass hC := ⟨x', hx, rfl⟩
  have hyI : π y' ∈ imageClass hC := ⟨y', hy, rfl⟩
  have htI : π t' ∈ imageClass hC := ⟨t', ht, rfl⟩
  have hsq : ∀ a : H, (a : G) ∈ D → π a * π a = 1 := fun a ha => by
    rw [← map_mul, show a * a = 1 from Subtype.ext (hS.oddT.mul_self_eq_one ha), map_one]
  have hcube : ∀ a b : H, (a : G) ∈ D → (b : G) ∈ D → ¬ Commute (a : G) b →
      π a ∈ imageClass hC → π b ∈ imageClass hC → (π a * π b) ^ 3 = 1 := by
    intro a b ha hb hab haI hbI
    have hodd : Odd (orderOf ((a : G) * b)) := hS.oddT.odd_of_not_commute ha hb hab
    have hdvd : orderOf (π a * π b) ∣ orderOf ((a : G) * b) := by
      have hc : orderOf ((a : G) * b) = orderOf (a * b) := Subgroup.orderOf_coe (a * b)
      rw [← map_mul, hc]
      exact orderOf_map_dvd _ _
    have hne2 : orderOf (π a * π b) ≠ 2 := fun h2 => by
      rw [h2] at hdvd
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
    rw [← orderOf_dvd_iff_pow_eq_one]
    rcases h3 _ haI _ hbI with h | h | h
    · rw [h]; exact one_dvd 3
    · exact absurd h hne2
    · rw [Set.mem_singleton_iff] at h
      rw [h]
  have hxy3 := hcube x' y' htri.1 htri.2.2.1 htri.2.2.2.2.2.1 hxI hyI
  have hyt3 : (π y' * π t') ^ 3 = 1 :=
    hcube y' t' htri.2.2.1 htri.2.1 (fun h => htri.2.2.2.2.2.2 h.symm) hyI htI
  have hxt : Commute (π x') (π t') :=
    ((show Commute x' t' from Subtype.ext htri.2.2.2.2.1.eq)).map π
  have hxx := hsq x' htri.1
  have hyy := hsq y' htri.2.2.1
  have htt := hsq t' htri.2.1
  have hYbar : Group.IsSolvable
      (Subgroup.closure ({π x', π y', π t'} : Set (H ⧸ CFSG.solvableRadical H))) :=
    isSolvable_closure_of_braid hxx hyy htt hxt (braid_of_cube hxx hyy hxy3)
      (braid_of_cube hyy htt hyt3)
  set Ybar := Subgroup.closure ({π x', π y', π t'} : Set (H ⧸ CFSG.solvableRadical H))
  set P : Subgroup H := Ybar.comap π
  have hMP : CFSG.solvableRadical H ≤ P := fun m hm => by
    change π m ∈ Ybar
    have h1 : π m = 1 := (QuotientGroup.eq_one_iff m).mpr hm
    rw [h1]
    exact Subgroup.one_mem _
  have hPsolv : Group.IsSolvable P := by
    have : Group.IsSolvable (CFSG.solvableRadical H) :=
      CFSG.Timmesfeld.Bridge.OddTransp.isSolvable_solvableRadical
    have := hYbar
    let g : P →* Ybar := (π.comp P.subtype).codRestrict Ybar fun p => p.2
    exact solvable_of_ker_le_range (Subgroup.inclusion hMP) g fun p hp => by
      have hp1 : π (p : H) = 1 := congrArg Subtype.val hp
      exact ⟨⟨p, (QuotientGroup.eq_one_iff _).mp hp1⟩, rfl⟩
  set X : Subgroup G := P.map H.subtype
  have hXsolv : Group.IsSolvable X :=
    haveI := hPsolv
    solvable_of_surjective (H.subtype.subgroupMap_surjective P)
  have hmem : ∀ a : H, π a ∈ Ybar → (a : G) ∈ X := fun a ha => ⟨a, ha, rfl⟩
  exact PartThree.orderOf_mul_eq_four_of_solvable_subgroup hS.oddT hS.normal hXsolv
    (hmem x' (Subgroup.subset_closure (by simp)))
    (hmem y' (Subgroup.subset_closure (by simp)))
    (hmem t' (Subgroup.subset_closure (by simp))) htri

end CFSG.OddTranspositions.PartFour
