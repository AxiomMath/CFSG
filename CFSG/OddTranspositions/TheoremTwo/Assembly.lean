module

public import CFSG.OddTranspositions.AscTheoremTwo

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem nonempty_hypothesisC (hS : Setup G D) (hconn : ¬ Disconnected D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) :
    Nonempty (HypothesisC D) := by
  classical
  obtain ⟨d, hd⟩ := hS.nonempty
  have hne : (commSet D d).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hreach : ∀ y, Reach D d y → y = d := by
      intro y hy
      induction hy with
      | refl => rfl
      | tail _ hbc ih =>
          obtain ⟨-, hc, hcomm⟩ := hbc
          rw [ih] at hcomm
          by_contra hne'
          have hmem : _ ∈ commSet D d := ⟨hc, hcomm.symm, hne'⟩
          rw [h] at hmem
          exact hmem
    have hD : ∀ y ∈ D, y = d := fun y hy => hreach y (by
      by_contra hr
      exact hconn ⟨d, hd, y, hy, hr⟩)
    have hcent : ∀ g : G, g * d * g⁻¹ = d := fun g => hD _ (hS.normal g d hd)
    have hN : (Subgroup.zpowers d).Normal := by
      refine ⟨fun x hx g => ?_⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [← conj_zpow, hcent]
      exact Subgroup.zpow_mem_zpowers d k
    have hsolv : Group.IsSolvable (Subgroup.zpowers d) := inferInstance
    have hbot := hrad _ hN hsolv
    have hd1 : d = 1 := by
      have : d ∈ Subgroup.zpowers d := Subgroup.mem_zpowers d
      rwa [hbot, Subgroup.mem_bot] at this
    exact hS.oddT.ne_one hd hd1
  have hfin := (commSet D d).toFinite
  obtain ⟨e, he, hmax⟩ := Finset.exists_max_image hfin.toFinset
    (fun e => (orbitIn D d e).ncard) (hfin.toFinset_nonempty.mpr hne)
  exact ⟨⟨hS, hconn, d, hd, orbitIn D d e,
    ⟨e, hfin.mem_toFinset.mp he, rfl, fun e' he' => hmax e' (hfin.mem_toFinset.mpr he')⟩⟩⟩

@[expose] def ThirdKindExclusionStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G), HypothesisC D →
    (∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) → LocalSecond D →
    SmallerTwoStar (Nat.card G) →
    (∀ u w v : G, IsTriangle D u w v → orderOf (u * v * w) = 4) ∨ O4PairData G D

@[expose] def TheoremTwoLiteStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G), HypothesisC D →
    (∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) →
    (∀ u w v : G, IsTriangle D u w v → orderOf (u * v * w) = 4) →
    SmallerTwoStar (Nat.card G) →
    ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)

theorem smallerTwoStar_of_steps (h71 : ThirdKindExclusionStep) (hlite : TheoremTwoLiteStep) :
    ∀ m, SmallerTwoStar m := by
  intro m
  induction m with
  | zero =>
      intro Y _ _ Θ hcard
      exact absurd hcard (Nat.not_lt_zero _)
  | succ m ih =>
      intro Y _ _ Θ hcard hS hconn hrad hL
      rcases Nat.lt_succ_iff_lt_or_eq.mp hcard with h | h
      · exact ih Y Θ h hS hconn hrad hL
      · have hmin : SmallerTwoStar (Nat.card Y) := h ▸ ih
        obtain ⟨hC⟩ := nonempty_hypothesisC hS hconn hrad
        rcases h71 Y Θ hC hrad hL hmin with hsec | hO4
        · exact Or.inl (hlite Y Θ hC hrad hsec hmin)
        · exact Or.inr hO4

theorem aschbacherTheoremTwo_of_steps (h71 : ThirdKindExclusionStep)
    (hlite : TheoremTwoLiteStep) : AschbacherTheoremTwo := by
  intro G _ _ D hS hC hL hrad
  exact smallerTwoStar_of_steps h71 hlite (Nat.card G + 1) G D (Nat.lt_succ_self _) hS hC.conn
    hrad hL

end CFSG.OddTranspositions

end
