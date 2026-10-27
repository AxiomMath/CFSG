module

public import CFSG.Timmesfeld.RootInvolutionCenter
public import CFSG.Timmesfeld.Bridge.OddTranspMain
public import CFSG.RankThree.GF2n.Tim79aSec23One

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] {M V Q P H : Subgroup G} [Finite G]

@[expose] def Dtilde (V H : Subgroup G) : Set (Xbar V H ⧸ Subgroup.center (Xbar V H)) :=
  QuotientGroup.mk' (Subgroup.center (Xbar V H)) '' Dy V H

theorem exists_two_ne {α : Type*} [Finite α] (h : 2 < Nat.card α) (e : α) :
    ∃ a b : α, a ≠ e ∧ b ≠ e ∧ a ≠ b := by
  haveI := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card] at h
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp h
  by_cases ha : a = e
  · exact ⟨b, c, fun h => hab (ha.trans h.symm), fun h => hac (ha.trans h.symm), hbc⟩
  by_cases hb : b = e
  · exact ⟨a, c, ha, fun h => hbc (hb.trans h.symm), hac⟩
  exact ⟨a, b, ha, hb, hab⟩

namespace MinCex

variable (hc : MinCex M V Q P H)
include hc

theorem tilde_noSolvable (hd : Sec23Data V H) :
    ∀ N : Subgroup (Xbar V H ⧸ Subgroup.center (Xbar V H)), N.Normal →
      Group.IsSolvable N → N = ⊥ := fun N hN hsol => by
  haveI := hN
  exact CFSG.Timmesfeld.solvable_normal_eq_bot_quotient_center hd.solv N hsol

theorem tilde_hyp (hd : Sec23Data V H)
    (hnondeg : ∃ d ∈ Dy V H, ∃ e ∈ Dy V H, orderOf (d * e) = 4) :
    CFSG.Timmesfeld.Hyp (Xbar V H ⧸ Subgroup.center (Xbar V H)) (Dtilde V H) :=
  CFSG.Timmesfeld.image_hyp_center hd.isClass hd.root hd.gen hd.solv hd.noncentral hnondeg

theorem tilde_setup (hd : Sec23Data V H)
    (hdeg : ∀ d ∈ Dy V H, ∀ e ∈ Dy V H, orderOf (d * e) ≠ 4) :
    CFSG.Timmesfeld.Bridge.Asc72.Setup (Xbar V H ⧸ Subgroup.center (Xbar V H)) (Dtilde V H) where
  isClass := CFSG.Timmesfeld.image_isClass_center hd.isClass
  oddT := CFSG.Timmesfeld.image_isOddTransp_center hd.root hd.noncentral hdeg
  gen := CFSG.Timmesfeld.image_closure_eq_top_center hd.gen

theorem tilde_meetsSq (hd : Sec23Data V H) (h4 : 4 ≤ Nat.card (barOf V H V)) :
    ∃ u ∈ Dtilde V H, ∃ v ∈ Dtilde V H, u ≠ v ∧ Commute u v ∧ u * v ∈ Dtilde V H := by
  obtain ⟨a, b, ha1, hb1, hab⟩ := exists_two_ne (α := ↥(barOf V H V)) (by omega) 1
  have hmem : ∀ x : Hbar V H, x ∈ barOf V H V → x ≠ 1 →
      ∃ y : Xbar V H, y ∈ Dy V H ∧ (y : Hbar V H) = x :=
    fun x hx hx1 => ⟨⟨x, barOf_V_le V H hx⟩, hc.barOf_V_subset_dbarOf hx hx1, rfl⟩
  obtain ⟨a', ha'D, ha'⟩ := hmem a.1 a.2 (fun h => ha1 (Subtype.ext h))
  obtain ⟨b', hb'D, hb'⟩ := hmem b.1 b.2 (fun h => hb1 (Subtype.ext h))
  have hb2 : b.1 * b.1 = 1 := by
    have := hc.barOf_V_sq b.2
    rwa [pow_two] at this
  have hab1 : a.1⁻¹ * b.1 ≠ 1 := by
    intro h
    exact hab (Subtype.ext (inv_mul_eq_one.mp h))
  have hab2 : a.1 * b.1 ≠ 1 := by
    intro h
    have : b.1⁻¹ = b.1 := inv_eq_of_mul_eq_one_right hb2
    exact hab (Subtype.ext ((eq_inv_of_mul_eq_one_left h).trans this))
  obtain ⟨c', hc'D, hc'⟩ := hmem (a.1⁻¹ * b.1)
    ((barOf V H V).mul_mem ((barOf V H V).inv_mem a.2) b.2) hab1
  obtain ⟨e', he'D, he'⟩ := hmem (a.1 * b.1) ((barOf V H V).mul_mem a.2 b.2) hab2
  refine ⟨_, ⟨a', ha'D, rfl⟩, _, ⟨b', hb'D, rfl⟩, ?_, ?_, ?_⟩
  · intro h
    have hz : a'⁻¹ * b' ∈ Subgroup.center (Xbar V H) := QuotientGroup.eq.mp h
    have hcb : a'⁻¹ * b' = c' := by
      apply Subtype.ext
      simp [ha', hb', hc']
    exact hd.noncentral c' hc'D (hcb ▸ hz)
  · have : Commute a' b' := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, ha', hb']
      exact hc.barOf_V_comm a.2 b.2
    exact this.map _
  · refine ⟨e', he'D, ?_⟩
    have : a' * b' = e' := by
      apply Subtype.ext
      simp [ha', hb', he']
    simp [← this]

theorem tilde_solvableRadical_eq_bot (hd : Sec23Data V H) :
    CFSG.solvableRadical (Xbar V H ⧸ Subgroup.center (Xbar V H)) = ⊥ := by
  refine le_antisymm (sSup_le fun N hN => ?_) bot_le
  obtain ⟨hNn, hsol⟩ := hN
  exact (hc.tilde_noSolvable hd N hNn hsol).le

theorem tilde_isSimple (hd : Sec23Data V H)
    (hdeg : ∀ d ∈ Dy V H, ∀ e ∈ Dy V H, orderOf (d * e) ≠ 4)
    (hsq : ∃ u ∈ Dtilde V H, ∃ v ∈ Dtilde V H, u ≠ v ∧ Commute u v ∧ u * v ∈ Dtilde V H) :
    IsSimpleGroup (Xbar V H ⧸ Subgroup.center (Xbar V H)) := by
  obtain ⟨hrad, hsimp⟩ := CFSG.Timmesfeld.Bridge.OddTransp.oddTranspSimple _ _
    (hc.tilde_setup hd hdeg) hsq
  have hz : CFSG.Timmesfeld.Bridge.zStar (Xbar V H ⧸ Subgroup.center (Xbar V H)) = ⊥ :=
    hrad ▸ hc.tilde_solvableRadical_eq_bot hd
  haveI := hsimp
  exact ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.isSimpleGroup

theorem tilde_isBender (hd : Sec23Data V H)
    (hdeg : ∀ d ∈ Dy V H, ∀ e ∈ Dy V H, orderOf (d * e) ≠ 4)
    (hsq : ∃ u ∈ Dtilde V H, ∃ v ∈ Dtilde V H, u ≠ v ∧ Commute u v ∧ u * v ∈ Dtilde V H)
    (hdisc : CFSG.Timmesfeld.Connectivity.Disconnected (Dtilde V H)) :
    CFSG.BenderSuzuki.IsBenderGroup (Xbar V H ⧸ Subgroup.center (Xbar V H)) :=
  CFSG.Timmesfeld.Bridge.OddTransp.oddTranspBender _ _ (hc.tilde_setup hd hdeg)
    (hc.tilde_noSolvable hd) hsq hdisc

end MinCex

end CFSG.RankThree.GF2n.Tim79a
