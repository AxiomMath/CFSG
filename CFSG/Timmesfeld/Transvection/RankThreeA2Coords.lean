module

public import CFSG.Timmesfeld.Transvection.RankThreeA2
public import CFSG.Timmesfeld.Transvection.RankThreeCoords
public import CFSG.Timmesfeld.Transvection.ShortRoot
public import CFSG.Timmesfeld.Transvection.ShortRootField

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.NaturalModule RankThree
open scoped commutatorElement

variable {G : Type*} [Group G] {Δ : Set (Subgroup G)} {r : ℕ} {P Q : Fin r → Subgroup G}

theorem shortRootGroup_swap_pairs (A E D E' : Subgroup G) :
    shortRootGroup Δ D E' A E = shortRootGroup Δ A E D E' := by
  rw [shortRootGroup, shortRootGroup, lineGroup_comm D A, lineStab_comm E' A, lineStab_comm D E,
    inf_right_comm]

theorem IsFrame.toPairFrame (hF : IsFrame Δ P Q) {i j : Fin r} (hij : i ≠ j) :
    PairFrame Δ (P i) (Q i) (P j) (Q j) :=
  ⟨hF.memP i, hF.memQ i, hF.memP j, hF.memQ j, (hF.opposite i).symm, (hF.opposite j).symm,
    hF.commuting i j hij⟩

namespace IsMaxFrame

variable [Finite G] (hfr : IsMaxFrame Δ P Q) (hΔ : IsTransvectionClass Δ)
  (hiso : NoIsolated Δ) (hpts : PointsDetermined Δ) (hml : MeetsLines Δ)
  (hq : ∀ l, 4 ≤ Nat.card (P l)) {n : ℕ} (φ : ∀ l, SL2Coords (P l) (Q l) n)
  {μ : (GaloisField 2 n)ˣ} (hμ1 : μ ≠ 1)
include hfr hΔ hiso hpts hml hq φ hμ1

theorem commutator_mem_shortRootGroup_of_coords {i j l : Fin r} (hij : i ≠ j) (hil : i ≠ l)
    (hjl : j ≠ l) {x y : G} (hx : x ∈ shortRootGroup Δ (Q i) (P i) (P j) (Q j))
    (hy : y ∈ shortRootGroup Δ (Q j) (P j) (P l) (Q l)) :
    ⁅x, y⁆ ∈ shortRootGroup Δ (Q i) (P i) (P l) (Q l) := by
  have hF := hfr.toIsFrame
  have hR := hΔ.root
  have hcard : ∀ m, Nat.card (Q m) = Nat.card (P m) := fun m => hR.card_eq (hF.memQ m) (hF.memP m)
  have hqQ : ∀ m, 4 ≤ Nat.card (Q m) := fun m => by rw [hcard]; exact hq m
  have hn0 : n ≠ 0 := by
    intro h0
    have h1 := (φ i).card_eq
    rw [h0, pow_zero] at h1
    have := hq i
    omega
  have hmem : ∀ m, (φ m).torusElt μ ∈ P m ⊔ Q m := fun m => (φ m).torusElt_mem μ
  have hmem' : ∀ m, (φ m).torusElt μ ∈ Q m ⊔ P m := fun m => by
    rw [sup_comm]
    exact hmem m
  have hmat : ∀ m, (φ m).mat ((φ m).torusElt μ) = diagElt μ := fun m => (φ m).mat_torusElt μ
  have hmat' : ∀ m, ((φ m).swap (hcard m)).mat ((φ m).torusElt μ) = diagElt μ⁻¹ := fun m =>
    (φ m).swap_mat_of_mat_eq_diagElt (hcard m) (hmat m)
  have hconj : ∀ m, conjSub (P m) ((φ m).torusElt μ) = P m ∧
      conjSub (Q m) ((φ m).torusElt μ) = Q m := fun m => (φ m).conjSub_torusElt μ
  have hodd : ∀ m, Odd (orderOf ((φ m).torusElt μ)) := fun m =>
    (φ m).odd_orderOf_of_mat_eq_diagElt hn0 (hmem m) (hmat m)
  have hμ1' : μ⁻¹ ≠ 1 := inv_ne_one.2 hμ1
  refine hfr.commutator_mem_shortRootGroup hΔ hpts hml hij hil hjl (hmem i) (hconj i).1
    (hconj i).2 (hodd i) ?_ (hmem j) (hconj j).1 (hodd j) ?_ (hmem l) (hconj l).1 (hconj l).2
    (hodd l) ?_ ?_ hx hy
  · intro x' hx' hc
    exact ((hF.toPairFrame hij).flip.commute_shortRootGroup_iff hΔ hiso hpts (hqQ i)
      ((φ i).swap (hcard i)) (hmem' i) (hmat' i) hμ1' hx').1 hc
  · intro D' hD' u hu hc
    have hjD' : Commuting (P j) D' :=
      hD'.2 (P j) (hF.memP j) (hF.commuting_QP hij).symm (hF.commuting_PP hjl)
    have hQjD' : Commuting (Q j) D' :=
      hD'.2 (Q j) (hF.memQ j) (hF.commuting_QQ hij).symm (hF.commuting_QP hjl)
    have hD'j : D' ≠ P j := by
      rintro rfl
      exact ModelRank.not_commuting_of_opposite (hF.opposite j) hQjD'.symm
    exact (commute_lineGroup_iff (φ j) (hmem j) (hmat j) hΔ hiso hpts (hF.memP j) (hF.memQ j)
      hD'.1 (hF.opposite j).symm hjD' hQjD' hD'j (hq j) hμ1 hu).1 hc
  · intro y' hy' hc
    exact ((hF.toPairFrame hjl).flip.commute_shortRootGroup_iff_swap hΔ hiso hpts (hqQ j) (φ l)
      (hmem l) (hmat l) hμ1 hy').1 hc
  · rw [(hF.toPairFrame hil).flip.shortRootGroup_eq_inf hΔ hiso hpts hml (hqQ i)
      ((φ i).swap (hcard i)) (hmem' i) (hmat' i) hμ1' (φ l) (hmem l) (hmat l) hμ1]

theorem commutator_mem_plus_left {i j l : Fin r} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    {v y : G} (hv : v ∈ shortRootGroup Δ (P i) (Q i) (P j) (Q j))
    (hy : y ∈ shortRootGroup Δ (Q j) (P j) (P l) (Q l)) :
    ⁅v, y⁆ ∈ shortRootGroup Δ (P i) (Q i) (P l) (Q l) := by
  have hF := hfr.toIsFrame
  have hR := hΔ.root
  obtain ⟨w, hw, hww, hwP, hwQ⟩ := exists_weylElt hΔ (hF.memP i) (hF.memQ i) (hF.opposite i).symm
  have hw' : w ∈ P i ⊔ Q i := by
    rw [sup_comm]
    exact hw
  have hfix : ∀ {m : Fin r}, i ≠ m → conjSub (P m) w = P m ∧ conjSub (Q m) w = Q m := fun hm =>
    ⟨conjSub_of_forall_commute fun p hp => (hF.commuting_sup_framePt hR (i := i)
      (a := Sum.inl _) (by simpa using hm.symm)) w hw' p hp,
     conjSub_of_forall_commute fun p hp => (hF.commuting_sup_framePt hR (i := i)
      (a := Sum.inr _) (by simpa using hm.symm)) w hw' p hp⟩
  have hX1 : conjSub (shortRootGroup Δ (P i) (Q i) (P j) (Q j)) w =
      shortRootGroup Δ (Q i) (P i) (P j) (Q j) := by
    rw [← shortRootGroup_conjSub hR, hwP, hwQ, (hfix hij).1, (hfix hij).2]
  have hX2 : conjSub (shortRootGroup Δ (Q i) (P i) (P l) (Q l)) w =
      shortRootGroup Δ (P i) (Q i) (P l) (Q l) := by
    rw [← shortRootGroup_conjSub hR, hwP, hwQ, (hfix hil).1, (hfix hil).2]
  have hx : w * v * w⁻¹ ∈ shortRootGroup Δ (Q i) (P i) (P j) (Q j) :=
    hX1 ▸ conj_mem_conjSub w hv
  have hwy : w * y * w⁻¹ = y := by
    rw [((hF.commuting_sup_shortRootGroup hR (i := i) (a := Sum.inr j) (b := Sum.inl l)
      (by simpa using hij.symm) (by simpa using hil.symm)) w hw' y hy).eq, mul_inv_cancel_right]
  have hc := hfr.commutator_mem_shortRootGroup_of_coords hΔ hiso hpts hml hq φ hμ1 hij hil hjl hx hy
  have h1 : ⁅v, y⁆ = w * ⁅w * v * w⁻¹, y⁆ * w⁻¹ := by
    rw [conj_commutatorElement, hwy,
      show w * (w * v * w⁻¹) * w⁻¹ = (w * w) * v * (w * w)⁻¹ by group, hww, one_mul, inv_one,
      mul_one]
  rw [h1, ← hX2]
  exact conj_mem_conjSub w hc

theorem commutator_mem_plus_right {i j l : Fin r} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    {x u : G} (hx : x ∈ shortRootGroup Δ (Q i) (P i) (P j) (Q j))
    (hu : u ∈ shortRootGroup Δ (P i) (Q i) (P l) (Q l)) :
    ⁅x, u⁆ ∈ shortRootGroup Δ (P j) (Q j) (P l) (Q l) := by
  have hF := hfr.toIsFrame
  have hR := hΔ.root
  obtain ⟨w, hw, hww, hwP, hwQ⟩ := exists_weylElt hΔ (hF.memP l) (hF.memQ l) (hF.opposite l).symm
  have hw' : w ∈ P l ⊔ Q l := by
    rw [sup_comm]
    exact hw
  have hfix : ∀ {m : Fin r}, l ≠ m → conjSub (P m) w = P m ∧ conjSub (Q m) w = Q m := fun hm =>
    ⟨conjSub_of_forall_commute fun p hp => (hF.commuting_sup_framePt hR (i := l)
      (a := Sum.inl _) (by simpa using hm.symm)) w hw' p hp,
     conjSub_of_forall_commute fun p hp => (hF.commuting_sup_framePt hR (i := l)
      (a := Sum.inr _) (by simpa using hm.symm)) w hw' p hp⟩
  have hX1 : conjSub (shortRootGroup Δ (P i) (Q i) (P l) (Q l)) w =
      shortRootGroup Δ (Q l) (P l) (P i) (Q i) := by
    rw [← shortRootGroup_swap_pairs (P i), ← shortRootGroup_conjSub hR, hwP, hwQ,
      (hfix hil.symm).1, (hfix hil.symm).2]
  have hX2 : conjSub (shortRootGroup Δ (Q l) (P l) (P j) (Q j)) w =
      shortRootGroup Δ (P j) (Q j) (P l) (Q l) := by
    rw [← shortRootGroup_conjSub hR, hwP, hwQ, (hfix hjl.symm).1, (hfix hjl.symm).2,
      shortRootGroup_swap_pairs]
  have hu' : w * u * w⁻¹ ∈ shortRootGroup Δ (Q l) (P l) (P i) (Q i) :=
    hX1 ▸ conj_mem_conjSub w hu
  have hwx : w * x * w⁻¹ = x := by
    rw [((hF.commuting_sup_shortRootGroup hR (i := l) (a := Sum.inr i) (b := Sum.inl j)
      (by simpa using hil) (by simpa using hjl)) w hw' x hx).eq, mul_inv_cancel_right]
  have hc := hfr.commutator_mem_shortRootGroup_of_coords hΔ hiso hpts hml hq φ hμ1 hil.symm
    hjl.symm hij hu' hx
  have h1 : ⁅u, x⁆ = w * ⁅w * u * w⁻¹, x⁆ * w⁻¹ := by
    rw [conj_commutatorElement, hwx,
      show w * (w * u * w⁻¹) * w⁻¹ = (w * w) * u * (w * w)⁻¹ by group, hww, one_mul, inv_one,
      mul_one]
  have h2 : ⁅u, x⁆ ∈ shortRootGroup Δ (P j) (Q j) (P l) (Q l) := by
    rw [h1, ← hX2]
    exact conj_mem_conjSub w hc
  rw [← commutatorElement_inv]
  exact Subgroup.inv_mem _ h2

end IsMaxFrame

end CFSG.Timmesfeld.Transvection
