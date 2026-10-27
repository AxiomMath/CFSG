module

public import CFSG.Timmesfeld.Transvection.RankThreeA2Coords
public import CFSG.Timmesfeld.Transvection.RankThreeAlignCoords

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.NaturalModule RankThree
open scoped commutatorElement

variable {G : Type*} [Group G] {Δ : Set (Subgroup G)} {r : ℕ} {P Q : Fin r → Subgroup G}

namespace IsMaxFrame

variable [Finite G] (hfr : IsMaxFrame Δ P Q) (hΔ : IsTransvectionClass Δ)
  (hiso : NoIsolated Δ) (hpts : PointsDetermined Δ) (hml : MeetsLines Δ)
  (hq : ∀ l, 4 ≤ Nat.card (P l)) {n : ℕ} (φ : ∀ l, SL2Coords (P l) (Q l) n)
  {μ : (GaloisField 2 n)ˣ} (hμ1 : μ ≠ 1)
include hfr hΔ hiso hpts hml hq φ hμ1

omit hml in
theorem eq_one_of_conjSub_eq_of_coords {i j : Fin r} (hij : i ≠ j) {x : G}
    (hx : x ∈ shortRootGroup Δ (Q i) (P i) (P j) (Q j)) (hxP : conjSub (P i) x = P i) : x = 1 := by
  have hF := hfr.toIsFrame
  have hR := hΔ.root
  have hcard : Nat.card (Q i) = Nat.card (P i) := hR.card_eq (hF.memQ i) (hF.memP i)
  obtain ⟨⟨hxL, -⟩, -⟩ := mem_shortRootGroup.1 hx
  have hxQ : ∀ e ∈ Q i, Commute x e := fun e he =>
    ((hF.commuting_framePt_lineGroup hR (a := Sum.inr i) (c := Sum.inr i) (d := Sum.inl j)
      (by simp) (by simpa using hij.symm)) e he x hxL).symm
  have hxP' : ∀ a ∈ P i, Commute x a := fun a ha =>
    commute_of_commute_partner (hF.opposite i) hxP hxQ ha
  have hxh : Commute x ((φ i).torusElt μ) := by
    have hle : P i ⊔ Q i ≤ Subgroup.centralizer {x} := sup_le
      (fun a ha => Subgroup.mem_centralizer_singleton_iff.2 (hxP' a ha).symm.eq)
      (fun e he => Subgroup.mem_centralizer_singleton_iff.2 (hxQ e he).symm.eq)
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle ((φ i).torusElt_mem μ))).symm
  have hmem' : (φ i).torusElt μ ∈ Q i ⊔ P i := by
    rw [sup_comm]
    exact (φ i).torusElt_mem μ
  have hqQ : 4 ≤ Nat.card (Q i) := by rw [hcard]; exact hq i
  exact ((hF.toPairFrame hij).flip.commute_shortRootGroup_iff hΔ hiso hpts hqQ
    ((φ i).swap hcard) hmem' ((φ i).swap_mat_of_mat_eq_diagElt hcard ((φ i).mat_torusElt μ))
    (inv_ne_one.2 hμ1) hx).1 hxh

omit hml in
theorem eq_one_of_commutator_eq_one_of_coords {i j k : Fin r} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) {x y : G} (hx : x ∈ shortRootGroup Δ (Q i) (P i) (P j) (Q j))
    (hy : y ∈ shortRootGroup Δ (Q j) (P j) (P k) (Q k)) (hy1 : y ≠ 1) (hxy : ⁅x, y⁆ = 1) :
    x = 1 :=
  hfr.toIsFrame.eq_one_of_commutator_eq_one hΔ hpts hij hik
    (fun _ hx' hP => hfr.eq_one_of_conjSub_eq_of_coords hΔ hiso hpts hq φ hμ1 hij hx' hP)
    (fun _ hy' hP => hfr.eq_one_of_conjSub_eq_of_coords hΔ hiso hpts hq φ hμ1 hjk hy' hP)
    hx hy hy1 hxy

theorem aligned_of_aligned_of_coords {o i j : Fin r} (hoi : o ≠ i) (hoj : o ≠ j) (hij : i ≠ j)
    (hoi' : SL2Coords.Aligned Δ (φ o) (φ i)) (hoj' : SL2Coords.Aligned Δ (φ o) (φ j))
    (hne : ∃ y₀ ∈ shortRootGroup Δ (Q o) (P o) (P i) (Q i), y₀ ≠ 1) :
    SL2Coords.Aligned Δ (φ i) (φ j) :=
  hfr.toIsFrame.aligned_of_aligned hΔ hoi hoj hij φ hoi' hoj'
    (fun _ hy _ hx => hfr.commutator_mem_shortRootGroup_of_coords hΔ hiso hpts hml hq φ hμ1 hoi
      hoj hij hy hx)
    (fun _ hy _ hx hx1 h => hfr.eq_one_of_commutator_eq_one_of_coords hΔ hiso hpts hq φ hμ1
      hoi hoj hij hy hx hx1 h) hne

end IsMaxFrame

end CFSG.Timmesfeld.Transvection
