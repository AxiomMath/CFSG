module

public import CFSG.Timmesfeld.Transvection.RankThreeAlignFrame
public import CFSG.Timmesfeld.Transvection.ShortRootHyp

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS
open scoped commutatorElement

variable {G : Type*} [Group G] {Δ : Set (Subgroup G)} {r : ℕ} {P Q : Fin r → Subgroup G}

theorem IsFrame.card_shortRootGroup_swap (hF : IsFrame Δ P Q) (hΔ : IsTransvectionClass Δ)
    {i j : Fin r} (hij : i ≠ j) :
    Nat.card (shortRootGroup Δ (Q i) (P i) (P j) (Q j)) =
      Nat.card (shortRootGroup Δ (Q j) (P j) (P i) (Q i)) := by
  obtain ⟨wi, hwi, -, hPi, hQi⟩ := exists_weylElt hΔ (hF.memP i) (hF.memQ i) (hF.opposite i).symm
  obtain ⟨wj, hwj, -, hPj, hQj⟩ := exists_weylElt hΔ (hF.memP j) (hF.memQ j) (hF.opposite j).symm
  have hfix : ∀ {X : Subgroup G} (k : Fin r), k ≠ i → X ≤ P k ⊔ Q k → conjSub X wi = X :=
    fun {X} k hki hX => conjSub_of_forall_commute fun x hx =>
      (hF.commuting k i hki x (hX hx) wi (sup_comm (P i) (Q i) ▸ hwi)).symm
  have hfix' : ∀ {X : Subgroup G} (k : Fin r), k ≠ j → X ≤ P k ⊔ Q k → conjSub X wj = X :=
    fun {X} k hkj hX => conjSub_of_forall_commute fun x hx =>
      (hF.commuting k j hkj x (hX hx) wj (sup_comm (P j) (Q j) ▸ hwj)).symm
  have hconj : conjSub (shortRootGroup Δ (Q i) (P i) (P j) (Q j)) (wi * wj) =
      shortRootGroup Δ (Q j) (P j) (P i) (Q i) := by
    rw [← shortRootGroup_conjSub hΔ.root, conjSub_mul, conjSub_mul, conjSub_mul, conjSub_mul,
      hfix' i hij le_sup_right, hfix' i hij le_sup_left, hPj, hQj, hQi, hPi,
      hfix j hij.symm le_sup_left, hfix j hij.symm le_sup_right, shortRootGroup_swap_pairs]
  rw [← hconj, Subgroup.card_map_of_injective (MulAut.conj _).injective]

namespace IsMaxFrame

variable [Finite G] (hfr : IsMaxFrame Δ P Q) (hΔ : IsTransvectionClass Δ)
  (hiso : NoIsolated Δ) (hpts : PointsDetermined Δ) (hml : MeetsLines Δ) (hthick : ThickLines Δ)
  (hq : ∀ l, 4 ≤ Nat.card (P l)) {n : ℕ} (φ : ∀ l, SL2Coords (P l) (Q l) n)
  {μ : (GaloisField 2 n)ˣ} (hμ1 : μ ≠ 1)
include hfr hΔ hiso hpts hml hthick hq φ hμ1

theorem card_shortRootGroup_le {i j k : Fin r} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Nat.card (shortRootGroup Δ (Q i) (P i) (P j) (Q j)) ≤
      Nat.card (shortRootGroup Δ (Q i) (P i) (P k) (Q k)) := by
  have hF := hfr.toIsFrame
  obtain ⟨y, hy, hy1⟩ := (hF.toPairFrame hjk).exists_ne_one_of_thickLines hΔ hpts hml (hq j)
    hthick
  have hcomm := fun {x : G} (hx : x ∈ shortRootGroup Δ (Q i) (P i) (P j) (Q j)) =>
    hfr.commutator_mem_shortRootGroup_of_coords hΔ hiso hpts hml hq φ hμ1 hij hik hjk hx hy
  let f : shortRootGroup Δ (Q i) (P i) (P j) (Q j) → shortRootGroup Δ (Q i) (P i) (P k) (Q k) :=
    fun x => ⟨⁅(x : G), y⁆, hcomm x.2⟩
  refine Nat.card_le_card_of_injective f fun x x' hxx' => ?_
  have h1 : ⁅(x : G), y⁆ = ⁅(x' : G), y⁆ := congrArg Subtype.val hxx'
  have hL : ∀ {z : G}, z ∈ shortRootGroup Δ (Q i) (P i) (P k) (Q k) →
      z ∈ lineGroup Δ (Q i) (P k) := fun hz => shortRootGroup_le_lineGroup _ _ _ _ hz
  have hmul : ⁅(x : G) * x', y⁆ = 1 := by
    rw [hF.commutator_mul_left hΔ hij hik x.2 (hL (hcomm x.2)) (hL (hcomm x'.2)), ← h1]
    exact mul_self_of_mem_lineGroup hΔ (hF.memQ i) (hF.memP k) (hF.commuting_QP hik)
      (hL (hcomm x.2))
  have h2 := hfr.eq_one_of_commutator_eq_one_of_coords hΔ hiso hpts hq φ hμ1 hij hik hjk
    (Subgroup.mul_mem _ x.2 x'.2) hy hy1 hmul
  have hxx : (x : G) * x = 1 := mul_self_of_mem_lineGroup hΔ (hF.memQ i) (hF.memP j)
    (hF.commuting_QP hij) (shortRootGroup_le_lineGroup _ _ _ _ x.2)
  refine Subtype.ext ?_
  rw [← mul_left_cancel_iff (a := (x : G)), hxx, h2]

theorem card_shortRootGroup_eq {i j k l : Fin r} (hij : i ≠ j) (hkl : k ≠ l) :
    Nat.card (shortRootGroup Δ (Q i) (P i) (P j) (Q j)) =
      Nat.card (shortRootGroup Δ (Q k) (P k) (P l) (Q l)) := by
  have hF := hfr.toIsFrame
  have hE : ∀ {a b c : Fin r}, a ≠ b → a ≠ c →
      Nat.card (shortRootGroup Δ (Q a) (P a) (P b) (Q b)) =
        Nat.card (shortRootGroup Δ (Q a) (P a) (P c) (Q c)) := by
    intro a b c hab hac
    by_cases hbc : b = c
    · rw [hbc]
    exact le_antisymm (hfr.card_shortRootGroup_le hΔ hiso hpts hml hthick hq φ hμ1 hab hac hbc)
      (hfr.card_shortRootGroup_le hΔ hiso hpts hml hthick hq φ hμ1 hac hab (Ne.symm hbc))
  by_cases hik : i = k
  · subst hik
    exact hE hij hkl
  rw [hE hij hik, hF.card_shortRootGroup_swap hΔ hik]
  exact hE (Ne.symm hik) hkl

end IsMaxFrame

end CFSG.Timmesfeld.Transvection
