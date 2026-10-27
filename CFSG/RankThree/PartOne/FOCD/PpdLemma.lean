module

public import CFSG.Timmesfeld.Orders.Bang
import CFSG.RankThree.PartOne.S12K.Rigidity
import all CFSG.Timmesfeld.Orders.Distinct
public import CFSG.RankThree.PartOne.FOC.Transfer

public section

namespace CFSG.RankThree.PartOne.FOCD

open Subgroup CFSG CFSG.Blueprint CFSG.RankThree.PartOne CFSG.RankThree.PartOne.FOC
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)

open CFSG.RankThree.PartOne.S12K (charTwoOrder card_of_lieModel_two)

open CFSG.Timmesfeld CFSG.Timmesfeld.Orders
open CFSG.Open

section Certs


theorem ppd_dvd_card_lieModel_two {X : Type} [Group X] {t : StatedLieTag} {n m : ℕ}
    (hX : LieModel X t n 2 m) (hm : 2 ≤ m) :
    (∀ r, IsPrimitivePrimeDivisor r (2 * m) → r ∣ Nat.card X) ∨
      (t = .twistedB2 ∧ ∀ r, IsPrimitivePrimeDivisor r (4 * m) → r ∣ Nat.card X) := by
  obtain ⟨hadm, hcard⟩ := card_of_lieModel_two hX
  have hm1 : 1 ≤ m := by omega
  have h2m : 2 * m ∣ m * 2 := by rw [mul_comm]
  have hpos : 0 < 2 * m := by omega
  have hpos4 : 0 < 4 * m := by omega
  cases t
  case PSL =>
    obtain ⟨-, -, hn, -⟩ := hadm
    refine Or.inl fun r hr => ?_
    rw [hcard]
    exact (profile_ordA (n := n - 1) (f := m) (by omega) hm1 |>.prim r _ hr hpos).2
      (by unfold zA; exact ⟨2, by simp; omega, h2m⟩)
  case PSU =>
    obtain ⟨-, -, hn, -⟩ := hadm
    refine Or.inl fun r hr => ?_
    rw [hcard]
    exact (profile_ordTwistedA (n := n - 1) (g := m) (by omega) hm1 |>.prim r _ hr hpos).2
      (by unfold zU; exact ⟨2, by simp; omega, Or.inl ⟨even_two, h2m⟩⟩)
  case PSp =>
    obtain ⟨-, -, hn, -⟩ := hadm
    refine Or.inl fun r hr => ?_
    rw [hcard]
    exact (profile_ordBC (n := n) hm1 |>.prim r _ hr hpos).2
      (by unfold zBC; exact ⟨1, by simp; omega, by simpa using h2m⟩)
  case POmegaOdd => exact absurd rfl hadm.2.2.2
  case POmegaPlus =>
    obtain ⟨-, -, hn⟩ := hadm
    refine Or.inl fun r hr => ?_
    rw [hcard]
    exact (profile_ordD (n := n) (by omega) hm1 |>.prim r _ hr hpos).2
      (by unfold zD; exact Or.inr ⟨1, by simp; omega, by simpa using h2m⟩)
  case POmegaMinus =>
    obtain ⟨-, -, hn⟩ := hadm
    refine Or.inl fun r hr => ?_
    rw [hcard]
    exact (profile_ordTwistedD (n := n) (by omega) hm1 |>.prim r _ hr hpos).2
      (by unfold z2D; exact Or.inr ⟨1, by simp; omega, by simpa using h2m⟩)
  case G2 =>
    refine Or.inl fun r hr => ?_
    rw [hcard]
    exact (profile_ordG2 (f := m) hm1 |>.prim r _ hr hpos).2
      (by unfold zG2 zList; exact ⟨2, by simp, h2m⟩)
  case F4 =>
    refine Or.inl fun r hr => ?_
    rw [hcard]
    exact (profile_ordF4 (f := m) hm1 |>.prim r _ hr hpos).2
      (by unfold zF4 zList; exact ⟨2, by simp, h2m⟩)
  case E6 =>
    refine Or.inl fun r hr => ?_
    rw [hcard]
    exact (profile_ordE6 (f := m) hm1 |>.prim r _ hr hpos).2
      (by unfold zE6 zList; exact ⟨2, by simp, h2m⟩)
  case E7 =>
    refine Or.inl fun r hr => ?_
    rw [hcard]
    exact (profile_ordE7 (f := m) hm1 |>.prim r _ hr hpos).2
      (by unfold zE7 zList; exact ⟨2, by simp, h2m⟩)
  case E8 =>
    refine Or.inl fun r hr => ?_
    rw [hcard]
    exact (profile_ordE8 (f := m) hm1 |>.prim r _ hr hpos).2
      (by unfold zE8 zList; exact ⟨2, by simp, h2m⟩)
  case twistedE6 =>
    refine Or.inl fun r hr => ?_
    rw [hcard]
    exact (profile_ordTwistedE6 (f := m) hm1 |>.prim r _ hr hpos).2
      (by unfold z2E6; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h2m)))))
  case trialityD4 =>
    refine Or.inl fun r hr => ?_
    rw [hcard]
    exact (profile_ordTrialityD4 (f := m) hm1 |>.prim r _ hr hpos).2
      (by unfold zD4; exact Or.inr (Or.inr h2m))
  case twistedB2 =>
    refine Or.inr ⟨rfl, fun r hr => ?_⟩
    rw [hcard]
    refine (profile_ordSuzuki (f := m) hm1 |>.prim r _ hr hpos4).2 ?_
    unfold zSz
    refine Or.inl ⟨by rw [show m * 2 = 2 * m by ring, ← mul_assoc]; exact dvd_refl _, ?_⟩
    intro hd
    have := Nat.le_of_dvd (by omega) hd
    omega
  case twistedG2 =>
    obtain ⟨-, -, -, hp3, -⟩ := hadm
    omega
  case twistedF4 =>
    refine Or.inl fun r hr => ?_
    rw [hcard]
    exact (profile_ordTwistedF4 (f := m) hm1 |>.prim r _ hr hpos).2
      (by unfold z2F4; exact Or.inr (Or.inl ⟨2, by ring⟩))
  case Tits =>
    obtain ⟨-, -, -, -, hm1'⟩ := hadm
    omega

theorem fieldInnerT_of_no_ppd {T : Type} [Group T] [Finite T] {p : ℕ} (hp5 : 5 ≤ p)
    (h : ∀ f : ℕ, 1 ≤ f → ∀ r : ℕ, r.Prime → r ∣ Nat.card T →
      ¬ IsPrimitivePrimeDivisor r (2 * (p * f)) ∧ ¬ IsPrimitivePrimeDivisor r (4 * (p * f))) :
    FieldInnerT p T := by
  intro _ x β E _ _ _ _ _ _ _ ⟨t, n, f, hf, hLie⟩
  have hm : 5 ≤ p * f := le_trans hp5 (Nat.le_mul_of_pos_right p hf)
  have h2 : Nat.card (↥E ⧸ Subgroup.center ↥E) ∣ Nat.card E := by
    rw [← Subgroup.index_eq_card]
    exact Subgroup.index_dvd_card _
  have hdvd : Nat.card (↥E ⧸ Subgroup.center ↥E) ∣ Nat.card T :=
    h2.trans (Subgroup.card_subgroup_dvd_card E)
  rcases ppd_dvd_card_lieModel_two hLie (by omega) with h2m | ⟨-, h4m⟩
  · obtain ⟨r, hr⟩ := exists_isPrimitivePrimeDivisor (k := 2 * (p * f)) (by omega) (by omega)
    exact (h f hf r hr.1 ((h2m r hr).trans hdvd)).1 hr
  · obtain ⟨r, hr⟩ := exists_isPrimitivePrimeDivisor (k := 4 * (p * f)) (by omega) (by omega)
    exact (h f hf r hr.1 ((h4m r hr).trans hdvd)).2 hr

end Certs

end CFSG.RankThree.PartOne.FOCD
