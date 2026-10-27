module

public import CFSG.Timmesfeld.Transvection.RankThreeA2Coords
import CFSG.Timmesfeld.Transvection.RankTwoRelMain

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS

variable {G : Type*} [Group G] {Δ : Set (Subgroup G)}

theorem PairFrame.ncard_lineOf_le_sq [Finite G] {A E D E' : Subgroup G}
    (F : PairFrame Δ A E D E') (hΔ : IsTransvectionClass Δ) (hiso : NoIsolated Δ)
    (hpts : PointsDetermined Δ) (hML : MeetsLines Δ) (hthick : ThickLines Δ)
    (hq : 4 ≤ Nat.card A) :
    (lineOf Δ A D).ncard ≤ Nat.card A ^ 2 + 1 := by
  obtain ⟨k, hk⟩ := (hΔ.root.isPGroup F.memA).exists_card_eq
  have hkD : Nat.card D = 2 ^ k := (hΔ.root.card_eq F.memD F.memA).trans hk
  obtain ⟨φ₀⟩ := nonempty_sl2Coords hΔ.root F.memA F.memE F.oppA hk
  obtain ⟨φ₁⟩ := nonempty_sl2Coords hΔ.root F.memD F.memE' F.oppD hkD
  obtain ⟨τ, hτ⟩ := F.exists_aligned_of_meetsLines hΔ hpts hML hthick hq φ₀ φ₁
  have hX : Nat.card ↥(shortRootGroup Δ E A D E') ≤ (2 ^ k) ^ 2 := by
    rcases F.exists_pairRelations hΔ hpts hML hthick hq φ₀ (φ₁.map τ) hτ with
      ⟨h1, -⟩ | ⟨h2, -⟩
    · rw [h1]
      exact Nat.le_self_pow (by norm_num) _
    · exact h2.le
  rw [F.ncard_lineOf hΔ hiso hpts hML hq, hk]
  exact Nat.add_le_add_right hX 1

theorem IsFrame.ncard_lineOf_le_sq [Finite G] {r : ℕ} {P Q : Fin r → Subgroup G}
    (hF : IsFrame Δ P Q) (hΔ : IsTransvectionClass Δ) (hiso : NoIsolated Δ)
    (hpts : PointsDetermined Δ) (hML : MeetsLines Δ) (hthick : ThickLines Δ)
    (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) {i j : Fin r} (hij : i ≠ j) :
    (lineOf Δ (P i) (P j)).ncard ≤ Nat.card (P i) ^ 2 + 1 :=
  (hF.toPairFrame hij).ncard_lineOf_le_sq hΔ hiso hpts hML hthick (hq _ (hF.memP i))

end CFSG.Timmesfeld.Transvection
