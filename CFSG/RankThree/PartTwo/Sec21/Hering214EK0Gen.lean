module

public import CFSG.RankThree.PartTwo.Sec21.Hering214EFinal

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214Even

open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier CFSG.RankThree.PerfectCover

theorem multiplierOdd_of_odd_hopfMultiplier {X : Type} [Group X]
    (h : Odd (Nat.card (hopfMultiplier X))) : MultiplierOdd X := by
  intro K _ hfin Z _ hK hZ hf
  obtain ⟨e⟩ := hf
  have hqs : Function.Surjective (e.toMonoidHom.comp (QuotientGroup.mk' Z)) :=
    e.surjective.comp (QuotientGroup.mk'_surjective Z)
  have hker : (e.toMonoidHom.comp (QuotientGroup.mk' Z)).ker = Z := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk' Z x) = 1 ↔ x ∈ Z
    rw [map_eq_one_iff e e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hd := CFSG.GH74.Generic.card_ker_dvd_hopfMultiplier hK
    (e.toMonoidHom.comp (QuotientGroup.mk' Z)) hqs (by rw [hker]; exact hZ)
  rw [hker] at hd
  exact Odd.of_dvd_nat h hd

theorem card_hopfMultiplier_of_row {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (h : commutator X = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier X ≃* generic t n p f × exceptional t n p f)) :
    Nat.card (hopfMultiplier X) = (genericOrders t n p f).1 * (genericOrders t n p f).2 *
      ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2) := by
  obtain ⟨-, ⟨e⟩⟩ := h
  rw [← Nat.card_congr (hopfMultiplierEquivGriess X).toEquiv, Nat.card_congr e.toEquiv,
    Nat.card_prod]
  unfold generic exceptional
  simp only [Nat.card_prod, Nat.card_congr (Multiplicative.toAdd : _ ≃ _), Nat.card_zmod]

end CFSG.RankThree.PartTwo.Sec21.Hering214Even
