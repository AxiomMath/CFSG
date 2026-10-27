module

public import CFSG.LocalAnalysis.StandardType.GGPZCutsDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Mult
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog8L4

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier

private theorem ggPZMult_card_mult_zmod (m : ℕ) : Nat.card (Multiplicative (ZMod m)) = m := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem ggPZMult_card_dvd {Y : Type} [Group Y] (hperf : commutator Y = ⊤)
    {t : StatedLieTag} {n p f : ℕ}
    (h : Nonempty (CFSG.Open.griessHopfMultiplier (Y ⧸ Subgroup.center Y) ≃*
      generic t n p f × exceptional t n p f)) :
    Nat.card (Subgroup.center Y) ∣
      ((genericOrders t n p f).1 * (genericOrders t n p f).2) *
        ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2) := by
  haveI : Group.IsPerfect Y := ⟨hperf⟩
  have hd := CFSG.ComponentClassification.CatFactsL4U4.Cover82.Mult.card_center_dvd_hopfMultiplier
    (Q := Y) (S := Y ⧸ Subgroup.center Y) (MulEquiv.refl _)
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv] at hd
  simpa [generic, exceptional, Nat.card_prod, ggPZMult_card_mult_zmod] using hd

theorem ggPZMult_exceptional_two_pow (t : StatedLieTag) (n f : ℕ) :
    ∃ k : ℕ, (exceptionalOrders t n 2 f).1 * (exceptionalOrders t n 2 f).2 = 2 ^ k := by
  unfold exceptionalOrders
  split <;> first | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩ | exact ⟨4, rfl⟩ | simp_all

theorem ggPZMult_not_dvd_of_row {Y : Type} [Group Y] (hperf : commutator Y = ⊤)
    {t : StatedLieTag} {n f p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : Nonempty (CFSG.Open.griessHopfMultiplier (Y ⧸ Subgroup.center Y) ≃*
      generic t n 2 f × exceptional t n 2 f))
    (hg : ¬ p ∣ (genericOrders t n 2 f).1 * (genericOrders t n 2 f).2) :
    ¬ p ∣ Nat.card (Subgroup.center Y) := by
  intro hdvd
  rcases (Nat.Prime.dvd_mul hp).mp (hdvd.trans (ggPZMult_card_dvd hperf h)) with h1 | h2
  · exact hg h1
  · obtain ⟨k, hk⟩ := ggPZMult_exceptional_two_pow t n f
    rw [hk] at h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2))

end CFSG.StandardType

end
