module

public import CFSG.RankThree.PartOne.KF.ClsCenter
public import CFSG.RankThree.PartOne.Assembly

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne

section Count

variable {E X : Type} [Group E] [Group X] [Finite E] [Finite X]

theorem card_comap_eq_card_ker_mul (π : E →* X) (hπ : Function.Surjective π)
    (S : Subgroup X) : Nat.card (S.comap π) = Nat.card π.ker * Nat.card S := by
  have h1 := Subgroup.card_ker_mul_card_of_surjective hπ
  have h2 : Nat.card (S.comap π) * (S.comap π).index = Nat.card E := Subgroup.card_mul_index _
  have h3 : Nat.card S * S.index = Nat.card X := Subgroup.card_mul_index _
  rw [Subgroup.index_comap_of_surjective S hπ] at h2
  have hpos : 0 < S.index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h2, mul_assoc, h3, h1]

end Count

section Cover

open CFSG.Blueprint.Multiplier

theorem card_ker_mul_card_dvd (hGA : GriessAllModelsStatement) {X : Type} [Group X] [Finite X]
    {S : Subgroup X} [S.Normal] (hS : S ≤ Subgroup.center X) {t : StatedLieTag} {n f : ℕ}
    (hm : Models.LieModel (X ⧸ S) t n 2 f) {E : Type} [Group E] [Finite E]
    (hE : Group.IsPerfect E) (π : E →* X) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center E) :
    Nat.card π.ker * Nat.card S ∣ Nat.card (generic t n 2 f × exceptional t n 2 f) := by
  obtain ⟨hperf, hcard⟩ := card_hopfMultiplier_of_model hGA hm
  let p : E →* X ⧸ S := (QuotientGroup.mk' S).comp π
  have hp : Function.Surjective p := (QuotientGroup.mk'_surjective S).comp hπ
  have hpker : p.ker = S.comap π := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  have hpc : p.ker ≤ Subgroup.center E := by
    rw [hpker]
    exact (Subgroup.comap_mono hS).trans
      (CFSG.LocalCores.comap_center_eq_of_perfect hE π hπ hker).le
  have hd := card_ker_dvd_card_hopfMultiplier hperf hE p hp hpc
  rw [hcard, hpker, card_comap_eq_card_ker_mul π hπ S] at hd
  exact hd

theorem card_generic_prod_exceptional (t : StatedLieTag) (n p f : ℕ) :
    Nat.card (generic t n p f × exceptional t n p f) =
      ((genericOrders t n p f).1 * (genericOrders t n p f).2) *
        ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2) := by
  simp only [generic, exceptional, Nat.card_prod]
  have h : ∀ k : ℕ, Nat.card (Multiplicative (ZMod k)) = k := fun k => by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  rw [h, h, h, h]

end Cover

end CFSG.RankThree.GF2n.Stroth80
