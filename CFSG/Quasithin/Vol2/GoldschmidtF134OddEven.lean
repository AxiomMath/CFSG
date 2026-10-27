module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddBorel
public import CFSG.LocalAnalysis.ComponentInitial.LinearTwoOuterOrder
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddShared

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.QuasithinUnique.Vol2Native
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem odd_outer_of_psl2_two {X : Type} [Group X] {m : ℕ} (hm : Odd m)
    (h : StatedClassicalModel X .PSL 2 2 m) : Odd (Nat.card (Outer X)) := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact absurd hm (by decide)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := nonempty_mulEquiv_psl2_odd h
  have hK : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m hm0
  have hdvd := (CFSG.LocalAnalysis.ComponentInitial.linear_two_outer_order_divisor
    Nat.prime_two (GaloisField 2 m) hK).2 X ⟨e⟩
  have hgcd : Nat.gcd 2 (2 ^ m - 1) = 1 := by
    have h2 : 2 ∣ 2 ^ m := dvd_pow_self 2 hm0
    have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    exact Nat.coprime_two_left.mpr (Nat.odd_iff.mpr (by omega))
  rw [hgcd, mul_one] at hdvd
  exact hm.of_dvd_nat hdvd

theorem facts134Odd_psl2Even :
    ∀ (A : Type) [Group A] [Finite A] (L B U : Subgroup A) (m p : ℕ) (y g : A),
      SQTKHypCat A → p.Prime → 5 ≤ p → IsPSL 2 2 m ↥L → U ≤ B → B ≤ L → IsSylowTwoOf U L →
      (∀ q : ℕ, q.Prime → q ∣ Nat.card B → q = 2 ∨ q = p) → y ∈ B → orderOf y = p →
      g ∈ Subgroup.normalizer (L : Set A) → g ∈ Subgroup.normalizer (U : Set A) →
      g ∈ Subgroup.normalizer ((Subgroup.zpowers y : Subgroup A) : Set A) →
      (∃ k : ℕ, g ^ 2 ^ k = 1) → g * y * g⁻¹ ≠ y → Even m := by
  intro A _ _ L B U m p y g _ hp hp5 hL hUB hBL hU hB hy hyo hgL hgU hgy hg2 hne
  by_contra hev
  have hodd : Odd m := Nat.not_even_iff_odd.mp hev
  have hyU : y ∈ Subgroup.normalizer (U : Set A) :=
    (psl2_borel_data hp hp5 hL hUB hBL hU hB hy hyo).2 hy
  obtain ⟨x, hx⟩ := exists_inner_of_odd_outer hgL (odd_outer_of_psl2_two hodd hL) hg2
  exact hne (fix_of_inner (CFSG.Quasithin.F420.center_eq_bot_of_statedPSL hL) hU hp
    (by omega) (hBL hy) hyo hyU hgU hgy hg2 hx)

end CFSG.Quasithin.H13.NQCore
