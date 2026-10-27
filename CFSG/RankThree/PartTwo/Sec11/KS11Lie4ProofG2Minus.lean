module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofSplit

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.HighestRoot

namespace KS11Lie4Proof

@[expose] def G2ThreeConjSL2Minus :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K], 3 ∣ Nat.card K + 1 → 4 ≤ Nat.card K →
    ∀ z : adjointGroup .G2 K, z ^ 3 = 1 → z ≠ 1 →
      ∃ g : adjointGroup .G2 K, g * z * g⁻¹ ∈ g2ShortSL2 K ∨ g * z * g⁻¹ ∈ g2LongSL2 K

@[expose] def G2ThreeACentMinus :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K], 3 ∣ Nat.card K + 1 → 4 ≤ Nat.card K →
    ∀ z ∈ g2ShortSL2 K, z ^ 3 = 1 → z ≠ 1 →
      ∃ N : Subgroup (adjointGroup .G2 K),
        N ≤ Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)) ∧
        (∀ x ∈ Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)),
          ∀ y ∈ Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)),
            x * y * x⁻¹ * y⁻¹ ∈ N) ∧
        CFSG.IsQuasisimple N ∧
        ∃ x ∈ N, (∀ n ∈ N, x * n = n * x) ∧ x ≠ 1 ∧ x ^ 3 = 1

@[expose] def G2ThreeBCentMinus :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K], 3 ∣ Nat.card K + 1 → 4 ≤ Nat.card K →
    ∀ z ∈ g2LongSL2 K, z ^ 3 = 1 → z ≠ 1 →
      (∀ x ∈ Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)),
        ∀ y ∈ Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)),
          x * y * x⁻¹ * y⁻¹ ∈ g2ShortSL2 K) ∧
      ∀ b ∈ Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)),
        b ∈ Subgroup.centralizer (g2ShortSL2 K : Set (adjointGroup .G2 K)) →
          b ^ (Nat.card K ^ 2 - 1) = 1

@[expose] def G2ShortNineCentMinus :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K], 3 ∣ Nat.card K + 1 → 4 ≤ Nat.card K →
    ∀ y ∈ g2ShortSL2 K, (∃ k : ℕ, y ^ 3 ^ k = 1) → y ^ 3 ≠ 1 →
      (∀ x ∈ Subgroup.centralizer ({y} : Set (adjointGroup .G2 K)),
        ∀ w ∈ Subgroup.centralizer ({y} : Set (adjointGroup .G2 K)),
          x * w * x⁻¹ * w⁻¹ ∈ g2LongSL2 K) ∧
      ∀ x ∈ Subgroup.centralizer ({y} : Set (adjointGroup .G2 K)),
        x ∈ Subgroup.centralizer (g2ShortSL2 K : Set (adjointGroup .G2 K)) → x ∈ g2LongSL2 K

theorem three_dvd_card_sub_one_or_add_one {K : Type} [Field K] [Finite K]
    (hK3 : ringChar K ≠ 3) : 3 ∣ Nat.card K - 1 ∨ 3 ∣ Nat.card K + 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hp, hcard⟩ := FiniteField.card K (ringChar K)
  have h3 : ¬ 3 ∣ Nat.card K := by
    intro h
    rw [Nat.card_eq_fintype_card, hcard] at h
    exact hK3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
      (Nat.prime_three.dvd_of_dvd_pow h)).symm
  have h1 : 1 ≤ Nat.card K := Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
  omega

section Combine


theorem g2ThreeConjSL2_of_minus (h : G2ThreeConjSL2Minus) : G2ThreeConjSL2 := by
  intro K _ _ hK3 hK4 z hz3 hz1
  rcases three_dvd_card_sub_one_or_add_one hK3 with h31 | h31
  · exact g2ThreeConjSL2_split h31 hz3 hz1
  · exact h K h31 hK4 z hz3 hz1

theorem g2ThreeACent_of_minus (h : G2ThreeACentMinus) : G2ThreeACent := by
  intro K _ _ hK3 hK4 z hzS hz3 hz1
  rcases three_dvd_card_sub_one_or_add_one hK3 with h31 | h31
  · exact g2ThreeACent_split h31 hzS hz3 hz1
  · exact h K h31 hK4 z hzS hz3 hz1

theorem g2ThreeBCent_of_minus (h : G2ThreeBCentMinus) : G2ThreeBCent := by
  intro K _ _ hK3 hK4 z hzM hz3 hz1
  rcases three_dvd_card_sub_one_or_add_one hK3 with h31 | h31
  · exact g2ThreeBCent_split h31 hzM hz3 hz1
  · exact h K h31 hK4 z hzM hz3 hz1

theorem g2ShortNineCent_of_minus (h : G2ShortNineCentMinus) : G2ShortNineCent := by
  intro K _ _ hK3 hK4 y hyS hy hy3
  rcases three_dvd_card_sub_one_or_add_one hK3 with h31 | h31
  · exact g2ShortNineCent_split h31 hyS hy hy3
  · exact h K h31 hK4 y hyS hy hy3

end Combine

section Provers


theorem thetaCentral119G2Ss_of_minus (hC : G2ThreeConjSL2Minus) (hA : G2ThreeACentMinus)
    (hB : G2ThreeBCentMinus) : ThetaCentral119G2Ss :=
  thetaCentral119G2Ss_of (g2ThreeConjSL2_of_minus hC) (g2ThreeACent_of_minus hA)
    (g2ThreeBCent_of_minus hB)

theorem centJ119G2Inn_of_minus (hC : G2ThreeConjSL2Minus) (hA : G2ThreeACentMinus)
    (hB : G2ThreeBCentMinus) : CentJ119G2Inn :=
  centJ119G2Inn_of (g2ThreeConjSL2_of_minus hC) (g2ThreeACent_of_minus hA)
    (g2ThreeBCent_of_minus hB)

theorem centJ119G2Out_of_minus (hC : G2ThreeConjSL2Minus) (hA : G2ThreeACentMinus)
    (hB : G2ThreeBCentMinus) : CentJ119G2Out :=
  centJ119G2Out_of (g2ThreeConjSL2_of_minus hC) (g2ThreeACent_of_minus hA)
    (g2ThreeBCent_of_minus hB) g2ShortOut_holds

theorem normCentJ1117G2Ss_of_minus (hC : G2ThreeConjSL2Minus) (hA : G2ThreeACentMinus)
    (hB : G2ThreeBCentMinus) (hN : G2ShortNineCentMinus) : NormCentJ1117G2Ss :=
  normCentJ1117G2Ss_of (g2ThreeConjSL2_of_minus hC) (g2ThreeACent_of_minus hA)
    (g2ThreeBCent_of_minus hB) (g2ShortNineCent_of_minus hN)

end Provers

end KS11Lie4Proof

end CFSG.RankThree.PartTwo.Sec11
