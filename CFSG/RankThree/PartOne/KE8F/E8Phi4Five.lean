module

public import CFSG.RankThree.PartOne.KE8F.E8FourSL2
public import CFSG.RankThree.CentralCover.SteinbergBNCommutingSL2CrossPrime
public import CFSG.RankThree.Classical.SteinbergBJOrthogonalDefiningComponent
public import CFSG.RankThree.PartOne.KE.EndpointStatements

public noncomputable section

namespace CFSG.RankThree.PartOne.KE8F

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
open scoped MatrixGroups Matrix Pointwise

set_option linter.unusedSectionVars false


theorem four_le_localRank_of_E8_phi4_five {Lg : Type*} [Group Lg] [Finite Lg] {K : Type}
    [Field K] [Finite K] (hK : Odd (Nat.card K)) (h5 : 5 ∣ Nat.card K * Nat.card K + 1)
    (e : Lg ⧸ Subgroup.center Lg ≃* AdjointQuotient .E8 K) : 4 ≤ localRank 5 Lg := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  set ℓ := ringChar K with hℓdef
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := ringChar.charP K
  have hK' : Nat.card K = ℓ ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hn
  have hf : 1 ≤ (n : ℕ) := n.pos
  have hℓ2 : ℓ ≠ 2 := by
    intro h2
    rw [hK', h2] at hK
    exact (Nat.not_even_iff_odd.2 hK) (Nat.even_pow.2 ⟨even_two, n.pos.ne'⟩)
  have hℓodd : Odd ℓ := hℓ.odd_of_ne_two hℓ2
  let Ω := AlgebraicClosure K
  have : CharP Ω ℓ := charP_of_injective_algebraMap (algebraMap K Ω).injective ℓ
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  obtain ⟨D⟩ := exists_e8P4Frame0 K hf hK' Ω
  obtain ⟨k₂, _, _, _, hk₂⟩ := exists_finite_field_into ℓ (2 * (n : ℕ)) (by omega) Ω
  obtain ⟨ι, hι, hcomm⟩ := exists_four_commuting_SL2 D hℓ2 hf hk₂
  obtain ⟨φ, hφ, hker⟩ := exists_central_surjection_adjointGroup e
  have : Fintype k₂ := Fintype.ofFinite k₂
  have hq : Odd (Fintype.card k₂) := by
    rw [← Nat.card_eq_fintype_card, hk₂]
    exact hℓodd.pow
  have hpq : 5 ∣ Fintype.card k₂ ^ 2 - 1 := by
    rw [← Nat.card_eq_fintype_card, hk₂]
    have h1 : (ℓ ^ (2 * (n : ℕ))) ^ 2 = (Nat.card K * Nat.card K) * (Nat.card K * Nat.card K) := by
      rw [hK', pow_mul]
      ring
    rw [h1]
    have h2 : (Nat.card K * Nat.card K) * (Nat.card K * Nat.card K) - 1 =
        (Nat.card K * Nat.card K + 1) * (Nat.card K * Nat.card K - 1) := by
      have := Nat.mul_self_sub_mul_self_eq (Nat.card K * Nat.card K) 1
      simpa using this
    rw [h2]
    exact Dvd.dvd.mul_right h5 _
  obtain ⟨-, -, -, -, -, -, -, hrank⟩ :=
    CFSG.RankThree.CentralCover.commuting_SL2_actual_central_cover_cross_prime_local_rank
      (⊤ : Subgroup Lg) hq (by norm_num : Nat.Prime 5) (by norm_num) hpq (by norm_num : 1 ≤ 4)
      φ hφ hker ι hι hcomm
  exact hrank

theorem E8Phi4FiveOddExclusion {X : Type} [Group X] [Finite X] (N : Subgroup X) [N.Normal]
    (hN : ¬ 5 ∣ Nat.card N) (hX : localRank 5 X ≤ 3) (L : Subgroup (X ⧸ N)) {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (h5 : (5 : ℤ) ∣ cycloVal 4 ℓ f) :
    ¬ ChevalleyExceptionalModel (L ⧸ Subgroup.center L) .E8 ℓ f := by
  intro hmod
  have hL := CFSG.RankThree.Classical.localRank_le_of_le_quotient (p := 5) (by norm_num)
    (by norm_num) N hN L
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmod.2
  have hodd : Odd (ℓ ^ f) := (hℓ.odd_of_ne_two hℓ2).pow
  have h5' : 5 ∣ Nat.card K * Nat.card K + 1 := by
    have h1 : (5 : ℤ) ∣ (exhaustionPhi 4).eval ((ℓ ^ f : ℕ) : ℤ) := h5
    have e4 : (exhaustionPhi 4).eval ((ℓ ^ f : ℕ) : ℤ) = ((ℓ ^ f : ℕ) : ℤ) ^ 2 + 1 := by
      simp only [exhaustionPhi, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_one]
    rw [e4] at h1
    rw [hK]
    have h2 : (5 : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) * ((ℓ ^ f : ℕ) : ℤ) + 1 := by simpa [sq] using h1
    exact_mod_cast h2
  have := four_le_localRank_of_E8_phi4_five (hK ▸ hodd) h5' e
  omega

end CFSG.RankThree.PartOne.KE8F
