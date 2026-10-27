module

public import CFSG.Quasithin.Background.F918Z8Op4a1
import CFSG.LinearAlgebra.SteinbergBQEvenSL2OddCyclic
import CFSG.LocalAnalysis.ShultStronglyClosedTI.OddPrimeInvertersLinear

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open CFSG.ShultStronglyClosedTI.OddPrimeInverters
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator CFSG.Glauberman.Dickson
open scoped MatrixGroups

theorem opq4a_center_sl2_eq_bot {F : Type} [Field F] [CharP F 2] :
    Subgroup.center SL(2, F) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hr1 : r = 1 := by
    have h0 : (r - 1) ^ 2 = 0 := by linear_combination hr - (r - 1) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h0)
  subst hr1
  ext1
  rw [Matrix.SpecialLinearGroup.coe_one, ← hrA, map_one]

theorem opq4a_exists_mulEquiv_sl2 {X : Type} [Group X] {n : ℕ} (hX : IsPSL 2 2 n X) :
    2 ≤ n ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 2 ^ n ∧
      Nonempty (X ≃* SL(2, F)) := by
  obtain ⟨⟨-, hn1, -, hne4, -⟩, F, hF, hFin, hcard, ⟨e⟩⟩ := hX
  have hn2 : 2 ≤ n := by
    by_contra h
    have : n = 1 := by omega
    subst this
    exact hne4 (by simp)
  have : CharP F 2 := charP_two_of_card_eq_two_pow hcard
  exact ⟨hn2, F, hF, hFin, this, hcard, ⟨e.trans
    (((QuotientGroup.quotientMulEquivOfEq opq4a_center_sl2_eq_bot).trans
      QuotientGroup.quotientBot).symm.trans
        (projectiveSpecialLinearGroupEquivStatedProj 2 F)).symm⟩⟩

theorem opq4a_sl2_exists_involution_inverts {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}
    (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (S : Sylow p SL(2, K)) (hS1 : (S : Subgroup SL(2, K)) ≠ ⊥) :
    ∃ s : SL(2, K), s * s = 1 ∧ ∀ x ∈ (S : Subgroup SL(2, K)), s * x * s⁻¹ = x⁻¹ := by
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hqeven : Even (Nat.card K) := by
    rw [hK]
    exact (Nat.even_pow' (by omega)).mpr even_two
  refine opq4a_exists_involution_inverts_sylow (q := Nat.card K)
    (N := Nat.card K * (Nat.card K + 1)) (sl2_commutator_eq_top hf hK)
    (fun p _ hp2 P => CFSG.LinearAlgebra.even_SL2_odd_prime_subgroups_cyclic hp2 _ P.isPGroup')
    (fun t ht => sl2_involution_centralizer_isPGroup t ht)
    (by rw [sl2_card, linear_card_factor hq1]) (linear_card_coprime hqeven hq1)
    (splitTorusSLHom K).range card_range_splitTorusSLHom sl2Swap ?_
    (fun p hp hp2 hpq y g hy hgy hne =>
      Or.inl (sl2_conj_eq_inv_of_frobenius hK p hp hp2 hpq y g hy hgy hne)) hp hp2 S hS1
  rintro _ ⟨a, rfl⟩
  exact sl2Swap_conj_splitTorus a

theorem a38_invSyl_psl2even {G : Type} [Group G] {L : Subgroup G} {n : ℕ} (hL : IsPSL 2 2 n ↥L)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpL : p ∣ Nat.card L) : InvSylAll L p := by
  obtain ⟨hn, K, _, _, _, hK, ⟨e⟩⟩ := opq4a_exists_mulEquiv_sl2 hL
  exact opq4a_invSylAll_of_mulEquiv e hp hpL
    (fun S hS1 => opq4a_sl2_exists_involution_inverts hn hK hp hp2 S hS1)

end CFSG.Quasithin
