module

public import CFSG.Quasithin.Vol2.Ch4Sec2T425C27D
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineGroups
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A134EvenClassical
public import CFSG.Quasithin.EmptyFaithful.SBc17Sp4
public import CFSG.Assembly.GL83LieDefs
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.Ch4.T425C27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SmithC27 CFSG.Quasithin.SBc17

open Polynomial in
theorem pow_three_eq_one_of_pow_three_pow {K : Type} [Field K] [CharP K 3]
    (A : Matrix (Fin 3) (Fin 3) K) (k : ℕ) (hA : A ^ (3 ^ k) = 1) : A ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : (X - 1 : K[X]) ^ (3 ^ k) = X ^ (3 ^ k) - 1 := by
    simpa using sub_pow_char_pow (R := K[X]) (p := 3) (X : K[X]) 1 k
  have h2 : (X - 1 : K[X]) ^ 3 = X ^ 3 - 1 := by
    simpa using sub_pow_char (R := K[X]) (p := 3) (X : K[X]) 1
  have hN : (A - 1) ^ (3 ^ k) = 0 := by
    have := congrArg (Polynomial.aeval A) h1
    simpa [hA, map_pow, map_sub] using this
  have hcp : (A - 1).charpoly = X ^ 3 := by
    have h := Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent ⟨3 ^ k, hN⟩
    rw [Fintype.card_fin] at h
    exact sub_eq_zero.mp (IsNilpotent.eq_zero h)
  have hN3 : (A - 1) ^ 3 = 0 := by
    have := Matrix.aeval_self_charpoly (A - 1)
    rw [hcp] at this
    simpa using this
  have := congrArg (Polynomial.aeval A) h2
  simp only [map_pow, map_sub, aeval_X, map_one] at this
  rw [hN3] at this
  exact sub_eq_zero.mp this.symm

open CFSG.Assembly.LowTwoRank CFSG.LinearGroups.UnitaryThreeOverNine in
theorem two_le_pRank_of_isPSU_three_three {X : Type} [Group X] [Finite X] (h : IsPSU 3 3 1 X) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨-, K, _, hKfin, hK, ⟨e⟩⟩ := h
  have hK9 : Nat.card K = 9 := by rw [hK]; norm_num
  have e' : X ≃* StatedSU 3 3 K := e.trans ((QuotientGroup.quotientMulEquivOfEq
    (statedScalars_subgroupOf_statedSU_eq_bot hK9)).trans QuotientGroup.quotientBot)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := Fintype.ofFinite K
  have hch : CharP K 3 := charP_of_card_eq_prime_pow (p := 3) (f := 2)
    (by rw [← Nat.card_eq_fintype_card, hK9]; norm_num)
  have hfin : Finite (StatedSU 3 3 K) :=
    Nat.finite_of_card_ne_zero (by rw [card_statedSU hK9]; norm_num)
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e']
  let P : Sylow 3 (StatedSU 3 3 K) := default
  have h9 : 3 ^ 2 ∣ Nat.card (P : Subgroup (StatedSU 3 3 K)) :=
    P.pow_dvd_card_of_pow_dvd_card (by rw [card_statedSU hK9]; norm_num)
  refine A3Facts.two_le_pRank_of_not_isCyclic (by norm_num)
    (P := (P : Subgroup (StatedSU 3 3 K))) P.isPGroup' fun hcyc => ?_
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hord := orderOf_eq_card_of_forall_mem_zpowers hg
  have hg3 : g ^ 3 = 1 := by
    obtain ⟨k, hk⟩ := P.isPGroup' g
    have h1 : (((g : StatedSU 3 3 K) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ (3 ^ k) = 1 := by
      have := congrArg (fun x : ↥(P : Subgroup (StatedSU 3 3 K)) =>
        (((x : StatedSU 3 3 K) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hk
      simpa [map_pow] using this
    have h3 := pow_three_eq_one_of_pow_three_pow _ k h1
    exact Subtype.ext (Subtype.ext (Units.ext (by simpa using h3)))
  have hdvd := hord ▸ orderOf_dvd_of_pow_eq_one hg3
  have := Nat.le_of_dvd (by norm_num) (dvd_trans h9 hdvd)
  omega

theorem eq_or_dvd_of_dvd_pow_mul {r p a m : ℕ} (hr : r.Prime) (hp : p.Prime)
    (h : r ∣ p ^ a * m) : r = p ∨ r ∣ m := by
  rcases (Nat.Prime.dvd_mul hr).mp h with h1 | h1
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr hp).mp (hr.dvd_of_dvd_pow h1))
  · exact Or.inr h1

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {H R M K J : Subgroup G} (c : Ctx H R M K J)
include c

theorem dvd_quot {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrd : r ∣ Nat.card J) :
    r ∣ Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) := by
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 (CFSG.pCore_isPGroup (p := 2) (G := ↥K))
  have h1 : r ∣ 2 ^ a * Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) := by
    rw [← ha, mul_comm, ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
    exact hrd.trans (Subgroup.card_dvd_of_le c.J_le_K)
  exact (eq_or_dvd_of_dvd_pow_mul hr Nat.prime_two h1).resolve_left hr2

variable (hC27 : ASC27Statement G)
include hC27

omit hC27 in
theorem false_of_a6 (hA : IsAltBlockType K 6) : False := by
  obtain ⟨-, α, hα, hker, -⟩ := hA
  let e : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* alternatingGroup (Fin 6) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hα)
  have hq : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 2 ^ 3 * (3 ^ 2 * 5) := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  have h3 : 3 ∣ Nat.card J := by
    by_contra h3
    refine c.nonsolv (isSolvable_of_prime_dvd Nat.prime_two Nat.prime_five fun r hr hrd => ?_)
    by_cases hr2 : r = 2
    · exact Or.inl hr2
    have h1 := c.dvd_quot hr hr2 hrd
    rw [hq] at h1
    rcases eq_or_dvd_of_dvd_pow_mul hr Nat.prime_two h1 with h | h
    · exact absurd h hr2
    rcases eq_or_dvd_of_dvd_pow_mul hr Nat.prime_three h with h | h
    · exact absurd (h ▸ hrd) h3
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_five).mp h)
  have hle := c.rank 3 Nat.prime_three (by norm_num) h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hge := two_le_pRank_of_surjective α hα (p := 3) (by norm_num) (two_le_pRank_alt le_rfl
    (by norm_num))
  omega

omit hC27 in
theorem false_of_sp4 (hA : IsSp4Block K) : False := by
  obtain ⟨-, F, _, _, hF4, α, hα, hker, -⟩ := hA
  have hF : Nat.card F = 4 := by rw [Nat.card_eq_fintype_card, hF4]
  let e : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hα)
  have hq : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 2 ^ 8 * (3 ^ 2 * (5 ^ 2 * 17)) := by
    rw [Nat.card_congr e.toEquiv, CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp,
      hF, show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num)]
    norm_num
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h3K : 2 ≤ CFSG.Open.pRank 3 K :=
    two_le_pRank_of_surjective ((QuotientGroup.mk' _).comp α)
      ((QuotientGroup.mk'_surjective _).comp hα) (by norm_num)
      (CFSG.QuasithinUnique.Vol2Native.EvenWit.two_le_pRank_three_psp (K := F) le_rfl)
  have h5K : 2 ≤ CFSG.Open.pRank 5 K :=
    two_le_pRank_of_surjective α hα (by norm_num) (two_le_pRank_statedSp_four hF4)
  by_cases h3 : 3 ∣ Nat.card J
  · have := c.rank 3 Nat.prime_three (by norm_num) h3
    omega
  by_cases h5 : 5 ∣ Nat.card J
  · have := c.rank 5 Nat.prime_five (by norm_num) h5
    omega
  refine c.nonsolv (isSolvable_of_prime_dvd Nat.prime_two (by norm_num : Nat.Prime 17)
    fun r hr hrd => ?_)
  by_cases hr2 : r = 2
  · exact Or.inl hr2
  have h1 := c.dvd_quot hr hr2 hrd
  rw [hq] at h1
  rcases eq_or_dvd_of_dvd_pow_mul hr Nat.prime_two h1 with h | h
  · exact absurd h hr2
  rcases eq_or_dvd_of_dvd_pow_mul hr Nat.prime_three h with h | h
  · exact absurd (h ▸ hrd) h3
  rcases eq_or_dvd_of_dvd_pow_mul hr Nat.prime_five h with h | h
  · exact absurd (h ▸ hrd) h5
  exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp h)

theorem false_of_g2 (hG : IsG2Block K)
    (hg2 : IsG2Two ↥(autOn (K ⊔ R) (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))))) : False := by
  obtain ⟨-, hU, -⟩ := hG
  have h3 := c.three_dvd hC27 (s := 7) (by norm_num) fun r hr hrd => by
    have h1 : r ∣ 2 ^ 6 * (3 ^ 3 * 7) := by
      have hle := Subgroup.card_dvd_of_le
        (autOn_mono' (V := omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) (Y' := K ⊔ R)
          (c.J_le_K.trans le_sup_left))
      have := hrd.trans hle
      rwa [hg2.1] at this
    rcases eq_or_dvd_of_dvd_pow_mul hr Nat.prime_two h1 with h | h
    · exact Or.inl h
    rcases eq_or_dvd_of_dvd_pow_mul hr Nat.prime_three h with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp h))
  have hle := c.rank_three h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hge := two_le_pRank_of_surjective (QuotientGroup.mk' (CFSG.pCore 2 ↥K))
    (QuotientGroup.mk'_surjective _) (by norm_num) (two_le_pRank_of_isPSU_three_three hU)
  omega

end Ctx

end CFSG.Quasithin.H13.Ch4.T425C27
