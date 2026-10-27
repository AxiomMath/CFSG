module

public import CFSG.RankThree.PartOne.TCX.RankInterface
public import CFSG.RankThree.PartOne.K128.D4Syl
public import CFSG.RankThree.PartOne.KLC.TriTorus
public import CFSG.RankThree.PartOne.S11d.FixedFactsTri
public import CFSG.RankThree.PartOne.KLC.PRankTwo
public import CFSG.RankThree.PartOne.TCX.Interface

public section

namespace CFSG.RankThree.PartOne.TCX.Tri

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec66T
  CFSG.RankThree.PartOne.FieldFix CFSG.RankThree.PartOne.K128 CFSG.RankThree.PartOne.KLC
open CFSG.RankThree.PartOne.KE (cycloVal cycloVal_twelve)

open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)

open CFSG.RankThree.PartOne.TCX

section Main


theorem fixedRankT_trialityD4 : FixedRankT .trialityD4 := by
  intro T _ _ p hp hp5 hLR hpr n f₀ hf₀ hM α hαp hαinn hLRA hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  have hnd1 : ¬ (p : ℤ) ∣ 1 := fun h =>
    hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h)
  have hF : FixedFacts p α := tagFixedFacts_trialityD4 T p hp hp5 hLR n f₀ hf₀ hM α hαp hαinn hLRA
    hX α hαp hαinn hLRA ⟨1, hnd1, by simp [(innerAut T).one_mem]⟩
  have hadm := statedLieAdmissible_of_lieModel hM
  have hn0 : n = 0 := hadm.2.2
  subst hn0
  have hm1 : 1 ≤ p * f₀ := hadm.2.1
  have hch := chevalleyModel_of_lieModel (by decide) (by decide) (by decide) hM
  obtain ⟨K, hKf, hKfin, σ, hK, hσ, ⟨eT⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_two hm1 hch.2
  have hK3 : Nat.card K = (2 ^ (p * f₀)) ^ 3 := hK
  have hmodN : LieModel (↥(fixRes α) ⧸ Subgroup.center ↥(fixRes α)) .trialityD4 0 2 f₀ := by
    rcases hX with h | ⟨ht, -⟩
    · exact h
    · exact absurd ht (by decide)
  have hch' := chevalleyModel_of_lieModel (by decide) (by decide) (by decide) hmodN
  obtain ⟨K', hK'f, hK'fin, σ', hK', hσ', ⟨e'⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_two hf₀ hch'.2
  have hK'3 : Nat.card K' = (2 ^ f₀) ^ 3 := hK'
  have eN : ↥(fixRes α) ≃* graphFixedRootGroup TwistTag.D4 K' σ'.toRingHom :=
    (fixResEquivQuotient hF).trans e'
  have hpT : p ∣ Nat.card T := dvd_card_of_pRank_pos hp (by omega)
  obtain ⟨m, hmem, hdvd⟩ := ((exact_E_type_and_triality_cross_prime_factor_exhaustion hp
    (by omega) (by omega : 2 ≠ p) hch).1 hpT).2.2.2.2 rfl
  have hd : (p : ℤ) ∣ cycloVal m 2 (p * f₀) := hdvd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hq1 : 1 ≤ 2 ^ (p * f₀) := Nat.one_le_pow _ _ (by norm_num)
  have hq1' : 1 ≤ 2 ^ f₀ := Nat.one_le_pow _ _ (by norm_num)
  have hQ : 2 ^ (p * f₀) = (2 ^ f₀) ^ p := by rw [← pow_mul, mul_comm]
  by_cases h12 : m = 12
  ·
    exfalso
    subst h12
    rw [cycloVal_twelve] at hd
    have hpd : p ∣ (2 ^ (p * f₀)) ^ 4 - (2 ^ (p * f₀)) ^ 2 + 1 := by
      have h24 : (2 ^ (p * f₀)) ^ 2 ≤ (2 ^ (p * f₀)) ^ 4 :=
        Nat.pow_le_pow_right hq1 (by omega)
      have h1 : (p : ℤ) ∣ (((2 ^ (p * f₀)) ^ 4 - (2 ^ (p * f₀)) ^ 2 + 1 : ℕ) : ℤ) := by
        rw [Nat.cast_add, Nat.cast_sub h24]
        push_cast
        exact hd
      exact_mod_cast h1
    have h1 := pRank_le_one_D4_twelve Nat.prime_two hm1 K hK3 σ hσ hp hp5 hpd
    have h2 := pRank_eq_of_mulEquiv_of_one_lt hp.one_lt eT
    omega
  have hm' : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 6 := by omega
  have hpdQ : p ∣ phiNat m (2 ^ (p * f₀)) := dvd_phiNat_of_dvd_cycloVal hq1 hm' hd
  have hpdq : p ∣ phiNat m (2 ^ f₀) := by
    refine dvd_phiNat_of_dvd_pow hp hq1' hm' ?_
    rw [← hQ]
    exact hpdQ
  rw [pRank_congr_mulEquiv eN hp.one_lt]
  have hf5 : 3 < p := by omega
  rcases hm' with rfl | rfl | rfl | rfl
  ·
    have h1 : p ∣ 2 ^ f₀ - 1 := hpdq
    exact two_le_pRank_triality_phi1 (σ := σ'.toRingHom) ⟨hp, hp5, hf₀, hK', hσ', h1⟩
  ·
    exact two_le_pRank_triality_phi2 (ℓ := 2) hf₀ hK' σ' hσ' hp hf5
      (by have : p ∣ 2 ^ f₀ + 1 := hpdq
          exact_mod_cast this)
  ·
    exact two_le_pRank_triality_phi36 (ℓ := 2) hf₀ hK' σ' hσ' (ε := 1) (Or.inl rfl) hp
      (by have : p ∣ (2 ^ f₀) ^ 2 + 2 ^ f₀ + 1 := hpdq
          have e : ((2 ^ f₀ : ℕ) : ℤ) ^ 2 + 1 * ((2 ^ f₀ : ℕ) : ℤ) + 1 =
              (((2 ^ f₀) ^ 2 + 2 ^ f₀ + 1 : ℕ) : ℤ) := by push_cast; ring
          rw [e]
          exact_mod_cast this)
  ·
    have hle : 2 ^ f₀ ≤ (2 ^ f₀) ^ 2 := Nat.le_self_pow (by norm_num) _
    exact two_le_pRank_triality_phi36 (ℓ := 2) hf₀ hK' σ' hσ' (ε := -1) (Or.inr rfl) hp
      (by have : p ∣ (2 ^ f₀) ^ 2 - 2 ^ f₀ + 1 := hpdq
          have e : ((2 ^ f₀ : ℕ) : ℤ) ^ 2 + (-1) * ((2 ^ f₀ : ℕ) : ℤ) + 1 =
              (((2 ^ f₀) ^ 2 - 2 ^ f₀ + 1 : ℕ) : ℤ) := by push_cast [Nat.cast_sub hle]; ring
          rw [e]
          exact_mod_cast this)

end Main

end CFSG.RankThree.PartOne.TCX.Tri
