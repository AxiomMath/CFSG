module

public import CFSG.RankThree.PartOne.FOC.SylowData
public import CFSG.RankThree.PartOne.K128.D4Syl
public import CFSG.RankThree.PartOne.FOCD.PRank

public section

namespace CFSG.RankThree.PartOne.FOC

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne CFSG.RankThree.PartOne.FOCD
open CFSG.RankThree.PartOne.K128 CFSG.RankThree.PartOne.KE
open CFSG.Assembly.LowTwoRank (StatedLieTag)



theorem sylowData_D4 {f p : ℕ} {T : Type} [Group T] [Finite T]
    (hch : ChevalleyExceptionalModel T .trialityD4 2 f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    (e : T ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (hp : p.Prime) (hp5 : 5 ≤ p) :
    SylowAbelian p T ∧ PRankLeTwo p T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : 1 ≤ f := hch.1.2.1
  by_cases hpT : p ∣ Nat.card T
  swap
  · exact ⟨sylowAbelian_of_not_dvd hp hpT, pRankLeTwo_of_not_dvd hp hpT⟩
  obtain ⟨m, hmem, hdvd⟩ := ((exact_E_type_and_triality_cross_prime_factor_exhaustion hp
    (by omega) (by omega : 2 ≠ p) hch).1 hpT).2.2.2.2 rfl
  have hd : (p : ℤ) ∣ cycloVal m 2 f := hdvd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hq1 : 1 ≤ 2 ^ f := Nat.one_le_pow _ _ (by norm_num)
  by_cases h12 : m = 12
  · subst h12
    rw [cycloVal_twelve] at hd
    have hpd : p ∣ (2 ^ f) ^ 4 - (2 ^ f) ^ 2 + 1 := by
      have h24 : (2 ^ f) ^ 2 ≤ (2 ^ f) ^ 4 := Nat.pow_le_pow_right hq1 (by omega)
      have h1 : (p : ℤ) ∣ (((2 ^ f) ^ 4 - (2 ^ f) ^ 2 + 1 : ℕ) : ℤ) := by
        rw [Nat.cast_add, Nat.cast_sub h24]
        push_cast
        exact hd
      exact_mod_cast h1
    have h1 := pRank_le_one_D4_twelve Nat.prime_two hf K hK σ hσ hp hp5 hpd
    have h2 : CFSG.pRank p T ≤ 1 := by
      rw [pRank_eq_of_mulEquiv_of_one_lt hp.one_lt e]
      exact h1
    exact ⟨sylowAbelian_of_pRank_le_one hp (by omega) h2, pRankLeTwo_of_pRank_le_one hp h2⟩
  · have hm' : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 6 := by omega
    have hpdQ : p ∣ phiNat m (2 ^ f) := dvd_phiNat_of_dvd_cycloVal hq1 hm' hd
    have hsh := (sylowShape_D4 hf K hK σ hσ hm' hp hp5 hpdQ).of_mulEquiv e
    exact ⟨sylowAbelian_of_shape hp hsh, pRankLeTwo_of_sylowShape hp hsh⟩

end CFSG.RankThree.PartOne.FOC
