module

public import CFSG.Quasithin.Background.Harris.R1.Q8L2B
public import CFSG.Quasithin.Background.Harris.R1.SpecialL28
public import CFSG.Quasithin.EmptyFaithful.S1421QA27Surv

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.SzR1
  CFSG.Quasithin.F7
open scoped commutatorElement

theorem card_S_of_sylow {G : Type} [Group G] [Finite G] {K1 S : Subgroup G}
    (hSyl : IsSylowTwoOf (S ⊓ K1) K1) (hSK : S ≤ K1) (hK : Nat.card ↥K1 = 258048) :
    Nat.card ↥S = 2 ^ 12 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := isSylowTwoOf_exists_sylow hSyl
  have h1 := Sylow.card_eq_multiplicity P
  have hf : (Nat.card ↥K1).factorization 2 = 12 := by
    rw [hK, show (258048 : ℕ) = 2 ^ 12 * 63 by norm_num,
      Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (show ¬ 2 ∣ 63 by norm_num)]
    rfl
  rw [hf, hP] at h1
  rw [inf_eq_left.mpr hSK] at h1
  rw [← h1]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSK).toEquiv).symm

theorem l2B_facts {G : Type} [Group G] [Finite G]
    {K1 L2 S Zs : Subgroup G} (hset : R1SettingLegacyBare K1 L2 S Zs) (hL : IsL2Quot 3 (OTwoQuot K1))
    (hna : ⁅vBeta K1 L2 S Zs, vBeta K1 L2 S Zs⁆ ≠ ⊥)
    (hQK : pCoreOf 2 K1 = vBeta K1 L2 S Zs) (hSK : S ≤ K1) :
    Nat.card ↥(L2 ⊔ bigB K1 L2 S) = 86016 ∧
      pCoreOf 2 (L2 ⊔ bigB K1 L2 S) = pCoreOf 2 (L2 ⊔ S) ∧
      pCoreOf 2 (L2 ⊔ S) = S ⊓ Subgroup.centralizer (conjClosure Zs L2 : Set G) ∧
      (∀ x ∈ L2 ⊔ bigB K1 L2 S, x ∈ Subgroup.centralizer (pCoreOf 2 (L2 ⊔ S) : Set G) →
        x ∈ pCoreOf 2 (L2 ⊔ S)) := by
  classical
  obtain ⟨Ω, hΩ, C, hodd, hcard, -⟩ :=
    famStmt_holds G K1 L2 S Zs hset 3 (by norm_num) (Or.inl hL) hna
  have hc9 : Fintype.card Ω = 9 := (hcard hL).trans (by norm_num)
  have hsp : IsSpecialPow 2 2 4 ↥(pCoreOf 2 K1) := by
    rw [hQK]; exact vBeta_special_of_L28 G K1 L2 S Zs hset hL hna
  have hK : Nat.card ↥K1 = 258048 := S1421QA27.card_K1_of_survivor4 hL hsp
  have hS : Nat.card ↥S = 2 ^ 12 := card_S_of_sylow hset.hyp.h1.sylow hSK hK
  exact ⟨card_L2B C hc9 hL hSK hK hS, pCore_L2B_eq C hc9 hL hSK hK hS, C.pCore_eq,
    centralizer_L2B_le C hc9 hL hSK hK hS⟩

end CFSG.Quasithin.Background.Harris.R1
