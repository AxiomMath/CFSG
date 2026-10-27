module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31NoM22
public import CFSG.Quasithin.Vol2.KGFactM22Hex
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.Quasithin.H13.P31Sec.M22Hex

theorem exists_surj_oThreePrimeResidual {Γ : Type} [Group Γ] [Finite Γ] (B : Subgroup Γ)
    (φ : ↥B →* ↥(alternatingGroup (Fin 6))) (hφ : Function.Surjective φ) :
    ∃ ψ : ↥(oThreePrimeResidual B) →* ↥(alternatingGroup (Fin 6)), Function.Surjective ψ := by
  have hOB : oThreePrimeResidual B ≤ B := oThreePrimeResidual_le B
  have hN : ((oThreePrimeResidual B).subgroupOf B).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOB).2 (le_normalizer_oThreePrimeResidual B)
  have hNφ : (((oThreePrimeResidual B).subgroupOf B).map φ).Normal := hN.map φ hφ
  have hsimp : IsSimpleGroup ↥(alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hbot : ((oThreePrimeResidual B).subgroupOf B).map φ ≠ ⊥ := by
    obtain ⟨x, hx⟩ := hφ CFSG.Quasithin.H13.S126M22.a6a
    obtain ⟨e, m, hm, hnm⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x).ne' 3 (by norm_num)
    have hmn : m * 3 ^ e = orderOf x := by
      rw [hnm]
      exact Nat.mul_comm _ _
    have hyO : ((x ^ m : ↥B) : Γ) ∈ oThreePrimeResidual B := by
      refine Subgroup.subset_closure ⟨(x ^ m : ↥B).2, e, ?_⟩
      have h1 : (x ^ m) ^ 3 ^ e = 1 := by
        rw [← pow_mul, hmn, pow_orderOf_eq_one]
      simpa using congrArg Subtype.val h1
    have hyN : x ^ m ∈ (oThreePrimeResidual B).subgroupOf B :=
      Subgroup.mem_subgroupOf.2 hyO
    have hφy : φ (x ^ m) = CFSG.Quasithin.H13.S126M22.a6a ^ m := by
      rw [map_pow, hx]
    have hne : CFSG.Quasithin.H13.S126M22.a6a ^ m ≠ 1 := by
      intro h
      have h3 := orderOf_dvd_of_pow_eq_one h
      rw [orderOf_eq_prime CFSG.Quasithin.H13.S126M22.a6a_pow
        CFSG.Quasithin.H13.S126M22.a6a_ne] at h3
      exact hm h3
    intro hbot0
    have hmem : CFSG.Quasithin.H13.S126M22.a6a ^ m ∈
        ((oThreePrimeResidual B).subgroupOf B).map φ := by
      rw [← hφy]
      exact Subgroup.mem_map_of_mem φ hyN
    rw [hbot0, Subgroup.mem_bot] at hmem
    exact hne hmem
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (((oThreePrimeResidual B).subgroupOf B).map φ) with h1 | h1
  · exact absurd h1 hbot
  · refine ⟨φ.comp (Subgroup.inclusion hOB), fun b => ?_⟩
    have hb : b ∈ ((oThreePrimeResidual B).subgroupOf B).map φ := by
      rw [h1]
      exact Subgroup.mem_top b
    obtain ⟨x, hxN, hxb⟩ := Subgroup.mem_map.1 hb
    exact ⟨⟨(x : Γ), Subgroup.mem_subgroupOf.1 hxN⟩, hxb⟩

end CFSG.Quasithin.H13.P31Sec.M22Hex
