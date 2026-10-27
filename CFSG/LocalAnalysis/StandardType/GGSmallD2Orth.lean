module

public import CFSG.LocalAnalysis.StandardType.GGSmallD2Ctx
import CFSG.LocalAnalysis.StandardType.GGExtCtxSplitFour
import CFSG.LocalAnalysis.StandardType.GGExtCtxSplitFive
import CFSG.LocalAnalysis.StandardType.ZS.ClassReflNegFour
import CFSG.LocalAnalysis.StandardType.ZS.IsIsomCard
import CFSG.LocalAnalysis.StandardType.ZS.OrthClass

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
  {A : Subgroup (V ≃ₗ[ZMod p] V)} {T : Submodule (ZMod p) V}
  {AT : Subgroup (↥T ≃ₗ[ZMod p] ↥T)}

namespace GGSmallD2Ctx

theorem false_of_orthClass (X : GGSmallD2Ctx p N A T AT)
    (hcell : (p = 5 ∧ N = 5) ∨ (p = 7 ∧ N = 7) ∨ (p = 5 ∧ N = 10))
    {Q : QuadraticForm (ZMod p) ↥T} {c : ZMod p} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hc : c ≠ 0) (hA : AT = Subgroup.closure (ZS.ClassRefl p Q c)) : False := by
  haveI : Module.Finite (ZMod p) V := X.finite
  haveI : Module.Finite (ZMod p) ↥T := X.finite_T
  rcases hcell with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rcases X.finrank_T with hd | hd
    · have hd4 : Module.finrank (ZMod 5) ↥T = 4 := by omega
      by_cases hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q
      · have hneg : (LinearEquiv.neg (ZMod 5) : ↥T ≃ₗ[ZMod 5] ↥T) ∈ AT := by
          rw [hA]
          exact ZS.neg_mem_closure_classRefl_of_isPlusType_four hd4 hQ hplus hc
        exact X.false_of_neg_mem hneg
      · exact X.ne_top (GGExtCtx.eq_top_of_classRefl_minus_four X.ext hd4 hQ hplus hc hA)
    · have hd3 : Module.finrank (ZMod 5) ↥T = 3 := by omega
      haveI : Finite ↥T := Module.finite_of_finite (ZMod 5)
      haveI : Finite (↥T ≃ₗ[ZMod 5] ↥T) :=
        Finite.of_injective
          (fun e : ↥T ≃ₗ[ZMod 5] ↥T => (e : ↥T → ↥T))
          (fun e f h => LinearEquiv.ext (congrFun h))
      have hOcard : Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup Q) = 240 := by
        have h := ZS.natCard_isIsom_of_finrank_eq_odd (p := 5) (U := ↥T) (n := 1)
          (by norm_num) (by omega) hQ
        rw [show Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup Q) =
            Nat.card {g : ↥T ≃ₗ[ZMod 5] ↥T // ZS.IsIsom 5 Q g} from
          Nat.card_congr (Equiv.subtypeEquivRight fun g =>
            TauCeti.QuadraticMap.mem_orthogonalGroup_iff)]
        rw [h]
        norm_num [Finset.prod_Icc_succ_top]
      have hQO : AT ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
        intro g hg
        rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
        exact ZS.isIsom_of_mem_closure_classRefl (by rwa [hA] at hg)
      have hdiv : Nat.card ↥AT ∣ 240 := by
        have h := Subgroup.card_dvd_of_le hQO
        rwa [hOcard] at h
      have h120 : 120 ∣ Nat.card ↥AT := by
        simpa [show Nat.factorial 5 = 120 by norm_num] using X.factorial_dvd
      have hne : Nat.card ↥AT ≠ 120 := by
        simpa [show Nat.factorial 5 = 120 by norm_num] using X.natCard_ne
      have hcard : Nat.card ↥AT = 240 := by
        obtain ⟨t, ht⟩ := h120
        have ht2 : t ∣ 2 := by
          have h' : 120 * t ∣ 120 * 2 := by
            rw [ht] at hdiv
            exact hdiv
          exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 120)).mp h'
        rcases (Nat.dvd_prime Nat.prime_two).mp ht2 with h1 | h2
        · exact absurd (by rw [ht, h1, mul_one]) hne
        · rw [ht, h2]
      have hQeq : AT = TauCeti.QuadraticMap.orthogonalGroup Q :=
        Subgroup.eq_of_le_of_card_ge hQO (by rw [hOcard, hcard])
      have hneg : (LinearEquiv.neg (ZMod 5) : ↥T ≃ₗ[ZMod 5] ↥T) ∈ AT := by
        rw [hQeq, TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
        intro v
        simp [LinearEquiv.neg_apply]
      exact X.false_of_neg_mem hneg
  · rcases X.finrank_T with hd | hd
    · have hd6 : Module.finrank (ZMod 7) ↥T = 6 := by omega
      have horth : GGOrthType AT :=
        ZS.ggOrthType_of_orthClass (Q := Q) (c := c) (A := AT)
          X.p_ne_two (by omega) hQ hc hA
      have hpow := ZS.pow_le_card_of_ggOrthType (p := 7) (U := ↥T)
        (n := Module.finrank (ZMod 7) ↥T) (by norm_num) rfl (by omega) horth
      have hbound : Nat.card ↥AT ≤ 7 ^ 7 * (6 * (7 - 1) * Nat.factorial 7) := X.natCard_le
      have hle : 7 ^ (Module.finrank (ZMod 7) ↥T *
          (Module.finrank (ZMod 7) ↥T - 1) / 2) ≤
          8 * (7 ^ 7 * (6 * (7 - 1) * Nat.factorial 7)) :=
        le_trans hpow (Nat.mul_le_mul_left 8 hbound)
      rw [hd6] at hle
      norm_num [Nat.factorial] at hle
    · have hd5 : Module.finrank (ZMod 7) ↥T = 5 := by omega
      exact X.ne_top (GGExtCtx.eq_top_of_classRefl_five_seven X.ext hd5 hQ hc hA)
  · rcases X.finrank_T with hd | hd
    · have hd9 : Module.finrank (ZMod 5) ↥T = 9 := by omega
      have horth : GGOrthType AT :=
        ZS.ggOrthType_of_orthClass (Q := Q) (c := c) (A := AT)
          X.p_ne_two (by omega) hQ hc hA
      have hpow := ZS.pow_le_card_of_ggOrthType (p := 5) (U := ↥T)
        (n := Module.finrank (ZMod 5) ↥T) (by norm_num) rfl (by omega) horth
      have hbound : Nat.card ↥AT ≤ 5 ^ 10 * (6 * (5 - 1) * Nat.factorial 10) := X.natCard_le
      have hle : 5 ^ (Module.finrank (ZMod 5) ↥T *
          (Module.finrank (ZMod 5) ↥T - 1) / 2) ≤
          8 * (5 ^ 10 * (6 * (5 - 1) * Nat.factorial 10)) :=
        le_trans hpow (Nat.mul_le_mul_left 8 hbound)
      rw [hd9] at hle
      norm_num [Nat.factorial] at hle
    · have hd8 : Module.finrank (ZMod 5) ↥T = 8 := by omega
      have horth : GGOrthType AT :=
        ZS.ggOrthType_of_orthClass (Q := Q) (c := c) (A := AT)
          X.p_ne_two (by omega) hQ hc hA
      have hpow := ZS.pow_le_card_of_ggOrthType (p := 5) (U := ↥T)
        (n := Module.finrank (ZMod 5) ↥T) (by norm_num) rfl (by omega) horth
      have hbound : Nat.card ↥AT ≤ 5 ^ 10 * (6 * (5 - 1) * Nat.factorial 10) := X.natCard_le
      have hle : 5 ^ (Module.finrank (ZMod 5) ↥T *
          (Module.finrank (ZMod 5) ↥T - 1) / 2) ≤
          8 * (5 ^ 10 * (6 * (5 - 1) * Nat.factorial 10)) :=
        le_trans hpow (Nat.mul_le_mul_left 8 hbound)
      rw [hd8] at hle
      norm_num [Nat.factorial] at hle

end GGSmallD2Ctx

end CFSG.StandardType

end
