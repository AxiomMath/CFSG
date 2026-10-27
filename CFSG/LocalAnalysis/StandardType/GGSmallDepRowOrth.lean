module

public import CFSG.LocalAnalysis.StandardType.GGSmallDepRowMisc
public import CFSG.LocalAnalysis.StandardType.GGWAutDefs
import CFSG.LocalAnalysis.StandardType.ZS.OrthClass
import CFSG.LocalAnalysis.StandardType.ZS.TableCommon
import CFSG.LocalAnalysis.StandardType.ZS.IsIsomCard
import CFSG.LocalAnalysis.StandardType.ZS.OrthClassIndex
import CFSG.LocalAnalysis.StandardType.ZS.ClassReflNegFour
import CFSG.LocalAnalysis.StandardType.GGExtCtxSplitFour
import CFSG.LocalAnalysis.StandardType.GGExtCtxSplitFive
import CFSG.LocalAnalysis.StandardType.GGSmallDepStabFive
import CFSG.LocalAnalysis.StandardType.GGSmallDepStabSix

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
  {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
  {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {T : Type} {s : T → (V ≃ₗ[ZMod p] V)} {x : V}

namespace GGNineDepCtx

private lemma weylTypeData_six_natCard_le {n c : ℕ} (h : GGWeylTypeData 6 n c) :
    n ≤ 51840 := by
  rcases h with ⟨-, hn, -⟩ | ⟨-, hn, -⟩ | ⟨-, hn, -⟩ | ⟨-, hn, -⟩ |
    ⟨hr, -, -⟩ | ⟨hr, -, -⟩ | ⟨hr, -, -⟩ | ⟨hr, -, -⟩
  · rw [hn]; norm_num [Nat.factorial]
  · rw [hn]; norm_num [Nat.factorial]
  · rw [hn]; norm_num [Nat.factorial]
  · omega
  · omega
  · omega
  · omega
  · omega

private lemma weylTypeData_nine_natCard_le {n c : ℕ} (h : GGWeylTypeData 9 n c) :
    n ≤ 185794560 := by
  rcases h with ⟨-, hn, -⟩ | ⟨-, hn, -⟩ | ⟨-, hn, -⟩ | ⟨hr, -, -⟩ |
    ⟨hr, -, -⟩ | ⟨hr, -, -⟩ | ⟨hr, -, -⟩ | ⟨hr, -, -⟩
  · rw [hn]; norm_num [Nat.factorial]
  · rw [hn]; norm_num [Nat.factorial]
  · rw [hn]; norm_num [Nat.factorial]
  · omega
  · omega
  · omega
  · omega
  · omega

theorem false_of_ggOrthType_pow
    (X : GGNineDepCtx h α r s x)
    (hcell : (p = 7 ∧ N = 7 ∧ 6 ≤ Module.finrank (ZMod p) ↥(ggFixLineT r s)) ∨
      (p = 5 ∧ N = 10))
    (hO : GGOrthType (ggNineQ X)) : False := by
  classical
  haveI : Module.Finite (ZMod p) V := X.finite
  haveI : Finite V := Module.finite_of_finite (ZMod p)
  haveI : Module.Finite (ZMod p) ↥(ggFixLineT r s) := Module.Finite.of_finite
  rcases hcell with ⟨rfl, rfl, hd6⟩ | ⟨rfl, rfl⟩
  · have hd_ge : 5 ≤ Module.finrank (ZMod 7) ↥(ggFixLineT r s) := by
      simpa using X.d_ge
    have hd_le : Module.finrank (ZMod 7) ↥(ggFixLineT r s) ≤ 7 := by
      simpa using X.d_le
    have hHle : Nat.card ↥(Subgroup.closure (Set.range s)) ≤ 51840 :=
      weylTypeData_six_natCard_le X.weylTypeData
    have hpow := ZS.pow_le_card_of_ggOrthType (p := 7) (U := ↥(ggFixLineT r s))
      (n := Module.finrank (ZMod 7) ↥(ggFixLineT r s)) (by norm_num) rfl hd_ge hO
    have hbound : Nat.card ↥(ggNineQ X) ≤
        7 ^ Module.finrank (ZMod 7) ↥(ggFixLineT r s) *
          (6 * (7 - 1) * Nat.card ↥(Subgroup.closure (Set.range s))) := X.natCard_le
    have hle : 7 ^ (Module.finrank (ZMod 7) ↥(ggFixLineT r s) *
        (Module.finrank (ZMod 7) ↥(ggFixLineT r s) - 1) / 2) ≤
        8 * (7 ^ Module.finrank (ZMod 7) ↥(ggFixLineT r s) *
          (6 * (7 - 1) * Nat.card ↥(Subgroup.closure (Set.range s)))) :=
      le_trans hpow (Nat.mul_le_mul_left 8 hbound)
    have hle' : 7 ^ (Module.finrank (ZMod 7) ↥(ggFixLineT r s) *
        (Module.finrank (ZMod 7) ↥(ggFixLineT r s) - 1) / 2) ≤
        8 * (7 ^ Module.finrank (ZMod 7) ↥(ggFixLineT r s) *
          (6 * (7 - 1) * 51840)) := by
      refine le_trans hle ?_
      gcongr
    have hcases : Module.finrank (ZMod 7) ↥(ggFixLineT r s) = 6 ∨
        Module.finrank (ZMod 7) ↥(ggFixLineT r s) = 7 := by omega
    rcases hcases with hd | hd
    · rw [hd] at hle'
      norm_num at hle'
    · rw [hd] at hle'
      norm_num at hle'
  · have hd_ge : 8 ≤ Module.finrank (ZMod 5) ↥(ggFixLineT r s) := by
      simpa using X.d_ge
    have hHle : Nat.card ↥(Subgroup.closure (Set.range s)) ≤ 185794560 :=
      weylTypeData_nine_natCard_le X.weylTypeData
    have hpow := ZS.pow_le_card_of_ggOrthType (p := 5) (U := ↥(ggFixLineT r s))
      (n := Module.finrank (ZMod 5) ↥(ggFixLineT r s)) (by norm_num) rfl (by omega) hO
    have hbound : Nat.card ↥(ggNineQ X) ≤
        5 ^ Module.finrank (ZMod 5) ↥(ggFixLineT r s) *
          (6 * (5 - 1) * Nat.card ↥(Subgroup.closure (Set.range s))) := X.natCard_le
    have hle : 5 ^ (Module.finrank (ZMod 5) ↥(ggFixLineT r s) *
        (Module.finrank (ZMod 5) ↥(ggFixLineT r s) - 1) / 2) ≤
        8 * (5 ^ Module.finrank (ZMod 5) ↥(ggFixLineT r s) *
          (6 * (5 - 1) * Nat.card ↥(Subgroup.closure (Set.range s)))) :=
      le_trans hpow (Nat.mul_le_mul_left 8 hbound)
    have hle' : 5 ^ (Module.finrank (ZMod 5) ↥(ggFixLineT r s) *
        (Module.finrank (ZMod 5) ↥(ggFixLineT r s) - 1) / 2) ≤
        8 * (5 ^ Module.finrank (ZMod 5) ↥(ggFixLineT r s) *
          (6 * (5 - 1) * 185794560)) := by
      refine le_trans hle ?_
      gcongr
    have hcases : Module.finrank (ZMod 5) ↥(ggFixLineT r s) = 8 ∨
        Module.finrank (ZMod 5) ↥(ggFixLineT r s) = 9 ∨
        Module.finrank (ZMod 5) ↥(ggFixLineT r s) = 10 := by
      have h := X.d_le
      omega
    rcases hcases with hd | hd | hd
    · rw [hd] at hle'
      norm_num at hle'
    · rw [hd] at hle'
      norm_num at hle'
    · rw [hd] at hle'
      norm_num at hle'

theorem false_of_orth
    (X : GGNineDepCtx h α r s x)
    (hcell : (p = 5 ∧ N = 5) ∨ (p = 3 ∧ N = 6) ∨ (p = 7 ∧ N = 7) ∨ (p = 5 ∧ N = 10))
    {Q : QuadraticForm (ZMod p) ↥(ggFixLineT r s)}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hiso : ∀ g, g ∈ ggNineQ X ↔ ZS.IsIsom p Q g) : False := by
  classical
  haveI : Module.Finite (ZMod p) V := X.finite
  haveI : Finite V := Module.finite_of_finite (ZMod p)
  haveI : Module.Finite (ZMod p) ↥(ggFixLineT r s) := Module.Finite.of_finite
  rcases hcell with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hneg : (LinearEquiv.neg (ZMod 5) :
        ↥(ggFixLineT r s) ≃ₗ[ZMod 5] ↥(ggFixLineT r s)) ∈ ggNineQ X := by
      refine (hiso _).mpr ?_
      intro v
      simp [LinearEquiv.neg_apply]
    have hdN := X.finrank_eq_of_neg_mem hneg
    have hTtop : ggFixLineT r s = ⊤ := by
      refine Submodule.eq_top_of_finrank_eq ?_
      rw [hdN, X.finrank_eq]
    have hxT : x ∈ ggFixLineT r s := by rw [hTtop]; exact Submodule.mem_top
    obtain ⟨x', H', hx', hH', hcard, hstab⟩ := X.exists_stab_restrict hxT
    refine ggSmallDep_false_of_stab_five (U := ↥(ggFixLineT r s)) (Q := Q)
      (A := ggNineQ X)
      (z := Nat.card ↥(Subgroup.center ↥(Subgroup.closure (Set.range s)))) hdN hQ
      (Or.inl hiso) hx' hH' ?_ ?_
    · rw [hcard]; exact X.weylTypeData
    · rw [← hcard] at hstab
      norm_num at hstab ⊢
      exact hstab
  · have hneg : (LinearEquiv.neg (ZMod 3) :
        ↥(ggFixLineT r s) ≃ₗ[ZMod 3] ↥(ggFixLineT r s)) ∈ ggNineQ X := by
      refine (hiso _).mpr ?_
      intro v
      simp [LinearEquiv.neg_apply]
    have hdN := X.finrank_eq_of_neg_mem hneg
    have hTtop : ggFixLineT r s = ⊤ := by
      refine Submodule.eq_top_of_finrank_eq ?_
      rw [hdN, X.finrank_eq]
    have hxT : x ∈ ggFixLineT r s := by rw [hTtop]; exact Submodule.mem_top
    obtain ⟨x', H', hx', hH', hcard, hstab⟩ := X.exists_stab_restrict hxT
    refine ggSmallDep_false_of_stab_six (U := ↥(ggFixLineT r s)) (Q := Q)
      (A := ggNineQ X)
      (z := Nat.card ↥(Subgroup.center ↥(Subgroup.closure (Set.range s)))) hdN hQ
      (Or.inl hiso) hx' hH' ?_ ?_
    · rw [hcard]; exact X.weylTypeData
    · rw [← hcard] at hstab
      norm_num at hstab ⊢
      exact hstab
  · have hneg : (LinearEquiv.neg (ZMod 7) :
        ↥(ggFixLineT r s) ≃ₗ[ZMod 7] ↥(ggFixLineT r s)) ∈ ggNineQ X := by
      refine (hiso _).mpr ?_
      intro v
      simp [LinearEquiv.neg_apply]
    have hdN := X.finrank_eq_of_neg_mem hneg
    exact false_of_ggOrthType_pow X (Or.inl ⟨rfl, rfl, by omega⟩)
      (ZS.ggOrthType_of_orth hQ hiso)
  · exact false_of_ggOrthType_pow X (Or.inr ⟨rfl, rfl⟩) (ZS.ggOrthType_of_orth hQ hiso)

theorem false_of_orthClass
    (X : GGNineDepCtx h α r s x)
    (hcell : (p = 5 ∧ N = 5) ∨ (p = 3 ∧ N = 6) ∨ (p = 7 ∧ N = 7) ∨ (p = 5 ∧ N = 10))
    {Q : QuadraticForm (ZMod p) ↥(ggFixLineT r s)}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {c : ZMod p} (hc : c ≠ 0)
    (hcl : ggNineQ X = Subgroup.closure (ZS.ClassRefl p Q c)) : False := by
  classical
  haveI : Module.Finite (ZMod p) V := X.finite
  haveI : Finite V := Module.finite_of_finite (ZMod p)
  haveI : Module.Finite (ZMod p) ↥(ggFixLineT r s) := Module.Finite.of_finite
  rcases hcell with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · haveI : Finite (↥(ggFixLineT r s) ≃ₗ[ZMod 5] ↥(ggFixLineT r s)) :=
      Finite.of_injective
        (fun e : ↥(ggFixLineT r s) ≃ₗ[ZMod 5] ↥(ggFixLineT r s) =>
          (e : ↥(ggFixLineT r s) → ↥(ggFixLineT r s)))
        (fun e f h => LinearEquiv.ext (congrFun h))
    have hcases : Module.finrank (ZMod 5) ↥(ggFixLineT r s) = 3 ∨
        Module.finrank (ZMod 5) ↥(ggFixLineT r s) = 4 ∨
        Module.finrank (ZMod 5) ↥(ggFixLineT r s) = 5 := by
      have h1 := X.d_ge
      have h2 := X.d_le
      omega
    rcases hcases with hd | hd | hd
    · have hOcard : Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup Q) = 240 := by
        have h := ZS.natCard_isIsom_of_finrank_eq_odd (p := 5) (U := ↥(ggFixLineT r s))
          (n := 1) (by norm_num) (by rw [hd]) hQ
        rw [show Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup Q) =
            Nat.card {g : ↥(ggFixLineT r s) ≃ₗ[ZMod 5] ↥(ggFixLineT r s) //
              ZS.IsIsom 5 Q g} from
          Nat.card_congr (Equiv.subtypeEquivRight fun g =>
            TauCeti.QuadraticMap.mem_orthogonalGroup_iff)]
        rw [h]
        norm_num [Finset.prod_Icc_succ_top]
      have hQO : ggNineQ X ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
        intro g hg
        rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
        exact ZS.isIsom_of_mem_closure_classRefl (by rwa [hcl] at hg)
      have hdiv : Nat.card ↥(ggNineQ X) ∣ 240 := by
        have h := Subgroup.card_dvd_of_le hQO
        rwa [hOcard] at h
      have h120 : 120 ∣ Nat.card ↥(ggNineQ X) := by
        simpa [show Nat.factorial 5 = 120 by norm_num] using X.factorial_dvd
      have hne : Nat.card ↥(ggNineQ X) ≠ 120 := by
        simpa [show Nat.factorial 5 = 120 by norm_num] using X.natCard_ne_factorial
      have hcardQ : Nat.card ↥(ggNineQ X) = 240 := by
        obtain ⟨t, ht⟩ := h120
        have ht2 : t ∣ 2 := by
          have h' : 120 * t ∣ 120 * 2 := by
            rw [ht] at hdiv
            exact hdiv
          exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 120)).mp h'
        rcases (Nat.dvd_prime Nat.prime_two).mp ht2 with h1 | h2
        · exact absurd (by rw [ht, h1, mul_one]) hne
        · rw [ht, h2]
      have hQeq : ggNineQ X = TauCeti.QuadraticMap.orthogonalGroup Q :=
        Subgroup.eq_of_le_of_card_ge hQO (by rw [hOcard, hcardQ])
      have hneg : (LinearEquiv.neg (ZMod 5) :
          ↥(ggFixLineT r s) ≃ₗ[ZMod 5] ↥(ggFixLineT r s)) ∈ ggNineQ X := by
        rw [hQeq, TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
        intro v
        simp [LinearEquiv.neg_apply]
      have := X.finrank_eq_of_neg_mem hneg
      omega
    · by_cases hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q
      · have hneg := ZS.neg_mem_closure_classRefl_of_isPlusType_four
          (U := ↥(ggFixLineT r s)) hd hQ hplus hc
        have hmem : (LinearEquiv.neg (ZMod 5) :
            ↥(ggFixLineT r s) ≃ₗ[ZMod 5] ↥(ggFixLineT r s)) ∈ ggNineQ X := by
          rwa [hcl]
        have := X.finrank_eq_of_neg_mem hmem
        omega
      · have htop := GGExtCtx.eq_top_of_classRefl_minus_four (V := V) X.extCtx hd hQ hplus hc hcl
        have hTfin : Module.finrank (ZMod 5) ↥(ggFixLineT r s) = 5 := by
          rw [htop, finrank_top, X.finrank_eq]
        omega
    · have hTtop : ggFixLineT r s = ⊤ := by
        refine Submodule.eq_top_of_finrank_eq ?_
        rw [hd, X.finrank_eq]
      have hxT : x ∈ ggFixLineT r s := by rw [hTtop]; exact Submodule.mem_top
      obtain ⟨x', H', hx', hH', hcard, hstab⟩ := X.exists_stab_restrict hxT
      refine ggSmallDep_false_of_stab_five (U := ↥(ggFixLineT r s)) (Q := Q)
        (A := ggNineQ X)
        (z := Nat.card ↥(Subgroup.center ↥(Subgroup.closure (Set.range s)))) hd hQ
        (Or.inr ⟨c, hc, hcl⟩) hx' hH' ?_ ?_
      · rw [hcard]; exact X.weylTypeData
      · rw [← hcard] at hstab
        norm_num at hstab ⊢
        exact hstab
  · haveI : Finite (↥(ggFixLineT r s) ≃ₗ[ZMod 3] ↥(ggFixLineT r s)) :=
      Finite.of_injective
        (fun e : ↥(ggFixLineT r s) ≃ₗ[ZMod 3] ↥(ggFixLineT r s) =>
          (e : ↥(ggFixLineT r s) → ↥(ggFixLineT r s)))
        (fun e f h => LinearEquiv.ext (congrFun h))
    have hcases : Module.finrank (ZMod 3) ↥(ggFixLineT r s) = 4 ∨
        Module.finrank (ZMod 3) ↥(ggFixLineT r s) = 5 ∨
        Module.finrank (ZMod 3) ↥(ggFixLineT r s) = 6 := by
      have h1 := X.d_ge
      have h2 := X.d_le
      omega
    rcases hcases with hd | hd | hd
    · by_cases hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q
      · have hOcard : Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup Q) = 1152 := by
          have h := ZS.natCard_isIsom_of_isPlusType (p := 3) (U := ↥(ggFixLineT r s))
            (n := 2) (by norm_num) (by norm_num) (by rw [hd]) hQ hplus
          rw [show Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup Q) =
              Nat.card {g : ↥(ggFixLineT r s) ≃ₗ[ZMod 3] ↥(ggFixLineT r s) //
                ZS.IsIsom 3 Q g} from
            Nat.card_congr (Equiv.subtypeEquivRight fun g =>
              TauCeti.QuadraticMap.mem_orthogonalGroup_iff)]
          rw [h]
          norm_num [Finset.prod_Icc_succ_top]
        have hQO : ggNineQ X ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
          intro g hg
          rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
          exact ZS.isIsom_of_mem_closure_classRefl (by rwa [hcl] at hg)
        have hdiv : Nat.card ↥(ggNineQ X) ∣ 1152 := by
          have h := Subgroup.card_dvd_of_le hQO
          rwa [hOcard] at h
        have h720 : 720 ∣ Nat.card ↥(ggNineQ X) := by
          simpa [show Nat.factorial 6 = 720 by norm_num] using X.factorial_dvd
        have hbad : 720 ∣ 1152 := h720.trans hdiv
        norm_num at hbad
      · have hOcard : Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup Q) = 1440 := by
          have h := ZS.natCard_isIsom_of_not_isPlusType (p := 3) (U := ↥(ggFixLineT r s))
            (n := 2) (by norm_num) (by norm_num) (by rw [hd]) hQ hplus
          rw [show Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup Q) =
              Nat.card {g : ↥(ggFixLineT r s) ≃ₗ[ZMod 3] ↥(ggFixLineT r s) //
                ZS.IsIsom 3 Q g} from
            Nat.card_congr (Equiv.subtypeEquivRight fun g =>
              TauCeti.QuadraticMap.mem_orthogonalGroup_iff)]
          rw [h]
          norm_num [Finset.prod_Icc_succ_top]
        have hQO : ggNineQ X ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
          intro g hg
          rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
          exact ZS.isIsom_of_mem_closure_classRefl (by rwa [hcl] at hg)
        have hdiv : Nat.card ↥(ggNineQ X) ∣ 1440 := by
          have h := Subgroup.card_dvd_of_le hQO
          rwa [hOcard] at h
        have h720 : 720 ∣ Nat.card ↥(ggNineQ X) := by
          simpa [show Nat.factorial 6 = 720 by norm_num] using X.factorial_dvd
        have hne : Nat.card ↥(ggNineQ X) ≠ 720 := by
          simpa [show Nat.factorial 6 = 720 by norm_num] using X.natCard_ne_factorial
        have hcardQ : Nat.card ↥(ggNineQ X) = 1440 := by
          obtain ⟨t, ht⟩ := h720
          have ht2 : t ∣ 2 := by
            have h' : 720 * t ∣ 720 * 2 := by
              rw [ht] at hdiv
              exact hdiv
            exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 720)).mp h'
          rcases (Nat.dvd_prime Nat.prime_two).mp ht2 with h1 | h2
          · exact absurd (by rw [ht, h1, mul_one]) hne
          · rw [ht, h2]
        have hQeq : ggNineQ X = TauCeti.QuadraticMap.orthogonalGroup Q :=
          Subgroup.eq_of_le_of_card_ge hQO (by rw [hOcard, hcardQ])
        have hneg : (LinearEquiv.neg (ZMod 3) :
            ↥(ggFixLineT r s) ≃ₗ[ZMod 3] ↥(ggFixLineT r s)) ∈ ggNineQ X := by
          rw [hQeq, TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
          intro v
          simp [LinearEquiv.neg_apply]
        have := X.finrank_eq_of_neg_mem hneg
        omega
    · exact X.false_of_heart rfl rfl hd hQ hc hcl
    · have hTtop : ggFixLineT r s = ⊤ := by
        refine Submodule.eq_top_of_finrank_eq ?_
        rw [hd, X.finrank_eq]
      have hxT : x ∈ ggFixLineT r s := by rw [hTtop]; exact Submodule.mem_top
      obtain ⟨x', H', hx', hH', hcard, hstab⟩ := X.exists_stab_restrict hxT
      refine ggSmallDep_false_of_stab_six (U := ↥(ggFixLineT r s)) (Q := Q)
        (A := ggNineQ X)
        (z := Nat.card ↥(Subgroup.center ↥(Subgroup.closure (Set.range s)))) hd hQ
        (Or.inr ⟨c, hc, hcl⟩) hx' hH' ?_ ?_
      · rw [hcard]; exact X.weylTypeData
      · rw [← hcard] at hstab
        norm_num at hstab ⊢
        exact hstab
  · have hcases : Module.finrank (ZMod 7) ↥(ggFixLineT r s) = 5 ∨
        6 ≤ Module.finrank (ZMod 7) ↥(ggFixLineT r s) := by
      have h1 := X.d_ge
      have h2 := X.d_le
      omega
    rcases hcases with hd | hd
    · have htop := GGExtCtx.eq_top_of_classRefl_five_seven (V := V) X.extCtx hd hQ hc hcl
      have hTfin : Module.finrank (ZMod 7) ↥(ggFixLineT r s) = 7 := by
        rw [htop, finrank_top, X.finrank_eq]
      omega
    · exact false_of_ggOrthType_pow X (Or.inl ⟨rfl, rfl, hd⟩)
        (ZS.ggOrthType_of_orthClass (p := 7) (U := ↥(ggFixLineT r s)) (by norm_num)
          (by omega) hQ hc hcl)
  · have hd5 : 5 ≤ Module.finrank (ZMod 5) ↥(ggFixLineT r s) := by
      have h := X.d_ge
      omega
    exact false_of_ggOrthType_pow X (Or.inr ⟨rfl, rfl⟩)
      (ZS.ggOrthType_of_orthClass (p := 5) (U := ↥(ggFixLineT r s)) (by norm_num)
        hd5 hQ hc hcl)

end GGNineDepCtx

end CFSG.StandardType

end
