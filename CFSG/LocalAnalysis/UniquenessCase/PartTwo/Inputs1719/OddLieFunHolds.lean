module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLieCover
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLieFundPairs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLieFun
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLieFunRank
public import CFSG.ClassicalInvolution.Uniform.U3Edge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLie

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F14 (FunSet)
open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase (IsFundamentalOver fundPred isFundamentalOver_map_mulEquiv)
open CFSG.ClassicalInvolution.ModelFacts
  (nonempty_equiv_sl2_galoisField_of_mem_fundamentalSubgroups)

section FunPairModel


theorem funSet_pair_of_model {X : Type} [Group X] [Finite X] {r q : ℕ} [Fact r.Prime]
    (hr2 : r ≠ 2) {t : StatedLieTag} {n : ℕ}
    (hfund : CFSG.ClassicalInvolution.Generic.IsFundTag t) (hadm : StatedLieAdmissible t n r 1)
    (hD4 : t ≠ .trialityD4) (hqs : CFSG.Open.IsQuasisimple X)
    (hX : LieModel (X ⧸ Subgroup.center X) t n r 1) (hr5 : 5 ≤ r) (hA1 : ¬ (t = .PSL ∧ n = 2))
    (hq : q = r)
    (hpair : ∃ R ∈ CFSG.ClassicalInvolution.RouteD.ModelFund r t n 1,
      ∃ S ∈ CFSG.ClassicalInvolution.RouteD.ModelFund r t n 1,
        CFSG.ClassicalInvolution.Generic.Commutes R S)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpr : p ∣ r ^ 2 - 1) (P : Sylow 2 X) :
    ∃ K₁ K₂ : Subgroup X, K₁ ∈ FunSet (fundPred q) X (P : Subgroup X) ∧
      K₂ ∈ FunSet (fundPred q) X (P : Subgroup X) ∧
      ∃ E : Subgroup X, IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧ E ≤ K₁ ⊔ K₂ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨ψ, hψs, hψk⟩ := exists_cover_of_lieModel Fact.out hr2 hfund hadm hqs hX
    (Or.inl ⟨by rw [pow_one]; exact hr5, hA1⟩)
  obtain ⟨R, hR, S, hS, hRS⟩ := hpair
  have hfundOf : ∀ R ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups t
      (CFSG.ClassicalInvolution.Generic.modelUniv t n r 1 Fact.out).D,
        IsFundamentalOver q (R.map ψ) :=
    fun R hR => ⟨t, n, r, 1, Fact.out, hr2, by rw [hq, pow_one], hfund, hadm, ψ, hψs, hψk, R, hR,
      rfl⟩
  have hsl : ∀ R ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups t
      (CFSG.ClassicalInvolution.Generic.modelUniv t n r 1 Fact.out).D,
      (∃ a ∈ R, orderOf a = p) ∧ (∀ c ∈ R, (∀ y ∈ R, c * y = y * c) → c * c = 1) := by
    intro R hR
    rcases nonempty_equiv_sl2_galoisField_of_mem_fundamentalSubgroups
        hr2 hfund hadm hR with h1 | ⟨h, -⟩
    · obtain ⟨φ⟩ := h1
      refine ⟨exists_orderOf_of_equiv_sl2 φ ?_, fun c hc hcc =>
        CFSG.ClassicalInvolution.ModelFacts.fundCentral_sq_of_equiv_sl2 φ hc hcc⟩
      rw [GaloisField.card r 1 one_ne_zero, pow_one]
      exact Dvd.dvd.mul_left hpr _
    · exact absurd h hD4
  obtain ⟨⟨a, ha, hao⟩, hR2⟩ := hsl R hR
  obtain ⟨⟨b, hb, hbo⟩, hS2⟩ := hsl S hS
  exact exists_funSet_pair ψ hψk (hfundOf R hR) (hfundOf S hS) hRS hR2 hS2 hp hp2 ha hb hao hbo P

end FunPairModel

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLie

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F14 (FunSet)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase (IsFundamentalOver fundPred isFundamentalOver_map_mulEquiv)
open CFSG.ClassicalInvolution.ModelFacts
  (nonempty_equiv_sl2_galoisField_of_mem_fundamentalSubgroups)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17 (IsL2Over17 IsL3EpsOdd17 IsReeOver17)
open OddLie


theorem k_FunNonempty_holds : K_FunNonempty := by
  intro X _ _ r q hr hr2 ⟨t, n, f, hadm, hq, hX⟩ hqs _ hL2 _ hRee hq3 P
  have hfund := isFundTag_of_not_ree hr2 hadm hq hqs hX hRee
  have hA1 : ¬ (t = .PSL ∧ n = 2) := by
    rintro ⟨rfl, rfl⟩
    exact hL2 ⟨r, f, hr, hr2, hq, hadm.2.1, hX⟩
  have hq5 : 5 ≤ r ^ f := by
    obtain ⟨k, hk⟩ : Odd (r ^ f) := (hr.eq_two_or_odd'.resolve_left hr2).pow
    omega
  obtain ⟨ψ, hψs, hψk⟩ :=
    exists_cover_of_lieModel hr hr2 hfund hadm hqs hX (Or.inl ⟨hq5, hA1⟩)
  obtain ⟨γ, hγ⟩ := exists_isLongestRoot _
    (CFSG.LieType.HighestRoot.rank_pos_modelUniv t n r f hr hfund hadm)
  have hK₀ : IsFundamentalOver q
      (((CFSG.ClassicalInvolution.Generic.modelUniv t n r f hr).D.rootGroup γ ⊔
        (CFSG.ClassicalInvolution.Generic.modelUniv t n r f hr).D.rootGroup (-γ)).map ψ) :=
    ⟨t, n, r, f, hr, hr2, hq, hfund, hadm, ψ, hψs, hψk, _,
      ⟨1, γ, Or.inl hγ, (CFSG.ClassicalInvolution.Generic.conjSub_one _).symm⟩, rfl⟩
  obtain ⟨g, hg⟩ := exists_conj_mem_funSet (𝔉 := fundPred q)
    (fun g _ hK => isFundamentalOver_map_mulEquiv (MulAut.conj g) hK) hK₀ P
  exact ⟨_, hg⟩

theorem k_FunRankTwo_holds : K_FunRankTwo := by
  intro X _ _ r q hr hr2 ⟨t, n, f, hadm, hq, hX⟩ hqs _ hcl hL2 hL3 hRee P
  have : Fact r.Prime := ⟨hr⟩
  have hfund := isFundTag_of_not_ree hr2 hadm hq hqs hX hRee
  have hf1 : 1 ≤ f := hadm.2.1
  have hodd_r : Odd r := hr.eq_two_or_odd'.resolve_left hr2
  have h2r := hr.two_le
  have hA1 : ¬ (t = .PSL ∧ n = 2) := by
    rintro ⟨rfl, rfl⟩
    exact hL2 ⟨r, f, hr, hr2, hq, hf1, hX⟩
  have hcl' : (5 ≤ r ^ f ∧ ¬ (t = .PSL ∧ n = 2)) ∨
      (r = 3 ∧ f = 1 ∧ ¬ 3 ∣ Nat.card (Subgroup.center X)) := by
    by_cases h5 : 5 ≤ r ^ f
    · exact Or.inl ⟨h5, hA1⟩
    · right
      have hrf : r ≤ r ^ f := Nat.le_self_pow (by omega) r
      obtain ⟨k, hk⟩ := hodd_r
      have hr3 : r = 3 := by omega
      subst hr3
      have hf : f = 1 := by
        by_contra hne
        have h9 : 9 ≤ 3 ^ f :=
          calc 9 = 3 ^ 2 := by norm_num
            _ ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      subst hf
      refine ⟨rfl, rfl, ?_⟩
      rcases hcl with h | h
      · rw [hq, pow_one] at h
        omega
      · exact h
  obtain ⟨ψ, hψs, hψk⟩ := exists_cover_of_lieModel hr hr2 hfund hadm hqs hX hcl'
  have hfundOf : ∀ R ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups t
      (CFSG.ClassicalInvolution.Generic.modelUniv t n r f hr).D, IsFundamentalOver q (R.map ψ) :=
    fun R hR => ⟨t, n, r, f, hr, hr2, hq, hfund, hadm, ψ, hψs, hψk, R, hR, rfl⟩
  obtain ⟨γ, hγ⟩ := exists_isLongestRoot _
    (CFSG.LieType.HighestRoot.rank_pos_modelUniv t n r f hr hfund hadm)
  have hR₀ : ((CFSG.ClassicalInvolution.Generic.modelUniv t n r f hr).D.rootGroup γ ⊔
      (CFSG.ClassicalInvolution.Generic.modelUniv t n r f hr).D.rootGroup (-γ)) ∈
      CFSG.ClassicalInvolution.Generic.fundamentalSubgroups t
        (CFSG.ClassicalInvolution.Generic.modelUniv t n r f hr).D :=
    ⟨1, γ, Or.inl hγ, (CFSG.ClassicalInvolution.Generic.conjSub_one _).symm⟩
  refine ⟨?_, ?_⟩
  · have key : ∃ K₁ K₂ : Subgroup X, K₁ ∈ FunSet (fundPred q) X (P : Subgroup X) ∧
        K₂ ∈ FunSet (fundPred q) X (P : Subgroup X) ∧
        ∃ E : Subgroup X, IsElemAbelian r E ∧ Nat.card E = r ^ 2 ∧ E ≤ K₁ ⊔ K₂ := by
      by_cases hf2 : 2 ≤ f
      · rcases nonempty_equiv_sl2_galoisField_of_mem_fundamentalSubgroups
            hr2 hfund hadm hR₀ with h1 | ⟨-, h1⟩
        · obtain ⟨φ⟩ := h1
          obtain ⟨E, hE, hEc, hEle⟩ := exists_elemAbelian_sq_of_equiv_sl2 hf2
            (GaloisField.card r f (by omega)) ψ hψk φ
          exact exists_funSet_single (hfundOf _ hR₀) hE hEc hEle P
        · obtain ⟨φ⟩ := h1
          obtain ⟨E, hE, hEc, hEle⟩ := exists_elemAbelian_sq_of_equiv_sl2 (k := 3 * f)
            (by omega) (GaloisField.card r (3 * f) (by omega)) ψ hψk φ
          exact exists_funSet_single (hfundOf _ hR₀) hE hEc hEle P
      · have hf : f = 1 := by omega
        subst hf
        obtain ⟨R, hR, S, hS, hRS⟩ : ∃ R ∈ CFSG.ClassicalInvolution.RouteD.ModelFund r t n 1,
            ∃ S ∈ CFSG.ClassicalInvolution.RouteD.ModelFund r t n 1,
              CFSG.ClassicalInvolution.Generic.Commutes R S := by
          by_cases hG2 : t = .G2
          · subst hG2
            exact exists_commuting_fund_g2 hadm
          by_cases hD4 : t = .trialityD4
          · subst hD4
            exact exists_commuting_fund_trialityD4 hadm
          refine CFSG.ClassicalInvolution.Uniform.exists_commuting_fund hr2 hfund hadm hG2 hD4 hA1
            ?_ hR₀
          rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
          · exact hL3 (Or.inl hX)
          · exact hL3 (Or.inr hX)
        obtain ⟨⟨a, ha, hao⟩, hR2⟩ := fund_facts hr2 hfund hadm hR
        obtain ⟨⟨b, hb, hbo⟩, hS2⟩ := fund_facts hr2 hfund hadm hS
        exact exists_funSet_pair ψ hψk (hfundOf _ hR) (hfundOf _ hS) hRS hR2 hS2 hr hr2 ha hb
          hao hbo P
    obtain ⟨K₁, K₂, h1, h2, E, hE, hEc, hEle⟩ := key
    exact ⟨E, K₁, K₂, h1, h2, hE, hEc, hEle⟩
  · intro hqr hM p hp hp2 hpr
    have hr5 : 5 ≤ r := by
      obtain ⟨k, hk⟩ := hodd_r
      by_contra hlt
      have hr3 : r = 3 := by omega
      subst hr3
      have h8 : p ∣ 2 ^ 3 := by norm_num at hpr ⊢; exact hpr
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h8))
    rcases hM with hG | hS
    · have hadmG : StatedLieAdmissible .G2 0 r 1 :=
        show r.Prime ∧ 1 ≤ 1 ∧ (0 = 0 ∧ 3 ≤ r ^ 1) from ⟨hr, le_rfl, rfl, by rw [pow_one]; omega⟩
      exact funSet_pair_of_model hr2 (t := .G2) trivial hadmG (by decide) hqs hG hr5 (by decide)
        hqr (exists_commuting_fund_g2 hadmG) hp hp2 hpr P
    · have hadmS : StatedLieAdmissible .PSp 2 r 1 :=
        show r.Prime ∧ 1 ≤ 1 ∧ (2 ≤ 2 ∧ (2, r ^ 1) ≠ (2, 2)) from
          ⟨hr, le_rfl, le_rfl, by rw [pow_one]; intro h; simp only [Prod.mk.injEq] at h; omega⟩
      exact funSet_pair_of_model hr2 (t := .PSp) trivial hadmS (by decide) hqs hS hr5 (by decide)
        hqr (CFSG.ClassicalInvolution.Uniform.exists_commuting_small_sp4 hadmS) hp hp2 hpr P

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
