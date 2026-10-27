module

import CFSG.ClassicalInvolution.ModelFacts.FundamentalSL2All
import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinStd
import CFSG.LocalAnalysis.ComponentInitial.BlockTwoFactorSylowShape
public import CFSG.ClassicalInvolution.Balance.LayerGenerationField
public import CFSG.ClassicalInvolution.ModelFacts.ClauseZero
public import CFSG.LocalAnalysis.UniquenessCase.FundamentalLie
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase (IsFundamentalOver)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
open scoped MatrixGroups

theorem isL2Over17_of_surjective_psl_two {K X : Type} [Group K] [Group X]
    (hK : CFSG.Open.IsQuasisimple K) (ψ : K →* X) (hψ : Function.Surjective ψ)
    (hψ1 : ∃ x, ψ x ≠ 1) {r f q : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hf : 1 ≤ f)
    (hmodel : LieModel (K ⧸ Subgroup.center K) .PSL 2 r f) (hq : q = r ^ f) :
    IsL2Over17 (X ⧸ Subgroup.center X) q :=
  ⟨r, f, hr, hr2, hq, hf,
    CFSG.ClassicalInvolution.Balance.lieModel_of_surjective hK ψ hψ hψ1 hmodel⟩


theorem inf_ker_eq_bot_of_mem_fundamentalSubgroups {X : Type} [Group X] {r f : ℕ}
    [Fact r.Prime] {t : StatedLieTag} {n : ℕ} (hfund : CFSG.ClassicalInvolution.Generic.IsFundTag t)
    (hadm : StatedLieAdmissible t n r f) (hnA1 : ¬ (t = .PSL ∧ n = 2))
    (ψ : (CFSG.ClassicalInvolution.Generic.modelUniv t n r f Fact.out).K →* X)
    (hker : ψ.ker ≤ Subgroup.center (CFSG.ClassicalInvolution.Generic.modelUniv t n r f Fact.out).K)
    {R : Subgroup (CFSG.ClassicalInvolution.Generic.modelUniv t n r f Fact.out).K}
    (hR : R ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups t
      (CFSG.ClassicalInvolution.Generic.modelUniv t n r f Fact.out).D) :
    R ⊓ ψ.ker = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxR, hxker⟩ := Subgroup.mem_inf.mp hx
  rw [Subgroup.mem_bot]
  exact CFSG.ClassicalInvolution.Asc77.fund_noncentral_modelUniv hfund hadm hnA1 R hR x hxR
    (hker hxker)

theorem exists_model_of_isFundamentalOver {X : Type} [Group X] [Finite X] {r f q : ℕ}
    [Fact r.Prime] (hr2 : r ≠ 2) (hqf : q = r ^ f)
    (hL2 : ¬ IsL2Over17 (X ⧸ Subgroup.center X) q) {Kb : Subgroup X}
    (hKb : IsFundamentalOver q Kb) :
    ∃ (t : StatedLieTag) (n : ℕ), CFSG.ClassicalInvolution.Generic.IsFundTag t ∧
      StatedLieAdmissible t n r f ∧ ¬ (t = .PSL ∧ n = 2) ∧
      ∃ ψ : (CFSG.ClassicalInvolution.Generic.modelUniv t n r f Fact.out).K →* X,
        Function.Surjective ψ ∧
        ψ.ker ≤ Subgroup.center (CFSG.ClassicalInvolution.Generic.modelUniv t n r f Fact.out).K ∧
        ∃ R ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups t
            (CFSG.ClassicalInvolution.Generic.modelUniv t n r f Fact.out).D,
          R ⊓ ψ.ker = ⊥ ∧ Kb = R.map ψ := by
  have hKb_ne : Kb ≠ ⊥ := IsFundamentalOver.ne_bot hKb
  obtain ⟨t, n, p, e, hp, hp2, hqe, hfund, hadm, ψ, hsurj, hker, R, hR, rfl⟩ := hKb
  have he0 : e ≠ 0 := by
    have := hadm.2.1
    omega
  have hf0 : f ≠ 0 := by
    rintro rfl
    have h1 := Nat.one_lt_pow he0 hp.one_lt
    rw [← hqe, hqf, pow_zero] at h1
    exact lt_irrefl 1 h1
  obtain ⟨hp_eq, he_eq⟩ := Nat.Prime.pow_inj' hp Fact.out he0 hf0 (hqe.symm.trans hqf)
  cases hp_eq.symm
  cases he_eq.symm
  have hp_eq' : hp = Fact.out := Subsingleton.elim _ _
  subst hp_eq'
  have hψ1 : ∃ x : (CFSG.ClassicalInvolution.Generic.modelUniv t n r f Fact.out).K, ψ x ≠ 1 := by
    obtain ⟨y, ⟨x, -, rfl⟩, hy⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hKb_ne)
    exact ⟨x, fun h => hy (Subgroup.mem_bot.mpr h)⟩
  have hnA1 : ¬ (t = .PSL ∧ n = 2) := by
    rintro ⟨rfl, rfl⟩
    apply hL2
    have hU := CFSG.ClassicalInvolution.ModelFacts.modelClauseZero .PSL 2 r f Fact.out hfund hadm
    exact isL2Over17_of_surjective_psl_two hU.1 ψ hsurj hψ1 Fact.out hr2 hadm.2.1 hU.2 hqe
  exact ⟨t, n, hfund, hadm, hnA1, ψ, hsurj, hker, R, hR,
    inf_ker_eq_bot_of_mem_fundamentalSubgroups hfund hadm hnA1 ψ hker hR, rfl⟩

theorem isFundamentalOver_mulEquiv_sl2 {X : Type} [Group X] [Finite X] {r f q : ℕ}
    [Fact r.Prime] (hr2 : r ≠ 2) (hqf : q = r ^ f)
    (hL2 : ¬ IsL2Over17 (X ⧸ Subgroup.center X) q) {Kb : Subgroup X}
    (hKb : IsFundamentalOver q Kb) :
    ∃ f' : ℕ, (f' = f ∨ f' = 3 * f) ∧ Nonempty (↥Kb ≃* SL(2, GaloisField r f')) := by
  obtain ⟨t, n, hfund, hadm, -, ψ, -, -, R, hR, hdisj, rfl⟩ :=
    exists_model_of_isFundamentalOver hr2 hqf hL2 hKb
  have eK := (CFSG.LocalAnalysis.ComponentInitial.equivMapOfInfKerEqBot ψ hdisj).symm
  rcases
    CFSG.ClassicalInvolution.ModelFacts.nonempty_equiv_sl2_galoisField_of_mem_fundamentalSubgroups
      hr2 hfund hadm hR with h | ⟨-, h⟩
  · exact ⟨f, Or.inl rfl, h.map eK.trans⟩
  · exact ⟨3 * f, Or.inr rfl, h.map eK.trans⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
