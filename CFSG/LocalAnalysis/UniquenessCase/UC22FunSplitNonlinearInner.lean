module

public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitSymplecticInner
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitG2Inner
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitTrialityInner
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitUnitaryInner
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitExceptionalModelInner
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitF4Inner
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitOrthogonalInner
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitTwistedE6Inner

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.ClassicalInvolution.Generic


theorem odd_normalizer_inner_fundamental_remaining
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (t : StatedLieTag) (n e : ℕ) (hfund : IsFundTag t)
    (hadm : StatedLieAdmissible t n p e) (ht : t ≠ .PSL)
    (hSp : t ≠ .PSp) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4) (hSU : t ≠ .PSU)
    (hE : ¬ (t = .E6 ∨ t = .E7 ∨ t = .E8))
    (hF4 : t ≠ .F4)
    (hOrth : ¬ (t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus))
    (R : Subgroup (modelUniv t n p e Fact.out).K)
    (hR : R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D)
    (hRperf : Group.IsPerfect R)
    (g : (modelUniv t n p e Fact.out).K)
    (hg : g ∈ normalizer (R : Set (modelUniv t n p e Fact.out).K))
    (hgo : Odd (orderOf g)) :
    ∃ r ∈ R, ∀ x ∈ R, g * x * g⁻¹ = r * x * r⁻¹ := by
  cases t <;> simp_all [IsFundTag]
  exact odd_normalizer_inner_fundamental_twistedE6_model hp2 n e hadm hR hg hgo

theorem odd_normalizer_inner_fundamental_nonpsl
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (t : StatedLieTag) (n e : ℕ) (hfund : IsFundTag t)
    (hadm : StatedLieAdmissible t n p e) (ht : t ≠ .PSL)
    (R : Subgroup (modelUniv t n p e Fact.out).K)
    (hR : R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D)
    (hRperf : Group.IsPerfect R)
    (g : (modelUniv t n p e Fact.out).K)
    (hg : g ∈ normalizer (R : Set (modelUniv t n p e Fact.out).K))
    (hgo : Odd (orderOf g)) :
    ∃ r ∈ R, ∀ x ∈ R, g * x * g⁻¹ = r * x * r⁻¹ := by
  by_cases hSp : t = .PSp
  · subst t
    exact normalizer_inner_fundamental_psp hp2 hadm R hR g hg
  by_cases hG2 : t = .G2
  · subst t
    exact odd_normalizer_inner_fundamental_g2_model hp2 hadm R hR g hg hgo
  by_cases hD4 : t = .trialityD4
  · subst t
    exact odd_normalizer_inner_fundamental_triality_model hp2 hadm R hR g hg hgo
  by_cases hSU : t = .PSU
  · subst t
    exact odd_normalizer_inner_fundamental_psu_model hp2 hadm R hR g hg hgo
  by_cases hE : t = .E6 ∨ t = .E7 ∨ t = .E8
  · exact odd_normalizer_inner_fundamental_exceptional_model hE hp2 n e hadm hR hRperf hg hgo
  by_cases hF4 : t = .F4
  · subst t
    exact odd_normalizer_inner_fundamental_f4_model hp2 n e hadm hR hg hgo
  by_cases hOrth : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus
  · rcases hOrth with rfl | rfl | rfl
    · exact odd_normalizer_inner_fundamental_orthogonal_model hp2 (Or.inl rfl) hadm R hR g hg hgo
    · exact odd_normalizer_inner_fundamental_orthogonal_model hp2 (Or.inr (Or.inl rfl)) hadm R hR g hg hgo
    · exact odd_normalizer_inner_fundamental_orthogonal_model hp2 (Or.inr (Or.inr rfl)) hadm R hR g hg hgo
  exact odd_normalizer_inner_fundamental_remaining hp2 t n e hfund hadm ht hSp hG2 hD4 hSU hE hF4 hOrth
    R hR hRperf g hg hgo

end CFSG.LocalAnalysis.UniquenessCase.UC22
