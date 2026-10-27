module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrEnnolaLabel
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearDescentFixedBasis

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal

theorem markLabel_eq_D4 {lab : LargeEvenLabel} {f : ℕ} (h1 : markTag lab = .POmegaPlus)
    (h2 : markRank lab = 4) (h3 : markDeg lab = f) : lab = ⟨.D, 4, f⟩ := by
  obtain ⟨tg, rk, m⟩ := lab
  subst h3
  cases tg <;> simp_all [markTag, markRank, markDeg]
  split_ifs at *

theorem eq_D4_of_ggLabelIso {lab : LargeEvenLabel} {f : ℕ} (h : GGLabelIso lab ⟨.D, 4, f⟩) :
    lab = ⟨.D, 4, f⟩ := by
  rcases h with h | ⟨-, h, -⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩
  · exact h
  all_goals simp_all

theorem ggSplitPresentation_label
    {G : Type} [Group G] {L : Subgroup G} {t : StatedLieTag} {n f : ℕ}
    (ht : t = .PSL ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8)
    (ψ : (ggU t n f).K →* G) (hadm : StatedLieAdmissible t n 2 f)
    (hker : ψ.ker ≤ Subgroup.center (ggU t n f).K) (hrange : ψ.range = L) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ GGHasLabel lab (L ⧸ Subgroup.center L) ∧
      markTag lab = t ∧ markRank lab = n ∧ markDeg lab = f := by
  have hfund : CFSG.ClassicalInvolution.Generic.IsFundTag t := by
    rcases ht with rfl | rfl | rfl | rfl | rfl <;> trivial
  have h0 := CFSG.ClassicalInvolution.ModelFacts.modelClauseZero t n 2 f Nat.prime_two
    hfund hadm
  have heq : CFSG.ClassicalInvolution.Generic.modelUniv t n 2 f Nat.prime_two = ggU t n f := by
    rcases ht with rfl | rfl | rfl | rfl | rfl <;> rfl
  have key : ∀ M : LieUniversal, CFSG.ClassicalInvolution.Generic.modelUniv t n 2 f
      Nat.prime_two = M → CFSG.Open.IsQuasisimple M.K ∧
        LieModel (M.K ⧸ Subgroup.center M.K) t n 2 f := by
    rintro M rfl; exact h0
  obtain ⟨hq, hm⟩ := key _ heq
  have hperf : commutator (ggU t n f).K = ⊤ := hq.1
  subst hrange
  obtain ⟨e⟩ := nonempty_centerQuotEquiv_aux (Group.isPerfect_def.mpr hperf) ψ.rangeRestrict
    ψ.rangeRestrict_surjective (by rwa [MonoidHom.ker_rangeRestrict])
  obtain ⟨lab, hlab, hhas, R, _, I, F, θ, h1, h2, -, h3⟩ :=
    largeEvenMarking_exists_hasLabel
      (CFSG.StandardType.largeEvenMarking_of_lieModel_centerQuot hperf hm)
  exact ⟨lab, hlab, ggHasLabel_congr_aux hhas e, h1, h2, h3⟩

theorem ggTBJD4_presentation_eq
    {G : Type} [Group G] {L : Subgroup G} {t : StatedLieTag} {n f₀ : ℕ}
    (ht : t = .PSL ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8)
    (ψ₀ : (ggU t n f₀).K →* G) (hadm₀ : StatedLieAdmissible t n 2 f₀)
    (hker₀ : ψ₀.ker ≤ Subgroup.center (ggU t n f₀).K) (hrange₀ : ψ₀.range = L) {f : ℕ}
    (ψ : (ggU .POmegaPlus 4 f).K →* G) (hadm : StatedLieAdmissible .POmegaPlus 4 2 f)
    (hker : ψ.ker ≤ Subgroup.center (ggU .POmegaPlus 4 f).K) (hrange : ψ.range = L) :
    t = .POmegaPlus ∧ n = 4 ∧ f₀ = f := by
  obtain ⟨lab₀, hl₀, hh₀, ht₀, hn₀, hf₀⟩ := ggSplitPresentation_label ht ψ₀ hadm₀ hker₀ hrange₀
  obtain ⟨lab₁, hl₁, hh₁, ht₁, hn₁, hf₁⟩ :=
    ggSplitPresentation_label (Or.inr (Or.inl rfl)) ψ hadm hker hrange
  have hiso := ggLabelRigidInput_holds lab₀ lab₁ _ hl₀ hl₁ hh₀ hh₁
  rw [markLabel_eq_D4 ht₁ hn₁ hf₁] at hiso
  obtain rfl := eq_D4_of_ggLabelIso hiso
  simp only [markTag, markRank, markDeg] at ht₀ hn₀ hf₀
  exact ⟨by simpa using ht₀.symm, by simpa using hn₀.symm, hf₀.symm⟩

end CFSG.StandardType

end
