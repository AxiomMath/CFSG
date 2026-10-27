module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGReverseMarking
public import CFSG.LocalAnalysis.StandardType.MarkingDict
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearDescentFixedBasis

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal

theorem markLabel_deg_aux {lab : LargeEvenLabel} {t : StatedLieTag} {f : ℕ}
    (ht : t = .PSL ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8)
    (h1 : markTag lab = t) (h2 : markChar lab = 2) (h3 : markDeg lab = f) :
    f = lab.n ∨ (lab.tag = .twD ∧ lab.rank = 2 ∧ f = 2 * lab.n) := by
  obtain ⟨tg, rk, m⟩ := lab
  subst h3
  subst h1
  cases tg <;> simp_all [markTag, markChar, markDeg] <;> split_ifs at * <;> simp_all

theorem ggHasLabel_congr_aux {lab : LargeEvenLabel} {R R' : Type} [Group R] [Group R']
    (h : GGHasLabel lab R) (e : R ≃* R') : GGHasLabel lab R' := by
  unfold GGHasLabel at h ⊢
  refine largeEvenRawDatum_mono ?_ h
  rintro R₀ _ I F ⟨e'⟩
  exact ⟨e.symm.trans e'⟩

theorem nonempty_centerQuotEquiv_aux {P Q : Type*} [Group P] [Group Q] (hP : Group.IsPerfect P)
    (f : P →* Q) (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center P) :
    Nonempty (P ⧸ Subgroup.center P ≃* Q ⧸ Subgroup.center Q) := by
  have hc : Subgroup.center P = ((QuotientGroup.mk' (Subgroup.center Q)).comp f).ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact (CFSG.LocalCores.comap_center_eq_of_perfect hP f hf hker).symm
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hc).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ ((QuotientGroup.mk'_surjective _).comp hf))⟩

section Inputs

theorem ggSplitLie_markLabel
    {G : Type} [Group G] {X : Subgroup G} {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* G} (hadm : StatedLieAdmissible t n 2 f)
    (hker : ψ.ker ≤ Subgroup.center (ggU t n f).K) (hrange : ψ.range = X)
    (ht : t = .PSL ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ GGHasLabel lab (X ⧸ Subgroup.center X) ∧
      markTag lab = t ∧ markChar lab = 2 ∧ markDeg lab = f := by
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
  obtain ⟨lab, hlab, hhas, R, _, I, F, θ, hP⟩ :=
    largeEvenMarking_exists_hasLabel
      (CFSG.StandardType.largeEvenMarking_of_lieModel_centerQuot hperf hm)
  obtain ⟨h1, -, h2, h3⟩ := hP
  exact ⟨lab, hlab, ggHasLabel_congr_aux hhas e, h1, h2, h3⟩

theorem ggSplitLie_label
    {G : Type} [Group G] [Finite G] {p : ℕ} {L : Subgroup G}
    (hp : p.Prime) (hp2 : p ≠ 2) (hL : GGSplitLie p L) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧
      GGHasLabel lab (L ⧸ Subgroup.center L) ∧ p ∣ 2 ^ lab.n - 1 := by
  obtain ⟨t, n, f, ψ, hadm, hker, hrange, ht, hpf⟩ := hL
  obtain ⟨lab, hlab, hhas', h1, h2, h3⟩ := ggSplitLie_markLabel hadm hker hrange ht
  rcases markLabel_deg_aux ht h1 h2 h3 with hf | ⟨htw, hr2, hf⟩
  · exact ⟨lab, hlab, hhas', by rwa [← hf]⟩
  · have hlabeq : lab = ⟨.twD, 2, lab.n⟩ := by
      obtain ⟨tg, rk, m⟩ := lab
      simp_all
    have hiso : GGLabelIso lab ⟨.A, 1, 2 * lab.n⟩ :=
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hlabeq, rfl⟩))))))
    refine ⟨⟨.A, 1, 2 * lab.n⟩, ⟨by have := hlab.1; simp; omega, le_rfl, fun _ => by
      have := hlab.1; simp; omega⟩, ?_, by simpa [← hf] using hpf⟩
    unfold GGHasLabel at hhas' ⊢
    exact largeEvenRawDatum_of_ggLabelIso hiso hhas'

end Inputs

end CFSG.StandardType

end
