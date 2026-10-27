module

public import CFSG.LocalAnalysis.StandardType.GGLieCoreA3LatticeE6Defs
public import CFSG.LocalAnalysis.StandardType.GGLieCoreA3DictPhi
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerYPerfect
public import CFSG.HardMathSupport.Timmesfeld.Torality.LangAssembly
public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotClassesRoots
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotToralCentralizer
public import CFSG.Walter.JRFacts

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Torality
open CFSG.Open (StatedLieTag)
open CFSG.LieType.Steinberg.Adjoint (iform)
open scoped commutatorElement

theorem ggLie_conj_mem_ratComp
    (hΦ : IsSteinbergEnd (langTag .E6) GGL (2 ^ 1) (ggPhi .E6 1)) (w : WeylGroup (langTag .E6))
    (g : ModGL (langTag .E6) GGL) (hg : g ∈ adjointGroup (langTag .E6) GGL)
    (hlang : ggPhi .E6 1 g = g * canonicalRep (coxeterSystem (langTag .E6)) GGL w)
    (ρ : Equiv.Perm (Fin (langTag .E6).rank → ℤ)) (a : Fin 2 → Fin (langTag .E6).rank → GGLˣ)
    (Ψ : Set (Fin (langTag .E6).rank → ℤ))
    (hΨ : ∀ ψ ∈ Ψ, IsRoot (langTag .E6) ψ ∧ ψ ∈ familyKernel a)
    (hK : familyKernel a ⊆ Ψ) (hneg : ∀ ψ ∈ Ψ, -ψ ∈ Ψ)
    (hsum : ∀ ψ ∈ Ψ, ∃ x ∈ Ψ, ∃ y ∈ Ψ, ψ = x + y)
    (z c h : ModGL (langTag .E6) GGL) (hz : z ∈ familyGroup (K := GGL) a)
    (hcg : g * z = c * h) (hc : c ∈ ratPoints (ggPhi .E6 1))
    (hh : ∀ ψ ∈ Ψ, ∀ t : GGL,
      h * pinnedX (langTag .E6) GGL ψ t * h⁻¹ = pinnedX (langTag .E6) GGL ψ t) :
    ∀ ψ ∈ Ψ, z * (pinnedX (langTag .E6) GGL ψ 1 * pinnedX (langTag .E6) GGL (-ψ) 1) * z⁻¹ ∈
      ratComp (fun u => ρ u) (langDatumOfPosition hΦ w g hg hlang).Γ Ψ := by
  intro ψ hψ
  let D : LangDatum (langTag .E6) GGL := langDatumOfPosition hΦ w g hg hlang
  let S : Subgroup (ModGL (langTag .E6) GGL) :=
    rootSpan (langTag .E6) GGL (ratOrbit (fun u => ρ u) Ψ)
  have hΨroot : ∀ γ ∈ Ψ, IsRoot (langTag .E6) γ := fun γ hγ => (hΨ γ hγ).1
  have hnorm : z ∈ Subgroup.normalizer
      (rootSpan (langTag .E6) GGL Ψ : Set (ModGL (langTag .E6) GGL)) := by
    have hle : familyGroup (K := GGL) a ≤ Subgroup.normalizer
        (rootSpan (langTag .E6) GGL Ψ : Set (ModGL (langTag .E6) GGL)) := by
      refine sup_le ?_ ?_
      · exact torusGroup_le_normalizer_rootSpan (τ := langTag .E6) (K := GGL) hΨroot
      · exact (rootSpan_mono (τ := langTag .E6) (R := GGL) hK).trans Subgroup.le_normalizer
    exact hle hz
  have hspan : ∀ γ ∈ Ψ, z * pinnedX (langTag .E6) GGL γ 1 * z⁻¹ ∈ S := by
    intro γ hγ
    have hx : pinnedX (langTag .E6) GGL γ 1 ∈ rootSpan (langTag .E6) GGL Ψ :=
      rootSubgroup_le_rootSpan hγ (Subgroup.subset_closure (Set.mem_range_self 1))
    have hconj : z * pinnedX (langTag .E6) GGL γ 1 * z⁻¹ ∈ rootSpan (langTag .E6) GGL Ψ :=
      (Subgroup.mem_normalizer_iff.1 hnorm _).1 hx
    exact rootSpan_mono (τ := langTag .E6) (R := GGL)
      (T := ratOrbit (fun u => ρ u) Ψ) (fun δ hδ => ⟨0, δ, hδ, by simp⟩) hconj
  have hz_eq : z = g⁻¹ * c * h := by
    have h := congrArg (fun u => g⁻¹ * u) hcg
    rw [← mul_assoc, inv_mul_cancel, one_mul] at h
    simpa [mul_assoc] using h
  have hconj_eq : ∀ γ ∈ Ψ, z * pinnedX (langTag .E6) GGL γ 1 * z⁻¹ =
      g⁻¹ * (c * pinnedX (langTag .E6) GGL γ 1 * c⁻¹) * g := by
    intro γ hγ
    rw [hz_eq]
    calc (g⁻¹ * c * h) * pinnedX (langTag .E6) GGL γ 1 * (g⁻¹ * c * h)⁻¹
        = g⁻¹ * (c * (h * pinnedX (langTag .E6) GGL γ 1 * h⁻¹) * c⁻¹) * g := by group
      _ = g⁻¹ * (c * pinnedX (langTag .E6) GGL γ 1 * c⁻¹) * g := by rw [hh γ hγ 1]
  have hmodel : ∀ γ ∈ Ψ, z * pinnedX (langTag .E6) GGL γ 1 * z⁻¹ ∈ D.model := by
    intro γ hγ
    rw [hconj_eq γ hγ]
    refine (LangDatum.mem_model D).2 ⟨?_, ?_⟩
    · refine mul_mem (mul_mem (inv_mem hg) ?_) hg
      exact mul_mem (mul_mem hc.1 (pinnedX_mem_adjointGroup γ 1)) (inv_mem hc.1)
    · have hPhi_c : D.Φ c = c := by
        change (ggPhi .E6 1) c = c
        simpa using hc.2
      have hPhi_X : D.Φ (pinnedX (langTag .E6) GGL γ 1) =
          pinnedX (langTag .E6) GGL γ 1 := by
        change (ggPhi .E6 1) (pinnedX (langTag .E6) GGL γ 1) = pinnedX (langTag .E6) GGL γ 1
        have h := ggPhi_pinnedX_untw (t := .E6) (Or.inr (Or.inl rfl)) 1 (hΨroot γ hγ) 1
        simpa using h
      have hPhi_g : D.Φ g = g * D.n := by
        change (ggPhi .E6 1) g = g * canonicalRep (coxeterSystem (langTag .E6)) GGL w
        exact hlang
      simp only [map_mul, map_inv, hPhi_g, hPhi_c, hPhi_X]
      group
  have hPcomm : ∀ γ ∈ Ψ, ∀ α ∈ Ψ, ∀ β ∈ Ψ, γ = α + β →
      z * pinnedX (langTag .E6) GGL γ 1 * z⁻¹ =
        ⁅z * pinnedX (langTag .E6) GGL α 1 * z⁻¹,
          z * pinnedX (langTag .E6) GGL β 1 * z⁻¹⁆ := by
    intro γ hγ α hα β hβ hγ_eq
    have hne : α ≠ β := by
      rintro rfl
      have h2 : γ = (2 : ℤ) • α := by rw [hγ_eq]; abel
      rcases (hΨroot γ hγ).eq_one_or_neg_one_of_eq_smul h2 with hh2 | hh2 <;> norm_num at hh2
    have hr : IsRoot (langTag .E6) (α + β) := by rw [← hγ_eq]; exact hΨroot γ hγ
    have hcomm : ⁅pinnedX (langTag .E6) GGL α 1, pinnedX (langTag .E6) GGL β 1⁆ =
        pinnedX (langTag .E6) GGL (α + β) (1 * 1) := by
      exact CFSG.SeitzReduction.E6Pilot.commutator_pinnedX_charTwo (K := GGL)
        (hΨroot α hα) (hΨroot β hβ) hne hr (1 : GGL) (1 : GGL)
    have hcomm' : ⁅pinnedX (langTag .E6) GGL α 1, pinnedX (langTag .E6) GGL β 1⁆ =
        pinnedX (langTag .E6) GGL γ 1 := by
      rw [hcomm, hγ_eq]
      simp
    rw [← hcomm']
    group
  have hGamma : ∀ γ ∈ Ψ, z * pinnedX (langTag .E6) GGL γ 1 * z⁻¹ ∈ D.Γ := by
    intro γ hγ
    obtain ⟨α, hα, β, hβ, hγ_eq⟩ := hsum γ hγ
    rw [hPcomm γ hγ α hα β hβ hγ_eq]
    exact Subgroup.commutator_mem_commutator (hmodel α hα) (hmodel β hβ)
  have hinf : ∀ γ ∈ Ψ, z * pinnedX (langTag .E6) GGL γ 1 * z⁻¹ ∈ S ⊓ D.Γ :=
    fun γ hγ => ⟨hspan γ hγ, hGamma γ hγ⟩
  have hC : ∀ γ ∈ Ψ, z * pinnedX (langTag .E6) GGL γ 1 * z⁻¹ ∈
      ratComp (fun u => ρ u) D.Γ Ψ := by
    intro γ hγ
    obtain ⟨α, hα, β, hβ, hγ_eq⟩ := hsum γ hγ
    rw [hPcomm γ hγ α hα β hβ hγ_eq]
    exact Subgroup.commutator_mem_commutator (hinf α hα) (hinf β hβ)
  have hmul : z * (pinnedX (langTag .E6) GGL ψ 1 * pinnedX (langTag .E6) GGL (-ψ) 1) * z⁻¹ =
      (z * pinnedX (langTag .E6) GGL ψ 1 * z⁻¹) *
        (z * pinnedX (langTag .E6) GGL (-ψ) 1 * z⁻¹) := by group
  rw [hmul]
  exact Subgroup.mul_mem _ (hC ψ hψ) (hC (-ψ) (hneg ψ hψ))

end CFSG.StandardType.LieCore
