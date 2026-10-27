module

public import CFSG.RankThree.PartOne.KC.OrthogonalEvenPlusSixAut
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusSixSimilarity
import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Orth

public section

open Module _root_.QuadraticMap
open CFSG.LieType.Universal.Spin CFSG.RankThree.Classical2
open CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCOrthogonalDescent
open CFSG.LocalAnalysis.GLTheoremA.K155XOr CFSG.GroupTheory.WeirSylow

namespace CFSG.RankThree.PartOne.KCOrthogonalAut

variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem orthogonal_aut_semilinear_minus_six (Q : QuadraticForm K V)
    (hQ : (polarBilin Q).Nondegenerate) (hdim : finrank K V = 6) (hminus : ¬ IsPlusType Q)
    (α : MulAut (ProjOrthDerived Q)) : InducedBySemilinear Q α := by
  classical
  have hts : ∀ U : Submodule K V, finrank K U = 3 → ∃ u ∈ U, Q u ≠ 0 := by
    intro U hU
    by_contra h
    push Not at h
    exact hminus ⟨U, by omega, h⟩
  obtain ⟨E, fieldE, algebraE, D, ψ, ρ, hψ, hρψ, hρinj, -, hcomm, -⟩ :=
    CFSG.RankThree.PartOne.even_minus_six_actual_derived_extraction Q hQ hdim hts
  let : Field E := fieldE
  let : Algebra K E := algebraE
  let eSU : D.sixSU ≃* orthDerived Q :=
    (MonoidHom.ofInjective hρinj).trans (MulEquiv.subgroupCongr hcomm.symm)
  have heSU : ∀ g : D.sixSU, (eSU g : V ≃ₗ[K] V) = ρ g := fun _ => rfl
  have hQne : ∃ v, Q v ≠ 0 := by
    refine ⟨ψ.symm (D.sixElement 1 0 0 1 0), ?_⟩
    rw [← hψ, LinearEquiv.apply_symm_apply, D.sixForm_sixElement]
    simp
  let eQ : ProjOrthDerived Q ≃* orthDerived Q := orthProjEquiv hQne
  let αΩ : MulAut (orthDerived Q) := MulAut.congr eQ α
  let β : MulAut D.sixSU := MulAut.congr eSU.symm αΩ
  have hβ : ∀ g, eSU (β g) = αΩ (eSU g) := by intro g; simp [β, MulAut.congr_apply]
  have hα : ∀ p, eQ (α p) = αΩ (eQ p) := by intro p; simp [αΩ, MulAut.congr_apply]
  have heMk : ∀ g : orthDerived Q, eQ (QuotientGroup.mk g) = g := fun _ => rfl
  obtain ⟨σ, B₆, hsemi₆, hQ₆, hB₆⟩ := D.exists_sixSpace_similarity_intertwine β
  let B : V ≃+ V := ψ.toAddEquiv.trans (B₆.trans ψ.symm.toAddEquiv)
  have hBψ : ∀ v, ψ (B v) = B₆ (ψ v) := by intro v; simp [B]
  have hsemi : ∀ c v, B (c • v) = σ c • B v := by
    intro c v
    change ψ.symm (B₆ (ψ (c • v))) = σ c • ψ.symm (B₆ (ψ v))
    rw [map_smul, hsemi₆, map_smul]
  have hQB : ∀ v, Q (B v) = σ (Q v) := by
    intro v
    have h := hψ (B v)
    rw [hBψ, hQ₆, hψ] at h
    exact h.symm
  have hB : ∀ g v, B (ρ g v) = ρ (β g) (B v) := by
    intro g v
    apply ψ.injective
    simpa only [hBψ, hρψ] using hB₆ g (ψ v)
  refine ⟨σ, B, hsemi, 1, one_ne_zero, ?_, ?_⟩
  · intro v
    simpa only [one_mul] using hQB v
  · intro g g' hgg
    apply eQ.injective
    rw [hα, heMk, heMk]
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    obtain ⟨s, rfl⟩ := eSU.surjective g
    rw [← hβ, heSU]
    have h := hB s (B.symm v)
    rw [AddEquiv.apply_symm_apply] at h
    have hh : (g' : V ≃ₗ[K] V) v = B (ρ s (B.symm v)) := by
      simpa only [heSU] using hgg v
    exact h.symm.trans hh.symm

theorem orthogonal_aut_semilinear_even_six (Q : QuadraticForm K V)
    (hQ : (polarBilin Q).Nondegenerate) (hdim : finrank K V = 6)
    (α : MulAut (ProjOrthDerived Q)) : InducedBySemilinear Q α := by
  by_cases hp : IsPlusType Q
  · obtain ⟨ε⟩ := nonempty_isometry_quadPlus hQ (n := 3) (by omega) hp
    exact inducedBySemilinear_of_similarity ε.toLinearEquiv (1 : Kˣ)
      (fun v => by
        simpa only [_root_.QuadraticMap.IsometryEquiv.coe_toLinearEquiv,
          Units.val_one, one_mul] using ε.map_app v)
      (fun α' => orthogonal_aut_semilinear_plus_six α') α
  · exact orthogonal_aut_semilinear_minus_six Q hQ hdim hp α

end CFSG.RankThree.PartOne.KCOrthogonalAut

end
