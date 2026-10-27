module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentComp
public import CFSG.RankThree.PartOne.KC.OrthogonalCommutatorCore

public section

namespace CFSG.RankThree.GF2n.Smith81.OrthModel

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (matrixDerived_map_native matrixDerived_comap_native)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
  (isometryConjugationHom inner_eq_map_commutator)
open CFSG.ComponentClassification.OuterAutomorphisms (congr_conj)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem isometryConjugationHom_injective_of_charTwo
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K (Fin d → K), Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) :
    Function.Injective (isometryConjugationHom Q) := by
  have hQ : ∃ v, Q v ≠ 0 := CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT
  have hZ :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.matrixDerivedScalars_eq_bot_of_charTwo Q hQ
  have hproj : Function.Injective (matrixProjectiveProjection Q) := by
    rw [injective_iff_map_eq_one]
    intro A hA
    have h1 : A ∈ matrixDerivedScalars Q := by
      rw [← QuotientGroup.eq_one_iff]
      exact hA
    rw [hZ, Subgroup.mem_bot] at h1
    exact h1
  rw [injective_iff_map_eq_one]
  intro g hg
  have hcomm : ∀ A ∈ matrixDerived Q, (g : GL (Fin d) K) * A = A * g := by
    intro A hA
    have h1 := congrArg (fun φ : MulAut (matrixProjectiveDerived Q) =>
      φ (matrixProjectiveProjection Q ⟨A, hA⟩)) hg
    change matrixProjectiveConjugation Q (matrixIsometryInclusion Q g)
      (matrixProjectiveProjection Q ⟨A, hA⟩) = matrixProjectiveProjection Q ⟨A, hA⟩ at h1
    rw [matrixProjectiveConjugation_mk] at h1
    have h2 := congrArg Subtype.val (hproj h1)
    rw [matrixDerivedConjugation_val, matrixIsometryInclusion_val] at h2
    simp only [SemidirectProduct.left_inl, SemidirectProduct.right_inl, map_one,
      MulAut.one_apply] at h2
    calc (g : GL (Fin d) K) * A = (g : GL (Fin d) K) * A * (g : GL (Fin d) K)⁻¹ * g := by group
      _ = A * g := by rw [h2]
  obtain ⟨U, hU3, hU⟩ := hT
  have h1 : matrixLinearIso (g : GL (Fin d) K) = 1 := by
    refine CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.eq_one_of_commute_orthDerived hnd
      ⟨U, hU3, hU⟩ g.2 fun h hh => ?_
    have hh' : h ∈ (matrixDerived Q).map matrixLinearIso.toMonoidHom := by
      rw [matrixDerived_map_native Q]
      exact hh
    obtain ⟨A, hA, rfl⟩ := hh'
    change matrixLinearIso (g : GL (Fin d) K) * matrixLinearIso A =
      matrixLinearIso A * matrixLinearIso (g : GL (Fin d) K)
    rw [← map_mul, ← map_mul, hcomm A hA]
  exact Subtype.ext (matrixLinearIso.injective (h1.trans (map_one matrixLinearIso).symm))

theorem exists_isometric_model (hnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K (Fin d → K), Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {X : Type*} [Group X] {F : Subgroup X} [F.Normal] (hC : Subgroup.centralizer (F : Set X) = ⊥)
    (e : ↥F ≃* matrixProjectiveDerived Q) {Y : Subgroup X} (hFY : F ≤ Y)
    (hY : ∀ y ∈ Y, MulAut.congr e (MulAut.conjNormal y) ∈ (isometryConjugationHom Q).range) :
    ∃ ψ : Y →* ((Fin d → K) ≃ₗ[K] (Fin d → K)), Function.Injective ψ ∧
      (∀ y, ψ y ∈ TauCeti.QuadraticMap.orthogonalGroup Q) ∧
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ≤
        ψ.range ∧
      ∀ y, ψ y ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ →
        (y : X) ∈ F := by
  have hκ := isometryConjugationHom_injective_of_charTwo hnd hT
  let β : X →* MulAut (matrixProjectiveDerived Q) :=
    (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal
  have hβinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : MulAut.conjNormal x = (1 : MulAut ↥F) :=
      (MulAut.congr e).injective (by rw [map_one]; exact hx)
    have hc : x ∈ Subgroup.centralizer (F : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h2 := congrArg (fun φ : MulAut ↥F => ((φ ⟨y, hy⟩ : ↥F) : X)) h1
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h2
      calc y * x = x * y * x⁻¹ * x := by rw [h2]
        _ = x * y := by group
    rwa [hC, Subgroup.mem_bot] at hc
  have hβF : ∀ f : F, β f = MulAut.conj (e f) := fun f => by
    change MulAut.congr e (MulAut.conjNormal (f : X)) = _
    rw [← congr_conj]
    congr 1
    refine MulEquiv.ext fun y => Subtype.ext ?_
    rw [MulAut.conjNormal_apply, MulAut.conj_apply]
    rfl
  let βY : Y →* (isometryConjugationHom Q).range :=
    (β.comp Y.subtype).codRestrict _ fun y => hY y y.2
  let κe : matrixIsometries Q ≃* (isometryConjugationHom Q).range := MonoidHom.ofInjective hκ
  let ψ₀ : Y →* matrixIsometries Q := κe.symm.toMonoidHom.comp βY
  have hψ₀ : ∀ y : Y, isometryConjugationHom Q (ψ₀ y) = β y := fun y =>
    congrArg Subtype.val (κe.apply_symm_apply (βY y))
  let ψ : Y →* ((Fin d → K) ≃ₗ[K] (Fin d → K)) :=
    matrixLinearIso.toMonoidHom.comp ((matrixIsometries Q).subtype.comp ψ₀)
  have hψ : ∀ y, ψ y = matrixLinearIso ((ψ₀ y : matrixIsometries Q) : GL (Fin d) K) :=
    fun y => rfl
  refine ⟨ψ, fun y y' h => ?_, fun y => (ψ₀ y).2, fun h hh => ?_, fun y hy => ?_⟩
  · have h1 : ψ₀ y = ψ₀ y' := Subtype.ext (matrixLinearIso.injective h)
    have h2 : β y = β y' := by rw [← hψ₀, ← hψ₀, h1]
    exact Subtype.ext (hβinj h2)
  ·
    have hh' : h ∈ (matrixDerived Q).map matrixLinearIso.toMonoidHom := by
      rw [matrixDerived_map_native Q]
      exact hh
    obtain ⟨A, hA, rfl⟩ := hh'
    rw [matrixDerived_eq_map_commutator] at hA
    obtain ⟨g, hg, rfl⟩ := hA
    have hκg : isometryConjugationHom Q g ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner (matrixProjectiveDerived Q) := by
      rw [inner_eq_map_commutator]
      exact ⟨g, hg, rfl⟩
    obtain ⟨p, hp⟩ := hκg
    have hfY : ((e.symm p : F) : X) ∈ Y := hFY (e.symm p).2
    refine ⟨⟨_, hfY⟩, ?_⟩
    have h1 : ψ₀ ⟨_, hfY⟩ = g := by
      apply hκ
      rw [hψ₀]
      change β ((e.symm p : F) : X) = _
      rw [hβF, MulEquiv.apply_symm_apply]
      exact hp
    rw [hψ, h1]
    rfl
  ·
    have hA : ((ψ₀ y : matrixIsometries Q) : GL (Fin d) K) ∈ matrixDerived Q := by
      rw [matrixDerived_comap_native Q]
      exact hy
    rw [matrixDerived_eq_map_commutator] at hA
    obtain ⟨g, hg, hgy⟩ := hA
    have hg' : g = ψ₀ y := Subtype.ext hgy
    have hκg : isometryConjugationHom Q (ψ₀ y) ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner (matrixProjectiveDerived Q) := by
      rw [inner_eq_map_commutator, ← hg']
      exact ⟨g, hg, rfl⟩
    obtain ⟨p, hp⟩ := hκg
    have h1 : β (y : X) = β ((e.symm p : F) : X) := by
      rw [hβF, MulEquiv.apply_symm_apply, hp]
      exact (hψ₀ y).symm
    rw [hβinj h1]
    exact (e.symm p).2

end CFSG.RankThree.GF2n.Smith81.OrthModel
