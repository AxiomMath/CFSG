module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.Quasithin.Background.HOm4Norm
import CFSG.Quasithin.Background.P3OrthoOm4
import CFSG.Quasithin.Background.G64Realize

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin.H.Om4
open CFSG.Quasithin
open CFSG.Open
open CFSG.Quasithin.G11.P3Ortho.Om4
open Matrix

private theorem s16c11_case5_mem_map_iff {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    {G : Type} [Group G] {K : Type} [Field K] {π : G →* ↥L}
    (hπs : Function.Surjective π) {β : W ≃* VM K} (φ : MulAut (VM K)) :
    φ ∈ L.map (MulAut.congr β).toMonoidHom ↔
      ∃ γ : G, (MulAut.congr β) (((π γ : ↥L) : MulAut W)) = φ := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨l, hl, rfl⟩
    obtain ⟨γ, hγ⟩ := hπs ⟨l, hl⟩
    exact ⟨γ, congrArg (MulAut.congr β).toMonoidHom
      (congrArg (fun x : ↥L => (x : MulAut W)) hγ)⟩
  · rintro ⟨γ, rfl⟩
    exact ⟨((π γ : ↥L) : MulAut W), (π γ).2, rfl⟩

private theorem s16c11_case5_toAdd_rho {K : Type} [Field K]
    (g h : Matrix.SpecialLinearGroup (Fin 2) K) (X : VM K) :
    Multiplicative.toAdd (rho (g, h) X) =
      (g : Matrix (Fin 2) (Fin 2) K) * Multiplicative.toAdd X *
        (h : Matrix (Fin 2) (Fin 2) K)ᵀ := by
  rw [rho_apply, toAdd_lr]
  simp [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]

private theorem s16c11_case5_toAdd_rho_transpose {K : Type} [Field K]
    (g r : Matrix.SpecialLinearGroup (Fin 2) K) (X : VM K) :
    Multiplicative.toAdd (rho (g, Matrix.SpecialLinearGroup.transpose r) X) =
      (g : Matrix (Fin 2) (Fin 2) K) * Multiplicative.toAdd X *
        (r : Matrix (Fin 2) (Fin 2) K) := by
  rw [s16c11_case5_toAdd_rho, Matrix.SpecialLinearGroup.coe_transpose,
    Matrix.transpose_transpose]

private theorem s16c11_case5_omega_tensor {K : Type} [Field K] [Finite K] [CharP K 2]
    (h4 : 4 ≤ Nat.card K) {A : GL (Fin 2 ⊕ Fin 2) K}
    (hA : A ∈ StatedOmega (StatedQuadPlus 2 K)) :
    ∃ z : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K,
      ∀ X : Matrix (Fin 2) (Fin 2) K,
        toMat K ((A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ (toMat K).symm X) =
          (z.1 : Matrix (Fin 2) (Fin 2) K) * X *
            ((z.2⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
  have hmem : Ψ K A ∈ (StatedOmega (StatedQuadPlus 2 K)).map (Ψ K).toMonoidHom :=
    ⟨A, hA, rfl⟩
  rw [map_statedOmega, commutator_eq_range h4] at hmem
  obtain ⟨z, hz⟩ := hmem
  refine ⟨z, fun X => ?_⟩
  have h1 := LinearEquiv.congr_fun hz X
  rw [Ψ_apply] at h1
  rw [← h1]
  exact (CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit.specialRho_apply z X).symm

private theorem s16c11_case5_exists_omega_of_tensor {K : Type} [Field K] [Finite K] [CharP K 2]
    (h4 : 4 ≤ Nat.card K)
    (z : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) :
    ∃ A ∈ StatedOmega (StatedQuadPlus 2 K), ∀ X : Matrix (Fin 2) (Fin 2) K,
      toMat K ((A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ (toMat K).symm X) =
        (z.1 : Matrix (Fin 2) (Fin 2) K) * X *
          ((z.2⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
  have hmem : (rho' K z : Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) ∈
      (rho' K).range := ⟨z, rfl⟩
  rw [← commutator_eq_range h4, ← map_statedOmega] at hmem
  obtain ⟨A, hA, hAz⟩ := hmem
  refine ⟨A, hA, fun X => ?_⟩
  have h1 : toMat K ((A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ (toMat K).symm X) =
      rho' K z X := by
    rw [← Ψ_apply]
    exact LinearEquiv.congr_fun hAz X
  rw [h1]
  exact (CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit.specialRho_apply z X).symm

private theorem s16c11_case5_aux {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    {K : Type} [Field K] [Finite K] (hKcard : Nat.card K = 2 ^ 2)
    (hR : (FFModel.nat (StatedOmega (StatedQuadPlus 2 K))).Realizes L ⊤ ⊥) :
    ∃ β : W ≃* VM K, L.map (MulAut.congr β).toMonoidHom = (rho (K := K)).range := by
  haveI : Fintype K := Fintype.ofFinite K
  have hKfcard : Fintype.card K = 2 ^ 2 := by rwa [← Nat.card_eq_fintype_card]
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2) hKfcard
  have h4 : 4 ≤ Nat.card K := by rw [hKcard]; norm_num
  obtain ⟨π, hπ⟩ := hR
  obtain ⟨E, hE⟩ :=
    G64.RealizesVia.exists_secEquiv (D := FFModel.nat (StatedOmega (StatedQuadPlus 2 K))) rfl hπ
  let E₁ : W ≃* Multiplicative (Fin 2 ⊕ Fin 2 → K) := E.trans Subgroup.topEquiv
  let TM : Multiplicative (Fin 2 ⊕ Fin 2 → K) ≃* VM K :=
    AddEquiv.toMultiplicative (toMat K).toAddEquiv
  let β : W ≃* VM K := E₁.trans TM
  have hE₁ : ∀ (γ : ↥(StatedOmega (StatedQuadPlus 2 K))) (v : W),
      E₁ (((π γ : ↥L) : MulAut W) v) =
        natAct (StatedOmega (StatedQuadPlus 2 K)) γ (E₁ v) := by
    intro γ v
    exact hE γ v
  have hβE : ∀ v : W, Multiplicative.toAdd (β v) =
      toMat K (Multiplicative.toAdd (E₁ v)) := by
    intro v
    rfl
  have hEβ : ∀ v : W, Multiplicative.toAdd (E₁ v) =
      (toMat K).symm (Multiplicative.toAdd (β v)) := by
    intro v
    rw [hβE v, LinearEquiv.symm_apply_apply]
  have hkey : ∀ (γ : ↥(StatedOmega (StatedQuadPlus 2 K))) (v : W),
      β (((π γ : ↥L) : MulAut W) v) =
        Multiplicative.ofAdd (toMat K (((γ : GL (Fin 2 ⊕ Fin 2) K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
            (toMat K).symm (Multiplicative.toAdd (β v)))) := by
    intro γ v
    have h1 : β (((π γ : ↥L) : MulAut W) v) =
        TM (natAct (StatedOmega (StatedQuadPlus 2 K)) γ (E₁ v)) := by
      rw [show β (((π γ : ↥L) : MulAut W) v) =
        TM (E₁ (((π γ : ↥L) : MulAut W) v)) from rfl]
      rw [hE₁ γ v]
    rw [h1]
    change Multiplicative.ofAdd (toMat K (((γ : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
        Multiplicative.toAdd (E₁ v))) =
      Multiplicative.ofAdd (toMat K (((γ : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
          (toMat K).symm (Multiplicative.toAdd (β v))))
    rw [hEβ v]
  have hstep : ∀ (A : GL (Fin 2 ⊕ Fin 2) K) (hA : A ∈ StatedOmega (StatedQuadPlus 2 K))
      (w : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K),
      (∀ X : Matrix (Fin 2) (Fin 2) K,
        toMat K ((A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ (toMat K).symm X) =
          (w.1 : Matrix (Fin 2) (Fin 2) K) * X *
            ((w.2⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) →
      (MulAut.congr β) (((π ⟨A, hA⟩ : ↥L) : MulAut W)) =
        rho (w.1, Matrix.SpecialLinearGroup.transpose (w.2⁻¹)) := by
    intro A hA w hw
    apply MulEquiv.ext
    intro X
    change β (((π ⟨A, hA⟩ : ↥L) : MulAut W) (β.symm X)) =
      rho (w.1, Matrix.SpecialLinearGroup.transpose (w.2⁻¹)) X
    have h := hkey ⟨A, hA⟩ (β.symm X)
    rw [MulEquiv.apply_symm_apply] at h
    rw [hw (Multiplicative.toAdd X)] at h
    rw [h, ← s16c11_case5_toAdd_rho_transpose w.1 w.2⁻¹ X]
    exact ofAdd_toAdd _
  refine ⟨β, ?_⟩
  apply le_antisymm
  · intro φ hφ
    rw [s16c11_case5_mem_map_iff hπ.1] at hφ
    obtain ⟨γ, hγ⟩ := hφ
    let γ' : ↥(StatedOmega (StatedQuadPlus 2 K)) := γ
    obtain ⟨w, hw⟩ := s16c11_case5_omega_tensor (K := K) h4
      (A := (γ' : GL (Fin 2 ⊕ Fin 2) K)) γ'.2
    exact ⟨(w.1, Matrix.SpecialLinearGroup.transpose (w.2⁻¹)),
      (hstep (γ' : GL (Fin 2 ⊕ Fin 2) K) γ'.2 w hw).symm.trans hγ⟩
  · intro φ hφ
    obtain ⟨z, rfl⟩ := hφ
    rw [s16c11_case5_mem_map_iff hπ.1]
    let w : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K :=
      (z.1, (Matrix.SpecialLinearGroup.transpose z.2)⁻¹)
    obtain ⟨A, hA, hAw⟩ := s16c11_case5_exists_omega_of_tensor (K := K) h4 w
    refine ⟨⟨A, hA⟩, ?_⟩
    have h2 := hstep A hA w hAw
    have hwz : (w.1, Matrix.SpecialLinearGroup.transpose (w.2⁻¹)) = z := by
      have h1 : w.2⁻¹ = Matrix.SpecialLinearGroup.transpose z.2 := by
        simp [w]
      refine Prod.ext rfl ?_
      rw [h1]
      exact Subtype.ext (by
        simp [Matrix.SpecialLinearGroup.transpose, Matrix.transpose_transpose])
    rwa [hwz] at h2

theorem s16c11_case5_tensor {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    (h : NatOmegaPlus L ⊤ ⊥ 4 2) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (β : W ≃* VM K), Nat.card K = 4 ∧
      L.map (MulAut.congr β).toMonoidHom = (rho (K := K)).range := by
  rw [NatOmegaPlus] at h
  obtain ⟨-, K, hKf, hKfin, hKcard, hR⟩ := h
  letI : Field K := hKf
  letI : Finite K := hKfin
  have hdiv : 4 / 2 = 2 := by decide
  rw [hdiv] at hR
  obtain ⟨β, hβ⟩ := s16c11_case5_aux (K := K) hKcard hR
  exact ⟨K, hKf, hKfin, β, by rw [hKcard]; norm_num, hβ⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
