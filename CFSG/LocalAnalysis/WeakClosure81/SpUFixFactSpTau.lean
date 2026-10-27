module

public import CFSG.RankThree.PartOne.KC.SymplecticFullCentralizerTransvection
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveTauGrp
import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviRootSL2Sp
import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelSpFixRoot
import CFSG.RankThree.PartOne.KC.SymplecticFullRankTwo

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.Classical
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.QuasithinUnique.Lin2.Five (tauSp)
open CFSG.LieType.Universal.Symplectic.SpExtras
  (mat mat_apply mat_elt mat_elt_positiveLong mat_injective E)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (gram)

variable {F : Type} [Field F]

private theorem spUFix_spEnd_injective (g : StatedSp 2 F) : Function.Injective (spEnd g) := by
  intro x y h
  have h1 := congrArg (spEnd g⁻¹) h
  rwa [← Module.End.mul_apply, ← Module.End.mul_apply, ← spEnd_mul, inv_mul_cancel, spEnd_one,
    Module.End.one_apply, Module.End.one_apply] at h1

private theorem spUFix_spEnd_inv_apply (g : StatedSp 2 F) (y : Fin 2 ⊕ Fin 2 → F) :
    spEnd g⁻¹ (spEnd g y) = y := by
  rw [← Module.End.mul_apply, ← spEnd_mul, inv_mul_cancel, spEnd_one, Module.End.one_apply]

private theorem spUFix_smul_single (c : F) (i j : Fin 2 ⊕ Fin 2) :
    c • Matrix.single i j (1 : F) = Matrix.single i j c := by
  ext p q
  simp [Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]

private theorem spUFix_mat_spTransvection_inl_zero (c : F) [CharP F 2] :
    mat 2 F (spTransvection (Pi.single (Sum.inl (0 : Fin 2)) 1) c) =
      Matrix.transvection (Sum.inl (0 : Fin 2)) (Sum.inr (0 : Fin 2)) c := by
  ext i j
  have h : (mat 2 F (spTransvection (Pi.single (Sum.inl (0 : Fin 2)) 1) c)) i j =
      (spEnd (spTransvection (Pi.single (Sum.inl (0 : Fin 2)) 1) c) (Pi.single j 1)) i := by
    rw [spEnd_apply, mat_apply, Matrix.mulVec_single_one, Matrix.col_apply]
  rw [h, spEnd_spTransvection, spForm_single_inl_zero]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.transvection, Matrix.single_apply, Matrix.one_apply, Pi.single_apply,
      CharTwo.neg_eq]

private theorem spUFix_mat_tauSp_spTransvection_inl_zero (c : F) [CharP F 2] :
    mat 2 F (tauSp (spTransvection (Pi.single (Sum.inl (0 : Fin 2)) 1) c)) =
      1 + Matrix.single (Sum.inl (0 : Fin 2)) (Sum.inr (1 : Fin 2)) c +
        Matrix.single (Sum.inl (1 : Fin 2)) (Sum.inr (0 : Fin 2)) c := by
  have h1 : spTransvection (Pi.single (Sum.inl (0 : Fin 2)) 1) c =
      CFSG.LieType.Universal.Symplectic.SpExtras.elt (.positiveLong (0 : Fin 2)) c := by
    apply mat_injective
    rw [spUFix_mat_spTransvection_inl_zero, mat_elt_positiveLong]
  rw [h1, CFSG.SeitzReduction.F4Pilot.tauSp_elt,
    CFSG.LieType.Universal.Symplectic.SpExtras.mat_elt]
  simp [CFSG.SeitzReduction.F4Pilot.tauIdx,
    CFSG.SeitzReduction.F4Pilot.tauExp,
    CFSG.LieType.Universal.Symplectic.SpExtras.E, spUFix_smul_single]
  abel

private theorem spUFix_tauSp_sub_one (c : F) [CharP F 2] :
    (spEnd (tauSp (spTransvection (Pi.single (Sum.inl (0 : Fin 2)) 1) c)) - 1)
        (Pi.single (Sum.inr (1 : Fin 2)) 1) = c • Pi.single (Sum.inl (0 : Fin 2)) 1 ∧
    (spEnd (tauSp (spTransvection (Pi.single (Sum.inl (0 : Fin 2)) 1) c)) - 1)
        (Pi.single (Sum.inr (0 : Fin 2)) 1) = c • Pi.single (Sum.inl (1 : Fin 2)) 1 := by
  constructor
  · rw [LinearMap.sub_apply, Module.End.one_apply, spEnd_apply, ← mat_apply,
      spUFix_mat_tauSp_spTransvection_inl_zero]
    simp only [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq]
    simp [Pi.single_apply, Pi.smul_apply, smul_eq_mul]
  · rw [LinearMap.sub_apply, Module.End.one_apply, spEnd_apply, ← mat_apply,
      spUFix_mat_tauSp_spTransvection_inl_zero]
    simp only [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq]
    simp [Pi.single_apply, Pi.smul_apply, smul_eq_mul]

private theorem spUFix_spEnd_conj_sub_one_apply (H G0 : StatedSp 2 F) (y : Fin 2 ⊕ Fin 2 → F) :
    (spEnd (H * G0 * H⁻¹) - 1) (spEnd H y) = spEnd H ((spEnd G0 - 1) y) := by
  have hmul : spEnd (H * G0 * H⁻¹) = spEnd H * spEnd G0 * spEnd H⁻¹ := by
    rw [spEnd_mul, spEnd_mul]
  simp only [hmul, LinearMap.sub_apply, Module.End.one_apply, Module.End.mul_apply,
    spUFix_spEnd_inv_apply H y, map_sub]

private theorem spUFix_conj_tauSp_ne [CharP F 2] (H : StatedSp 2 F) {c : F} (hc : c ≠ 0)
    (b : Fin 2 ⊕ Fin 2 → F) (s : F) :
    H * tauSp (spTransvection (Pi.single (Sum.inl (0 : Fin 2)) 1) c) * H⁻¹ ≠
      spTransvection b s := by
  intro hEq
  obtain ⟨hA1, hA0⟩ := spUFix_tauSp_sub_one (F := F) (c := c)
  have hc1 := spUFix_spEnd_conj_sub_one_apply H
    (tauSp (spTransvection (Pi.single (Sum.inl (0 : Fin 2)) 1) c))
    (Pi.single (Sum.inr (1 : Fin 2)) 1)
  have hc0 := spUFix_spEnd_conj_sub_one_apply H
    (tauSp (spTransvection (Pi.single (Sum.inl (0 : Fin 2)) 1) c))
    (Pi.single (Sum.inr (0 : Fin 2)) 1)
  have hu1a : (spEnd (H * tauSp (spTransvection (Pi.single (Sum.inl (0 : Fin 2)) 1) c) * H⁻¹)
        - 1) (spEnd H (Pi.single (Sum.inr (1 : Fin 2)) 1)) =
      c • spEnd H (Pi.single (Sum.inl (0 : Fin 2)) 1) := by
    rw [hc1, hA1, map_smul]
  have hu0a : (spEnd (H * tauSp (spTransvection (Pi.single (Sum.inl (0 : Fin 2)) 1) c) * H⁻¹)
        - 1) (spEnd H (Pi.single (Sum.inr (0 : Fin 2)) 1)) =
      c • spEnd H (Pi.single (Sum.inl (1 : Fin 2)) 1) := by
    rw [hc0, hA0, map_smul]
  have hu1b : (spEnd (H * tauSp (spTransvection (Pi.single (Sum.inl (0 : Fin 2)) 1) c) * H⁻¹)
        - 1) (spEnd H (Pi.single (Sum.inr (1 : Fin 2)) 1)) =
      (s * spForm 2 F (spEnd H (Pi.single (Sum.inr (1 : Fin 2)) 1)) b) • b := by
    rw [hEq, LinearMap.sub_apply, Module.End.one_apply, spEnd_spTransvection]
    simp
  have hu0b : (spEnd (H * tauSp (spTransvection (Pi.single (Sum.inl (0 : Fin 2)) 1) c) * H⁻¹)
        - 1) (spEnd H (Pi.single (Sum.inr (0 : Fin 2)) 1)) =
      (s * spForm 2 F (spEnd H (Pi.single (Sum.inr (0 : Fin 2)) 1)) b) • b := by
    rw [hEq, LinearMap.sub_apply, Module.End.one_apply, spEnd_spTransvection]
    simp
  have hLI0 : LinearIndependent F
      (![Pi.single (Sum.inl (0 : Fin 2)) 1, Pi.single (Sum.inl (1 : Fin 2)) 1] :
        Fin 2 → (Fin 2 ⊕ Fin 2 → F)) := by
    rw [linearIndependent_fin2]
    constructor
    · intro hz
      have h := congrFun hz (Sum.inl (1 : Fin 2))
      simpa using h
    · intro a hz
      have h := congrFun hz (Sum.inl (0 : Fin 2))
      simp at h
  have hLI := hLI0.map' (spEnd H)
    (LinearMap.ker_eq_bot_of_injective (spUFix_spEnd_injective H))
  have hLI' : LinearIndependent F (fun i : Fin 2 => c • (spEnd H ∘
      (![Pi.single (Sum.inl (0 : Fin 2)) 1, Pi.single (Sum.inl (1 : Fin 2)) 1] :
        Fin 2 → (Fin 2 ⊕ Fin 2 → F))) i) :=
    hLI.units_smul (fun _ : Fin 2 => Units.mk0 c hc)
  have hfin := linearIndependent_fin2.mp hLI'
  have hne : c • spEnd H (Pi.single (Sum.inl (1 : Fin 2)) 1) ≠ 0 := hfin.1
  have hforall : ∀ a : F, a • (c • spEnd H (Pi.single (Sum.inl (1 : Fin 2)) 1)) ≠
      c • spEnd H (Pi.single (Sum.inl (0 : Fin 2)) 1) := hfin.2
  have hne' : (spEnd (H * tauSp (spTransvection (Pi.single (Sum.inl (0 : Fin 2)) 1) c) * H⁻¹)
        - 1) (spEnd H (Pi.single (Sum.inr (0 : Fin 2)) 1)) ≠ 0 := by
    rw [hu0a]
    exact hne
  have hforall' : ∀ a : F, a • ((spEnd
        (H * tauSp (spTransvection (Pi.single (Sum.inl (0 : Fin 2)) 1) c) * H⁻¹) - 1)
        (spEnd H (Pi.single (Sum.inr (0 : Fin 2)) 1))) ≠
      (spEnd (H * tauSp (spTransvection (Pi.single (Sum.inl (0 : Fin 2)) 1) c) * H⁻¹)
        - 1) (spEnd H (Pi.single (Sum.inr (1 : Fin 2)) 1)) := by
    intro a
    rw [hu0a, hu1a]
    exact hforall a
  have hβ : s * spForm 2 F (spEnd H (Pi.single (Sum.inr (0 : Fin 2)) 1)) b ≠ 0 := by
    intro hb
    exact hne' (by rw [hu0b, hb, zero_smul])
  have hαβ : (s * spForm 2 F (spEnd H (Pi.single (Sum.inr (1 : Fin 2)) 1)) b) •
        ((spEnd (H * tauSp (spTransvection (Pi.single (Sum.inl (0 : Fin 2)) 1) c) * H⁻¹) - 1)
          (spEnd H (Pi.single (Sum.inr (0 : Fin 2)) 1))) =
      (s * spForm 2 F (spEnd H (Pi.single (Sum.inr (0 : Fin 2)) 1)) b) •
        ((spEnd (H * tauSp (spTransvection (Pi.single (Sum.inl (0 : Fin 2)) 1) c) * H⁻¹) - 1)
          (spEnd H (Pi.single (Sum.inr (1 : Fin 2)) 1))) := by
    rw [hu0b, hu1b, smul_smul, smul_smul, mul_comm]
  have hcontra : ((s * spForm 2 F (spEnd H (Pi.single (Sum.inr (0 : Fin 2)) 1)) b)⁻¹ *
        (s * spForm 2 F (spEnd H (Pi.single (Sum.inr (1 : Fin 2)) 1)) b)) •
        ((spEnd (H * tauSp (spTransvection (Pi.single (Sum.inl (0 : Fin 2)) 1) c) * H⁻¹) - 1)
          (spEnd H (Pi.single (Sum.inr (0 : Fin 2)) 1))) =
      (spEnd (H * tauSp (spTransvection (Pi.single (Sum.inl (0 : Fin 2)) 1) c) * H⁻¹) - 1)
        (spEnd H (Pi.single (Sum.inr (1 : Fin 2)) 1)) := by
    rw [← smul_smul, hαβ, smul_smul, inv_mul_cancel₀ hβ, one_smul]
  exact hforall' _ hcontra

theorem spUFix_tauSp_spTransvection_ne [Finite F] [CharP F 2] {a : Fin 2 ⊕ Fin 2 → F}
    (ha : a ≠ 0) {c : F} (hc : c ≠ 0) (b : Fin 2 ⊕ Fin 2 → F) (s : F) :
    tauSp (spTransvection a c) ≠ spTransvection b s := by
  have he : (Pi.single (Sum.inl (0 : Fin 2)) 1 : Fin 2 ⊕ Fin 2 → F) ≠ 0 := by
    intro hz
    have h := congrFun hz (Sum.inl (0 : Fin 2))
    simpa using h
  obtain ⟨h, hh⟩ := exists_spEnd_eq he ha
  have hconj : spTransvection a c =
      h * spTransvection (Pi.single (Sum.inl (0 : Fin 2)) 1) c * h⁻¹ := by
    rw [← hh]
    exact (spTransvection_conj h (Pi.single (Sum.inl (0 : Fin 2)) 1) c).symm
  have hG : tauSp (spTransvection a c) =
      tauSp h * tauSp (spTransvection (Pi.single (Sum.inl (0 : Fin 2)) 1) c) * (tauSp h)⁻¹ := by
    rw [hconj, map_mul, map_mul, map_inv]
  intro hEq
  exact spUFix_conj_tauSp_ne (tauSp h) hc b s (by rw [← hG]; exact hEq)

theorem spUFix_eq_tau_spTransvection_ne [Finite F] [CharP F 2] {α : MulAut ↥(StatedSp 2 F)}
    {s₀ : ↥(StatedSp 2 F)} {σ : F ≃+* F} (hα : ∀ g, α g = s₀ * fieldSp 2 F σ (tauSp g) * s₀⁻¹)
    {a : Fin 2 ⊕ Fin 2 → F} (ha : a ≠ 0) {c : F} (hc : c ≠ 0) (b : Fin 2 ⊕ Fin 2 → F) (s : F) :
    α (spTransvection a c) ≠ spTransvection b s := by
  intro hEq
  have h1 : s₀ * fieldSp 2 F σ (tauSp (spTransvection a c)) * s₀⁻¹ =
      spTransvection b s := by
    rw [← hα]
    exact hEq
  have h2 : fieldSp 2 F σ (tauSp (spTransvection a c)) = s₀⁻¹ * spTransvection b s * s₀ := by
    rw [← h1]
    group
  have h3 : fieldSp 2 F σ (tauSp (spTransvection a c)) = spTransvection (spEnd s₀⁻¹ b) s := by
    have hc1 := spTransvection_conj s₀⁻¹ b s
    rw [inv_inv] at hc1
    exact h2.trans hc1
  have h4 : tauSp (spTransvection a c) =
      spTransvection ((fun x => σ⁻¹ x) ∘ spEnd s₀⁻¹ b) (σ⁻¹ s) := by
    have h5 := congrArg (fieldSp 2 F σ⁻¹) h3
    have hcomp : fieldSp 2 F σ⁻¹ (fieldSp 2 F σ (tauSp (spTransvection a c))) =
        tauSp (spTransvection a c) := by
      rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
    rw [hcomp, borel86_spr_fieldSp_spTransvection] at h5
    exact h5
  exact (spUFix_tauSp_spTransvection_ne ha hc _ _) h4

end CFSG.LocalAnalysis.WeakClosure81

end
