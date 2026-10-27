module

public import CFSG.LocalAnalysis.StandardType.GGF4N2JPositions
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRestGen
import CFSG.RankThree.PartOne.AUTSL.Interface
import CFSG.RankThree.PartTwo.KFacts.K71L28TwoFree

public section

namespace CFSG.StandardType

open Matrix CFSG.ComponentClassification.CatalogueBHigherLinearAction
  CFSG.ComponentClassification.CatalogueBHigherLinearField
  CFSG.ComponentClassification.CatalogueBGraphForm

@[expose] def GGF4N2NbrReflectionAt {G : Type} [Group G] (Bs D J Y : Subgroup G) (z : G)
    (eJ : ↥J ≃* Matrix.SpecialLinearGroup (Fin 4) (GaloisField 2 2)) : Prop :=
  ∃ t ∈ Y, t ∈ Subgroup.normalizer (Bs : Set G) ∧ t ∈ Subgroup.normalizer (J : Set G) ∧
    t * z * t⁻¹ = z ∧
    (∃ htD : t ∈ Subgroup.normalizer (D : Set G), orderOf (D.normalizerMonoidHom ⟨t, htD⟩) = 2) ∧
    ∃ (C : Matrix.GeneralLinearGroup (Fin 4) (GaloisField 2 2)) (δ : ℕ), δ ≤ 1 ∧
      ∀ w : Matrix.SpecialLinearGroup (Fin 4) (GaloisField 2 2),
        t * (eJ.symm w : G) * t⁻¹ = (eJ.symm (N2KFieldCoefficient.blockGamma C δ w) : G)

theorem ringEquiv_eq_refl_of_fix {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 4) (σ : F ≃+* F) {c : F} (hc0 : c ≠ 0) (hc1 : c ≠ 1) (hσ : σ c = c) :
    σ = RingEquiv.refl F := by
  classical
  haveI := Fintype.ofFinite F
  have hne1 : c + 1 ≠ 0 := by
    intro h
    apply hc1
    calc c = c + 1 + 1 := by rw [add_assoc, CharTwo.add_self_eq_zero (1 : F), add_zero]
      _ = 1 := by rw [h, zero_add]
  have hne2 : c + 1 ≠ 1 := fun h => hc0 (by simpa using h)
  have hne3 : c + 1 ≠ c := fun h => (one_ne_zero : (1 : F) ≠ 0) (by simpa using h)
  have huniv : ({0, 1, c, c + 1} : Finset F) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_insert_of_notMem (by simp [hc0.symm, hne1.symm]),
      Finset.card_insert_of_notMem (by simp [hc1.symm, hne2.symm]),
      Finset.card_pair hne3.symm, Fintype.card_eq_nat_card, hF]
  apply RingEquiv.ext
  intro t
  have ht : t ∈ ({0, 1, c, c + 1} : Finset F) := huniv ▸ Finset.mem_univ t
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · simp
  · simp
  · exact hσ
  · rw [map_add, map_one, hσ]
    rfl

section Trace

variable {n : ℕ} {K : Type} [Field K]

theorem trace_slConjugation (A : Matrix.GeneralLinearGroup (Fin n) K)
    (g : Matrix.SpecialLinearGroup (Fin n) K) :
    Matrix.trace ((slConjugation n K A g : Matrix.SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = Matrix.trace (g : Matrix (Fin n) (Fin n) K) := by
  rw [slConjugation_matrix, Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, one_mul]

theorem trace_slFieldAut (σ : K ≃+* K) (g : Matrix.SpecialLinearGroup (Fin n) K) :
    Matrix.trace ((slFieldAut (Fin n) K σ g : Matrix.SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = σ (Matrix.trace (g : Matrix (Fin n) (Fin n) K)) := by
  simp only [Matrix.trace, Matrix.diag, map_sum]
  rfl

theorem trace_slGraphAut (g : Matrix.SpecialLinearGroup (Fin n) K) :
    Matrix.trace ((slGraphAut n K g : Matrix.SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) =
      Matrix.trace ((g⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  rw [slGraphAut_matrix, Matrix.trace_transpose]

end Trace

section Branches

theorem ggF4N2_nbrReflectionAt_of_psl6
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hL : GGCentralImage .POmegaMinus 4 2 L)
    (eJ : ↥J ≃* Matrix.SpecialLinearGroup (Fin 4) (GaloisField 2 2))
    {z : G} {Y : Subgroup G} (hzY : GGNbr 5 B x D J z Y) (hY : GGCentralImage .PSL 6 2 Y) :
    GGF4N2NbrReflectionAt Bs D J Y z eJ := by
  obtain ⟨t, htY, htBs, htJ, htD, htz, hord⟩ :=
    ggF4N2K_exists_original_inverter_orderTwo_on_D hR hzY hL hY
  refine ⟨t, htY, htBs, Subgroup.centralizer_le_normalizer _ htJ, htz, ⟨htD, hord⟩, 1, 0,
    le_refl 1 |>.trans' (Nat.zero_le 1), fun w => ?_⟩
  have hw : t * (eJ.symm w : G) = (eJ.symm w : G) * t :=
    (Subgroup.mem_centralizer_iff.mp htJ _ (eJ.symm w).2).symm
  rw [hw, mul_inv_cancel_right]
  congr 3
  simp [N2KFieldCoefficient.blockGamma]

end Branches

end CFSG.StandardType

end
