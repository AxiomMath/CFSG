module

public import CFSG.LocalAnalysis.StandardType.GGTableBTypeABstar
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeAEndModel

public section

namespace CFSG.StandardType.TypeA

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification CFSG.Assembly

variable {d p : ℕ} {K : Type} [Field K]

@[expose] def GGPGLTorality (p d : ℕ) (K : Type) [Field K] : Prop :=
  ∀ X : Subgroup (MulAut (projectiveSL d K)), IsElemAbelian p X →
    (X : Set (MulAut (projectiveSL d K))) ⊆ Set.range (conjAut d K) →
    p ^ (d - 2) ≤ Nat.card X → p ^ 3 ≤ Nat.card X →
    ∃ A₀ : GL (Fin d) K, ∀ A : GL (Fin d) K, conjAut d K A ∈ X → ∀ i j, i ≠ j →
      ((A₀ : Matrix (Fin d) (Fin d) K) * (A : Matrix (Fin d) (Fin d) K) *
        ((A₀⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) i j = 0

theorem coe_inv_of_diagonal {D : GL (Fin d) K} {t : Fin d → K}
    (hD : (D : Matrix (Fin d) (Fin d) K) = diagonal t) :
    ((D⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (fun k => (t k)⁻¹) := by
  have ht0 : ∀ k, t k ≠ 0 := by
    intro k hk
    have h1 := D.isUnit.map (Matrix.detMonoidHom (n := Fin d) (R := K))
    rw [Matrix.coe_detMonoidHom, hD, det_diagonal,
      Finset.prod_eq_zero (Finset.mem_univ k) hk] at h1
    exact not_isUnit_zero h1
  have h1 : diagonal t * diagonal (fun k => (t k)⁻¹) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext k
    exact mul_inv_cancel₀ (ht0 k)
  calc ((D⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
      = ((D⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
          ((D : Matrix (Fin d) (Fin d) K) * diagonal (fun k => (t k)⁻¹)) := by
        rw [hD, h1, Matrix.mul_one]
    _ = diagonal (fun k => (t k)⁻¹) := by
        rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]

theorem slConjugation_transvection_of_diagonal {D : GL (Fin d) K} {t : Fin d → K}
    (hD : (D : Matrix (Fin d) (Fin d) K) = diagonal t) {i j : Fin d} (hij : i ≠ j) (c : K) :
    CatalogueBHigherLinearAction.slConjugation d K D (SpecialLinearGroup.transvection hij c) =
      SpecialLinearGroup.transvection hij (t i * c * (t j)⁻¹) := by
  have ht0 : ∀ k, t k ≠ 0 := by
    intro k hk
    have h1 := D.isUnit.map (Matrix.detMonoidHom (n := Fin d) (R := K))
    rw [Matrix.coe_detMonoidHom, hD, det_diagonal,
      Finset.prod_eq_zero (Finset.mem_univ k) hk] at h1
    exact not_isUnit_zero h1
  ext a b
  rw [coe_slConjugation', CFSG.LinearGroups.coe_transvection, CFSG.LinearGroups.coe_transvection,
    hD, coe_inv_of_diagonal hD]
  have h1 := CFSG.LinearGroups.diagonal_mul_toMatrix_mul_diagonal_inv ht0 ⟨i, j, hij, c⟩
  simp only [TransvectionStruct.toMatrix_mk, CFSG.LinearGroups.transvectionDiagConj] at h1
  rw [show (1 : Matrix (Fin d) (Fin d) K) + single i j c = transvection i j c from rfl, h1]
  rfl

theorem ggBstarBound_of_torality [Finite K] [CharP K 2] (hp : p.Prime) (hp2 : p ≠ 2)
    (hd : 3 ≤ d) (htor : GGPGLTorality p d K) :
    GGBstarBound p (d - 2) (projectiveSL d K) (Set.range (conjAut d K)) := by
  intro Eb Eh hEbI _ hr h3 hle hEh hcard
  set E' := Eh ⊓ linearAutGroup d K with hE'
  have hE'A : IsElemAbelian p E' := TableB.isElemAbelian_mono hEh inf_le_left
  have hE'I : (E' : Set (MulAut (projectiveSL d K))) ⊆ Set.range (conjAut d K) :=
    fun x hx => mem_linearAutGroup_iff.mp hx.2
  have h1 := card_le_mul_card_inf_linear hp hp2 hd hEh
  have hEbE' : Eb ≤ E' := le_inf hle fun x hx => by
    obtain ⟨A, hA⟩ := hEbI hx
    rw [← hA]
    exact conjAut_mem_linearAutGroup A
  have hcardE' : p * Nat.card Eb ≤ Nat.card E' := by
    have h2 : p * (p * Nat.card Eb) ≤ p * Nat.card E' := by
      calc p * (p * Nat.card Eb) = p ^ 2 * Nat.card Eb := by ring
        _ ≤ Nat.card Eh := hcard
        _ ≤ p * Nat.card E' := h1
    exact Nat.le_of_mul_le_mul_left h2 hp.pos
  have hEbpos : 0 < Nat.card Eb := Nat.card_pos
  have hlt : Eb < E' := by
    refine lt_of_le_of_ne hEbE' fun heq => ?_
    rw [← heq] at hcardE'
    have := hp.two_le
    nlinarith
  have hr' : p ^ (d - 2) ≤ Nat.card E' :=
    hr.trans ((Nat.le_mul_of_pos_left _ hp.pos).trans hcardE')
  have h3' : p ^ 3 ≤ Nat.card E' :=
    h3.trans ((Nat.le_mul_of_pos_left _ hp.pos).trans hcardE')
  obtain ⟨A₀, hA₀⟩ := htor E' hE'A hE'I hr' h3'
  have h01 : (⟨0, by omega⟩ : Fin d) ≠ ⟨1, by omega⟩ := by simp
  set c₀ := CatalogueBHigherLinearAction.slConjugation d K A₀⁻¹ with hc₀
  set U₀ := (SpecialLinearGroup.transvectionHom h01 : Multiplicative K →* _).range with hU₀
  set U := (U₀.map c₀.toMonoidHom).map (proj d K) with hU
  refine ⟨E', hlt, inf_le_left, U, ?_, ?_, ?_⟩
  · intro hbot
    have hmem : proj d K (c₀ (SpecialLinearGroup.transvection h01 1)) ∈ U :=
      ⟨_, ⟨_, ⟨Multiplicative.ofAdd 1, by
        rw [SpecialLinearGroup.transvectionHom_apply, toAdd_ofAdd]⟩, rfl⟩, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    have h2 := mem_scalars_of_slConjugation_mem A₀⁻¹ (proj_eq_one_iff.mp hmem)
    obtain ⟨c, -, hc⟩ := mem_scalars.mp h2
    have h4 := congrArg (fun M : Matrix (Fin d) (Fin d) K => M ⟨0, by omega⟩ ⟨1, by omega⟩) hc
    simp [CFSG.LinearGroups.coe_transvection] at h4
  · refine IsPGroup.map (IsPGroup.map (fun x => ⟨1, ?_⟩) c₀.toMonoidHom) (proj d K)
    obtain ⟨y, c, hc⟩ := x
    have h2 : y ^ 2 = 1 := by
      rw [← hc, SpecialLinearGroup.transvectionHom_apply,
        CFSG.RankThree.CALinearPlane.transvection_pow, Nat.cast_ofNat, CharTwo.two_eq_zero,
        zero_mul]
      exact Matrix.SpecialLinearGroup.transvection_coeff_zero h01
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, pow_one]
    exact h2
  · intro φ hφ u hu
    obtain ⟨A, rfl⟩ := hE'I hφ
    obtain ⟨_, ⟨_, ⟨c, rfl⟩, rfl⟩, rfl⟩ := hu
    set D := A₀ * A * A₀⁻¹ with hD
    have hDdiag : (D : Matrix (Fin d) (Fin d) K) =
        diagonal fun i => (D : Matrix (Fin d) (Fin d) K) i i := by
      refine CFSG.RankThree.CALinearPlane.eq_diagonal_of_offDiag fun i j hij => ?_
      rw [hD, Units.val_mul, Units.val_mul]
      exact hA₀ A hφ i j hij
    have h2 : CatalogueBHigherLinearAction.slConjugation d K A (c₀
        (SpecialLinearGroup.transvectionHom h01 c)) =
        c₀ (CatalogueBHigherLinearAction.slConjugation d K D
          (SpecialLinearGroup.transvectionHom h01 c)) := by
      rw [hc₀, ← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul, hD]
      congr 2
      group
    refine ⟨_, ⟨_, ⟨Multiplicative.ofAdd
      ((D : Matrix (Fin d) (Fin d) K) ⟨0, by omega⟩ ⟨0, by omega⟩ * Multiplicative.toAdd c *
        ((D : Matrix (Fin d) (Fin d) K) ⟨1, by omega⟩ ⟨1, by omega⟩)⁻¹), rfl⟩, rfl⟩, ?_⟩
    rw [conjAut_proj]
    simp only [MulEquiv.coe_toMonoidHom]
    rw [h2]
    simp only [SpecialLinearGroup.transvectionHom_apply, toAdd_ofAdd]
    rw [slConjugation_transvection_of_diagonal hDdiag h01]

end CFSG.StandardType.TypeA
