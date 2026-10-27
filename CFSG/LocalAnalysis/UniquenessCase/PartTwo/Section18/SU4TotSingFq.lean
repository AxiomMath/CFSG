module

public import CFSG.ClassicalGroups.Unitary.Form
import CFSG.LocalAnalysis.RankThreeUC.AGL81S16RankFix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.ClassicalGroups.Unitary

variable {F : Type} [Field F] [Finite F] {σ : F ≃+* F} {n : ℕ}

private noncomputable def fixedField_T1J1 (σ : F ≃+* F) : Subfield F :=
  σ.toRingHom.eqLocusField (RingHom.id F)

private noncomputable def traceForm_T1J1 (hσ : IsUnitaryInvolution σ) (x y : Fin 4 → F) :
    ↥(fixedField_T1J1 σ) :=
  ⟨herm σ x y + σ (herm σ x y), hσ.trace_fixed (herm σ x y)⟩

private noncomputable def B_T1J1 (hσ : IsUnitaryInvolution σ) :
    LinearMap.BilinForm ↥(fixedField_T1J1 σ) (Fin 4 → F) :=
  LinearMap.mk₂ ↥(fixedField_T1J1 σ) (traceForm_T1J1 hσ)
    (fun x x' y => Subtype.ext (by
      show herm σ (x + x') y + σ (herm σ (x + x') y) =
        (herm σ x y + σ (herm σ x y)) + (herm σ x' y + σ (herm σ x' y))
      rw [herm_add_left, map_add]
      ring))
    (fun a x y => Subtype.ext (by
      show herm σ (a • x) y + σ (herm σ (a • x) y) =
        (a : F) * (herm σ x y + σ (herm σ x y))
      have ha : σ (a : F) = (a : F) := a.2
      rw [Subfield.smul_def, herm_smul_left, ha, map_mul, ha]
      ring))
    (fun x y y' => Subtype.ext (by
      show herm σ x (y + y') + σ (herm σ x (y + y')) =
        (herm σ x y + σ (herm σ x y)) + (herm σ x y' + σ (herm σ x y'))
      rw [herm_add_right, map_add]
      ring))
    (fun a x y => Subtype.ext (by
      show herm σ x (a • y) + σ (herm σ x (a • y)) =
        (a : F) * (herm σ x y + σ (herm σ x y))
      have ha : σ (a : F) = (a : F) := a.2
      rw [Subfield.smul_def, herm_smul_right, map_mul, ha]
      ring))

private lemma B_T1J1_val (hσ : IsUnitaryInvolution σ) (x y : Fin 4 → F) :
    (B_T1J1 hσ x y : F) = herm σ x y + σ (herm σ x y) := rfl

private lemma B_T1J1_comm (hσ : IsUnitaryInvolution σ) (x y : Fin 4 → F) :
    B_T1J1 hσ x y = B_T1J1 hσ y x := by
  apply Subtype.ext
  rw [B_T1J1_val, B_T1J1_val, herm_conj σ hσ.invol x y, hσ.invol]
  ring

private lemma B_T1J1_sepLeft (hσ : IsUnitaryInvolution σ) (h2 : (2 : F) = 0) :
    (B_T1J1 hσ).SeparatingLeft := by
  intro x hx
  by_contra hx0
  obtain ⟨y', hy'⟩ := exists_herm_ne_zero σ hx0
  obtain ⟨d, hd⟩ := hσ.trace_surj 1 (map_one σ)
  have hB : B_T1J1 hσ x ((d / herm σ x y') • y') = 1 := by
    apply Subtype.ext
    rw [B_T1J1_val, herm_smul_right, div_mul_cancel₀ d hy', hd]
    rfl
  have h0 := hx ((d / herm σ x y') • y')
  rw [hB] at h0
  exact one_ne_zero h0

private lemma B_T1J1_nondegenerate (hσ : IsUnitaryInvolution σ) (h2 : (2 : F) = 0) :
    (B_T1J1 hσ).Nondegenerate :=
  ⟨B_T1J1_sepLeft hσ h2, fun y hy =>
    B_T1J1_sepLeft hσ h2 y (fun z => by rw [B_T1J1_comm hσ y z]; exact hy z)⟩

private lemma B_T1J1_vanishes_span (hσ : IsUnitaryInvolution σ) (h2 : (2 : F) = 0)
    (S : Set (Fin 4 → F)) (hS : ∀ x ∈ S, ∀ y ∈ S, σ (herm σ x y) = herm σ x y) :
    ∀ a ∈ Submodule.span ↥(fixedField_T1J1 σ) S,
      ∀ b ∈ Submodule.span ↥(fixedField_T1J1 σ) S, B_T1J1 hσ a b = 0 := by
  have hmem : ∀ x ∈ S, ∀ y ∈ S, B_T1J1 hσ x y = 0 := by
    intro x hx y hy
    apply Subtype.ext
    rw [B_T1J1_val, hS x hx y hy, ← two_mul, h2, zero_mul]
    rfl
  have hspanSnd : ∀ x ∈ S, ∀ b ∈ Submodule.span ↥(fixedField_T1J1 σ) S,
      B_T1J1 hσ x b = 0 := by
    intro x hx b hb
    have hle : Submodule.span ↥(fixedField_T1J1 σ) S ≤ LinearMap.ker (B_T1J1 hσ x) := by
      rw [Submodule.span_le]
      intro y hy
      show B_T1J1 hσ x y = 0
      exact hmem x hx y hy
    exact hle hb
  intro a ha b hb
  have hle : Submodule.span ↥(fixedField_T1J1 σ) S ≤
      LinearMap.ker ((B_T1J1 hσ).flip b) := by
    rw [Submodule.span_le]
    intro x hx
    show B_T1J1 hσ x b = 0
    exact hspanSnd x hx b hb
  exact hle ha

private lemma two_le_two_pow_T1J1 (hF : Nat.card F = (2 ^ n) ^ 2) : 2 ≤ 2 ^ n := by
  haveI : Fintype F := Fintype.ofFinite F
  have hcardF : 1 < Nat.card F := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  by_contra h
  have hle : 2 ^ n ≤ 1 := by omega
  have hone : 2 ^ n = 1 := le_antisymm hle h1
  have hcard : Nat.card F = 1 := by
    calc Nat.card F = (2 ^ n) ^ 2 := hF
      _ = 1 ^ 2 := by rw [hone]
      _ = 1 := by norm_num
  omega

private lemma card_fixedField_T1J1 (hσ : IsUnitaryInvolution σ) (h2 : (2 : F) = 0)
    (hF : Nat.card F = (2 ^ n) ^ 2) :
    Nat.card ↥(fixedField_T1J1 σ) = 2 ^ n := by
  have hcardEquiv : Nat.card ↥(fixedField_T1J1 σ) = Nat.card {c : F // σ c = c} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)
  have hsq : Nat.card ↥(fixedField_T1J1 σ) ^ 2 = (2 ^ n) ^ 2 := by
    rw [pow_two, hcardEquiv,
      CFSG.LocalAnalysis.RankThreeUC.card_fixedField_mul_self hσ h2, hF]
  exact Nat.pow_left_injective (by norm_num) hsq

private lemma finrank_vec_T1J1 (hσ : IsUnitaryInvolution σ) (h2 : (2 : F) = 0)
    (hF : Nat.card F = (2 ^ n) ^ 2) :
    Module.finrank ↥(fixedField_T1J1 σ) (Fin 4 → F) = 8 := by
  have hbase : 2 ≤ 2 ^ n := two_le_two_pow_T1J1 hF
  have h := Module.natCard_eq_pow_finrank (K := ↥(fixedField_T1J1 σ)) (V := Fin 4 → F)
  rw [card_fixedField_T1J1 hσ h2 hF, Nat.card_fun, hF, Nat.card_fin, ← pow_mul] at h
  norm_num at h
  exact (Nat.pow_right_injective hbase h).symm

theorem card_closure_le_of_herm_fixed (hσ : IsUnitaryInvolution σ) (h2 : (2 : F) = 0)
    (hF : Nat.card F = (2 ^ n) ^ 2) (S : Set (Fin 4 → F))
    (hS : ∀ x ∈ S, ∀ y ∈ S, σ (herm σ x y) = herm σ x y) :
    Nat.card (AddSubgroup.closure S) ≤ 2 ^ (4 * n) := by
  have hfixcard : Nat.card ↥(fixedField_T1J1 σ) = 2 ^ n := card_fixedField_T1J1 hσ h2 hF
  have hdimV : Module.finrank ↥(fixedField_T1J1 σ) (Fin 4 → F) = 8 :=
    finrank_vec_T1J1 hσ h2 hF
  let W : Submodule ↥(fixedField_T1J1 σ) (Fin 4 → F) :=
    Submodule.span ↥(fixedField_T1J1 σ) S
  have hvan : ∀ a ∈ W, ∀ b ∈ W, B_T1J1 hσ a b = 0 :=
    B_T1J1_vanishes_span hσ h2 S hS
  have hnd : (B_T1J1 hσ).Nondegenerate := B_T1J1_nondegenerate hσ h2
  have hWle : W ≤ (B_T1J1 hσ).orthogonal W := by
    intro m hm
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro k hk
    exact hvan k hk m hm
  have hdimW : Module.finrank ↥(fixedField_T1J1 σ) W ≤ 4 := by
    have h1 : Module.finrank ↥(fixedField_T1J1 σ) W ≤
        Module.finrank ↥(fixedField_T1J1 σ) ((B_T1J1 hσ).orthogonal W) :=
      Submodule.finrank_mono hWle
    rw [LinearMap.BilinForm.finrank_orthogonal hnd W, hdimV] at h1
    omega
  have hcardW : Nat.card W = (2 ^ n) ^ Module.finrank ↥(fixedField_T1J1 σ) W := by
    rw [Module.natCard_eq_pow_finrank (K := ↥(fixedField_T1J1 σ)) (V := W), hfixcard]
  have hclosure : AddSubgroup.closure S ≤ W.toAddSubgroup :=
    (AddSubgroup.closure_le W.toAddSubgroup).2 fun x hx => Submodule.subset_span hx
  have hcard_le : Nat.card (AddSubgroup.closure S) ≤ Nat.card W :=
    Nat.card_mono (Set.finite_univ.subset (Set.subset_univ (W : Set (Fin 4 → F))))
      fun x hx => hclosure hx
  calc Nat.card (AddSubgroup.closure S) ≤ Nat.card W := hcard_le
    _ = (2 ^ n) ^ Module.finrank ↥(fixedField_T1J1 σ) W := hcardW
    _ ≤ (2 ^ n) ^ 4 := Nat.pow_le_pow_right (pow_pos (by norm_num) n) hdimW
    _ = 2 ^ (4 * n) := by rw [← pow_mul, Nat.mul_comm]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
