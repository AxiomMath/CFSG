module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFOU3Fld
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115OddU3AutFixed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115OddL3AutClass

public section

namespace CFSG.Quasithin.SBd19F

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.QuasithinUnique.Ch1
open CFSG.LocalAnalysis.ComponentInitial.FourGroupOddBilinear (isometrySL)

theorem exists_isometry_embedding_of_fixed {p : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData p 1 F) (hp : p ≠ 2) {A : GL (HypIndex 1 1) F}
    (hA : A ∈ hypUnitary h 1 1) {c : F} (hc0 : c ≠ 0)
    (hAc : (A : Matrix (HypIndex 1 1) (HypIndex 1 1) F) *
      (A : Matrix (HypIndex 1 1) (HypIndex 1 1) F).map h.bar = c • 1)
    {σ : F ≃+* F} (hσ : ∀ x, σ x = h.bar x)
    (hx : (⟨A, σ⟩ : SemiGL (HypIndex 1 1) F) ∈ semilinearSimilitudes h 1 1)
    (Q : Subgroup (hypPSU h 1 1))
    (hQ : ∀ y ∈ Q, semilinearAutHom h (le_refl 1) (le_refl 1) ⟨_, hx⟩ y = y) :
    ∃ (R : Matrix (Fin 3) (Fin 3) h.fixedField) (φ : isometrySL R →* hypPSU h 1 1),
      R.det ≠ 0 ∧ Rᵀ = R ∧ Function.Injective φ ∧ Q ≤ φ.range := by
  have : CharP F p := h.charP
  have : Finite F := h.finite
  obtain ⟨R, φ, hRdet, hRsym, hker, hfix⟩ :=
    exists_fixed_embedding h hp (r := 1) (ε := 1) (by norm_num) hA hc0 hAc
  have hk : ringChar h.fixedField ≠ 2 := by
    rw [ringChar.eq h.fixedField p]
    exact hp
  have hRs : Rᵀ = R := by
    rcases hRsym with hs | hneg
    · exact hs
    · exfalso
      have hdet := congrArg Matrix.det hneg
      rw [Matrix.det_transpose, Matrix.det_neg, Fintype.card_fin] at hdet
      have h3 : (2 : h.fixedField) * R.det = 0 := by linear_combination hdet
      exact hRdet ((mul_eq_zero.mp h3).resolve_left (Ring.two_ne_zero hk))
  have hR0 : R ≠ 0 := fun h0 => hRdet (by rw [h0, Matrix.det_zero])
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, ← hker, MonoidHom.ker_eq_bot_iff]
    exact soProj_injective hR0
  refine ⟨R, φ, hRdet, hRs, hφinj, fun y hy => ?_⟩
  obtain ⟨g, rfl, hg⟩ := exists_commuting_rep_of_fixed h (le_refl 1) (le_refl 1) (by norm_num)
    hσ hx (hQ y hy)
  exact hfix g hg

theorem eq_seven_of_perfect_card_168_fixed {p : ℕ} {F : Type}
    [Field F] (h : UnitaryFieldData p 1 F) (hp5 : 5 ≤ p) {A : GL (HypIndex 1 1) F}
    (hA : A ∈ hypUnitary h 1 1) {c : F} (hc0 : c ≠ 0)
    (hAc : (A : Matrix (HypIndex 1 1) (HypIndex 1 1) F) *
      (A : Matrix (HypIndex 1 1) (HypIndex 1 1) F).map h.bar = c • 1)
    {σ : F ≃+* F} (hσ : ∀ x, σ x = h.bar x)
    (hx : (⟨A, σ⟩ : SemiGL (HypIndex 1 1) F) ∈ semilinearSimilitudes h 1 1)
    {Q : Subgroup (hypPSU h 1 1)} (hperf : Group.IsPerfect Q) (hcard : Nat.card Q = 168)
    (hQ : ∀ y ∈ Q, semilinearAutHom h (le_refl 1) (le_refl 1) ⟨_, hx⟩ y = y) : p = 7 := by
  obtain ⟨R, φ, hRdet, hRs, hφinj, hle⟩ :=
    exists_isometry_embedding_of_fixed h (by omega) hA hc0 hAc hσ hx Q hQ
  obtain ⟨hperf', hcard'⟩ := isPerfect_comap_of_le_range hφinj hle hperf
  exact eq_seven_of_perfect_card_168_isometrySL h.prime hp5
    (by rw [h.card_fixedField, pow_one]) hRs hRdet hperf' (by rw [hcard', hcard])

end CFSG.Quasithin.SBd19F
