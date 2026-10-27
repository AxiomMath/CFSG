module

public import CFSG.ClassicalGroups.Unitary.Elements
public import CFSG.Timmesfeld.LieEmbed.UnitaryForms
import CFSG.ClassicalGroups.Unitary.Finite
import CFSG.Timmesfeld.Transvection.ModelRankSU

public section

namespace CFSG.Timmesfeld.Transvection.ModelRank

open Matrix CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.Timmesfeld.LieEmbed
  CFSG.ClassicalGroups.Unitary

section Witt

variable {F : Type*} [Field F] {σ : F ≃+* F} {n : ℕ}

theorem herm_mulVec_mulVec_of_conjTr_mul {P : Matrix (Fin n) (Fin n) F}
    (hP : conjTr σ P * P = antidiag n) (x y : Fin n → F) :
    herm σ (P *ᵥ x) (P *ᵥ y) = uForm σ x y := by
  rw [herm_mulVec, hP]
  rfl

theorem closure_uTrans_eq_top_of_T_eq_top {P : GL (Fin n) F}
    (hP : conjTr σ (P : Matrix (Fin n) (Fin n) F) * (P : Matrix (Fin n) (Fin n) F) = antidiag n)
    (hT : CFSG.ClassicalGroups.Unitary.T σ n = ⊤) :
    Subgroup.closure {x : SU σ n | ∃ (v : Fin n → F) (c : F), uForm σ v v = 0 ∧ c + σ c = 0 ∧
      suMat σ n x = uTrans σ v c} = ⊤ := by
  set S := {x : SU σ n | ∃ (v : Fin n → F) (c : F), uForm σ v v = 0 ∧ c + σ c = 0 ∧
    suMat σ n x = uTrans σ v c}
  set e := conjEquiv P hP
  set Pm := (P : Matrix (Fin n) (Fin n) F) with hPm
  set Pi := ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) with hPi
  have hPPi : Pm * Pi = 1 := by rw [hPm, hPi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hPiP : Pi * Pm = 1 := by rw [hPm, hPi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hsub : tvSet σ n ⊆ e.toMonoidHom '' S := by
    rintro g ⟨a, c, ha, hc, hg⟩
    refine ⟨e.symm g, ?_, e.apply_symm_apply g⟩
    set b := Pi *ᵥ a with hb
    have hab : Pm *ᵥ b = a := by rw [hb, mulVec_mulVec, hPPi, one_mulVec]
    refine ⟨b, c, ?_, hc, ?_⟩
    · rw [← herm_mulVec_mulVec_of_conjTr_mul hP, hab, ha]
    · have hmat : suMat σ n (e.symm g) =
          Pi * ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * Pm := rfl
      refine Matrix.ext_of_mulVec_single fun i => ?_
      rw [hmat, ← mulVec_mulVec, ← mulVec_mulVec, ← smul_def, hg, mulVec_add, mulVec_smul,
        mulVec_mulVec, hPiP, one_mulVec, ← hb, ← hab, herm_mulVec_mulVec_of_conjTr_mul hP,
        uTrans_mulVec]
  have hle : CFSG.ClassicalGroups.Unitary.T σ n ≤ (Subgroup.closure S).map e.toMonoidHom := by
    rw [CFSG.ClassicalGroups.Unitary.T, MonoidHom.map_closure]
    exact Subgroup.closure_mono hsub
  rw [eq_top_iff]
  intro x _
  have hx : e x ∈ (Subgroup.closure S).map e.toMonoidHom := hle (by rw [hT]; trivial)
  rwa [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] at hx

end Witt

theorem closure_uTrans_eq_top {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    [CharP F p] (hF : Nat.card F = (p ^ f) ^ 2) {m : ℕ} (hm : 2 ≤ m)
    (hm3 : (m, p ^ f) ≠ (3, 2)) :
    Subgroup.closure {x : SU (unitaryInvolution F p f) m | ∃ (v : Fin m → F) (c : F),
      uForm (unitaryInvolution F p f) v v = 0 ∧ c + unitaryInvolution F p f c = 0 ∧
      suMat (unitaryInvolution F p f) m x = uTrans (unitaryInvolution F p f) v c} = ⊤ := by
  obtain ⟨P, hP⟩ := exists_wittMatrix hF m
  exact closure_uTrans_eq_top_of_T_eq_top hP
    (T_eq_top (isUnitaryInvolution_unitaryInvolution hF) hm fun h3 =>
      exists_norm_ne_one hF fun hq => hm3 (by rw [h3, hq]))

theorem eq_top_of_forall_isUTransGroup_le {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) {m : ℕ} (hm : 4 ≤ m)
    {L : Subgroup (SU (unitaryInvolution F 2 f) m)}
    (h : ∀ (v : Fin m → F) (X : Subgroup (SU (unitaryInvolution F 2 f) m)),
      uForm (unitaryInvolution F 2 f) v v = 0 →
      IsUTransGroup (unitaryInvolution F 2 f) v X → X ≤ L) : L = ⊤ := by
  rw [eq_top_iff, ← closure_uTrans_eq_top hF (by omega) fun h3 => by
    simp only [Prod.mk.injEq] at h3
    omega, Subgroup.closure_le]
  rintro x ⟨v, c, hv, hc, hx⟩
  obtain ⟨X, hX⟩ := exists_isUTransGroup (unitaryInvolution_involutive hF) hv
  exact h v X hv hX ((hX.1 x).2 ⟨c, hc, hx⟩)

end CFSG.Timmesfeld.Transvection.ModelRank
