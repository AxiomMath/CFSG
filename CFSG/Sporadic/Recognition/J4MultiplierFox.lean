module

public import CFSG.Sporadic.Recognition.J4MultiplierInputs
public import CFSG.Sporadic.Co1.Cover.FoxProof

public section

namespace CFSG.Sporadic.Recognition.J4Multiplier

open CFSG.Sporadic.Co1.Cover CFSG.Sporadic.J4Schreier CFSG.Sporadic.SmallF2 Matrix

theorem hl_proof_j4 (l : Fin 11 → ZMod 2) (hA : j4Aᵀ *ᵥ l = l) (hB : j4Bᵀ *ᵥ l = l) :
    l = 0 := by
  have h := congrArg (fun M => M *ᵥ l) hl_cert_j4
  simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, hA, hB,
    Matrix.one_mulVec, sub_self, Matrix.mulVec_zero, add_zero] at h
  exact h.symm

theorem hC_proof_j4 (hForm : J4FormCert) (c : Matrix (Fin 11) (Fin 11) (ZMod 2)) (hs : cᵀ = c)
    (hd : ∀ i, c i i = 0) (hA : j4Aᵀ * c * j4A = c) (hB : j4Bᵀ * c * j4B = c) : c = 0 := by
  have h := congrArg (fun M => M *ᵥ (fun ij : I2 => c ij.1 ij.2)) hForm
  simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, Rsym_mulVec c hs, Rdiag_mulVec c hd,
    Rinv_mulVec j4A c hA, Rinv_mulVec j4B c hB, Matrix.mulVec_zero, add_zero,
    Matrix.one_mulVec] at h
  ext i j
  exact (congrFun h (i, j)).symm

section Fox

variable {P : Type*} [Group P] (a b : P)
  (ρ : P →* ((Fin 11 → ZMod 2) ≃ₗ[ZMod 2] (Fin 11 → ZMod 2)))
  (hA : ∀ v, ρ a v = j4A *ᵥ v) (hB : ∀ v, ρ b v = j4B *ᵥ v)

include hA hB in
theorem hfox_proof_j4 (hFox : J4FoxCert) (hrel : ∀ i, eltPos a b (wordsPos i) = 1)
    (l : P → Fin 11 → ZMod 2) (hl : ∀ p q x, l (p * q) ⬝ᵥ x = l p ⬝ᵥ ρ q x + l q ⬝ᵥ x) :
    ∃ φ : Fin 11 → ZMod 2, (∀ x, l a ⬝ᵥ x = φ ⬝ᵥ ρ a x + φ ⬝ᵥ x) ∧
      (∀ x, l b ⬝ᵥ x = φ ⬝ᵥ ρ b x + φ ⬝ᵥ x) := by
  set u : Fin (11 + 11) → ZMod 2 := Fin.append (l a) (l b) with hu
  have hR : j4FoxMat *ᵥ u = 0 := by
    funext r
    show (fun c => j4FoxMat r c) ⬝ᵥ u = 0
    have e : (fun c => j4FoxMat r c) =
        flat (foxVec j4A j4B (wordsPos r.1) (Pi.single r.2 1)) :=
      funext (j4FoxMat_apply r)
    rw [e, hu, flat_dot, ← fox_sound a b ρ j4A j4B hA hB l hl (wordsPos r.1) (Pi.single r.2 1),
      hrel]
    exact l_one_dot ρ l hl _
  have key : u = deltaMat j4A j4B *ᵥ (listMat j4FoxX 11 (11 + 11) *ᵥ u) := by
    have h := congrArg (fun M => M *ᵥ u) hFox
    simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hR, Matrix.mulVec_zero, add_zero,
      Matrix.one_mulVec] at h
    exact h.symm
  set φ := listMat j4FoxX 11 (11 + 11) *ᵥ u with hφ
  have hla : l a = (j4Aᵀ + 1) *ᵥ φ := by
    funext j
    have h1 := congrFun key (Fin.castAdd 11 j)
    rw [deltaMat_mulVec_left] at h1
    rw [hu, Fin.append_left] at h1
    exact h1
  have hlb : l b = (j4Bᵀ + 1) *ᵥ φ := by
    funext j
    have h1 := congrFun key (Fin.natAdd 11 j)
    rw [deltaMat_mulVec_right] at h1
    rw [hu, Fin.append_right] at h1
    exact h1
  exact ⟨φ, fun x => by rw [hA x]; exact dot_coboundary j4A φ (l a) hla x,
    fun x => by rw [hB x]; exact dot_coboundary j4B φ (l b) hlb x⟩

end Fox

end CFSG.Sporadic.Recognition.J4Multiplier
