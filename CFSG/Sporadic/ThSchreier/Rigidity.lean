
module

public import CFSG.Sporadic.ThSchreier.RigidityBase

public import CFSG.Sporadic.Th.Max3.QuotientBase1
public import CFSG.Sporadic.ThSchreier.Enc8
public meta import CFSG.Sporadic.ThSchreier.Enc8
public import CFSG.Sporadic.ThSchreier.RigidityInputs
public import Certificates.Certificate2321
public import Mathlib
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Certificates.SchreierStabilizerGenerators
public import Certificates.Data.CFSGNative.Th.Certificate
public import CFSG.Sporadic.Th.Max3.CoreBase1
public import CFSG.Sporadic.Th.Max3.QuotientInputs

public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3

theorem enc_basisP : mul8 (colMat8 B1enc B2enc 1) basisPInvEnc = id8 :=
  Certificates.certificate2321.1

theorem enc_commutant : ∀ u < 256,
    mul8 (candEnc B1enc B2enc u) B1enc = mul8 B1enc (candEnc B1enc B2enc u) →
    mul8 (candEnc B1enc B2enc u) B2enc = mul8 B2enc (candEnc B1enc B2enc u) →
    candEnc B1enc B2enc u = zero8 ∨ candEnc B1enc B2enc u = id8 :=
  Certificates.certificate2321.2.1

theorem enc_intertwiner : ∀ u < 256,
    mul8 (candEnc D1enc D2enc u) B1enc = mul8 D1enc (candEnc D1enc D2enc u) →
    mul8 (candEnc D1enc D2enc u) B2enc = mul8 D2enc (candEnc D1enc D2enc u) →
    candEnc D1enc D2enc u = zero8 :=
  Certificates.certificate2321.2.2.1

theorem enc8_facts : ∀ v : Fin 8 → ZMod 2, vec8 (enc8 v) = v ∧ enc8 v < 256 :=
  Certificates.certificate2321.2.2.2.1

theorem basisP_mul_inv : basisP * basisPInv = 1 := by
  have h1 := congrArg mat8 enc_basisP
  rw [mat8_mul, mat8_colMat8, mat8_B1enc, mat8_B2enc, ← e0_eq, mat8_id8] at h1
  exact h1

theorem eq_colMat_of_intertwine {T C₁ C₂ : Matrix (Fin 8) (Fin 8) (ZMod 2)}
    (h₁ : T * B1 = C₁ * T) (h₂ : T * B2 = C₂ * T) :
    T = colMat C₁ C₂ (T.mulVec e0) * basisPInv := by
  have hP : T * basisP = colMat C₁ C₂ (T.mulVec e0) := by
    ext i k
    rw [Matrix.mul_apply]
    have h := mul_posWord_of_intertwine h₁ h₂ (basisWords k)
    have h' : ((T * posWord B1 B2 (basisWords k)).mulVec e0) i =
        ((posWord C₁ C₂ (basisWords k) * T).mulVec e0) i := by rw [h]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at h'
    change ∑ j, T i j * (posWord B1 B2 (basisWords k)).mulVec e0 j =
      (posWord C₁ C₂ (basisWords k)).mulVec (T.mulVec e0) i
    rw [← h']
    rfl
  calc T = T * basisP * basisPInv := by rw [Matrix.mul_assoc, basisP_mul_inv, Matrix.mul_one]
    _ = _ := by rw [hP]

theorem encoded_intertwiner {T : Matrix (Fin 8) (Fin 8) (ZMod 2)} {C₁ C₂ : List ℕ}
    (hC₁ : ∀ x ∈ C₁, x < 256) (hC₂ : ∀ x ∈ C₂, x < 256)
    (h₁ : T * B1 = mat8 C₁ * T) (h₂ : T * B2 = mat8 C₂ * T) :
    T = mat8 (candEnc C₁ C₂ (enc8 (T.mulVec e0))) ∧
      mul8 (candEnc C₁ C₂ (enc8 (T.mulVec e0))) B1enc =
        mul8 C₁ (candEnc C₁ C₂ (enc8 (T.mulVec e0))) ∧
      mul8 (candEnc C₁ C₂ (enc8 (T.mulVec e0))) B2enc =
        mul8 C₂ (candEnc C₁ C₂ (enc8 (T.mulVec e0))) := by
  have hT : T = mat8 (candEnc C₁ C₂ (enc8 (T.mulVec e0))) := by
    rw [candEnc, mat8_mul, mat8_colMat8, (enc8_facts _).1]
    exact eq_colMat_of_intertwine h₁ h₂
  have hcol : ∀ x ∈ colMat8 C₁ C₂ (enc8 (T.mulVec e0)), x < 256 := by
    intro x hx
    simp only [colMat8, List.mem_map] at hx
    obtain ⟨k, -, rfl⟩ := hx
    apply app8_lt
    have key : ∀ w : List ℕ, ∀ y ∈ posWord8 C₁ C₂ w, y < 256 := by
      intro w
      induction w with
      | nil => intro y hy; simp [posWord8, id8] at hy; omega
      | cons l w ih =>
        intro y hy
        rw [posWord8, List.foldr_cons, ← posWord8] at hy
        refine (norm8_mul8 _ _ ?_).2 y hy
        split_ifs
        · exact hC₁
        · exact hC₂
    exact key _
  have hTlt : ∀ x ∈ candEnc C₁ C₂ (enc8 (T.mulVec e0)), x < 256 := (norm8_mul8 _ _ hcol).2
  refine ⟨hT, ?_, ?_⟩
  · apply mat8_injective (norm8_mul8 _ _ hTlt) (norm8_mul8 _ _ hC₁)
    rw [mat8_mul, mat8_mul, ← hT, mat8_B1enc, h₁]
  · apply mat8_injective (norm8_mul8 _ _ hTlt) (norm8_mul8 _ _ hC₂)
    rw [mat8_mul, mat8_mul, ← hT, mat8_B2enc, h₂]

theorem commutant_B {T : Matrix (Fin 8) (Fin 8) (ZMod 2)} :
    T * B1 = B1 * T ∧ T * B2 = B2 * T ↔ T = 0 ∨ T = 1 := by
  constructor
  · rintro ⟨h₁, h₂⟩
    have hB1 : ∀ x ∈ B1enc, x < 256 := by decide
    have hB2 : ∀ x ∈ B2enc, x < 256 := by decide
    obtain ⟨hT, e1, e2⟩ := encoded_intertwiner (T := T) hB1 hB2 (by rw [mat8_B1enc]; exact h₁)
      (by rw [mat8_B2enc]; exact h₂)
    rcases enc_commutant _ (enc8_facts _).2 e1 e2 with hu | hu
    · left; rw [hT, hu, mat8_zero8]
    · right; rw [hT, hu, mat8_id8]
  · rintro (rfl | rfl) <;> simp

theorem intertwiner_D {T : Matrix (Fin 8) (Fin 8) (ZMod 2)} :
    T * B1 = oddD1 * T ∧ T * B2 = oddD2 * T ↔ T = 0 := by
  constructor
  · rintro ⟨h₁, h₂⟩
    have hD1 : ∀ x ∈ D1enc, x < 256 := Certificates.certificate2321.2.2.2.2.1
    have hD2 : ∀ x ∈ D2enc, x < 256 := Certificates.certificate2321.2.2.2.2.2
    obtain ⟨hT, e1, e2⟩ := encoded_intertwiner (T := T) hD1 hD2 (by rw [mat8_D1enc]; exact h₁)
      (by rw [mat8_D2enc]; exact h₂)
    rw [hT, enc_intertwiner _ (enc8_facts _).2 e1 e2, mat8_zero8]
  · rintro rfl
    simp

end CFSG.Sporadic.ThSchreier
