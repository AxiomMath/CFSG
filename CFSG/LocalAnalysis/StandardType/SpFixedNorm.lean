module

public import CFSG.Open.StatedAPI

public section

namespace CFSG.StandardType

namespace SpFixed

open Matrix
open CFSG.Open (StatedSp)

@[expose] def gram (R : Type) [Ring R] (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R :=
  Matrix.fromBlocks 0 1 (-1) 0

@[expose] def matHom (F : Type) [Field F] (n : ℕ) :
    StatedSp n F →* Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F :=
  (Units.coeHom _).comp (StatedSp n F).subtype

variable {F : Type} [Field F] {n : ℕ}

theorem matHom_apply (a : StatedSp n F) :
    matHom F n a = ((a : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) :=
  rfl

theorem matHom_injective : Function.Injective (matHom F n) := fun _ _ h =>
  Subtype.ext (Units.ext h)

theorem matHom_transpose_mul_gram_mul (a : StatedSp n F) :
    (matHom F n a)ᵀ * gram F n * matHom F n a = gram F n := by
  have h := (CFSG.Open.StatedAPI.mem_statedSp_iff (n := n) (K := F)
    (A := (a : GL (Fin n ⊕ Fin n) F))).1 a.2
  simpa [gram, matHom_apply] using h

@[expose] noncomputable def fixedNorm (D : Subgroup (StatedSp n F)) [Fintype D] :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F :=
  ∑ a : D, matHom F n (a : StatedSp n F)

section Basic

variable (D : Subgroup (StatedSp n F)) [Fintype D]

theorem matHom_mul_fixedNorm {a : StatedSp n F} (ha : a ∈ D) :
    matHom F n a * fixedNorm D = fixedNorm D := by
  unfold fixedNorm
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft (⟨a, ha⟩ : D)) _ _ ?_
  intro b
  simp [map_mul]

theorem fixedNorm_mul_matHom {a : StatedSp n F} (ha : a ∈ D) :
    fixedNorm D * matHom F n a = fixedNorm D := by
  unfold fixedNorm
  rw [Finset.sum_mul]
  refine Fintype.sum_equiv (Equiv.mulRight (⟨a, ha⟩ : D)) _ _ ?_
  intro b
  simp [map_mul]

theorem fixedNorm_mul_fixedNorm [CharP F 2] (hodd : Odd (Fintype.card D)) :
    fixedNorm D * fixedNorm D = fixedNorm D := by
  calc fixedNorm D * fixedNorm D
      = ∑ b : D, matHom F n (b : StatedSp n F) * fixedNorm D := by
        rw [fixedNorm, Finset.sum_mul]
    _ = ∑ _b : D, fixedNorm D :=
        Finset.sum_congr rfl (fun b _ => matHom_mul_fixedNorm D b.2)
    _ = fixedNorm D := by
        rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul F,
          natCast_eq_one_of_odd_of_two_eq_zero hodd (CharP.cast_eq_zero F 2), one_smul]

theorem fixedNorm_transpose_mul_gram :
    (fixedNorm D)ᵀ * gram F n = gram F n * fixedNorm D := by
  have hterm : ∀ a : D,
      (matHom F n (a : StatedSp n F))ᵀ * gram F n =
        gram F n * matHom F n ((a⁻¹ : D) : StatedSp n F) := by
    intro a
    have h1 := matHom_transpose_mul_gram_mul (a : StatedSp n F)
    have hcancel : matHom F n (a : StatedSp n F) *
        matHom F n ((a : StatedSp n F)⁻¹) = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    have h2 : (matHom F n (a : StatedSp n F))ᵀ * gram F n =
        gram F n * matHom F n ((a : StatedSp n F)⁻¹) := by
      calc (matHom F n (a : StatedSp n F))ᵀ * gram F n
          = (matHom F n (a : StatedSp n F))ᵀ * gram F n * 1 := (mul_one _).symm
        _ = (matHom F n (a : StatedSp n F))ᵀ * gram F n *
              (matHom F n (a : StatedSp n F) *
                matHom F n ((a : StatedSp n F)⁻¹)) := by rw [hcancel]
        _ = (matHom F n (a : StatedSp n F))ᵀ * gram F n *
              matHom F n (a : StatedSp n F) *
                matHom F n ((a : StatedSp n F)⁻¹) := (mul_assoc _ _ _).symm
        _ = gram F n * matHom F n ((a : StatedSp n F)⁻¹) := by rw [h1]
    rwa [← Subgroup.coe_inv] at h2
  rw [fixedNorm, Matrix.transpose_sum, Finset.sum_mul, Finset.mul_sum]
  trans ∑ a : D, gram F n * matHom F n ((a⁻¹ : D) : StatedSp n F)
  · exact Finset.sum_congr rfl (fun a _ => hterm a)
  · exact Equiv.sum_comp (Equiv.inv D)
      (fun b : D => gram F n * matHom F n (b : StatedSp n F))

theorem matHom_mul_fixedNorm_comm {g : StatedSp n F}
    (hg : g ∈ Subgroup.centralizer (D : Set (StatedSp n F))) :
    matHom F n g * fixedNorm D = fixedNorm D * matHom F n g := by
  have hcomm : ∀ a : D, (a : StatedSp n F) * g = g * (a : StatedSp n F) :=
    fun a => (Subgroup.mem_centralizer_iff.1 hg) (a : StatedSp n F) a.2
  rw [fixedNorm, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← map_mul, ← hcomm a, map_mul]

end Basic

end SpFixed

end CFSG.StandardType
