module

public import CFSG.Quasithin.Background.SmithB45Sp4Low

public section

namespace CFSG.Quasithin.B45Sp4

open CFSG.Quasithin.B42Sp4 CFSG.Quasithin.H.Sp4 CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour (tau coe_tau radical card_radical)
open scoped Matrix

variable {F : Type} [Field F] [CharP F 2]

@[expose] def twm (a : ℕ) (g : StatedSp 2 F) (Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  tw a (spM g) Y - Y

omit [CharP F 2] in
theorem twm_tau_fromBlocks (a : ℕ) {C : Matrix (Fin 2) (Fin 2) F} (hC : Cᵀ = C)
    (A B C' D : Matrix (Fin 2) (Fin 2) F) :
    twm a (tau hC) (Matrix.fromBlocks A B C' D) =
      Matrix.fromBlocks (C * C' + (B + C * D) * frobPow a C) (C * D) (D * frobPow a C) 0 := by
  rw [twm, tw_tau_fromBlocks, sub_eq_iff_eq_add, Matrix.fromBlocks_add]
  congr 1 <;> abel

omit [CharP F 2] in
theorem radical_cubic (a : ℕ) {x y z : StatedSp 2 F} (hx : x ∈ radical F) (hy : y ∈ radical F)
    (hz : z ∈ radical F) (Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) :
    twm a z (twm a y (twm a x Y)) = 0 := by
  obtain ⟨C₁, hC₁, rfl⟩ := hx
  obtain ⟨C₂, hC₂, rfl⟩ := hy
  obtain ⟨C₃, hC₃, rfl⟩ := hz
  rw [← Matrix.fromBlocks_toBlocks Y, twm_tau_fromBlocks, twm_tau_fromBlocks, twm_tau_fromBlocks]
  simp

omit [CharP F 2] in
theorem twm_radical_fromBlocks (a : ℕ) {x : StatedSp 2 F} (hx : x ∈ radical F)
    (A : Matrix (Fin 2) (Fin 2) F) : twm a x (Matrix.fromBlocks A 0 0 0) = 0 := by
  obtain ⟨C, hC, rfl⟩ := hx
  rw [twm_tau_fromBlocks]
  simp

variable [Finite F]

theorem card_hermFix_radical {a : ℕ} (ha : 1 ≤ a) (hF : Nat.card F = 2 ^ (2 * a)) :
    Nat.card F ^ 2 ≤ Nat.card ↥(hermFix a _ F (spM '' (radical F : Set (StatedSp 2 F)))) := by
  classical
  have h2 : Nat.card ↥(hermA a (Fin 2) F) = Nat.card F ^ 2 := by
    have h := card_hermA_sq (ι := Fin 2) ha hF
    simp only [Fintype.card_fin] at h
    refine Nat.pow_left_injective (n := 2) (by norm_num) ?_
    simp only
    rw [h, ← pow_mul]
  rw [← h2]
  have hmem : ∀ A : ↥(hermA a (Fin 2) F),
      Matrix.fromBlocks (A : Matrix (Fin 2) (Fin 2) F) 0 0 0 ∈
        hermFix a _ F (spM '' (radical F : Set (StatedSp 2 F))) := by
    intro A
    refine mem_hermFix.mpr ⟨?_, ?_⟩
    · rw [mem_hermA, frobPow_fromBlocks, frobPow_zero', Matrix.fromBlocks_transpose,
        Matrix.transpose_zero, (mem_hermA.mp A.2)]
    · rintro _ ⟨x, hx, rfl⟩
      have := twm_radical_fromBlocks a hx (A : Matrix (Fin 2) (Fin 2) F)
      rw [twm] at this
      exact sub_eq_zero.mp this
  refine Nat.card_le_card_of_injective (fun A => ⟨_, hmem A⟩) ?_
  intro A B h
  have h1 := congrArg (fun Y : ↥(hermFix a _ F (spM '' (radical F : Set (StatedSp 2 F)))) =>
    (Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₁₁) h
  simp only [Matrix.toBlocks_fromBlocks₁₁] at h1
  exact Subtype.ext h1

end CFSG.Quasithin.B45Sp4
