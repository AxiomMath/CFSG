module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyLinearBinary

public section

namespace CFSG.Quasithin.H13.VolI

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem card_mulAut_projectiveSL_two_le {n : ℕ} (hn : 3 ≤ n) :
    Nat.card (MulAut (projectiveSL n (ZMod 2))) ≤ 2 * Nat.card (GL (Fin n) (ZMod 2)) := by
  have hsurj : Function.Surjective (fun p : GL (Fin n) (ZMod 2) × Fin 2 =>
      conjAut n (ZMod 2) p.1 * fieldAut n (ZMod 2) (RingEquiv.refl _) *
        dualAut n (ZMod 2) ^ (p.2 : ℕ)) := by
    intro α
    obtain ⟨A, σ, ε, hε, hα⟩ := (automorphism_generation (K := ZMod 2) hn).2 α
    have hσ : σ = RingEquiv.refl _ := RingEquiv.toRingHom_injective (Subsingleton.elim _ _)
    refine ⟨(A, ⟨ε, by omega⟩), ?_⟩
    rw [hα, hσ]
  calc Nat.card (MulAut (projectiveSL n (ZMod 2))) ≤
        Nat.card (GL (Fin n) (ZMod 2) × Fin 2) := Nat.card_le_card_of_surjective _ hsurj
    _ = 2 * Nat.card (GL (Fin n) (ZMod 2)) := by rw [Nat.card_prod, Nat.card_fin, mul_comm]

theorem card_GL_zmod_two_eq (n : ℕ) [NeZero n] :
    Nat.card (GL (Fin n) (ZMod 2)) = Nat.card (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := by
  have h := Matrix.card_SL_mul_card_units (n := Fin n) (R := ZMod 2)
  have hu : Nat.card (ZMod 2)ˣ = 1 := by
    rw [Nat.card_eq_fintype_card]
    rfl
  rw [hu, mul_one] at h
  exact h.symm

theorem autSLFiveTwo_holds : Nat.card (MulAut (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))) ≤
    2 * Nat.card (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) := by
  rw [Nat.card_congr (MulAut.congr (QuasithinUnique.Setup.Family.projEquiv 5)).toEquiv,
    ← card_GL_zmod_two_eq]
  exact card_mulAut_projectiveSL_two_le (by norm_num)

end CFSG.Quasithin.H13.VolI
