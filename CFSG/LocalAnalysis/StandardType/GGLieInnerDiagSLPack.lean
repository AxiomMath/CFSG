module

public import CFSG.LocalAnalysis.StandardType.GGLieInnerDiagDefs

public section

namespace CFSG.StandardType.SCFourCover

theorem ggLinearOn_of_slConj {G : Type} [Group G] {J : Subgroup G} {t : MulAut G}
    (hJq : CFSG.Open.IsQuasisimple ↥J) {F : Type} [Field F] [Finite F] [CharP F 2]
    (h4 : 4 ≤ Nat.card F) {m : ℕ}
    (φ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* ↥J) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    (A : GL (Fin (m + 1)) F) (hA : ∀ B, t (φ B) = (φ (InnerDiagA.conjSL A B) : G)) :
    GGLinearOn J t := by
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨f, -, hf⟩ := FiniteField.card F 2
  have hfc : Nat.card F = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hf]
  have hf2 : 2 ≤ (f : ℕ) := by
    by_contra hlt
    have hle : 2 ^ (f : ℕ) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hfc] at h4
    exact absurd (h4.trans hle) (by norm_num)
  have hm1 : 1 ≤ m := by
    by_contra hm0
    obtain rfl : m = 0 := by omega
    have hsub : Subsingleton (Matrix.SpecialLinearGroup (Fin (0 + 1)) F) := by
      change Subsingleton (Matrix.SpecialLinearGroup (Fin 1) F)
      refine ⟨fun B C => Subtype.ext (Matrix.ext fun i j => ?_)⟩
      have hB : (B : Matrix (Fin 1) (Fin 1) F).det = 1 := B.2
      have hC : (C : Matrix (Fin 1) (Fin 1) F).det = 1 := C.2
      rw [Matrix.det_unique] at hB hC
      rw [Subsingleton.elim i default, Subsingleton.elim j default, hB, hC]
    haveI : Subsingleton ↥J := ⟨fun a b => by
      obtain ⟨B, rfl⟩ := hφ a
      obtain ⟨C, rfl⟩ := hφ b
      rw [Subsingleton.elim B C]⟩
    haveI : Subsingleton (↥J ⧸ Subgroup.center ↥J) :=
      (QuotientGroup.mk'_surjective (Subgroup.center ↥J)).subsingleton
    haveI := hJq.2
    exact not_nontrivial (↥J ⧸ Subgroup.center ↥J) inferInstance
  exact ⟨F, inferInstance, inferInstance, f, m, hfc, by omega, hm1, fun _ => hf2, φ, hφ, hker,
    A, hA⟩

end CFSG.StandardType.SCFourCover

end
