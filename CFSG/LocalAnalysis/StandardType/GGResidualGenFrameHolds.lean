module

public import CFSG.LocalAnalysis.StandardType.GGResidualGenFrame

public section

namespace CFSG.StandardType

private def coxLabel {m : ℕ} (A : CoxeterMatrix (Fin m)) (i j : Fin m) : ℕ := A.M i j

private def TwoLeavesCommonNbr {m : ℕ} (A : CoxeterMatrix (Fin m)) : Prop :=
  ∃ a b c : Fin m, a ≠ b ∧ coxLabel A a c = 3 ∧ coxLabel A b c = 3 ∧
    (∀ d, coxLabel A a d = 3 → d = c) ∧ ∀ d, coxLabel A b d = 3 → d = c

private instance {m : ℕ} (A : CoxeterMatrix (Fin m)) : Decidable (TwoLeavesCommonNbr A) := by
  unfold TwoLeavesCommonNbr; infer_instance

private theorem TwoLeavesCommonNbr.of_equiv {m k : ℕ} {A : CoxeterMatrix (Fin m)}
    {A' : CoxeterMatrix (Fin k)} (σ : Fin m ≃ Fin k)
    (hσ : ∀ a b, coxLabel A' (σ a) (σ b) = coxLabel A a b) (h : TwoLeavesCommonNbr A) :
    TwoLeavesCommonNbr A' := by
  obtain ⟨a, b, c, hab, hac, hbc, ha, hb⟩ := h
  refine ⟨σ a, σ b, σ c, σ.injective.ne hab, (hσ a c).trans hac, (hσ b c).trans hbc,
    fun d hd => ?_, fun d hd => ?_⟩
  · rw [← σ.apply_symm_apply d, hσ] at hd
    rw [← ha _ hd, σ.apply_symm_apply]
  · rw [← σ.apply_symm_apply d, hσ] at hd
    rw [← hb _ hd, σ.apply_symm_apply]

theorem GGIsWeylMatrixE.not_weylMatrixD {ι : Type} {M : CoxeterMatrix ι}
    (hE : GGIsWeylMatrixE M) : ¬ GGIsWeylMatrixD M := by
  rintro ⟨n, e, -, rfl⟩
  have key : ∀ {k : ℕ} (E : CoxeterMatrix (Fin k)) (f : Fin k ≃ ι),
      (ggCoxeterMatrixD n).reindex e = E.reindex f →
      TwoLeavesCommonNbr (ggCoxeterMatrixD n) → TwoLeavesCommonNbr E := by
    intro k E f hEq hD
    refine hD.of_equiv (e.trans f.symm) fun a b => ?_
    have h := congrArg (fun N : CoxeterMatrix ι => N.M (e a) (e b)) hEq
    simp only [CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply] at h
    simpa only [coxLabel, Equiv.trans_apply] using h.symm
  rcases hE with ⟨f, hf⟩ | ⟨f, hf⟩ | ⟨f, hf⟩
  · obtain rfl : n = 6 := Fin.equiv_iff_eq.mp ⟨e.trans f.symm⟩
    exact absurd (key _ f hf (by decide +kernel)) (by decide +kernel)
  · obtain rfl : n = 7 := Fin.equiv_iff_eq.mp ⟨e.trans f.symm⟩
    exact absurd (key _ f hf (by decide +kernel)) (by decide +kernel)
  · obtain rfl : n = 8 := Fin.equiv_iff_eq.mp ⟨e.trans f.symm⟩
    exact absurd (key _ f hf (by decide +kernel)) (by decide +kernel)

section Proofs


theorem ggGenResidualFrameInputOf_weylE_holds :
    GGGenResidualFrameInputOf (fun {ι : Type} (M : CoxeterMatrix ι) => GGIsWeylMatrixE M) := by
  intro G _ _ p B Bs x L D J 𝒦 _ _ ι M e _ _ _ _ X hX _ _ hR hDL
  exfalso
  by_cases hD : NSJoin.NSTypeD M
  · rcases hX with hXL | ⟨-, hnD⟩ | ⟨hE, -⟩
    · exact hDL hD hXL
    · exact hnD hD
    · exact GGIsWeylMatrixE.not_weylMatrixD hE hD
  · obtain ⟨-, lab, -, hraw⟩ := hR hD
    obtain ⟨R, _, I, F, -, -, θ, hrow⟩ := largeEvenRawDatum_exists hraw
    exact hrow.1

end Proofs

end CFSG.StandardType

end
