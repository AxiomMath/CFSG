module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Model

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

namespace OmegaModel

variable {W : Type} [CommGroup W] (S : OmegaModel W)

@[expose] def line (e : W) : Subgroup W where
  carrier := {w | ∃ c : S.K, w = S.smul c e}
  mul_mem' := by
    rintro _ _ ⟨c, rfl⟩ ⟨c', rfl⟩
    exact ⟨c + c', (S.smul_add_eq c c' e).symm⟩
  one_mem' := ⟨0, (S.smul_zero_eq e).symm⟩
  inv_mem' := by
    rintro _ ⟨c, rfl⟩
    refine ⟨-c, S.vec_injective ?_⟩
    rw [S.vec_inv, S.vec_smul, S.vec_smul, neg_smul]

theorem card_line {e : W} (he : e ≠ 1) : Nat.card (S.line e) = Nat.card S.K := by
  obtain ⟨i, hi⟩ : ∃ i, S.vec e i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact he (S.vec_injective (by rw [S.vec_one]; funext j; exact hcon j))
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun c => (⟨S.smul c e, c, rfl⟩ : S.line e))
    ⟨fun c c' h => ?_, ?_⟩)
  · have h1 : S.smul c e = S.smul c' e := congrArg Subtype.val h
    have h2 := congrFun (congrArg S.vec h1) i
    rw [S.vec_smul, S.vec_smul] at h2
    exact mul_right_cancel₀ hi h2
  · rintro ⟨_, c, rfl⟩
    exact ⟨c, rfl⟩

theorem Q_ne_zero_of_mem_line {e : W} (hQ : S.Q e ≠ 0) {w : W} (hw : w ∈ S.line e) (hw1 : w ≠ 1) :
    S.Q w ≠ 0 := by
  obtain ⟨c, rfl⟩ := hw
  have hc : c ≠ 0 := by
    rintro rfl
    exact hw1 (S.smul_zero_eq e)
  rw [S.Q_smul]
  exact mul_ne_zero (pow_ne_zero 2 hc) hQ

end OmegaModel

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
