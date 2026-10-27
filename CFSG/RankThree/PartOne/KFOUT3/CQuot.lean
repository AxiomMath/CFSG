module

public import CFSG.RankThree.PartOne.KF.CentralQuot
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.RankThree.PartOne.KFOUT3

open CFSG.RankThree.PartOne.KFU

theorem isCentralPQuot_center' {L P : Type} [Group L] [Group P] {p : ℕ}
    (e : L ⧸ Subgroup.center L ≃* P) (hcop : Nat.Coprime p (Nat.card (Subgroup.center L))) :
    IsCentralPQuot p (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))) := by
  have hker : (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))).ker =
      Subgroup.center L := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (x : L ⧸ Subgroup.center L) = 1 ↔ x ∈ Subgroup.center L
    rw [map_eq_one_iff _ e.injective, QuotientGroup.eq_one_iff]
  refine ⟨e.surjective.comp (QuotientGroup.mk'_surjective _), hker.le, ?_⟩
  rw [hker]
  exact hcop

theorem isCentralPQuot_id {M : Type*} [Group M] (p : ℕ) : IsCentralPQuot p (MonoidHom.id M) := by
  have hker : (MonoidHom.id M).ker = ⊥ := MonoidHom.ker_id
  refine ⟨Function.surjective_id, ?_, ?_⟩
  · rw [hker]
    exact bot_le
  · rw [hker, Subgroup.card_bot]
    exact Nat.coprime_one_right p

end CFSG.RankThree.PartOne.KFOUT3
