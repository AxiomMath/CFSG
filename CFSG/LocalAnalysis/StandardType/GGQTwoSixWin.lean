module

public import CFSG.LocalAnalysis.StandardType.GGQTwoSixDefs
import CFSG.ClassicalInvolution.Phan.Blocks

public section

namespace CFSG.StandardType.QTwo.SixPoint

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem qTwoSix_blockEmb_injective {m k i : ℕ} (h : i + k ≤ m) :
    Function.Injective (blockEmb K 2 1 m k i h) :=
  blockEmb_injective h

theorem qTwoSix_map_win_coordBlock {m k i : ℕ} (h : i + k ≤ m) (J : Finset (Fin k)) :
    (coordBlockSU K 2 1 J).map (blockEmb K 2 1 m k i h) =
      coordBlockSU K 2 1 (J.map (qTwoSixWinEmb h)) := by
  classical
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro y ⟨x, hx, rfl⟩
    have hx' := (mem_coordBlockSU_iff (K := K) (p := 2) (f := 1)).mp hx
    apply mem_coordBlockSU_iff.mpr
    intro a b hab
    rw [coe_coe_blockEmb, blockMat_apply]
    by_cases hw : (i ≤ a.val ∧ a.val < i + k) ∧ (i ≤ b.val ∧ b.val < i + k)
    · rw [dif_pos hw]
      let a' : Fin k := ⟨a.val - i, by omega⟩
      let b' : Fin k := ⟨b.val - i, by omega⟩
      have ha : qTwoSixWinEmb h a' = a := by
        apply Fin.ext
        change a.val - i + i = a.val
        omega
      have hb : qTwoSixWinEmb h b' = b := by
        apply Fin.ext
        change b.val - i + i = b.val
        omega
      have hmem : a' ∉ J ∨ b' ∉ J := by
        rcases hab with haJ | hbJ
        · exact Or.inl fun ha' => haJ (Finset.mem_map.mpr ⟨a', ha', ha⟩)
        · exact Or.inr fun hb' => hbJ (Finset.mem_map.mpr ⟨b', hb', hb⟩)
      have heq : a' = b' ↔ a = b := by
        constructor
        · intro he
          exact ha.symm.trans ((congrArg (qTwoSixWinEmb h) he).trans hb)
        · intro he
          apply (qTwoSixWinEmb h).injective
          exact ha.trans (he.trans hb.symm)
      change (((x : Su K 2 1 k) : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) a' b' = _
      rw [hx' a' b' hmem]
      simp only [heq]
    · rw [dif_neg hw]
      exact Matrix.one_apply
  · have hcard : Nat.card ↥(coordBlockSU K 2 1 (J.map (qTwoSixWinEmb h))) =
        Nat.card ↥(coordBlockSU K 2 1 J) := by
      calc
        _ = Nat.card (Su K 2 1 (J.map (qTwoSixWinEmb h)).card) :=
          (Nat.card_congr (Equiv.ofInjective (blockSUOn K 2 1 _)
            (blockSUOn_injective _))).symm
        _ = Nat.card (Su K 2 1 J.card) := by rw [Finset.card_map]
        _ = _ := Nat.card_congr (Equiv.ofInjective (blockSUOn K 2 1 J)
          (blockSUOn_injective J))
    rw [Subgroup.card_map_of_injective (qTwoSix_blockEmb_injective h)]
    exact hcard.le

end CFSG.StandardType.QTwo.SixPoint

end
