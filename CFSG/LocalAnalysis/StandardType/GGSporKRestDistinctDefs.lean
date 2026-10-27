module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestPermCheckKey

public section

namespace CFSG.StandardType.SporadicShape.PermCover

open Equiv

@[expose] def fixCnt {n : ℕ} (σ : Perm (Fin n)) : ℕ := (Finset.univ.filter fun i => σ i = i).card

theorem fixCnt_of_isConj {n : ℕ} {x y : Perm (Fin n)} (h : IsConj x y) : fixCnt x = fixCnt y := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  have hcu : c * x * c⁻¹ = y := hc
  refine Finset.card_bij (fun i _ => c i) ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    rw [← hcu]
    simp [Equiv.Perm.mul_apply, hi]
  · intro i _ j _ hij
    exact c.injective hij
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    refine ⟨c⁻¹ j, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have := congrArg (fun z => c⁻¹ z) (show y j = j from hj)
    rw [← hcu] at this
    simp [Equiv.Perm.mul_apply] at this
    exact this

@[expose] def fixCntL {n : ℕ} (σ : Perm (Fin n)) : ℕ :=
  ((List.range n).filter fun i => if h : i < n then decide (σ ⟨i, h⟩ = ⟨i, h⟩) else false).length

theorem fixCntL_eq {n : ℕ} (σ : Perm (Fin n)) : fixCntL σ = fixCnt σ := by
  unfold fixCntL fixCnt
  have hnodup : ((List.range n).filter fun i =>
      if h : i < n then decide (σ ⟨i, h⟩ = ⟨i, h⟩) else false).Nodup :=
    List.Nodup.filter _ List.nodup_range
  rw [← List.toFinset_card_of_nodup hnodup]
  rw [List.toFinset_filter, List.toFinset_range]
  refine Finset.card_bij (fun i hi => (⟨i, Finset.mem_range.mp (Finset.mem_filter.mp hi).1⟩ : Fin n))
    ?_ ?_ ?_
  · intro i hi
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have hpred := (Finset.mem_filter.mp hi).2
    have hin : i < n := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    rw [dif_pos hin] at hpred
    exact of_decide_eq_true hpred
  · intro i hi i' hi' h
    exact congrArg Fin.val h
  · intro j hj
    refine ⟨j.val, ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr j.isLt, ?_⟩
      have hj' := (Finset.mem_filter.mp hj).2
      rw [dif_pos j.isLt]
      exact decide_eq_true hj'
    · exact Fin.ext rfl

@[expose] def classInvOkK {n : ℕ} (B : List ℕ) (p : ℕ) (a b : Perm (Fin n)) (d : Data) : Bool :=
  let a := mat a
  let b := mat b
  d.classes.all (fun c => let r := repMat a b c; keyEq B (r ^ p) 1 && !keyEq B r 1) &&
    decide ((d.classes.map fun c => fixCntL (repMat a b c)).Nodup)

end CFSG.StandardType.SporadicShape.PermCover
