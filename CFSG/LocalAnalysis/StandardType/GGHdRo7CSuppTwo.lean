module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CReflSteps

public section

open scoped BigOperators

namespace CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma hdRo7CSuppAux_two_ne_zero : (2 : ZMod 3) ≠ 0 := by decide

private lemma hdRo7CSuppAux_neg_one_ne_zero : (-1 : ZMod 3) ≠ 0 := by decide

private lemma hdRo7CSuppAux_case1 : (-1 : ZMod 3) * 1 - 1 ≠ 0 := by decide

theorem c2_suppTwo_holds : C2SuppTwoLeaf := by
  unfold C2SuppTwoLeaf
  intro p hp hp3 n hn V instACG instMod b s hsp hrefl v hv hsv
  subst hp3
  haveI : Module.Finite (ZMod 3) V := Module.Finite.of_basis b
  unfold C2SP at hsp
  obtain ⟨σ, c, hσ0, hc0, hc, hsdef⟩ := hsp
  unfold GGLinRefl at hrefl
  obtain ⟨hsq, hrank⟩ := hrefl
  let w : Fin (n + 1) → V := fun i => s (b i) - b i
  let S : Finset (Fin (n + 1)) := Finset.univ.filter (fun i => b.coord i v ≠ 0)
  change b.coord 0 v = 0 ∧ S.card ≤ 2
  have hcoord_b : ∀ (j i : Fin (n + 1)), b.coord j (b i) = (if j = i then 1 else 0 : ZMod 3) := by
    intro j i
    rw [Module.Basis.coord_apply, Module.Basis.repr_self]
    simp [Finsupp.single_apply, eq_comm]
  have hcoord : ∀ j, b.coord j (s v) = b.coord (σ.symm j) v * c (σ.symm j) := by
    intro j
    have hv_exp : v = ∑ i, b.coord i v • b i := by
      conv_lhs => rw [← b.sum_repr v]
      apply Finset.sum_congr rfl
      intro i _
      rw [Module.Basis.coord_apply]
    have hsv_exp : s v = ∑ i, (b.coord i v * c i) • b (σ i) := by
      conv_lhs => rw [hv_exp]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul, hsdef i, smul_smul]
    have hsum_eq : (∑ i, b.coord j ((b.coord i v * c i) • b (σ i)))
        = b.coord (σ.symm j) v * c (σ.symm j) := by
      rw [Finset.sum_eq_single (σ.symm j)]
      · rw [map_smul, hcoord_b j (σ (σ.symm j)), Equiv.apply_symm_apply, if_pos rfl,
          smul_eq_mul, mul_one]
      · intro i _ hi
        have hji : j ≠ σ i := by
          rintro rfl
          exact hi (by simp)
        rw [map_smul, hcoord_b j (σ i), if_neg hji, smul_zero]
      · intro hmem
        exact absurd (Finset.mem_univ _) hmem
    have h := congrArg (b.coord j) hsv_exp
    rw [map_sum, hsum_eq] at h
    exact h
  have hcoord0 : b.coord 0 v = 0 := by
    have h0 := hcoord 0
    have hσinv0 : σ.symm 0 = 0 := by
      have h := Equiv.symm_apply_apply σ 0
      rwa [hσ0] at h
    rw [hσinv0, hc0, mul_one] at h0
    have hs0 : b.coord 0 (s v) = - b.coord 0 v := by rw [hsv, map_neg]
    rw [hs0] at h0
    have hxx : b.coord 0 v + b.coord 0 v = 0 := (eq_neg_iff_add_eq_zero).mp h0.symm
    have h2 : (2 : ZMod 3) • b.coord 0 v = 0 := by rw [two_smul]; exact hxx
    have h2ne : (2 : ZMod 3) ≠ 0 := hdRo7CSuppAux_two_ne_zero
    exact (mul_eq_zero.mp (by simpa [smul_eq_mul] using h2)).resolve_left h2ne
  have hwcoord : ∀ i j, b.coord j (w i)
      = c i * (if j = σ i then 1 else 0 : ZMod 3) - (if j = i then 1 else 0 : ZMod 3) := by
    intro i j
    simp only [w]
    rw [map_sub, hsdef i, map_smul, hcoord_b j (σ i), hcoord_b j i, smul_eq_mul]
  have hwcoord_self : ∀ i ∈ S, b.coord i (w i) ≠ 0 := by
    intro i hi
    have hvi : b.coord i v ≠ 0 := by simpa [S] using hi
    rw [hwcoord i i]
    by_cases hσi : σ i = i
    · have hci : c i = -1 := by
        have hc_i := hcoord i
        have hσinv_i : σ.symm i = i := by
          have h := Equiv.symm_apply_apply σ i
          rwa [hσi] at h
        rw [hσinv_i] at hc_i
        have hs_i : b.coord i (s v) = - b.coord i v := by rw [hsv, map_neg]
        rw [hs_i] at hc_i
        have hmul : b.coord i v * (c i + 1) = 0 := by
          rw [mul_add, mul_one, ← hc_i]
          abel
        rcases mul_eq_zero.mp hmul with h | h
        · exact absurd h hvi
        · exact (eq_neg_iff_add_eq_zero).mpr h
      rw [if_pos hσi.symm, if_pos rfl, hci]
      exact hdRo7CSuppAux_case1
    · rw [if_neg (fun h => hσi h.symm), if_pos rfl]
      simp only [mul_zero, zero_sub]
      exact hdRo7CSuppAux_neg_one_ne_zero
  have hwmem : ∀ i, w i ∈ ggLinMove s := by
    intro i
    refine LinearMap.mem_range.mpr ⟨b i, ?_⟩
    simp only [w, ggLinMove, LinearMap.sub_apply, LinearMap.id_apply]
    rfl
  by_cases hcard : S.card ≤ 2
  · exact ⟨hcoord0, hcard⟩
  · rw [not_le] at hcard
    have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨i₁, hi₁⟩ := hSne
    have hw1_ne : w i₁ ≠ 0 := by
      intro h0
      exact hwcoord_self i₁ hi₁ (by rw [h0]; simp)
    have hspan_le : Submodule.span (ZMod 3) {w i₁} ≤ ggLinMove s := by
      rw [Submodule.span_singleton_le_iff_mem]
      exact hwmem i₁
    have hline : ggLinMove s = Submodule.span (ZMod 3) {w i₁} := by
      refine (Submodule.eq_of_le_of_finrank_eq hspan_le ?_).symm
      rw [finrank_span_singleton hw1_ne, hrank]
    have hle : S ⊆ ({i₁, σ i₁} : Finset (Fin (n + 1))) := by
      intro i hi
      by_contra hnot
      have hne1 : i ≠ i₁ := by intro h; exact hnot (by simp [h])
      have hne2 : i ≠ σ i₁ := by intro h; exact hnot (by simp [h])
      have hprop : w i ∈ Submodule.span (ZMod 3) {w i₁} := by
        rw [← hline]; exact hwmem i
      obtain ⟨lam, hlam⟩ := Submodule.mem_span_singleton.mp hprop
      have hzi : b.coord i (w i₁) = 0 := by
        rw [hwcoord i₁ i, if_neg hne2, if_neg hne1]
        simp
      have hzero : b.coord i (w i) = 0 := by
        rw [← hlam, map_smul, hzi, smul_zero]
      exact hwcoord_self i hi hzero
    have hcard_le : S.card ≤ Finset.card ({i₁, σ i₁} : Finset (Fin (n + 1))) := Finset.card_le_card hle
    have h2 : Finset.card ({i₁, σ i₁} : Finset (Fin (n + 1))) ≤ 2 := by
      have h := Finset.card_insert_le i₁ ({σ i₁} : Finset (Fin (n + 1)))
      simpa using h
    exact ⟨hcoord0, hcard_le.trans h2⟩

end CFSG.StandardType.HdRo7C

end
