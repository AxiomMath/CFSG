module

public import CFSG.LocalAnalysis.StandardType.GGSpFrameBasis

public section

namespace CFSG.StandardType.SpFrame

open Module

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

private theorem isRefl_injective {g : Module.End k V} (hg : IsRefl g) : Function.Injective g := by
  have h : Function.Involutive g := fun x => by
    rw [← Module.End.mul_apply, hg.1, Module.End.one_apply]
  exact h.injective

theorem exists_frame_of_family [FiniteDimensional k V] (h2 : (2 : k) ≠ 0) {m : ℕ}
    (hdim : finrank k V = m + 1) (T ε : Fin (m + 1) → Module.End k V)
    (hT : ∀ (i : Fin (m + 1)), i.val + 1 < m + 1 → IsRefl (T i))
    (hεlast : IsRefl (ε (Fin.last m)))
    (hcomm : ∀ i j, ε i * ε j = ε j * ε i)
    (hne : ∀ i j, i ≠ j → ε i ≠ ε j)
    (hconj : ∀ (i : Fin (m + 1)) (hi : i.val + 1 < m + 1) (j : Fin (m + 1)),
      T i * ε j * T i = ε (Equiv.swap i ⟨i.val + 1, hi⟩ j))
    (hTne : ∀ (i : Fin (m + 1)), i.val + 1 < m + 1 → ∀ j, T i ≠ ε j) :
    ∃ f : Basis (Fin (m + 1)) k V,
      (∀ (i : Fin (m + 1)) (hi : i.val + 1 < m + 1) (j : Fin (m + 1)),
        T i (f j) = f (Equiv.swap i ⟨i.val + 1, hi⟩ j)) ∧
      (∀ j : Fin (m + 1), ε (Fin.last m) (f j) = if j = Fin.last m then -f j else f j) := by
  have hε : ∀ j, IsRefl (ε j) := fun j => isRefl_of_sign_family T ε hT hεlast hconj j
  obtain ⟨b, hbne, hbneg⟩ := IsRefl.exists_neg hεlast
  obtain ⟨v, hvlast, hv⟩ := exists_downward_family T b
  have hA : ∀ j : Fin (m + 1), v j ≠ 0 ∧ ε j (v j) = -v j := by
    intro j
    refine Fin.reverseInduction (motive := fun j => v j ≠ 0 ∧ ε j (v j) = -v j) ?_ ?_ j
    · exact ⟨by rw [hvlast]; exact hbne, by rw [hvlast]; exact hbneg⟩
    · intro i ih
      have hi : (Fin.castSucc i : Fin (m + 1)).val + 1 < m + 1 := by
        simp only [Fin.val_castSucc]; exact Nat.succ_lt_succ i.isLt
      have hj'eq : i.succ = (⟨(Fin.castSucc i : Fin (m + 1)).val + 1, hi⟩ : Fin (m + 1)) :=
        Fin.ext rfl
      have ih' : v (⟨(Fin.castSucc i : Fin (m + 1)).val + 1, hi⟩ : Fin (m + 1)) ≠ 0 ∧
          ε (⟨(Fin.castSucc i : Fin (m + 1)).val + 1, hi⟩ : Fin (m + 1))
            (v (⟨(Fin.castSucc i : Fin (m + 1)).val + 1, hi⟩ : Fin (m + 1))) =
            -v (⟨(Fin.castSucc i : Fin (m + 1)).val + 1, hi⟩ : Fin (m + 1)) := by
        rw [hj'eq] at ih; exact ih
      have hveq : v (Fin.castSucc i) =
          T (Fin.castSucc i) (v ⟨(Fin.castSucc i : Fin (m + 1)).val + 1, hi⟩) := by
        simpa using hv (Fin.castSucc i) hi
      have hconj_i : T (Fin.castSucc i) * ε (⟨(Fin.castSucc i : Fin (m + 1)).val + 1, hi⟩)
          * T (Fin.castSucc i) = ε (Fin.castSucc i) := by
        simpa using hconj (Fin.castSucc i) hi ⟨(Fin.castSucc i : Fin (m + 1)).val + 1, hi⟩
      have hsq : T (Fin.castSucc i) * T (Fin.castSucc i) = 1 := (hT (Fin.castSucc i) hi).1
      have hTε : T (Fin.castSucc i) * ε (⟨(Fin.castSucc i : Fin (m + 1)).val + 1, hi⟩) =
          ε (Fin.castSucc i) * T (Fin.castSucc i) := by
        rw [← hconj_i, mul_assoc, hsq, mul_one]
      refine ⟨?_, ?_⟩
      · rw [hveq]
        intro h
        exact ih'.1 (isRefl_injective (hT (Fin.castSucc i) hi) (h.trans (map_zero _).symm))
      · calc ε (Fin.castSucc i) (v (Fin.castSucc i))
            = ε (Fin.castSucc i) (T (Fin.castSucc i)
                (v ⟨(Fin.castSucc i : Fin (m + 1)).val + 1, hi⟩)) := by rw [hveq]
          _ = (ε (Fin.castSucc i) * T (Fin.castSucc i))
                (v ⟨(Fin.castSucc i : Fin (m + 1)).val + 1, hi⟩) := by
                rw [Module.End.mul_apply]
          _ = (T (Fin.castSucc i) * ε (⟨(Fin.castSucc i : Fin (m + 1)).val + 1, hi⟩))
                (v ⟨(Fin.castSucc i : Fin (m + 1)).val + 1, hi⟩) := by rw [← hTε]
          _ = T (Fin.castSucc i) (ε (⟨(Fin.castSucc i : Fin (m + 1)).val + 1, hi⟩)
                (v ⟨(Fin.castSucc i : Fin (m + 1)).val + 1, hi⟩)) := by
                rw [Module.End.mul_apply]
          _ = T (Fin.castSucc i)
                (-(v ⟨(Fin.castSucc i : Fin (m + 1)).val + 1, hi⟩)) := by rw [ih'.2]
          _ = -(T (Fin.castSucc i) (v ⟨(Fin.castSucc i : Fin (m + 1)).val + 1, hi⟩)) :=
                map_neg _ _
          _ = -v (Fin.castSucc i) := by rw [← hveq]
  have hB : ∀ i j, i ≠ j → ε i (v j) = v j := fun i j hij =>
    IsRefl.apply_eq_self_of_commute h2 (hε i) (hε j) (hcomm i j) (hne i j hij) (hA j).2
  have hli : LinearIndependent k v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have hzero : (1 - ε i : Module.End k V) (∑ j, c j • v j) = 0 := by
      rw [hc]; exact map_zero (1 - ε i : Module.End k V)
    have hterm : ∀ j, (1 - ε i : Module.End k V) (v j) =
        if j = i then (2 : k) • v j else 0 := by
      intro j
      by_cases h : j = i
      · subst h
        rw [show (1 - ε j : Module.End k V) (v j) = v j - ε j (v j) by
              simp [sub_eq_add_neg, map_add, map_neg], (hA j).2]
        simp [sub_eq_add_neg, two_smul]
      · rw [show (1 - ε i : Module.End k V) (v j) = v j - ε i (v j) by
              simp [sub_eq_add_neg, map_add, map_neg], hB i j (Ne.symm h)]
        simp [h]
    have hcompute : (1 - ε i : Module.End k V) (∑ j, c j • v j) = c i • ((2 : k) • v i) := by
      calc (1 - ε i : Module.End k V) (∑ j, c j • v j)
          = ∑ j, (1 - ε i : Module.End k V) (c j • v j) := by rw [map_sum]
        _ = ∑ j, c j • ((1 - ε i : Module.End k V) (v j)) := by
              apply Finset.sum_congr rfl; intro j _; rw [map_smul]
        _ = ∑ j, c j • (if j = i then (2 : k) • v j else 0) := by
              apply Finset.sum_congr rfl; intro j _; rw [hterm]
        _ = ∑ j, (if j = i then c j • ((2 : k) • v j) else 0) := by
              apply Finset.sum_congr rfl; intro j _
              by_cases h : j = i <;> simp [h]
        _ = c i • ((2 : k) • v i) := by
              simpa using Finset.sum_ite_eq' Finset.univ i (fun j => c j • ((2 : k) • v j))
    have h1 : c i • ((2 : k) • v i) = 0 := hcompute ▸ hzero
    rw [smul_eq_zero] at h1
    rcases h1 with h | h
    · exact h
    · rw [smul_eq_zero] at h
      rcases h with h | h
      · exact absurd h h2
      · exact absurd h (hA i).1
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli ?_, ?_, ?_⟩
  · rw [Fintype.card_fin, hdim]
  · intro i hi j
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
    by_cases h1 : j = (⟨i.val + 1, hi⟩ : Fin (m + 1))
    · subst h1
      rw [Equiv.swap_apply_right]
      exact (hv i hi).symm
    · by_cases h2' : j = i
      · subst h2'
        rw [Equiv.swap_apply_left]
        rw [hv j hi, ← Module.End.mul_apply, (hT j hi).1, Module.End.one_apply]
      · have hswap : Equiv.swap i (⟨i.val + 1, hi⟩ : Fin (m + 1)) j = j :=
          Equiv.swap_apply_of_ne_of_ne h2' h1
        rw [hswap]
        have hconj_ij : T i * ε j * T i = ε j := by
          have := hconj i hi j
          rwa [hswap] at this
        have hcomm' : T i * ε j = ε j * T i := by
          calc T i * ε j = (T i * ε j) * 1 := (mul_one _).symm
            _ = (T i * ε j) * (T i * T i) := by rw [(hT i hi).1]
            _ = ((T i * ε j) * T i) * T i := (mul_assoc _ _ _).symm
            _ = ε j * T i := by rw [hconj_ij]
        exact IsRefl.apply_eq_self_of_commute h2 (hT i hi) (hε j) hcomm' (hTne i hi j) (hA j).2
  · intro j
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
    by_cases h : j = Fin.last m
    · subst h
      rw [if_pos rfl]
      exact (hA (Fin.last m)).2
    · rw [if_neg h]
      exact hB (Fin.last m) j (Ne.symm h)

end CFSG.StandardType.SpFrame
