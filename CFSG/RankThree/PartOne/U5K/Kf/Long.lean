module

public import CFSG.RankThree.PartOne.U5K.Hyp.Para

public section

namespace CFSG.RankThree.PartOne.U5K.Kf

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.U5K.Hyp

variable {f : ℕ} {K : Type} [Field K] {hK : UnitaryFieldData 2 f K}

theorem exists_mem_Usub_aOf (a : K) :
    ∃ u ∈ hypUnitriangular hK 2 1, aOf u = a := by
  obtain ⟨u, hu, hum⟩ := (exists_mem_hypUnitriangular_odd_iff (h := hK) (r := 2)
    (oddDiag hK !![1, a; 0, 1] 1 * oddUni hK 0 0)).2
      ⟨!![1, a; 0, 1], 0, 0, ⟨fun i j hij => by
        fin_cases i <;> fin_cases j <;> simp at hij ⊢, fun i => by
        fin_cases i <;> simp⟩, by simp, rfl⟩
  exact ⟨u, hu, aOf_eq_of_coord hum⟩

theorem central_Usub_long {s : hypSU hK 2 1} (hs : s ∈ Ssub hK)
    (h : ∀ u ∈ hypUnitriangular hK 2 1, s * u = u * s) :
    ∃ c : K, mat s = oddUni hK 0 !![c, 0; 0, 0] := by
  have hsV : s ∈ Vsub hK :=
    (central_Ssub_iff hs).1 fun s' hs' => (h s' (Ssub_le_Usub hs')).symm
  obtain ⟨-, Y, hY⟩ := hsV
  have hYh : IsHerm hK Y := herm_of_mem_Vsub hY
  obtain ⟨-, -, hY10⟩ := isHerm_iff.1 hYh
  have hYof : Yof s = Y := Yof_eq hY
  have key : ∀ a : K, a * Y 1 1 = 0 ∧
      a * Y 1 0 + Y 0 1 * hK.bar a + a * Y 1 1 * hK.bar a = 0 := by
    intro a
    obtain ⟨u, hu, hua⟩ := exists_mem_Usub_aOf (hK := hK) a
    have := commute_Vsub_entries hu ⟨Ssub_le_Usub hs, Y, hY⟩ (h u hu).symm
    rw [hua, hYof] at this
    exact this
  have hY11 : Y 1 1 = 0 := by simpa using (key 1).1
  have hY01 : Y 0 1 = 0 := by
    by_contra hne
    obtain ⟨c, hc⟩ := trace_surj (hK := hK) (a := 1) (by simp)
    have hb : hK.bar (Y 0 1) ≠ 0 := (map_ne_zero hK.bar).2 hne
    have h1 := (key (c / hK.bar (Y 0 1))).2
    rw [hY11, hY10] at h1
    have e1 : c / hK.bar (Y 0 1) * hK.bar (Y 0 1) = c := div_mul_cancel₀ _ hb
    have e2 : Y 0 1 * hK.bar (c / hK.bar (Y 0 1)) = hK.bar c := by
      rw [map_div₀, hK.bar_bar]
      field_simp
    have h2 : c + hK.bar c = 0 := by
      have := h1
      simp only [mul_zero, zero_mul, add_zero] at this
      rw [e1, e2] at this
      exact this
    rw [hc] at h2
    exact one_ne_zero h2
  refine ⟨Y 0 0, ?_⟩
  have hYe : Y = !![Y 0 0, 0; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hY01, hY11, hY10]
  have hEq : oddUni hK 0 Y = oddUni hK 0 !![Y 0 0, 0; 0, 0] := by rw [← hYe]
  exact hY.trans hEq

theorem oddUni_long (c : K) :
    oddUni hK 0 !![c, 0; 0, 0] =
      1 + c • Matrix.single (Sum.inl (0 : Fin 2) : HypIndex 2 1)
        (Sum.inr (Sum.inr (0 : Fin 2))) (1 : K) := by
  ext a b
  rcases a with i | k | i <;> rcases b with j | l | j
  all_goals simp [oddUni, Matrix.one_apply, Matrix.single_apply]
  all_goals fin_cases i <;> fin_cases j <;> simp

theorem act_eq_of_long_aux (x : Gam hK) (hx : x.1.right = 1) {α : K}
    (h1 : ∀ r : HypIndex 2 1, r ≠ Sum.inl 0 → lmat x r (Sum.inl 0) = 0)
    (h2 : lmat x (Sum.inl 0) (Sum.inl 0) = α)
    (h3 : ∀ c : HypIndex 2 1, c ≠ Sum.inr (Sum.inr 0) → lmat x (Sum.inr (Sum.inr 0)) c = 0)
    (h4 : lmat x (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inr 0)) = α)
    {s : hypSU hK 2 1} {c : K} (hs : mat s = oddUni hK 0 !![c, 0; 0, 0]) :
    act hK x s = s := by
  have hcomm : lmat x * mat s = mat s * lmat x := by
    rw [hs, oddUni_long, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul]
    congr 1
    rw [Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    ext a b
    simp only [Matrix.mul_apply, Matrix.single_apply, mul_ite, ite_mul, mul_one, one_mul,
      mul_zero, zero_mul]
    by_cases hb : b = Sum.inr (Sum.inr 0)
    · by_cases ha : a = Sum.inl 0
      · subst hb; subst ha
        simp [h2, h4]
      · have ha' : ¬ (Sum.inl 0 : HypIndex 2 1) = a := fun h => ha h.symm
        simp [hb, ha', h1 a ha]
    · have hb' : ¬ (Sum.inr (Sum.inr 0) : HypIndex 2 1) = b := fun h => hb h.symm
      by_cases ha : a = Sum.inl 0
      · subst ha
        simp [hb', h3 b hb]
      · have ha' : ¬ (Sum.inl 0 : HypIndex 2 1) = a := fun h => ha h.symm
        simp [hb', ha']
  have hmap : (mat s).map x.1.right = mat s := by
    ext i j
    simp [hx]
  have hact := lmat_mul_map x s
  rw [hmap] at hact
  have hinv : lmat x * (((x.1.left⁻¹ : GL (HypIndex 2 1) K)) : Matrix _ _ K) = 1 := by
    rw [lmat, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  apply mat_injective
  calc mat (act hK x s)
      = mat (act hK x s) * lmat x * (((x.1.left⁻¹ : GL (HypIndex 2 1) K)) : Matrix _ _ K) := by
        rw [Matrix.mul_assoc, hinv, Matrix.mul_one]
    _ = mat s * lmat x * (((x.1.left⁻¹ : GL (HypIndex 2 1) K)) : Matrix _ _ K) := by
        rw [← hact, hcomm]
    _ = mat s := by rw [Matrix.mul_assoc, hinv, Matrix.mul_one]

theorem row_of_col {M : Matrix (HypIndex 2 1) (HypIndex 2 1) K} {α : K}
    (hcol : ∀ r, M r (Sum.inl 0) = if r = Sum.inl 0 then α else 0) (hα : hK.bar α * α = 1)
    (hg : (M.map hK.bar)ᵀ * hypGram 2 1 K * M = hypGram 2 1 K) :
    ∀ c, M (Sum.inr (Sum.inr 0)) c = if c = Sum.inr (Sum.inr 0) then α else 0 := by
  have hα0 : α ≠ 0 := right_ne_zero_of_mul_eq_one hα
  have key : ∀ a : HypIndex 2 1, α * hK.bar (M (Sum.inr (Sum.inr 0)) a) =
      if a = Sum.inr (Sum.inr 0) then 1 else 0 := by
    intro a
    have h1 := congrFun (congrFun hg a) (Sum.inl 0)
    rw [conjTranspose_hypGram_mul_apply, hypGram_apply] at h1
    have h2 : ∀ x : HypIndex 2 1, hK.bar (M x a) * M (hypPartner x) (Sum.inl 0) =
        if x = Sum.inr (Sum.inr 0) then hK.bar (M x a) * α else 0 := by
      intro x
      rw [hcol]
      by_cases hx : x = Sum.inr (Sum.inr 0)
      · subst hx
        simp [hypPartner]
      · have : hypPartner x ≠ Sum.inl 0 := by
          intro hh
          apply hx
          rw [← hypPartner_hypPartner x, hh]
          rfl
        simp [hx, this]
    simp only [h2, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h1
    have h3 : (Sum.inl 0 : HypIndex 2 1) = hypPartner a ↔ a = Sum.inr (Sum.inr 0) := by
      constructor
      · intro hh
        have := hypPartner_eq_iff.1 hh.symm
        simpa [hypPartner] using this
      · intro hh
        rw [hh]
        rfl
    rw [if_congr h3 rfl rfl] at h1
    rw [mul_comm]
    exact h1
  intro c
  by_cases hc : c = Sum.inr (Sum.inr 0)
  · subst hc
    have h1 := key (Sum.inr (Sum.inr 0))
    simp only [ite_true] at h1
    have h2 : hK.bar (M (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inr 0))) = hK.bar α := by
      have : α * (hK.bar (M (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inr 0))) - hK.bar α) = 0 := by
        rw [mul_sub, h1, mul_comm α (hK.bar α), hα, sub_self]
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hα0
      · exact sub_eq_zero.1 h
    have h3 := congrArg hK.bar h2
    rw [hK.bar_bar, hK.bar_bar] at h3
    simpa using h3
  · have h1 := key c
    simp only [hc, ite_false] at h1
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd h hα0
    · simpa [hc] using (map_eq_zero hK.bar).1 h

theorem act_eq_of_long (x : Gam hK) (hx : x.1.right = 1) {α : K}
    (hcol : ∀ r, lmat x r (Sum.inl 0) = if r = Sum.inl 0 then α else 0) (hα : hK.bar α * α = 1)
    (hg : ((lmat x).map hK.bar)ᵀ * hypGram 2 1 K * lmat x = hypGram 2 1 K)
    {s : hypSU hK 2 1} {c : K} (hs : mat s = oddUni hK 0 !![c, 0; 0, 0]) :
    act hK x s = s := by
  have hrow := row_of_col hcol hα hg
  refine act_eq_of_long_aux x hx (α := α) (fun r hr => by simp [hcol r, hr])
    (by simp [hcol]) (fun c hc => by simp [hrow c, hc]) (by simp [hrow]) hs

end CFSG.RankThree.PartOne.U5K.Kf
