module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDCoxMat

public section

namespace CFSG.StandardType.QTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma plnf_w_injective {m k : ℕ} (c d w : Fin k → Fin m)
    (hw : ∀ j, w j = c j ∨ w j = d j) (htri : ∀ i j, i < j → w j ≠ c i ∧ w j ≠ d i) :
    Function.Injective w := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have h1 := htri i j h
    rcases hw i with hi | hi
    · exact h1.1 (hij.symm.trans hi)
    · exact h1.2 (hij.symm.trans hi)
  · have h1 := htri j i h
    rcases hw j with hj | hj
    · exact h1.1 (hij.trans hj)
    · exact h1.2 (hij.trans hj)

private lemma plnf_exists_off {m k : ℕ} (hk : 0 < k) (c d w : Fin k → Fin m)
    (hcd : ∀ j, c j ≠ d j) (hw : ∀ j, w j = c j ∨ w j = d j)
    (htri : ∀ i j, i < j → w j ≠ c i ∧ w j ≠ d i) :
    ∃ x, x ∉ Set.range w ∧ x ≠ w ⟨0, hk⟩ := by
  obtain ⟨x, hx0, hxw⟩ : ∃ x, (x = c ⟨0, hk⟩ ∨ x = d ⟨0, hk⟩) ∧ x ≠ w ⟨0, hk⟩ := by
    rcases hw ⟨0, hk⟩ with h | h
    · exact ⟨d ⟨0, hk⟩, Or.inr rfl, by rw [h]; exact (hcd _).symm⟩
    · exact ⟨c ⟨0, hk⟩, Or.inl rfl, by rw [h]; exact hcd _⟩
  refine ⟨x, ?_, hxw⟩
  rintro ⟨j, hj⟩
  by_cases hj0 : j = ⟨0, hk⟩
  · rw [hj0] at hj
    exact hxw hj.symm
  · have hlt : (⟨0, hk⟩ : Fin k) < j := by
      rw [Fin.lt_def]
      have : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
      change 0 < j.val
      omega
    have h1 := htri ⟨0, hk⟩ j hlt
    rcases hx0 with h | h
    · exact h1.1 (hj.trans h)
    · exact h1.2 (hj.trans h)

theorem dFix_card_le_of_triangular {m k : ℕ} (hk : 0 < k) (c d w : Fin k → Fin m)
    (sg : Fin k → ZMod 3) (hcd : ∀ j, c j ≠ d j) (hw : ∀ j, w j = c j ∨ w j = d j)
    (htri : ∀ i j, i < j → w j ≠ c i ∧ w j ≠ d i) :
    k + 1 ≤ m ∧
      Nat.card {v : DVec m // ∀ j, v (c j) = sg j * v (d j) ∧ v (d j) = sg j * v (c j)} ≤
        3 ^ (m - k) := by
  have hwinj : Function.Injective w := plnf_w_injective c d w hw htri
  obtain ⟨x, hxR, _⟩ := plnf_exists_off hk c d w hcd hw htri
  have hcons : Function.Injective (Fin.cons x w : Fin (k + 1) → Fin m) :=
    Fin.cons_injective_iff.mpr ⟨hxR, hwinj⟩
  refine ⟨by simpa using Fintype.card_le_of_injective _ hcons, ?_⟩
  let Φ : {v : DVec m // ∀ j, v (c j) = sg j * v (d j) ∧ v (d j) = sg j * v (c j)} →
      ({x : Fin m // x ∉ Set.range w} → ZMod 3) := fun v x => v.1 x.1
  have hΦ : Function.Injective Φ := by
    intro v v' hvv
    have hoff : ∀ x, x ∉ Set.range w → v.1 x = v'.1 x := fun x hx => congrFun hvv ⟨x, hx⟩
    have hon : ∀ n, ∀ j : Fin k, j.val = n → v.1 (w j) = v'.1 (w j) := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro j hj
        obtain ⟨y, hye, hyw, hvy, hvy'⟩ : ∃ y, (y = c j ∨ y = d j) ∧ y ≠ w j ∧
            v.1 (w j) = sg j * v.1 y ∧ v'.1 (w j) = sg j * v'.1 y := by
          rcases hw j with h | h
          · refine ⟨d j, Or.inr rfl, by rw [h]; exact (hcd j).symm, ?_, ?_⟩
            · rw [h]; exact (v.2 j).1
            · rw [h]; exact (v'.2 j).1
          · refine ⟨c j, Or.inl rfl, by rw [h]; exact hcd j, ?_, ?_⟩
            · rw [h]; exact (v.2 j).2
            · rw [h]; exact (v'.2 j).2
        have hyy : v.1 y = v'.1 y := by
          by_cases hyR : y ∈ Set.range w
          · obtain ⟨i, hi⟩ := hyR
            have hij : i ≠ j := fun h => hyw (by rw [← hi, h])
            rcases lt_or_gt_of_ne hij with hlt | hgt
            · rw [← hi]
              exact ih i.val (by rw [← hj]; exact hlt) i rfl
            · exfalso
              have h1 := htri j i hgt
              rcases hye with h | h
              · exact h1.1 (hi.trans h)
              · exact h1.2 (hi.trans h)
          · exact hoff y hyR
        rw [hvy, hvy', hyy]
    apply Subtype.ext
    funext y
    by_cases hy : y ∈ Set.range w
    · obtain ⟨j, rfl⟩ := hy
      exact hon j.val j rfl
    · exact hoff y hy
  have hcR : Nat.card {x : Fin m // x ∉ Set.range w} = m - k := by
    have h1 := Nat.card_congr (Equiv.sumCompl (fun x : Fin m => x ∈ Set.range w))
    rw [Nat.card_sum, Nat.card_fin] at h1
    have h2 : Nat.card {x : Fin m // x ∈ Set.range w} = k := by
      rw [Nat.card_congr (Equiv.ofInjective w hwinj).symm, Nat.card_fin]
    omega
  calc Nat.card {v : DVec m // ∀ j, v (c j) = sg j * v (d j) ∧ v (d j) = sg j * v (c j)}
      ≤ Nat.card ({x : Fin m // x ∉ Set.range w} → ZMod 3) :=
        Nat.card_le_card_of_injective Φ hΦ
    _ = 3 ^ (m - k) := by rw [Nat.card_fun, Nat.card_zmod, hcR]

private lemma plnf_far_disjoint {m k : ℕ} (hk : 4 ≤ k) (S : Fin k → Finset (Fin m))
    (hadj : ∀ i j : Fin k, i.val + 1 = j.val → ¬ Disjoint (S i) (S j) ∧ S i ≠ S j)
    (hfar : ∀ i j : Fin k, i.val + 2 ≤ j.val → Disjoint (S i) (S j) ∨ S i = S j)
    (i j : Fin k) (hij : i.val + 2 ≤ j.val) : Disjoint (S i) (S j) := by
  have hjk := j.isLt
  rcases hfar i j hij with hd | heq
  · exact hd
  · exfalso
    by_cases hA : j.val + 1 < k
    · have h1 := hadj j ⟨j.val + 1, hA⟩ rfl
      rcases hfar i ⟨j.val + 1, hA⟩ (by change i.val + 2 ≤ j.val + 1; omega) with hd | he
      · rw [heq] at hd
        exact h1.1 hd
      · rw [heq] at he
        exact h1.2 he
    · by_cases hB : 1 ≤ i.val
      · have hl : i.val - 1 < k := by omega
        have h1 := hadj ⟨i.val - 1, hl⟩ i (by change i.val - 1 + 1 = i.val; omega)
        rcases hfar ⟨i.val - 1, hl⟩ j (by change i.val - 1 + 2 ≤ j.val; omega) with hd | he
        · rw [← heq] at hd
          exact h1.1 hd
        · rw [← heq] at he
          exact h1.2 he
      · have hl : 1 < k := by omega
        have h1 := hadj i ⟨1, hl⟩ (by change i.val + 1 = 1; omega)
        rcases hfar ⟨1, hl⟩ j (by change 1 + 2 ≤ j.val; omega) with hd | he
        · rw [← heq] at hd
          exact h1.1 hd.symm
        · rw [← heq] at he
          exact h1.2 he.symm

theorem exists_fresh_of_path {m k : ℕ} (hk : 4 ≤ k) (S : Fin k → Finset (Fin m))
    (hcard : ∀ j, (S j).card = 2)
    (hadj : ∀ i j : Fin k, i.val + 1 = j.val → ¬ Disjoint (S i) (S j) ∧ S i ≠ S j)
    (hfar : ∀ i j : Fin k, i.val + 2 ≤ j.val → Disjoint (S i) (S j) ∨ S i = S j)
    (j : Fin k) : ∃ w ∈ S j, ∀ i : Fin k, i < j → w ∉ S i := by
  by_cases hj : j.val = 0
  · obtain ⟨w, hw⟩ : (S j).Nonempty := by
      rw [← Finset.card_pos, hcard j]
      norm_num
    exact ⟨w, hw, fun i hi => absurd hi (by rw [Fin.lt_def]; omega)⟩
  · have hjk := j.isLt
    have hl : j.val - 1 < k := by omega
    have hne := (hadj ⟨j.val - 1, hl⟩ j (by change j.val - 1 + 1 = j.val; omega)).2
    have hnsub : ¬ S j ⊆ S ⟨j.val - 1, hl⟩ := fun hsub =>
      hne (Finset.eq_of_subset_of_card_le hsub (by simp [hcard])).symm
    obtain ⟨w, hwj, hwi⟩ := Finset.not_subset.mp hnsub
    refine ⟨w, hwj, fun i hi => ?_⟩
    rw [Fin.lt_def] at hi
    by_cases hii : i.val = j.val - 1
    · have : i = ⟨j.val - 1, hl⟩ := Fin.ext hii
      rw [this]
      exact hwi
    · exact Finset.disjoint_right.mp (plnf_far_disjoint hk S hadj hfar i j (by omega)) hwj

end CFSG.StandardType.QTwo

end
