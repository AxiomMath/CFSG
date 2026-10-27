module

public import CFSG.LocalAnalysis.StandardType.GGK1CCoDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.Classical (spEnd IsReciprocalTransversal)
open CFSG.RankThree.PartOne.KCPrimary

private lemma ggK1CAr_hasOrbit_sl (t : ℕ) :
    ggK1CCo_Kind.hasOrbit (ggK1CCo_Kind.sl t) = decide (t ≠ 1) := by
  rcases t with _ | _ | t <;> rfl

private lemma ggK1CAr_hasOrbit_su (t : ℕ) :
    ggK1CCo_Kind.hasOrbit (ggK1CCo_Kind.su t) = decide (t ≠ 1) := by
  rcases t with _ | _ | t <;> rfl

private lemma ggK1CAr_decide_and (a b : Prop) [Decidable a] [Decidable b] :
    decide (a ∧ b) = (decide a && decide b) := by
  by_cases ha : a <;> by_cases hb : b <;> simp_all

private lemma ggK1CAr_bool_aux (j t : ℕ) :
    (decide (t ≠ 1) && decide (1 ≤ j ∧ 1 ≤ t)) = decide (1 ≤ j ∧ 2 ≤ t) := by
  rw [← ggK1CAr_decide_and, decide_eq_decide]
  omega

private lemma ggK1CAr_hasOrbit_and (d j t : ℕ) :
    (ggK1CCo_Kind.hasOrbit
        (if d = 1 then ggK1CCo_Kind.sl t else ggK1CCo_Kind.su t) &&
      decide (1 ≤ j ∧ 1 ≤ t)) = decide (1 ≤ j ∧ 2 ≤ t) := by
  by_cases hd : d = 1
  · rw [if_pos hd, ggK1CAr_hasOrbit_sl]
    exact ggK1CAr_bool_aux j t
  · rw [if_neg hd, ggK1CAr_hasOrbit_su]
    exact ggK1CAr_bool_aux j t

private lemma ggK1CAr_blockA_eq (r nf d : ℕ) (hd : d ≠ 1) :
    ggMultBlockA r nf 2 = ggMultBlockA r nf d := by
  rw [ggMultBlockA, ggMultBlockA]
  simp [hd]

private lemma ggK1CAr_kindOrbit_blockA (nf d t : ℕ) (ht : 2 ≤ t) :
    ggK1CCo_kindOrbit nf (if d = 1 then ggK1CCo_Kind.sl t else ggK1CCo_Kind.su t) =
      ggMultBlockA (t - 1) nf d := by
  by_cases hd : d = 1
  · subst hd
    rw [if_pos rfl]
    rcases t with _ | _ | t
    · omega
    · omega
    · rfl
  · rw [if_neg hd]
    rcases t with _ | _ | t
    · omega
    · omega
    · rw [show ggK1CCo_kindOrbit nf (ggK1CCo_Kind.su (t + 1 + 1)) =
            ggMultBlockA (t + 1 + 1 - 1) nf 2 from rfl]
      exact ggK1CAr_blockA_eq _ _ _ hd

private lemma ggK1CAr_filter_map_kindOrbit (L : List ℕ) (d nf : ℕ) (f : ℕ → ℕ) :
    (((L.filter (fun j => decide (1 ≤ j ∧ 1 ≤ f j))).map
        (fun j => if d = 1 then ggK1CCo_Kind.sl (f j) else ggK1CCo_Kind.su (f j))).filter
        (fun k => ggK1CCo_Kind.hasOrbit k)).map (ggK1CCo_kindOrbit nf) =
      (L.filter (fun j => decide (1 ≤ j ∧ 2 ≤ f j))).map
          (fun j => ggMultBlockA (f j - 1) nf d) := by
  rw [List.filter_map, List.filter_filter, List.map_map]
  simp only [Function.comp_apply]
  have hQ : L.filter (fun a =>
        ggK1CCo_Kind.hasOrbit
            (if d = 1 then ggK1CCo_Kind.sl (f a) else ggK1CCo_Kind.su (f a)) &&
          decide (1 ≤ a ∧ 1 ≤ f a)) =
      L.filter (fun j => decide (1 ≤ j ∧ 2 ≤ f j)) := by
    apply List.filter_congr
    intro j _
    exact ggK1CAr_hasOrbit_and d j (f j)
  rw [hQ]
  apply List.map_congr_left
  intro j hj
  have h2 : 2 ≤ f j := by
    have h := (List.mem_filter.mp hj).2
    rw [decide_eq_true_eq] at h
    exact h.2
  exact ggK1CAr_kindOrbit_blockA nf d (f j) h2

private lemma ggK1CAr_sp_part (nf m0 : ℕ) :
    ((if m0 = 0 then ([] : List ggK1CCo_Kind) else [ggK1CCo_Kind.sp m0]).filter
        (fun k => ggK1CCo_Kind.hasOrbit k)).map (ggK1CCo_kindOrbit nf) =
      (if m0 = 1 then [⟨⟨.A, 1, nf⟩, decide (nf ≠ 1)⟩]
        else if m0 = 2 ∧ nf = 1 then [⟨⟨.B2der, 0, 1⟩, true⟩]
        else if 2 ≤ m0 then [⟨⟨.C, m0, nf⟩, true⟩] else []) := by
  rcases m0 with _ | _ | _ | k
  · simp [ggK1CCo_Kind.hasOrbit]
  · simp [ggK1CCo_Kind.hasOrbit, ggK1CCo_kindOrbit]
  · by_cases hnf : nf = 1 <;> simp [ggK1CCo_Kind.hasOrbit, ggK1CCo_kindOrbit, hnf]
  · have h1 : ¬ (k + 3 = 1) := by omega
    have h2 : ¬ (k + 3 = 2 ∧ nf = 1) := by omega
    simp [ggK1CCo_Kind.hasOrbit, ggK1CCo_kindOrbit, h1, h2]

private lemma ggK1CAr_lambda2_A (n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r) (h : r = 1 → 2 ≤ n) :
    LargeEvenInLambda2 (⟨.A, r, n⟩ : LargeEvenLabel) := by
  simp only [LargeEvenInLambda2]
  exact ⟨hn, hr, h⟩

private lemma ggK1CAr_lambda2_C (n r : ℕ) (hn : 1 ≤ n) (hr : 2 ≤ r) (h : r = 2 → 2 ≤ n) :
    LargeEvenInLambda2 (⟨.C, r, n⟩ : LargeEvenLabel) := by
  simp only [LargeEvenInLambda2]
  exact ⟨hn, hr, h⟩

private lemma ggK1CAr_lambda2_twA (n r : ℕ) (hn : 1 ≤ n) (hr : 2 ≤ r) (h : r = 2 → 2 ≤ n) :
    LargeEvenInLambda2 (⟨.twA, r, n⟩ : LargeEvenLabel) := by
  simp only [LargeEvenInLambda2]
  exact ⟨hn, hr, h⟩

private lemma ggK1CAr_lambda2_B2der :
    LargeEvenInLambda2 (⟨.B2der, 0, 1⟩ : LargeEvenLabel) := by
  simp [LargeEvenInLambda2]

private lemma ggK1CAr_blockA_arith {r nf d : ℕ} (hnf : 1 ≤ nf) (hr : 1 ≤ r)
    (hqs : (ggMultBlockA r nf d).qs = true) :
    nf ∣ (ggMultBlockA r nf d).lab.n ∧ LargeEvenInLambda2 (ggMultBlockA r nf d).lab := by
  by_cases hd : d = 1
  · rw [ggMultBlockA, if_pos hd] at hqs ⊢
    rw [decide_eq_true_eq] at hqs
    exact ⟨dvd_refl nf, ggK1CAr_lambda2_A nf r hnf hr (by rintro rfl; omega)⟩
  · rw [ggMultBlockA, if_neg hd] at hqs ⊢
    by_cases h2 : 2 ≤ r
    · rw [if_pos h2] at hqs ⊢
      rw [decide_eq_true_eq] at hqs
      exact ⟨dvd_refl nf, ggK1CAr_lambda2_twA nf r hnf h2 (by rintro rfl; omega)⟩
    · rw [if_neg h2] at hqs ⊢
      have hr1 : r = 1 := by omega
      subst hr1
      rw [decide_eq_true_eq] at hqs
      exact ⟨dvd_refl nf, ggK1CAr_lambda2_A nf 1 hnf le_rfl (by intro _; omega)⟩

private lemma ggK1CAr_orb0_arith {m0 nf : ℕ} (hnf : 1 ≤ nf) {o : GGKacOrbit}
    (ho : o ∈ (if m0 = 1 then [⟨⟨.A, 1, nf⟩, decide (nf ≠ 1)⟩]
        else if m0 = 2 ∧ nf = 1 then [⟨⟨.B2der, 0, 1⟩, true⟩]
        else if 2 ≤ m0 then [⟨⟨.C, m0, nf⟩, true⟩] else []))
    (hqs : o.qs = true) : nf ∣ o.lab.n ∧ LargeEvenInLambda2 o.lab := by
  split_ifs at ho with h1 h2 h3
  · rw [List.mem_singleton] at ho
    subst ho
    have hne : nf ≠ 1 := by rwa [decide_eq_true_eq] at hqs
    exact ⟨dvd_refl nf, ggK1CAr_lambda2_A nf 1 hnf le_rfl (by intro _; omega)⟩
  · rw [List.mem_singleton] at ho
    subst ho
    obtain ⟨_, hnf1⟩ := h2
    subst hnf1
    exact ⟨one_dvd 1, ggK1CAr_lambda2_B2der⟩
  · rw [List.mem_singleton] at ho
    subst ho
    refine ⟨dvd_refl nf, ggK1CAr_lambda2_C nf m0 hnf h3 ?_⟩
    intro hm0
    have hnf1 : nf ≠ 1 := by rintro rfl; exact h2 ⟨hm0, rfl⟩
    omega
  · rw [List.mem_nil_iff] at ho
    exact absurd ho (by simp)

theorem ggK1CCo_kindOrbit_multiset (p nf d : ℕ) (m : List ℕ) :
    (ggK1CCo_orbitKindList p nf d m).map (ggK1CCo_kindOrbit nf) =
      (ggMultDatumC p nf d m).orbits := by
  simp only [ggK1CCo_orbitKindList, ggK1CCo_expectedKindList, ggMultDatumC]
  rw [List.filter_append, List.map_append]
  rw [ggK1CAr_sp_part nf (m.headD 0), ggK1CAr_filter_map_kindOrbit]

theorem ggK1CCo_orbit_arith {p nf d : ℕ} {m : List ℕ} (hnf : 1 ≤ nf) {o : GGKacOrbit}
    (ho : o ∈ (ggMultDatumC p nf d m).orbits) (hqs : o.qs = true) :
    nf ∣ o.lab.n ∧ LargeEvenInLambda2 o.lab := by
  simp only [ggMultDatumC] at ho
  rw [List.mem_append] at ho
  rcases ho with ho | ho
  · exact ggK1CAr_orb0_arith hnf ho hqs
  · obtain ⟨j, hj, hjeq⟩ := List.mem_map.mp ho
    have hj' : 2 ≤ m.getD j 0 := by
      have h := (List.mem_filter.mp hj).2
      rw [decide_eq_true_eq] at h
      exact h.2
    have hr : 1 ≤ m.getD j 0 - 1 := by omega
    rw [← hjeq] at hqs ⊢
    exact ggK1CAr_blockA_arith hnf hr hqs

end CFSG.StandardType

end
