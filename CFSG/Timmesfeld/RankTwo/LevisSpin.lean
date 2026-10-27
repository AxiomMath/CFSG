module

public import CFSG.Timmesfeld.RankTwo.LevisExtras
public import CFSG.LieType.Steinberg.Classical.SpinPlus

public section

namespace CFSG.Timmesfeld

open CFSG.LieType CFSG.LieType.Universal

@[expose] def edgeD (n : ℕ) (i j : Fin n) : Prop :=
  (i.val + 1 = j.val ∧ j.val + 1 < n) ∨ (i.val + 3 = n ∧ j.val + 1 = n)

instance (n : ℕ) : DecidableRel (edgeD n) := fun i j =>
  inferInstanceAs (Decidable ((i.val + 1 = j.val ∧ j.val + 1 < n) ∨
    (i.val + 3 = n ∧ j.val + 1 = n)))

namespace LevisSpin

theorem cartanD_apply {n : ℕ} (i j : Fin n) : Spin.cartanD n i j =
    if i = j then 2 else if (i.val + 1 = j.val ∧ j.val + 1 < n) ∨
      (j.val + 1 = i.val ∧ i.val + 1 < n) ∨ (i.val + 3 = n ∧ j.val + 1 = n) ∨
      (j.val + 3 = n ∧ i.val + 1 = n) then -1 else 0 := rfl

theorem edgeD_asymm {n : ℕ} (i j : Fin n) (h : edgeD n i j) : ¬ edgeD n j i := by
  unfold edgeD at *
  omega

theorem cartanD_of_edgeD {n : ℕ} {i j : Fin n} (h : edgeD n i j) :
    Spin.cartanD n i j = -1 ∧ Spin.cartanD n j i = -1 := by
  unfold edgeD at h
  have hij : i ≠ j := fun e => by subst e; omega
  rw [cartanD_apply, cartanD_apply, ite_eq_right hij, ite_eq_right (Ne.symm hij),
    ite_eq_left (by omega), ite_eq_left (by omega)]
  exact ⟨rfl, rfl⟩

theorem cartanD_of_not_edgeD {n : ℕ} {i j : Fin n} (hij : i ≠ j) (h1 : ¬ edgeD n i j)
    (h2 : ¬ edgeD n j i) : Spin.cartanD n i j = 0 ∧ Spin.cartanD n j i = 0 := by
  unfold edgeD at h1 h2
  rw [cartanD_apply, cartanD_apply, ite_eq_right hij, ite_eq_right (Ne.symm hij),
    ite_eq_right (by omega), ite_eq_right (by omega)]
  exact ⟨rfl, rfl⟩

theorem edgeD_neighbour {n : ℕ} (hn : 3 ≤ n) {i j : Fin n} (h : edgeD n i j) :
    ∃ k, k ≠ i ∧ k ≠ j ∧ ((edgeD n j k ∨ edgeD n k j) ∧ ¬ edgeD n i k ∧ ¬ edgeD n k i ∨
      (edgeD n i k ∨ edgeD n k i) ∧ ¬ edgeD n j k ∧ ¬ edgeD n k j) := by
  have hne : ∀ a b : Fin n, a.val ≠ b.val → a ≠ b := fun a b h e => h (congrArg Fin.val e)
  unfold edgeD at *
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · by_cases hi : 1 ≤ i.val
    · refine ⟨⟨i.val - 1, by omega⟩, hne _ _ (by simp; omega), hne _ _ (by simp; omega), ?_⟩
      right
      simp only
      omega
    · by_cases h4 : 4 ≤ n
      · refine ⟨⟨2, by omega⟩, hne _ _ (by simp; omega), hne _ _ (by simp; omega), ?_⟩
        left
        simp only
        omega
      · refine ⟨⟨2, by omega⟩, hne _ _ (by simp; omega), hne _ _ (by simp; omega), ?_⟩
        right
        simp only
        omega
  · refine ⟨⟨n - 2, by omega⟩, hne _ _ (by simp; omega), hne _ _ (by simp; omega), ?_⟩
    right
    simp only
    omega

end LevisSpin

open LevisSpin Steinberg in
theorem simplyLacedLevis_spinPlus {n : ℕ} (F : Type) [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n) : SimplyLacedLevis (Spin.plusDatum n F hn) F (edgeD n) (SpinPlus.x n F hn) := by
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (Spin.plusDatum n F hn).isFiniteType
    (Dv := (Spin.plusDatum n F hn).divisible) rfl
  exact simplyLacedLevis_of_chevalleyExtras
    (SpinPlus.chevalleyExtras hn O SpinPlus.commC (SpinPlus.commutatorFormula hn O)) rfl
    (fun α _ β _ _ _ => SpinPlus.commC_natAbs α β (1, 1)) edgeD_asymm
    (fun _ _ h => cartanD_of_edgeD h) (fun _ _ hij h1 h2 => cartanD_of_not_edgeD hij h1 h2)
    (fun _ _ h => edgeD_neighbour hn h)

theorem simplyLacedLevis_spinPlus_four (F : Type) [Field F] [Finite F] [CharP F 2] :
    SimplyLacedLevis (Spin.plusDatum 4 F (by norm_num)) F (edgeD 4)
      (Steinberg.SpinPlus.x 4 F (by norm_num)) :=
  simplyLacedLevis_spinPlus F (by norm_num)

end CFSG.Timmesfeld
