module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQOrbitExt

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin
open CFSG.StandardType

private theorem w135c2_omfPOrb_prod_spSgnOn {n : ℕ} (T : Finset (Fin n)) :
    ∏ a, spSgnOn T a = (-1 : ℤ) ^ T.card := by
  rw [show (∏ a, spSgnOn T a) = ∏ a, (if a ∈ T then (-1 : ℤ) else 1) from
    Finset.prod_congr rfl (fun a _ => rfl)]
  rw [Fintype.prod_ite_mem, Finset.prod_const]

private theorem w135c2_omfPOrb_even_card_pair {α : Type*} [DecidableEq α] {a b : α}
    (h : a ≠ b) : Even ({a, b} : Finset α).card := by
  rw [Finset.card_insert_of_notMem (by simpa using h), Finset.card_singleton]
  exact ⟨1, rfl⟩

private theorem w135c2_omfPOrb_exists_orbit {n j : ℕ} (hn : 2 ≤ n) (π : Equiv.Perm (Fin n))
    (T : Finset (Fin n)) (hT : Even T.card) :
    ∃ w : (coxeterMatrix (isFiniteType_cartanD n)).Group,
      toStdD n (weylAction (isFiniteType_cartanD n) w (omExtWt n j)) =
        fun b => 2 * (spSgnOn T b * (if (π.symm b).val ≤ j then (1 : ℤ) else 0)) := by
  have ht : SpIsSign (fun a => spSgnOn T (π a)) := fun a => spIsSign_spSgnOn T (π a)
  have hprod : ∏ a, spSgnOn T (π a) = 1 := by
    rw [Equiv.prod_comp π (spSgnOn T), w135c2_omfPOrb_prod_spSgnOn, hT.neg_one_pow]
  obtain ⟨w, hw⟩ := exists_omRealizes_of_even hn π ht hprod
  refine ⟨w, ?_⟩
  have key := hw (omExtWt n j)
  rw [show toStdD n (omExtWt n j) = fun a => 2 * (if a.val ≤ j then (1 : ℤ) else 0) from
    toStdD_omFromStdD2 hn _] at key
  rw [key]
  funext b
  show spSgnOn T (π (π.symm b)) * (2 * (if (π.symm b).val ≤ j then (1 : ℤ) else 0)) =
    2 * (spSgnOn T b * (if (π.symm b).val ≤ j then (1 : ℤ) else 0))
  rw [Equiv.apply_symm_apply]
  ring

private theorem w135c2_omfPOrb_stdReflD_indicator {n j : ℕ} (hj : j + 2 = n) {k : Fin n}
    (hk : k.val + 1 ≤ j) :
    stdReflD n k (fun a => if a.val ≤ j then (1 : ℤ) else 0) =
      fun a => if a.val ≤ j then (1 : ℤ) else 0 := by
  have hlt : k.val + 1 < n := by omega
  rw [stdReflD_of_lt n hlt]
  funext a
  rw [Function.comp_apply]
  by_cases hak : a = k
  · rw [hak, Equiv.swap_apply_left]
    rw [if_pos (show (⟨k.val + 1, hlt⟩ : Fin n).val ≤ j from by omega),
      if_pos (show k.val ≤ j from by omega)]
  · by_cases hak' : a = ⟨k.val + 1, hlt⟩
    · rw [hak', Equiv.swap_apply_right]
      rw [if_pos (show k.val ≤ j from by omega),
        if_pos (show (⟨k.val + 1, hlt⟩ : Fin n).val ≤ j from by omega)]
    · rw [Equiv.swap_apply_of_ne_of_ne hak hak']

theorem weylAction_simple_omExtWt_of_add_two_eq {n j : ℕ} (hn : 2 ≤ n) (hj : j + 2 = n)
    {k : Fin n} (hk : k.val + 2 < n) :
    weylAction (isFiniteType_cartanD n)
        ((coxeterMatrix (isFiniteType_cartanD n)).toCoxeterSystem.simple k) (omExtWt n j) =
      omExtWt n j := by
  have hk' : k.val + 1 ≤ j := by omega
  rw [show omExtWt n j = omFromStdD2 n (fun a => if a.val ≤ j then (1 : ℤ) else 0) from rfl,
    weylAction_simple_omFromStdD2 hn _ k, w135c2_omfPOrb_stdReflD_indicator hj hk']

theorem omExtWt_apply_last {n j : ℕ} (hj : j + 2 ≤ n) :
    omExtWt n j ⟨n - 2, by omega⟩ = omExtWt n j ⟨n - 1, by omega⟩ := by
  unfold omExtWt omFromStdD2
  rw [if_neg (by simp only; omega), dif_pos (by simp only; omega),
    if_pos (by simp only; omega)]
  dsimp only
  rw [if_neg (by omega)]
  ring

private theorem w135c2_omfPOrb_four_data {n j : ℕ} (hn : 4 ≤ n) (hj1 : 1 ≤ j)
    (hj : j + 2 ≤ n) :
    ∃ (d : Fin 4 → Fin n → ℤ)
      (w : Fin 4 → (coxeterMatrix (isFiniteType_cartanD n)).Group),
      (∀ i, toStdD n (weylAction (isFiniteType_cartanD n) (w i) (omExtWt n j)) =
        fun a => 2 * d i a) ∧
      (∀ i, d i ⟨0, by omega⟩ = ![0, 0, 1, -1] i) ∧
      (∀ i, d i ⟨1, by omega⟩ = ![1, -1, 0, 0] i) ∧
      (∀ i, d i ⟨n - 1, by omega⟩ = 1) := by
  have hn2 : 2 ≤ n := by omega
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  let ilast : Fin n := ⟨n - 1, by omega⟩
  have hi0 : i0.val = 0 := rfl
  have hi1 : i1.val = 1 := rfl
  have hil : ilast.val = n - 1 := rfl
  have h01 : i0 ≠ i1 := Fin.ne_of_val_ne (by rw [hi0, hi1]; omega)
  have h0l : i0 ≠ ilast := Fin.ne_of_val_ne (by rw [hi0, hil]; omega)
  have h1l : i1 ≠ ilast := Fin.ne_of_val_ne (by rw [hi1, hil]; omega)
  let π : Fin 4 → Equiv.Perm (Fin n) :=
    ![Equiv.swap i0 ilast, Equiv.swap i0 ilast, Equiv.swap i1 ilast, Equiv.swap i1 ilast]
  let T : Fin 4 → Finset (Fin n) := ![∅, {i0, i1}, ∅, {i0, i1}]
  let d : Fin 4 → Fin n → ℤ := fun i b =>
    spSgnOn (T i) b * (if ((π i).symm b).val ≤ j then (1 : ℤ) else 0)
  have hT : ∀ i, Even (T i).card := by
    intro i
    fin_cases i <;> simp only [T]
    · exact ⟨0, rfl⟩
    · exact w135c2_omfPOrb_even_card_pair h01
    · exact ⟨0, rfl⟩
    · exact w135c2_omfPOrb_even_card_pair h01
  have hex : ∀ i, ∃ w, toStdD n (weylAction (isFiniteType_cartanD n) w (omExtWt n j)) =
      fun a => 2 * d i a := fun i => w135c2_omfPOrb_exists_orbit hn2 (π i) (T i) (hT i)
  choose w hw using hex
  have hd0 : ∀ i, d i i0 = ![0, 0, 1, -1] i := by
    intro i
    fin_cases i <;>
      simp [d, π, T, spSgnOn, Equiv.swap_apply_of_ne_of_ne, h01, h0l] <;> omega
  have hd1 : ∀ i, d i i1 = ![1, -1, 0, 0] i := by
    intro i
    fin_cases i <;>
      simp [d, π, T, spSgnOn, Equiv.swap_apply_of_ne_of_ne, h1l, Ne.symm h01] <;> omega
  have hlast : ∀ i, d i ilast = 1 := by
    intro i
    fin_cases i <;>
      simp [d, π, T, spSgnOn, Ne.symm h0l, Ne.symm h1l] <;> omega
  exact ⟨d, w, hw, hd0, hd1, hlast⟩

private theorem w135c2_omfPOrb_four_points {n j : ℕ} (hn : 4 ≤ n) (hj1 : 1 ≤ j)
    (hj : j + 2 ≤ n) :
    ∃ u : Fin 4 → Fin n → ℤ,
      (∀ i, ∃ w, u i = weylAction (isFiniteType_cartanD n) w (omExtWt n j)) ∧
      Function.Injective u ∧ ∀ i, toStdD n (u i) ⟨n - 1, by omega⟩ = 2 := by
  obtain ⟨d, w, hw, hd0, hd1, hlast⟩ := w135c2_omfPOrb_four_data hn hj1 hj
  refine ⟨fun i => weylAction (isFiniteType_cartanD n) (w i) (omExtWt n j),
    fun i => ⟨w i, rfl⟩, ?_, ?_⟩
  · intro i l hil'
    have key := congrArg (toStdD n) hil'
    rw [hw i, hw l] at key
    have hd : d i = d l := by
      funext a
      exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) (congrFun key a)
    have hp := congrArg (fun f => (f ⟨0, by omega⟩, f ⟨1, by omega⟩)) hd
    rw [hd0 i, hd0 l, hd1 i, hd1 l] at hp
    fin_cases i <;> fin_cases l <;> simp_all
  · intro i
    have key := hw i
    show toStdD n (weylAction (isFiniteType_cartanD n) (w i) (omExtWt n j))
      ⟨n - 1, by omega⟩ = 2
    rw [key]
    change 2 * d i ⟨n - 1, by omega⟩ = 2
    rw [hlast i]
    ring

theorem exists_four_orbit_omExtWt_last {n : ℕ} (hn : 4 ≤ n) {j : ℕ} (hj1 : 1 ≤ j)
    (hj : j + 2 ≤ n) :
    ∃ u : Fin 4 → Fin n → ℤ,
      (∀ i, ∃ w, u i = weylAction (isFiniteType_cartanD n) w (omExtWt n j)) ∧
      Function.Injective u ∧ ∀ i, toStdD n (u i) ⟨n - 1, by omega⟩ = 2 :=
  w135c2_omfPOrb_four_points hn hj1 hj

end CFSG.LocalAnalysis.WeakClosure81
