module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusWeyl

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin
open CFSG.StandardType

@[expose] def omExtWt (n j : ℕ) : Fin n → ℤ :=
  omFromStdD2 n (fun a => if a.val ≤ j then 1 else 0)

private theorem c2slomqoe_indicator_shift {j m : ℕ} (hm : m ≠ j) :
    (if m + 1 ≤ j then (1 : ℤ) else 0) = (if m ≤ j then (1 : ℤ) else 0) := by
  by_cases h : m ≤ j
  · have hlt : m < j := lt_of_le_of_ne h hm
    rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]

private theorem c2slomqoe_stdReflD_indicator {n j : ℕ} (hj : j + 3 ≤ n) {k : Fin n}
    (hk : k.val ≠ j) :
    stdReflD n k (fun a => if a.val ≤ j then (1 : ℤ) else 0) =
      fun a => if a.val ≤ j then (1 : ℤ) else 0 := by
  by_cases hlt : k.val + 1 < n
  · rw [stdReflD_of_lt n hlt]
    funext a
    rw [Function.comp_apply]
    by_cases hak : a = k
    · rw [hak, Equiv.swap_apply_left]
      simpa only [Fin.val_mk] using c2slomqoe_indicator_shift (j := j) (m := k.val) hk
    · by_cases hak' : a = ⟨k.val + 1, hlt⟩
      · rw [hak', Equiv.swap_apply_right]
        simpa only [Fin.val_mk] using
          (c2slomqoe_indicator_shift (j := j) (m := k.val) hk).symm
      · rw [Equiv.swap_apply_of_ne_of_ne hak hak']
  · rw [stdReflD_of_not_lt n hlt]
    have hkval : k.val = n - 1 := by have := k.isLt; omega
    let h : Fin n := ⟨n - 2, by omega⟩
    have hkp : (⟨k.val - 1, by omega⟩ : Fin n) = h := Fin.ext (by dsimp only [h]; omega)
    rw [hkp]
    funext a
    by_cases hah : a = h
    · rw [hah, if_pos (Or.inl (by dsimp only [h]; omega)), Equiv.swap_apply_left]
      have hjk : ¬ k.val ≤ j := by omega
      have hjh : ¬ h.val ≤ j := by dsimp only [h]; omega
      rw [if_neg hjk, if_neg hjh]
      ring
    · by_cases hak : a = k
      · rw [hak, if_pos (Or.inr (by omega)), Equiv.swap_apply_right]
        have hjk : ¬ k.val ≤ j := by omega
        have hjh : ¬ h.val ≤ j := by dsimp only [h]; omega
        rw [if_neg hjk, if_neg hjh]
        ring
      · have hif : ¬ (a.val + 2 = n ∨ a.val + 1 = n) := by
          rintro (h' | h')
          · exact hah (Fin.ext (by dsimp only [h]; omega))
          · exact hak (Fin.ext (by omega))
        rw [if_neg hif, Equiv.swap_apply_of_ne_of_ne hah hak, one_mul]

theorem weylAction_simple_omExtWt {n j : ℕ} (hn : 2 ≤ n) (hj : j + 3 ≤ n) {k : Fin n}
    (hk : k.val ≠ j) :
    weylAction (isFiniteType_cartanD n)
        ((coxeterMatrix (isFiniteType_cartanD n)).toCoxeterSystem.simple k) (omExtWt n j) =
      omExtWt n j := by
  rw [show omExtWt n j = omFromStdD2 n (fun a => if a.val ≤ j then (1 : ℤ) else 0) from rfl,
    weylAction_simple_omFromStdD2 hn _ k, c2slomqoe_stdReflD_indicator hj hk]

private theorem c2slomqoe_prod_spSgnOn {n : ℕ} (T : Finset (Fin n)) :
    ∏ a, spSgnOn T a = (-1 : ℤ) ^ T.card := by
  rw [show (∏ a, spSgnOn T a) = ∏ a, (if a ∈ T then (-1 : ℤ) else 1) from
    Finset.prod_congr rfl (fun a _ => rfl)]
  rw [Fintype.prod_ite_mem, Finset.prod_const]

private theorem c2slomqoe_prod_spSgnOn_eq_one {n : ℕ} {T : Finset (Fin n)} (hT : Even T.card) :
    ∏ a, spSgnOn T a = 1 := by
  rw [c2slomqoe_prod_spSgnOn, hT.neg_one_pow]

private theorem c2slomqoe_even_card_pair {α : Type*} [DecidableEq α] {a b : α} (h : a ≠ b) :
    Even ({a, b} : Finset α).card := by
  rw [Finset.card_insert_of_notMem (by simpa using h), Finset.card_singleton]
  exact ⟨1, rfl⟩

private theorem c2slomqoe_spSgnOn_empty {n : ℕ} (x : Fin n) :
    spSgnOn (∅ : Finset (Fin n)) x = 1 := by
  simp [spSgnOn]

private theorem c2slomqoe_spSgnOn_pair_of_ne {n : ℕ} {a b x : Fin n} (hxa : x ≠ a)
    (hxb : x ≠ b) : spSgnOn ({a, b} : Finset (Fin n)) x = 1 := by
  simp only [spSgnOn, Finset.mem_insert, Finset.mem_singleton]
  rw [if_neg]
  exact fun h => h.elim hxa hxb

private theorem c2slomqoe_spSgnOn_pair_left {n : ℕ} {a b : Fin n} (hab : a ≠ b) :
    spSgnOn ({a, b} : Finset (Fin n)) a = -1 := by
  simp [spSgnOn, hab]

private theorem c2slomqoe_spSgnOn_pair_right {n : ℕ} {a b : Fin n} (hab : a ≠ b) :
    spSgnOn ({a, b} : Finset (Fin n)) b = -1 := by
  simp [spSgnOn, hab, Ne.symm hab]

private theorem c2slomqoe_exists_orbit {n j : ℕ} (hn : 2 ≤ n) (π : Equiv.Perm (Fin n))
    (T : Finset (Fin n)) (hT : Even T.card) :
    ∃ w : (coxeterMatrix (isFiniteType_cartanD n)).Group,
      toStdD n (weylAction (isFiniteType_cartanD n) w (omExtWt n j)) =
        fun b => 2 * (spSgnOn T b * (if (π.symm b).val ≤ j then (1 : ℤ) else 0)) := by
  have ht : SpIsSign (fun a => spSgnOn T (π a)) := fun a => spIsSign_spSgnOn T (π a)
  have hprod : ∏ a, spSgnOn T (π a) = 1 := by
    rw [Equiv.prod_comp π (spSgnOn T)]
    exact c2slomqoe_prod_spSgnOn_eq_one hT
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

private theorem c2slomqoe_orbit_four_of_sep {n j : ℕ} (hn : 2 ≤ n)
    {x : (coxeterMatrix (isFiniteType_cartanD n)).Group} {π : Equiv.Perm (Fin n)}
    {s : Fin n → ℤ} (hxr : OmRealizes n x π s)
    (d : Fin 4 → Fin n → ℤ)
    (hex : ∀ i, ∃ w, toStdD n (weylAction (isFiniteType_cartanD n) w (omExtWt n j)) =
      fun a => 2 * d i a)
    (hinj : Function.Injective d)
    (hsep : ∀ i l, (fun a => 2 * d i a) ≠
      fun b => s (π.symm b) * (2 * d l (π.symm b))) :
    ∃ u : Fin 4 → Fin n → ℤ,
      (∀ i, ∃ w, u i = weylAction (isFiniteType_cartanD n) w (omExtWt n j)) ∧
      Function.Injective u ∧ ∀ i l, u i ≠ weylAction (isFiniteType_cartanD n) x (u l) := by
  choose w hw using hex
  refine ⟨fun i => weylAction (isFiniteType_cartanD n) (w i) (omExtWt n j),
    fun i => ⟨w i, rfl⟩, ?_, ?_⟩
  · intro i l hil
    apply hinj
    have key := congrArg (toStdD n) hil
    rw [hw i, hw l] at key
    funext a
    exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) (congrFun key a)
  · intro i l hil
    have key := congrArg (toStdD n) hil
    rw [hw i, hxr (weylAction (isFiniteType_cartanD n) (w l) (omExtWt n j)), hw l] at key
    exact hsep i l key

theorem exists_four_orbit_omExtWt {n j : ℕ} (hn : 5 ≤ n) (hj1 : 1 ≤ j) (hj : j + 3 ≤ n)
    {x : (coxeterMatrix (isFiniteType_cartanD n)).Group} {π : Equiv.Perm (Fin n)}
    {s : Fin n → ℤ} (hxr : OmRealizes n x π s) (hs : SpIsSign s)
    (hx : (π ⟨0, by omega⟩ = ⟨0, by omega⟩ ∧ s ⟨0, by omega⟩ = -1) ∨
      (π ⟨0, by omega⟩ = ⟨1, by omega⟩ ∧ π ⟨1, by omega⟩ = ⟨0, by omega⟩ ∧
        s ⟨0, by omega⟩ = s ⟨1, by omega⟩)) :
    ∃ u : Fin 4 → Fin n → ℤ,
      (∀ i, ∃ w, u i = weylAction (isFiniteType_cartanD n) w (omExtWt n j)) ∧
      Function.Injective u ∧ ∀ i l, u i ≠ weylAction (isFiniteType_cartanD n) x (u l) := by
  have hn2 : 2 ≤ n := by omega
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  let jj : Fin n := ⟨j + 1, by omega⟩
  let ilast : Fin n := ⟨n - 1, by omega⟩
  have h01 : i0 ≠ i1 := Fin.ne_of_val_ne (by dsimp only [i0, i1]; omega)
  have h0j : i0 ≠ jj := Fin.ne_of_val_ne (by dsimp only [i0, jj]; omega)
  have h0l : i0 ≠ ilast := Fin.ne_of_val_ne (by dsimp only [i0, ilast]; omega)
  have h1j : i1 ≠ jj := Fin.ne_of_val_ne (by dsimp only [i1, jj]; omega)
  have h1l : i1 ≠ ilast := Fin.ne_of_val_ne (by dsimp only [i1, ilast]; omega)
  have hjl : jj ≠ ilast := Fin.ne_of_val_ne (by dsimp only [jj, ilast]; omega)
  have hjle : ¬ j + 1 ≤ j := by omega
  let σ : Equiv.Perm (Fin n) := Equiv.swap i1 jj
  have hσ : σ.symm = σ := by simp only [σ]; exact Equiv.symm_swap i1 jj
  have hσ0 : σ.symm i0 = i0 := by rw [hσ]; exact Equiv.swap_apply_of_ne_of_ne h01 h0j
  have hσ1 : σ.symm i1 = jj := by rw [hσ]; exact Equiv.swap_apply_left i1 jj
  have hσj : σ.symm jj = i1 := by rw [hσ]; exact Equiv.swap_apply_right i1 jj
  have hσl : σ.symm ilast = ilast := by
    rw [hσ]; exact Equiv.swap_apply_of_ne_of_ne (Ne.symm h1l) (Ne.symm hjl)
  rcases hx with ⟨hπ0, hs0⟩ | ⟨hπ0, hπ1, hs01⟩
  · have hπ0' : π i0 = i0 := hπ0
    have hs0' : s i0 = -1 := hs0
    have hsymi : π.symm i0 = i0 := (Equiv.symm_apply_eq π).2 hπ0'.symm
    let πA : Fin 4 → Equiv.Perm (Fin n) := ![Equiv.refl (Fin n), Equiv.refl (Fin n), σ, σ]
    let TA : Fin 4 → Finset (Fin n) := ![∅, {i1, ilast}, ∅, {jj, ilast}]
    let dA : Fin 4 → Fin n → ℤ := fun i b => spSgnOn (TA i) b *
      (if ((πA i).symm b).val ≤ j then (1 : ℤ) else 0)
    have hTA : ∀ i, Even (TA i).card := by
      intro i
      fin_cases i <;> simp only [TA]
      · exact ⟨0, rfl⟩
      · exact c2slomqoe_even_card_pair h1l
      · exact ⟨0, rfl⟩
      · exact c2slomqoe_even_card_pair hjl
    have hex : ∀ i, ∃ w, toStdD n (weylAction (isFiniteType_cartanD n) w (omExtWt n j)) =
        fun a => 2 * dA i a := fun i => c2slomqoe_exists_orbit hn2 (πA i) (TA i) (hTA i)
    have hd0 : ∀ i, dA i i0 = 1 := by
      intro i
      fin_cases i <;> simp [dA, πA, TA, i0, i1, jj, ilast, c2slomqoe_spSgnOn_empty,
        c2slomqoe_spSgnOn_pair_of_ne, hσ0, h01, h0j, h0l]
    have hA1v : ∀ i, dA i i1 = ![1, -1, 0, 0] i := by
      intro i
      fin_cases i <;> simp [dA, πA, TA, i0, i1, jj, ilast, c2slomqoe_spSgnOn_empty,
        c2slomqoe_spSgnOn_pair_of_ne, c2slomqoe_spSgnOn_pair_left, hσ1, hσj,
        h01, h1j, h1l, hjl, hj1, hjle]
    have hAjv : ∀ i, dA i jj = ![0, 0, 1, -1] i := by
      intro i
      fin_cases i <;> simp [dA, πA, TA, i0, i1, jj, ilast, c2slomqoe_spSgnOn_empty,
        c2slomqoe_spSgnOn_pair_of_ne, c2slomqoe_spSgnOn_pair_left, hσ1, hσj,
        h01, h1j, h1l, hjl, hj1, hjle]
    have hinj : Function.Injective dA := by
      intro i l hil
      have hsig : (dA i i1, dA i jj) = (dA l i1, dA l jj) := by rw [hil]
      rw [hA1v i, hA1v l, hAjv i, hAjv l] at hsig
      fin_cases i <;> fin_cases l <;> simp_all
    have hsep : ∀ i l, (fun a => 2 * dA i a) ≠
        fun b => s (π.symm b) * (2 * dA l (π.symm b)) := by
      intro i l hcontra
      have h0 := congrFun hcontra i0
      rw [hsymi, hs0', hd0 i, hd0 l] at h0
      norm_num at h0
    exact c2slomqoe_orbit_four_of_sep hn2 hxr dA hex hinj hsep
  · have hπ1' : π i1 = i0 := hπ1
    have hsymi : π.symm i0 = i1 := (Equiv.symm_apply_eq π).2 hπ1'.symm
    let πB : Fin 4 → Equiv.Perm (Fin n) := ![σ, σ, σ, σ]
    let TB : Fin 4 → Finset (Fin n) := ![∅, {i0, ilast}, {jj, ilast}, {i0, jj}]
    let dB : Fin 4 → Fin n → ℤ := fun i b => spSgnOn (TB i) b *
      (if ((πB i).symm b).val ≤ j then (1 : ℤ) else 0)
    have hTB : ∀ i, Even (TB i).card := by
      intro i
      fin_cases i <;> simp only [TB]
      · exact ⟨0, rfl⟩
      · exact c2slomqoe_even_card_pair h0l
      · exact c2slomqoe_even_card_pair hjl
      · exact c2slomqoe_even_card_pair h0j
    have hex : ∀ i, ∃ w, toStdD n (weylAction (isFiniteType_cartanD n) w (omExtWt n j)) =
        fun a => 2 * dB i a := fun i => c2slomqoe_exists_orbit hn2 (πB i) (TB i) (hTB i)
    have hB0v : ∀ i, dB i i0 = ![1, -1, 1, -1] i := by
      intro i
      fin_cases i <;> simp [dB, πB, TB, i0, i1, jj, ilast, c2slomqoe_spSgnOn_empty,
        c2slomqoe_spSgnOn_pair_of_ne, c2slomqoe_spSgnOn_pair_left, hσ0,
        h01, h0j, h0l, h1l, hjl]
    have hBjv : ∀ i, dB i jj = ![1, 1, -1, -1] i := by
      intro i
      fin_cases i <;> simp [dB, πB, TB, i0, i1, jj, ilast, c2slomqoe_spSgnOn_empty,
        c2slomqoe_spSgnOn_pair_of_ne, c2slomqoe_spSgnOn_pair_left,
        c2slomqoe_spSgnOn_pair_right, hσj, h01, h0j, h0l, h1l, hjl, hj1, hjle]
    have hB1v : ∀ i, dB i i1 = 0 := by
      intro i
      fin_cases i <;> simp [dB, πB, TB, i0, i1, jj, ilast, hσ1, h1j, h1l, hjle]
    have hinj : Function.Injective dB := by
      intro i l hil
      have hsig : (dB i i0, dB i jj) = (dB l i0, dB l jj) := by rw [hil]
      rw [hB0v i, hB0v l, hBjv i, hBjv l] at hsig
      fin_cases i <;> fin_cases l <;> simp_all
    have hsep : ∀ i l, (fun a => 2 * dB i a) ≠
        fun b => s (π.symm b) * (2 * dB l (π.symm b)) := by
      intro i l hcontra
      have h0 := congrFun hcontra i0
      rw [hsymi, hB1v l] at h0
      have hne : dB i i0 ≠ 0 := by
        rw [hB0v i]; fin_cases i <;> norm_num
      simp only [mul_zero] at h0
      exact hne (by omega)
    exact c2slomqoe_orbit_four_of_sep hn2 hxr dB hex hinj hsep

end CFSG.LocalAnalysis.WeakClosure81
