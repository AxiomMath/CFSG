module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusLat

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.StandardType

private lemma c2slomqmep_injective_four {α : Type*} {v0 v1 v2 v3 : α}
    (h01 : v0 ≠ v1) (h02 : v0 ≠ v2) (h03 : v0 ≠ v3)
    (h12 : v1 ≠ v2) (h13 : v1 ≠ v3) (h23 : v2 ≠ v3) :
    Function.Injective ![v0, v1, v2, v3] := by
  intro i l h
  fin_cases i <;> fin_cases l <;> simp_all

private lemma c2slomqmep_act_apply {m h : ℕ} (π : Equiv.Perm (Fin 3)) (s : Fin 3 → ℤ)
    (v : Fin 3 → ZMod m) (d : ZMod h) :
    omqMinusAct π s ((v, d) : OmqMinusLat 3 m h) =
      (fun b => ((s (π.symm b) : ℤ) : ZMod m) * v (π.symm b),
        ((∏ a, s a : ℤ) : ZMod h) * d) := by
  unfold omqMinusAct
  refine Prod.ext (funext fun b => ?_) rfl
  rfl

private lemma c2slomqmep_spIsSign_triple (t : Fin 3 → ℤ) (h0 : t 0 = 1 ∨ t 0 = -1)
    (h1 : t 1 = 1 ∨ t 1 = -1) (h2 : t 2 = 1 ∨ t 2 = -1) : SpIsSign t := by
  intro c
  fin_cases c <;> assumption

theorem omq_minus_exists_exc_points_ne {m h : ℕ} (hm : Odd m) {a b : ZMod m} (ha : a ≠ 0)
    (hba : b ≠ a) (hbna : b ≠ -a) (e : ZMod h) {π : Equiv.Perm (Fin 3)} {s : Fin 3 → ℤ}
    (hA : (∀ c, s c = 1) ∧ π * π = 1 ∧ π 0 = 1 ∧ π 1 = 0) :
    ∃ u : Fin 4 → OmqMinusLat 3 m h, Function.Injective u ∧
      (∀ i, OmqMinusInOrbit (((![b, a, a] : Fin 3 → ZMod m), e) : OmqMinusLat 3 m h) (u i)) ∧
      ∀ i i', u i ≠ omqMinusAct π s (u i') := by
  classical
  have hπs : π.symm 0 = 1 := by rw [← hA.2.2.2, Equiv.symm_apply_apply]
  have hs1 : s 1 = 1 := hA.1 1
  have hximg : ∀ u' : OmqMinusLat 3 m h,
      (omqMinusAct π s u').1 0 = u'.1 1 := by
    intro u'
    show ((s (π.symm 0) : ℤ) : ZMod m) * u'.1 (π.symm 0) = u'.1 1
    rw [hπs, hs1, Int.cast_one, one_mul]
  by_cases hb0 : b = 0
  · subst b
    have ha_neg : a ≠ -a := ZMod.ne_neg_self hm ha
    let base : OmqMinusLat 3 m h := ((![0, a, a] : Fin 3 → ZMod m), e)
    let v0 : OmqMinusLat 3 m h := ((![a, 0, a] : Fin 3 → ZMod m), e)
    let v1 : OmqMinusLat 3 m h := ((![-a, 0, a] : Fin 3 → ZMod m), e)
    let v2 : OmqMinusLat 3 m h := ((![-a, 0, -a] : Fin 3 → ZMod m), e)
    let v3 : OmqMinusLat 3 m h := ((![a, 0, -a] : Fin 3 → ZMod m), e)
    have h01 : v0 ≠ v1 := by
      intro hh
      have hc : a = -a := by
        have h' := congrArg (fun p : OmqMinusLat 3 m h => p.1 0) hh
        simpa [v0, v1] using h'
      exact ha_neg hc
    have h02 : v0 ≠ v2 := by
      intro hh
      have hc : a = -a := by
        have h' := congrArg (fun p : OmqMinusLat 3 m h => p.1 0) hh
        simpa [v0, v2] using h'
      exact ha_neg hc
    have h03 : v0 ≠ v3 := by
      intro hh
      have hc : a = -a := by
        have h' := congrArg (fun p : OmqMinusLat 3 m h => p.1 2) hh
        simpa [v0, v3] using h'
      exact ha_neg hc
    have h12 : v1 ≠ v2 := by
      intro hh
      have hc : a = -a := by
        have h' := congrArg (fun p : OmqMinusLat 3 m h => p.1 2) hh
        simpa [v1, v2] using h'
      exact ha_neg hc
    have h13 : v1 ≠ v3 := by
      intro hh
      have hc : -a = a := by
        have h' := congrArg (fun p : OmqMinusLat 3 m h => p.1 0) hh
        simpa [v1, v3] using h'
      exact ha_neg hc.symm
    have h23 : v2 ≠ v3 := by
      intro hh
      have hc : -a = a := by
        have h' := congrArg (fun p : OmqMinusLat 3 m h => p.1 0) hh
        simpa [v2, v3] using h'
      exact ha_neg hc.symm
    have o0 : OmqMinusInOrbit base v0 := by
      refine ⟨Equiv.swap 0 1, ![1, 1, 1],
        c2slomqmep_spIsSign_triple _ (Or.inl rfl) (Or.inl rfl) (Or.inl rfl), ?_⟩
      dsimp only [base, v0]
      rw [c2slomqmep_act_apply]
      refine Prod.ext (funext fun i => ?_) ?_
      · fin_cases i <;> simp [Equiv.swap_apply_def]
      · simp [Fin.prod_univ_three]
    have o1 : OmqMinusInOrbit base v1 := by
      refine ⟨Equiv.swap 0 1, ![-1, -1, 1],
        c2slomqmep_spIsSign_triple _ (Or.inr rfl) (Or.inr rfl) (Or.inl rfl), ?_⟩
      dsimp only [base, v1]
      rw [c2slomqmep_act_apply]
      refine Prod.ext (funext fun i => ?_) ?_
      · fin_cases i <;> simp [Equiv.swap_apply_def]
      · simp [Fin.prod_univ_three]
    have o2 : OmqMinusInOrbit base v2 := by
      refine ⟨Equiv.swap 0 1, ![1, -1, -1],
        c2slomqmep_spIsSign_triple _ (Or.inl rfl) (Or.inr rfl) (Or.inr rfl), ?_⟩
      dsimp only [base, v2]
      rw [c2slomqmep_act_apply]
      refine Prod.ext (funext fun i => ?_) ?_
      · fin_cases i <;> simp [Equiv.swap_apply_def]
      · simp [Fin.prod_univ_three]
    have o3 : OmqMinusInOrbit base v3 := by
      refine ⟨Equiv.swap 0 1, ![-1, 1, -1],
        c2slomqmep_spIsSign_triple _ (Or.inr rfl) (Or.inl rfl) (Or.inr rfl), ?_⟩
      dsimp only [base, v3]
      rw [c2slomqmep_act_apply]
      refine Prod.ext (funext fun i => ?_) ?_
      · fin_cases i <;> simp [Equiv.swap_apply_def]
      · simp [Fin.prod_univ_three]
    refine ⟨![v0, v1, v2, v3],
      c2slomqmep_injective_four h01 h02 h03 h12 h13 h23, ?_, ?_⟩
    · intro i
      fin_cases i
      · simpa using o0
      · simpa using o1
      · simpa using o2
      · simpa using o3
    · intro i i' hh
      have hc := congrArg (fun p : OmqMinusLat 3 m h => p.1 0) hh
      rw [hximg] at hc
      fin_cases i <;> fin_cases i' <;> simp [v0, v1, v2, v3] at hc <;>
        first | exact ha hc | exact (neg_ne_zero.mpr ha) hc
  · have hbne : b ≠ 0 := hb0
    have hb_neg : b ≠ -b := ZMod.ne_neg_self hm hbne
    have ha_neg : a ≠ -a := ZMod.ne_neg_self hm ha
    let base : OmqMinusLat 3 m h := ((![b, a, a] : Fin 3 → ZMod m), e)
    let v0 : OmqMinusLat 3 m h := ((![b, a, a] : Fin 3 → ZMod m), e)
    let v1 : OmqMinusLat 3 m h := ((![b, -a, -a] : Fin 3 → ZMod m), e)
    let v2 : OmqMinusLat 3 m h := ((![-b, a, -a] : Fin 3 → ZMod m), e)
    let v3 : OmqMinusLat 3 m h := ((![-b, -a, a] : Fin 3 → ZMod m), e)
    have h01 : v0 ≠ v1 := by
      intro hh
      have hc : a = -a := by
        have h' := congrArg (fun p : OmqMinusLat 3 m h => p.1 1) hh
        simpa [v0, v1] using h'
      exact ha_neg hc
    have h02 : v0 ≠ v2 := by
      intro hh
      have hc : b = -b := by
        have h' := congrArg (fun p : OmqMinusLat 3 m h => p.1 0) hh
        simpa [v0, v2] using h'
      exact hb_neg hc
    have h03 : v0 ≠ v3 := by
      intro hh
      have hc : b = -b := by
        have h' := congrArg (fun p : OmqMinusLat 3 m h => p.1 0) hh
        simpa [v0, v3] using h'
      exact hb_neg hc
    have h12 : v1 ≠ v2 := by
      intro hh
      have hc : b = -b := by
        have h' := congrArg (fun p : OmqMinusLat 3 m h => p.1 0) hh
        simpa [v1, v2] using h'
      exact hb_neg hc
    have h13 : v1 ≠ v3 := by
      intro hh
      have hc : b = -b := by
        have h' := congrArg (fun p : OmqMinusLat 3 m h => p.1 0) hh
        simpa [v1, v3] using h'
      exact hb_neg hc
    have h23 : v2 ≠ v3 := by
      intro hh
      have hc : -a = a := by
        have h' := congrArg (fun p : OmqMinusLat 3 m h => p.1 2) hh
        simpa [v2, v3] using h'
      exact ha_neg hc.symm
    have o0 : OmqMinusInOrbit base v0 := by
      refine ⟨Equiv.refl (Fin 3), ![1, 1, 1],
        c2slomqmep_spIsSign_triple _ (Or.inl rfl) (Or.inl rfl) (Or.inl rfl), ?_⟩
      dsimp only [base, v0]
      rw [c2slomqmep_act_apply]
      refine Prod.ext (funext fun i => ?_) ?_
      · fin_cases i <;> simp
      · simp [Fin.prod_univ_three]
    have o1 : OmqMinusInOrbit base v1 := by
      refine ⟨Equiv.refl (Fin 3), ![1, -1, -1],
        c2slomqmep_spIsSign_triple _ (Or.inl rfl) (Or.inr rfl) (Or.inr rfl), ?_⟩
      dsimp only [base, v1]
      rw [c2slomqmep_act_apply]
      refine Prod.ext (funext fun i => ?_) ?_
      · fin_cases i <;> simp
      · simp [Fin.prod_univ_three]
    have o2 : OmqMinusInOrbit base v2 := by
      refine ⟨Equiv.refl (Fin 3), ![-1, 1, -1],
        c2slomqmep_spIsSign_triple _ (Or.inr rfl) (Or.inl rfl) (Or.inr rfl), ?_⟩
      dsimp only [base, v2]
      rw [c2slomqmep_act_apply]
      refine Prod.ext (funext fun i => ?_) ?_
      · fin_cases i <;> simp
      · simp [Fin.prod_univ_three]
    have o3 : OmqMinusInOrbit base v3 := by
      refine ⟨Equiv.refl (Fin 3), ![-1, -1, 1],
        c2slomqmep_spIsSign_triple _ (Or.inr rfl) (Or.inr rfl) (Or.inl rfl), ?_⟩
      dsimp only [base, v3]
      rw [c2slomqmep_act_apply]
      refine Prod.ext (funext fun i => ?_) ?_
      · fin_cases i <;> simp
      · simp [Fin.prod_univ_three]
    refine ⟨![v0, v1, v2, v3],
      c2slomqmep_injective_four h01 h02 h03 h12 h13 h23, ?_, ?_⟩
    · intro i
      fin_cases i
      · simpa using o0
      · simpa using o1
      · simpa using o2
      · simpa using o3
    · intro i i' hh
      have hc := congrArg (fun p : OmqMinusLat 3 m h => p.1 0) hh
      rw [hximg] at hc
      have hb_a : -b ≠ a := by
        intro hh'
        apply hbna
        have h' : -(-b) = -a := congrArg Neg.neg hh'
        rwa [neg_neg] at h'
      have hb_na : -b ≠ -a := by
        intro hh'
        apply hba
        have h' : -(-b) = -(-a) := congrArg Neg.neg hh'
        rwa [neg_neg, neg_neg] at h'
      fin_cases i <;> fin_cases i' <;> simp [v0, v1, v2, v3] at hc <;>
        first | exact hba hc | exact hbna hc | exact hb_a hc | exact hb_na hc

theorem omq_minus_exists_exc_points_single {m h : ℕ} (hm : Odd m) (hh : Odd h) {p : ZMod m}
    (hp : p ≠ 0) {e : ZMod h} (he : e ≠ 0) {π : Equiv.Perm (Fin 3)} {s : Fin 3 → ℤ}
    (hA : (∀ c, s c = 1) ∧ π * π = 1 ∧ π 0 = 1 ∧ π 1 = 0) :
    ∃ u : Fin 4 → OmqMinusLat 3 m h, Function.Injective u ∧
      (∀ i, OmqMinusInOrbit (((![p, 0, 0] : Fin 3 → ZMod m), e) : OmqMinusLat 3 m h) (u i)) ∧
      ∀ i i', u i ≠ omqMinusAct π s (u i') := by
  classical
  have hπs : π.symm 0 = 1 := by rw [← hA.2.2.2, Equiv.symm_apply_apply]
  have hs1 : s 1 = 1 := hA.1 1
  have hximg : ∀ u' : OmqMinusLat 3 m h,
      (omqMinusAct π s u').1 0 = u'.1 1 := by
    intro u'
    show ((s (π.symm 0) : ℤ) : ZMod m) * u'.1 (π.symm 0) = u'.1 1
    rw [hπs, hs1, Int.cast_one, one_mul]
  have hp_neg : p ≠ -p := ZMod.ne_neg_self hm hp
  have he_neg : e ≠ -e := ZMod.ne_neg_self hh he
  let base : OmqMinusLat 3 m h := ((![p, 0, 0] : Fin 3 → ZMod m), e)
  let v0 : OmqMinusLat 3 m h := ((![p, 0, 0] : Fin 3 → ZMod m), e)
  let v1 : OmqMinusLat 3 m h := ((![-p, 0, 0] : Fin 3 → ZMod m), -e)
  let v2 : OmqMinusLat 3 m h := ((![-p, 0, 0] : Fin 3 → ZMod m), e)
  let v3 : OmqMinusLat 3 m h := ((![p, 0, 0] : Fin 3 → ZMod m), -e)
  have h01 : v0 ≠ v1 := by
    intro hh
    have hc : p = -p := by
      have h' := congrArg (fun p : OmqMinusLat 3 m h => p.1 0) hh
      simpa [v0, v1] using h'
    exact hp_neg hc
  have h02 : v0 ≠ v2 := by
    intro hh
    have hc : p = -p := by
      have h' := congrArg (fun p : OmqMinusLat 3 m h => p.1 0) hh
      simpa [v0, v2] using h'
    exact hp_neg hc
  have h03 : v0 ≠ v3 := by
    intro hh
    have hc : e = -e := by
      have h' := congrArg (fun p : OmqMinusLat 3 m h => p.2) hh
      simpa [v0, v3] using h'
    exact he_neg hc
  have h12 : v1 ≠ v2 := by
    intro hh
    have hc : -e = e := by
      have h' := congrArg (fun p : OmqMinusLat 3 m h => p.2) hh
      simpa [v1, v2] using h'
    exact he_neg hc.symm
  have h13 : v1 ≠ v3 := by
    intro hh
    have hc : -p = p := by
      have h' := congrArg (fun p : OmqMinusLat 3 m h => p.1 0) hh
      simpa [v1, v3] using h'
    exact hp_neg hc.symm
  have h23 : v2 ≠ v3 := by
    intro hh
    have hc : -p = p := by
      have h' := congrArg (fun p : OmqMinusLat 3 m h => p.1 0) hh
      simpa [v2, v3] using h'
    exact hp_neg hc.symm
  have o0 : OmqMinusInOrbit base v0 := by
    refine ⟨Equiv.refl (Fin 3), ![1, 1, 1],
      c2slomqmep_spIsSign_triple _ (Or.inl rfl) (Or.inl rfl) (Or.inl rfl), ?_⟩
    dsimp only [base, v0]
    rw [c2slomqmep_act_apply]
    refine Prod.ext (funext fun i => ?_) ?_
    · fin_cases i <;> simp
    · simp [Fin.prod_univ_three]
  have o1 : OmqMinusInOrbit base v1 := by
    refine ⟨Equiv.refl (Fin 3), ![-1, 1, 1],
      c2slomqmep_spIsSign_triple _ (Or.inr rfl) (Or.inl rfl) (Or.inl rfl), ?_⟩
    dsimp only [base, v1]
    rw [c2slomqmep_act_apply]
    refine Prod.ext (funext fun i => ?_) ?_
    · fin_cases i <;> simp
    · simp [Fin.prod_univ_three]
  have o2 : OmqMinusInOrbit base v2 := by
    refine ⟨Equiv.refl (Fin 3), ![-1, -1, 1],
      c2slomqmep_spIsSign_triple _ (Or.inr rfl) (Or.inr rfl) (Or.inl rfl), ?_⟩
    dsimp only [base, v2]
    rw [c2slomqmep_act_apply]
    refine Prod.ext (funext fun i => ?_) ?_
    · fin_cases i <;> simp
    · simp [Fin.prod_univ_three]
  have o3 : OmqMinusInOrbit base v3 := by
    refine ⟨Equiv.refl (Fin 3), ![1, -1, 1],
      c2slomqmep_spIsSign_triple _ (Or.inl rfl) (Or.inr rfl) (Or.inl rfl), ?_⟩
    dsimp only [base, v3]
    rw [c2slomqmep_act_apply]
    refine Prod.ext (funext fun i => ?_) ?_
    · fin_cases i <;> simp
    · simp [Fin.prod_univ_three]
  refine ⟨![v0, v1, v2, v3],
    c2slomqmep_injective_four h01 h02 h03 h12 h13 h23, ?_, ?_⟩
  · intro i
    fin_cases i
    · simpa using o0
    · simpa using o1
    · simpa using o2
    · simpa using o3
  · intro i i' hh
    have hc := congrArg (fun p : OmqMinusLat 3 m h => p.1 0) hh
    rw [hximg] at hc
    fin_cases i <;> fin_cases i' <;> simp [v0, v1, v2, v3] at hc <;>
      first | exact hp hc | exact (neg_ne_zero.mpr hp) hc

end CFSG.LocalAnalysis.WeakClosure81
