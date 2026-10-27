module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCensusInsideGrow

public section

namespace CFSG.StandardType.GGQ2Frame.ExcRaw

variable {m : Fin 6} {T : Chk.Tabs}

private theorem ofMask_or (a b : ℕ) :
    ofMask m (a ||| b) = ofMask m a ∪ ofMask m b := by
  ext t
  simp [ofMask, Nat.testBit_or]

private theorem ofMask_one (i : Root m) :
    ofMask m (1 <<< i.val) = {i} := by
  ext t
  rw [mem_ofMask, Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_eq,
    Finset.mem_singleton, Fin.ext_iff]
  exact eq_comm

private theorem ofMask_imgN_or (u : Root m) (a b : ℕ) :
    ofMask m (Chk.imgN T (nroots m) u (a ||| b)) =
      ofMask m (Chk.imgN T (nroots m) u a) ∪
        ofMask m (Chk.imgN T (nroots m) u b) := by
  ext t
  simp only [Finset.mem_union, mem_ofMask_imgN, ofMask_or]
  exact ⟨fun ⟨s, hs, hst⟩ => hs.elim (fun h => Or.inl ⟨s, h, hst⟩)
      (fun h => Or.inr ⟨s, h, hst⟩),
    fun h => h.elim (fun ⟨s, hs, hst⟩ => ⟨s, Or.inl hs, hst⟩)
      (fun ⟨s, hs, hst⟩ => ⟨s, Or.inr hs, hst⟩)⟩

private theorem imgN_or (hT : Chk.tabsOK m T = true) (u : Root m) (a b : ℕ) :
    Chk.imgN T (nroots m) u (a ||| b) =
      Chk.imgN T (nroots m) u a ||| Chk.imgN T (nroots m) u b := by
  apply Nat.eq_of_testBit_eq
  intro t
  by_cases ht : t < nroots m
  · have h1 : ((⟨t, ht⟩ : Root m) ∈ ofMask m (Chk.imgN T (nroots m) u (a ||| b))) ↔
        ((⟨t, ht⟩ : Root m) ∈ ofMask m (Chk.imgN T (nroots m) u a) ∪
          ofMask m (Chk.imgN T (nroots m) u b)) := by
      rw [ofMask_imgN_or u a b]
    have h2 : ((⟨t, ht⟩ : Root m) ∈ ofMask m
          (Chk.imgN T (nroots m) u a ||| Chk.imgN T (nroots m) u b)) ↔
        ((⟨t, ht⟩ : Root m) ∈ ofMask m (Chk.imgN T (nroots m) u a) ∪
          ofMask m (Chk.imgN T (nroots m) u b)) := by
      rw [ofMask_or]
    rw [Bool.eq_iff_iff, ← mem_ofMask (t := ⟨t, ht⟩), ← mem_ofMask (t := ⟨t, ht⟩)]
    exact h1.trans h2.symm
  · have hle : nroots m ≤ t := Nat.le_of_not_lt ht
    have hpow : 2 ^ nroots m ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) hle
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (imgN_lt hT u (a ||| b)) hpow),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le
        (Nat.or_lt_two_pow (imgN_lt hT u a) (imgN_lt hT u b)) hpow)]

private theorem imgN_one (hT : Chk.tabsOK m T = true) (u j : Root m) :
    Chk.imgN T (nroots m) u (1 <<< j.val) =
      1 <<< (T.rt[u.val]!)[j.val]! := by
  apply Nat.eq_of_testBit_eq
  intro t
  by_cases ht : t < nroots m
  · have h1 : ((⟨t, ht⟩ : Root m) ∈ ofMask m (Chk.imgN T (nroots m) u (1 <<< j.val))) ↔
        ((⟨t, ht⟩ : Root m) ∈ ofMask m (1 <<< (T.rt[u.val]!)[j.val]!)) := by
      rw [mem_ofMask_imgN]
      constructor
      · rintro ⟨s, hs, hst⟩
        rw [mem_ofMask, Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_eq] at hs
        rw [mem_ofMask, Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_eq]
        have hsj : s = j := Fin.ext hs.symm
        rw [hsj] at hst
        exact hst
      · intro h
        refine ⟨j, ?_, ?_⟩
        · rw [mem_ofMask, Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_eq]
        · rwa [mem_ofMask, Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_eq] at h
    rw [Bool.eq_iff_iff, ← mem_ofMask (t := ⟨t, ht⟩), ← mem_ofMask (t := ⟨t, ht⟩)]
    exact h1
  · have hle : nroots m ≤ t := Nat.le_of_not_lt ht
    have hpow : 2 ^ nroots m ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) hle
    have hone : 1 <<< (T.rt[u.val]!)[j.val]! < 2 ^ nroots m := by
      rw [Nat.one_shiftLeft]
      exact Nat.pow_lt_pow_right (by norm_num) (tabsOK_rt_lt hT u j)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (imgN_lt hT u (1 <<< j.val)) hpow),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hone hpow)]

private theorem le_cent_of_vanish {U : Submodule (ZMod 3) (V m)} {Y : Finset (Root m)}
    (h : ∀ i ∈ Y, Vanish m U i) : U ≤ cent m Y := by
  intro u hu
  simp only [cent, Submodule.mem_iInf, LinearMap.mem_ker]
  exact fun i hi => h i hi u hu

end CFSG.StandardType.GGQ2Frame.ExcRaw
