module

public import CFSG.LocalAnalysis.StandardType.GGSpJoinCoxeterCard

public section

namespace CFSG.StandardType.SpFrame

open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem CoxeterSystem
  CFSG.LieType.Universal.Symplectic

theorem simple_mul_self_C (r : ℕ) (i : Fin r) :
    (coxeterMatrix (isFiniteType_cartanC r)).toCoxeterSystem.simple i *
      (coxeterMatrix (isFiniteType_cartanC r)).toCoxeterSystem.simple i = 1 :=
  (coxeterMatrix (isFiniteType_cartanC r)).toCoxeterSystem.simple_mul_simple_self i

section UniqueAux

private theorem spFrame_toStd_single_of_lt {m : ℕ} {k : Fin m} (h : k.val + 1 < m) :
    toStd m (Pi.single k 1) = Pi.single k 1 - Pi.single ⟨k.val + 1, h⟩ 1 := by
  funext a
  simp only [toStd, Pi.sub_apply, Pi.single_apply, Fin.ext_iff]
  split_ifs <;> omega

private theorem spFrame_toStd_single_of_not_lt {m : ℕ} {k : Fin m} (h : ¬ k.val + 1 < m) :
    toStd m (Pi.single k 1) = 2 • Pi.single k 1 := by
  funext a
  simp only [toStd, Pi.smul_apply, Pi.single_apply, Fin.ext_iff, nsmul_eq_mul, Nat.cast_ofNat]
  split_ifs <;> omega

private theorem spFrame_toStd_single_of_lt_apply {m : ℕ} {k a : Fin m} (h : k.val + 1 < m) :
    toStd m (Pi.single k 1) a =
      (if a = k then (1 : ℤ) else 0) - (if a = ⟨k.val + 1, h⟩ then (1 : ℤ) else 0) := by
  rw [spFrame_toStd_single_of_lt h, Pi.sub_apply, Pi.single_apply, Pi.single_apply]

private theorem spFrame_toStd_single_of_not_lt_apply {m : ℕ} {k a : Fin m}
    (h : ¬ k.val + 1 < m) :
    toStd m (Pi.single k 1) a = if a = k then (2 : ℤ) else 0 := by
  rw [spFrame_toStd_single_of_not_lt h, Pi.smul_apply]
  split_ifs with hak
  · simp [hak]
  · simp [hak]

private theorem spFrame_toStd_single_of_lt_self {m : ℕ} {k : Fin m} (h : k.val + 1 < m) :
    toStd m (Pi.single k 1) k = 1 := by
  rw [spFrame_toStd_single_of_lt_apply h, if_pos rfl]
  have hne : k ≠ (⟨k.val + 1, h⟩ : Fin m) := fun e => by
    have := congrArg Fin.val e
    simp only [Fin.val_mk] at this
    omega
  rw [if_neg hne, sub_zero]

private theorem spFrame_toStd_single_of_not_lt_self {m : ℕ} {k : Fin m}
    (h : ¬ k.val + 1 < m) :
    toStd m (Pi.single k 1) k = 2 := by
  rw [spFrame_toStd_single_of_not_lt_apply h, if_pos rfl]

end UniqueAux

theorem _root_.CFSG.StandardType.SpRealizes.unique {m : ℕ}
    {w : (coxeterMatrix (isFiniteType_cartanC m)).Group} {π π' : Equiv.Perm (Fin m)}
    {s s' : Fin m → ℤ} (hs : SpIsSign s) (hs' : SpIsSign s') (h : SpRealizes m w π s)
    (h' : SpRealizes m w π' s') : π = π' ∧ s = s' := by
  have hkey : ∀ (c b : Fin m),
      s (π.symm b) * toStd m (Pi.single c 1) (π.symm b) =
        s' (π'.symm b) * toStd m (Pi.single c 1) (π'.symm b) := fun c b =>
    congrFun ((h (Pi.single c 1)).symm.trans (h' (Pi.single c 1))) b
  have key : ∀ d : ℕ, ∀ c : Fin m, c.val + d + 1 = m → π c = π' c ∧ s c = s' c := by
    intro d
    induction d with
    | zero =>
      intro c hc
      have hlt : ¬ c.val + 1 < m := by omega
      have hbase := hkey c (π c)
      rw [Equiv.symm_apply_apply, spFrame_toStd_single_of_not_lt_self hlt] at hbase
      rw [spFrame_toStd_single_of_not_lt_apply hlt] at hbase
      have ha : π'.symm (π c) = c := by
        by_contra hne
        rw [if_neg hne, mul_zero] at hbase
        have hsc : s c = 0 := by omega
        rcases hs c with h1 | h1 <;> omega
      have hπ : π c = π' c := by
        have := congrArg π' ha
        simpa using this
      have hsc : s c = s' c := by
        rw [ha, if_pos rfl] at hbase
        omega
      exact ⟨hπ, hsc⟩
    | succ d ih =>
      intro c hc
      have hlt : c.val + 1 < m := by omega
      let c' : Fin m := ⟨c.val + 1, hlt⟩
      have hPc' : π c' = π' c' ∧ s c' = s' c' := ih c' (by simp only [c']; omega)
      have hcne : c ≠ c' := by
        intro hh
        have := congrArg Fin.val hh
        simp only [c'] at this
        omega
      have hcne' : c ≠ (⟨c.val + 1, hlt⟩ : Fin m) := hcne
      have hbase := hkey c (π c)
      rw [Equiv.symm_apply_apply, spFrame_toStd_single_of_lt_self hlt] at hbase
      rw [spFrame_toStd_single_of_lt_apply hlt] at hbase
      rw [mul_one] at hbase
      by_cases ha : π'.symm (π c) = c
      · have hπ : π c = π' c := by
          have := congrArg π' ha
          simpa using this
        have hsc : s c = s' c := by
          rw [ha, if_pos rfl, if_neg hcne', sub_zero, mul_one] at hbase
          exact hbase
        exact ⟨hπ, hsc⟩
      · by_cases ha' : π'.symm (π c) = c'
        · exfalso
          have hπ' : π c = π' c' := by
            have := congrArg π' ha'
            simpa using this
          have hcc' : c' = c := Equiv.injective π (hPc'.1.trans hπ'.symm)
          exact hcne hcc'.symm
        · have h0 : s c = 0 := by
            rw [if_neg ha, if_neg ha', sub_zero, mul_zero] at hbase
            exact hbase
          rcases hs c with h1 | h1 <;> omega
  have hP : ∀ c : Fin m, π c = π' c ∧ s c = s' c := fun c =>
    key (m - c.val - 1) c (by omega)
  exact ⟨Equiv.ext fun c => (hP c).1, funext fun c => (hP c).2⟩

theorem exists_sign_family (m : ℕ) (hm : 1 ≤ m) :
    ∃ ε : Fin (m + 1) → (coxeterMatrix (isFiniteType_cartanC (m + 1))).Group,
      (∀ j, SpRealizes (m + 1) (ε j) 1 (spSgn j)) ∧
      ε (Fin.last m) = (coxeterMatrix (isFiniteType_cartanC (m + 1))).toCoxeterSystem.simple
        (Fin.last m) ∧
      (∀ i j, ε i * ε j = ε j * ε i) ∧
      (∀ i j, i ≠ j → ε i ≠ ε j) ∧
      (∀ (k : Fin (m + 1)) (hk : k.val + 1 < m + 1) (j : Fin (m + 1)),
        (coxeterMatrix (isFiniteType_cartanC (m + 1))).toCoxeterSystem.simple k * ε j *
            (coxeterMatrix (isFiniteType_cartanC (m + 1))).toCoxeterSystem.simple k =
          ε (Equiv.swap k ⟨k.val + 1, hk⟩ j)) ∧
      (∀ (k : Fin (m + 1)), k.val + 1 < m + 1 → ∀ j,
        (coxeterMatrix (isFiniteType_cartanC (m + 1))).toCoxeterSystem.simple k ≠ ε j) := by
  have hex : ∀ j : Fin (m + 1),
      ∃ w : (coxeterMatrix (isFiniteType_cartanC (m + 1))).Group,
        SpRealizes (m + 1) w 1 (spSgn j) := by
    intro j
    by_cases hj : j = 0
    · subst hj
      exact exists_spZeroSign hm
    · have hj1 : 1 ≤ j.val := by
        have := Fin.val_ne_of_ne hj
        simp only [Fin.val_zero] at this
        omega
      obtain ⟨v, -, hv⟩ := exists_spLeviW_sgnOn (n := m) hm {j} (by
        intro a ha
        rw [Finset.mem_singleton] at ha
        rw [ha]
        exact hj1)
      exact ⟨v, hv.congr rfl (by funext c; simp [spSgnOn, spSgn])⟩
  choose ε hε using hex
  refine ⟨ε, hε, ?_, ?_, ?_, ?_, ?_⟩
  · exact SpRealizes.inj (hε (Fin.last m))
      (spRealizes_simple_of_not_lt (k := Fin.last m) (by simp))
  · intro i j
    exact SpRealizes.inj ((hε i).mul (hε j))
      (((hε j).mul (hε i)).congr rfl (by funext c; simp [mul_comm]))
  · intro i j hij heq
    have h2 : SpRealizes (m + 1) (ε i) 1 (spSgn j) := heq.symm ▸ hε j
    have hsgn : spSgn i = spSgn j :=
      (SpRealizes.unique (spIsSign_spSgn i) (spIsSign_spSgn j) (hε i) h2).2
    have hii : spSgn i i = spSgn j i := congrFun hsgn i
    simp only [spSgn] at hii
    rw [if_neg hij] at hii
    norm_num at hii
  · intro k hk j
    let k' : Fin (m + 1) := ⟨k.val + 1, hk⟩
    have hk1 : SpRealizes (m + 1)
        ((coxeterMatrix (isFiniteType_cartanC (m + 1))).toCoxeterSystem.simple k)
        (Equiv.swap k k') 1 := spRealizes_simple_of_lt hk
    have hconj := (hk1.mul (hε j)).mul hk1
    have hconj' : SpRealizes (m + 1)
        ((coxeterMatrix (isFiniteType_cartanC (m + 1))).toCoxeterSystem.simple k * ε j *
          (coxeterMatrix (isFiniteType_cartanC (m + 1))).toCoxeterSystem.simple k) 1
        (spSgn (Equiv.swap k k' j)) :=
      hconj.congr (by rw [mul_one, Equiv.swap_mul_self])
        (by funext c; simp [spSgn, Equiv.swap_apply_eq_iff])
    exact SpRealizes.inj hconj' (hε (Equiv.swap k k' j))
  · intro k hk j heq
    have h2 : SpRealizes (m + 1)
        ((coxeterMatrix (isFiniteType_cartanC (m + 1))).toCoxeterSystem.simple k) 1
        (spSgn j) := heq.symm ▸ hε j
    have hsw : Equiv.swap k ⟨k.val + 1, hk⟩ = 1 :=
      (SpRealizes.unique spIsSign_one (spIsSign_spSgn j) (spRealizes_simple_of_lt hk) h2).1
    have hk' : (⟨k.val + 1, hk⟩ : Fin (m + 1)) = k := by
      have := DFunLike.congr_fun hsw k
      simpa using this
    have : k.val + 1 = k.val := congrArg Fin.val hk'
    omega

end CFSG.StandardType.SpFrame
