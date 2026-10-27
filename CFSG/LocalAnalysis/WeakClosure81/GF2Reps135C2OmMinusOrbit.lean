module

public import CFSG.LieType.Universal.Spin.Roots.TypeB

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin

noncomputable abbrev o8mW : Type := (coxeterMatrix (isFiniteType_cartanB 3)).Group

noncomputable abbrev o8mSimple (i : Fin 3) : o8mW :=
  (coxeterMatrix (isFiniteType_cartanB 3)).toCoxeterSystem.simple i

noncomputable abbrev o8mAct (w : o8mW) (v : Fin 3 → ℤ) : Fin 3 → ℤ :=
  weylAction (isFiniteType_cartanB 3) w v

@[expose] def o8mWt (j : Fin 3) : Fin 3 → ℤ :=
  ofStdB 3 fun a => if a.val ≤ j.val then 1 else 0

@[expose] def o8mWtPair (i : Fin 3) : Fin 3 → ℤ :=
  ofStdB 3 (![![3, 3, 1], ![3, 1, 1], ![2, 1, 0]] i)

private theorem o8mAct_mul (a b : o8mW) (v : Fin 3 → ℤ) :
    o8mAct (a * b) v = o8mAct a (o8mAct b v) := by
  simp only [o8mAct, weylAction_mul_apply]

private theorem o8mAct_one (v : Fin 3 → ℤ) : o8mAct 1 v = v := by
  show weylAction (isFiniteType_cartanB 3) 1 v = v
  rw [map_one, Module.End.one_apply]

private theorem o8m_toStdB_simple (i : Fin 3) (v : Fin 3 → ℤ) :
    toStdB 3 (o8mAct (o8mSimple i) v) = stdReflB 3 i (toStdB 3 v) := by
  simp only [o8mAct, o8mSimple, weylAction_simple, toStdB_reflection]

private noncomputable def o8mWordOfList : List (Fin 3) → o8mW
  | [] => 1
  | i :: l => o8mSimple i * o8mWordOfList l

private def o8mStdWord : List (Fin 3) → (Fin 3 → ℤ) → (Fin 3 → ℤ)
  | [], e => e
  | i :: l, e => stdReflB 3 i (o8mStdWord l e)

private theorem o8m_toStdB_wordOfList (l : List (Fin 3)) (v : Fin 3 → ℤ) :
    toStdB 3 (o8mAct (o8mWordOfList l) v) = o8mStdWord l (toStdB 3 v) := by
  induction l generalizing v with
  | nil => simp only [o8mWordOfList, o8mStdWord, o8mAct_one]
  | cons i l ih =>
      simp only [o8mWordOfList, o8mStdWord, o8mAct_mul, o8m_toStdB_simple, ih]

theorem o8mWt_fixed {i j : Fin 3} (hij : i ≠ j) : o8mAct (o8mSimple i) (o8mWt j) = o8mWt j := by
  apply toStdB_injective 3
  rw [o8m_toStdB_simple]
  simp only [o8mWt, toStdB_ofStdB]
  fin_cases i <;> fin_cases j <;> simp_all <;> decide

theorem o8mWtPair_fixed (i : Fin 3) : o8mAct (o8mSimple i) (o8mWtPair i) = o8mWtPair i := by
  apply toStdB_injective 3
  rw [o8m_toStdB_simple]
  simp only [o8mWtPair, toStdB_ofStdB]
  fin_cases i <;> simp [stdReflB] <;> decide

private def o8mFourOneListX0 : Fin 4 → List (Fin 3)
  | 0 => [1]
  | 1 => [2, 1]
  | 2 => [1, 0, 1, 2, 1]
  | 3 => [2, 1, 0, 1, 2, 1]

private noncomputable def o8mFourOneWordX0 (a : Fin 4) : o8mW :=
  o8mWordOfList (o8mFourOneListX0 a)

private def o8mFourOneStdX0 : Fin 4 → (Fin 3 → ℤ) :=
  ![![1, 0, 1], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, -1]]

private theorem o8m_toStdB_fourOneX0 (a : Fin 4) :
    toStdB 3 (o8mAct (o8mFourOneWordX0 a) (o8mWt 1)) = o8mFourOneStdX0 a := by
  fin_cases a <;>
    (simp only [o8mFourOneWordX0, o8mFourOneListX0, o8m_toStdB_wordOfList, o8mStdWord, o8mWt,
      toStdB_ofStdB]
     decide)

private theorem o8mFourOneX0_inj :
    Function.Injective (fun a => o8mAct (o8mFourOneWordX0 a) (o8mWt 1)) := by
  intro i j hij
  exact (by decide : Function.Injective o8mFourOneStdX0) (by
    have h := congrArg (toStdB 3) hij
    simpa only [o8m_toStdB_fourOneX0] using h)

private theorem o8mFourOneX0_ne :
    ∀ i j, o8mAct (o8mFourOneWordX0 i) (o8mWt 1) ≠
      o8mAct (o8mSimple 0) (o8mAct (o8mFourOneWordX0 j) (o8mWt 1)) := by
  intro i j hij
  have h := congrArg (toStdB 3) hij
  fin_cases i <;> fin_cases j <;>
    (simp only [o8mFourOneWordX0, o8mFourOneListX0, o8m_toStdB_wordOfList, o8mStdWord,
      o8m_toStdB_simple, o8mWt, toStdB_ofStdB] at h
     exact absurd h (by decide))

private def o8mFourOneListX2 : Fin 4 → List (Fin 3)
  | 0 => [1]
  | 1 => [1, 0, 1, 2, 1]
  | 2 => [0, 1]
  | 3 => [0, 1, 0, 1, 2, 1]

private noncomputable def o8mFourOneWordX2 (a : Fin 4) : o8mW :=
  o8mWordOfList (o8mFourOneListX2 a)

private def o8mFourOneStdX2 : Fin 4 → (Fin 3 → ℤ) :=
  ![![1, 0, 1], ![-1, 0, 1], ![0, 1, 1], ![0, -1, 1]]

private theorem o8m_toStdB_fourOneX2 (a : Fin 4) :
    toStdB 3 (o8mAct (o8mFourOneWordX2 a) (o8mWt 1)) = o8mFourOneStdX2 a := by
  fin_cases a <;>
    (simp only [o8mFourOneWordX2, o8mFourOneListX2, o8m_toStdB_wordOfList, o8mStdWord, o8mWt,
      toStdB_ofStdB]
     decide)

private theorem o8mFourOneX2_inj :
    Function.Injective (fun a => o8mAct (o8mFourOneWordX2 a) (o8mWt 1)) := by
  intro i j hij
  exact (by decide : Function.Injective o8mFourOneStdX2) (by
    have h := congrArg (toStdB 3) hij
    simpa only [o8m_toStdB_fourOneX2] using h)

private theorem o8mFourOneX2_ne_s2 :
    ∀ i j, o8mAct (o8mFourOneWordX2 i) (o8mWt 1) ≠
      o8mAct (o8mSimple 2) (o8mAct (o8mFourOneWordX2 j) (o8mWt 1)) := by
  intro i j hij
  have h := congrArg (toStdB 3) hij
  fin_cases i <;> fin_cases j <;>
    (simp only [o8mFourOneWordX2, o8mFourOneListX2, o8m_toStdB_wordOfList, o8mStdWord,
      o8m_toStdB_simple, o8mWt, toStdB_ofStdB] at h
     exact absurd h (by decide))

private theorem o8mFourOneX2_ne_s02 :
    ∀ i j, o8mAct (o8mFourOneWordX2 i) (o8mWt 1) ≠
      o8mAct (o8mSimple 0 * o8mSimple 2) (o8mAct (o8mFourOneWordX2 j) (o8mWt 1)) := by
  intro i j hij
  have h := congrArg (toStdB 3) hij
  fin_cases i <;> fin_cases j <;>
    (simp only [o8mFourOneWordX2, o8mFourOneListX2, o8m_toStdB_wordOfList, o8mStdWord,
      o8mAct_mul, o8m_toStdB_simple, o8mWt, toStdB_ofStdB] at h
     exact absurd h (by decide))

private theorem o8mFourOrbitOneX0 :
    ∃ u : Fin 4 → (Fin 3 → ℤ), (∀ i, ∃ w : o8mW, u i = o8mAct w (o8mWt 1)) ∧
      Function.Injective u ∧ ∀ i j, u i ≠ o8mAct (o8mSimple 0) (u j) :=
  ⟨_, fun i => ⟨o8mFourOneWordX0 i, rfl⟩, o8mFourOneX0_inj, o8mFourOneX0_ne⟩

private theorem o8mFourOrbitOneX2 :
    ∃ u : Fin 4 → (Fin 3 → ℤ), (∀ i, ∃ w : o8mW, u i = o8mAct w (o8mWt 1)) ∧
      Function.Injective u ∧ ∀ i j, u i ≠ o8mAct (o8mSimple 2) (u j) :=
  ⟨_, fun i => ⟨o8mFourOneWordX2 i, rfl⟩, o8mFourOneX2_inj, o8mFourOneX2_ne_s2⟩

private theorem o8mFourOrbitOneX02 :
    ∃ u : Fin 4 → (Fin 3 → ℤ), (∀ i, ∃ w : o8mW, u i = o8mAct w (o8mWt 1)) ∧
      Function.Injective u ∧ ∀ i j, u i ≠ o8mAct (o8mSimple 0 * o8mSimple 2) (u j) :=
  ⟨_, fun i => ⟨o8mFourOneWordX2 i, rfl⟩, o8mFourOneX2_inj, o8mFourOneX2_ne_s02⟩

theorem exists_four_orbit_o8mWt_one {x : o8mW}
    (hx : x = o8mSimple 0 ∨ x = o8mSimple 2 ∨ x = o8mSimple 0 * o8mSimple 2) :
    ∃ u : Fin 4 → (Fin 3 → ℤ), (∀ i, ∃ w : o8mW, u i = o8mAct w (o8mWt 1)) ∧
      Function.Injective u ∧ ∀ i j, u i ≠ o8mAct x (u j) := by
  rcases hx with rfl | rfl | rfl
  · exact o8mFourOrbitOneX0
  · exact o8mFourOrbitOneX2
  · exact o8mFourOrbitOneX02

private def o8mFourTwoList : Fin 4 → List (Fin 3)
  | 0 => []
  | 1 => [1, 2]
  | 2 => [0, 1, 2]
  | 3 => [1, 0, 2, 1, 2]

private noncomputable def o8mFourTwoWord (a : Fin 4) : o8mW := o8mWordOfList (o8mFourTwoList a)

private def o8mFourTwoStd : Fin 4 → (Fin 3 → ℤ) :=
  ![![1, 1, 1], ![1, -1, 1], ![-1, 1, 1], ![-1, -1, 1]]

private theorem o8m_toStdB_fourTwo (a : Fin 4) :
    toStdB 3 (o8mAct (o8mFourTwoWord a) (o8mWt 2)) = o8mFourTwoStd a := by
  fin_cases a <;>
    (simp only [o8mFourTwoWord, o8mFourTwoList, o8m_toStdB_wordOfList, o8mStdWord, o8mWt,
      toStdB_ofStdB]
     decide)

private theorem o8mFourTwo_inj :
    Function.Injective (fun a => o8mAct (o8mFourTwoWord a) (o8mWt 2)) := by
  intro i j hij
  exact (by decide : Function.Injective o8mFourTwoStd) (by
    have h := congrArg (toStdB 3) hij
    simpa only [o8m_toStdB_fourTwo] using h)

private theorem o8mFourTwo_ne_s2 :
    ∀ i j, o8mAct (o8mFourTwoWord i) (o8mWt 2) ≠
      o8mAct (o8mSimple 2) (o8mAct (o8mFourTwoWord j) (o8mWt 2)) := by
  intro i j hij
  have h := congrArg (toStdB 3) hij
  fin_cases i <;> fin_cases j <;>
    (simp only [o8mFourTwoWord, o8mFourTwoList, o8m_toStdB_wordOfList, o8mStdWord,
      o8m_toStdB_simple, o8mWt, toStdB_ofStdB] at h
     exact absurd h (by decide))

private theorem o8mFourTwo_ne_s02 :
    ∀ i j, o8mAct (o8mFourTwoWord i) (o8mWt 2) ≠
      o8mAct (o8mSimple 0 * o8mSimple 2) (o8mAct (o8mFourTwoWord j) (o8mWt 2)) := by
  intro i j hij
  have h := congrArg (toStdB 3) hij
  fin_cases i <;> fin_cases j <;>
    (simp only [o8mFourTwoWord, o8mFourTwoList, o8m_toStdB_wordOfList, o8mStdWord, o8mAct_mul,
      o8m_toStdB_simple, o8mWt, toStdB_ofStdB] at h
     exact absurd h (by decide))

private theorem o8mFourOrbitTwoS2 :
    ∃ u : Fin 4 → (Fin 3 → ℤ), (∀ i, ∃ w : o8mW, u i = o8mAct w (o8mWt 2)) ∧
      Function.Injective u ∧ ∀ i j, u i ≠ o8mAct (o8mSimple 2) (u j) :=
  ⟨_, fun i => ⟨o8mFourTwoWord i, rfl⟩, o8mFourTwo_inj, o8mFourTwo_ne_s2⟩

private theorem o8mFourOrbitTwoS02 :
    ∃ u : Fin 4 → (Fin 3 → ℤ), (∀ i, ∃ w : o8mW, u i = o8mAct w (o8mWt 2)) ∧
      Function.Injective u ∧ ∀ i j, u i ≠ o8mAct (o8mSimple 0 * o8mSimple 2) (u j) :=
  ⟨_, fun i => ⟨o8mFourTwoWord i, rfl⟩, o8mFourTwo_inj, o8mFourTwo_ne_s02⟩

theorem exists_four_orbit_o8mWt_two {x : o8mW}
    (hx : x = o8mSimple 2 ∨ x = o8mSimple 0 * o8mSimple 2) :
    ∃ u : Fin 4 → (Fin 3 → ℤ), (∀ i, ∃ w : o8mW, u i = o8mAct w (o8mWt 2)) ∧
      Function.Injective u ∧ ∀ i j, u i ≠ o8mAct x (u j) := by
  rcases hx with rfl | rfl
  · exact o8mFourOrbitTwoS2
  · exact o8mFourOrbitTwoS02

private def o8mTwoList : Fin 2 → List (Fin 3)
  | 0 => [1, 2]
  | 1 => [2, 1, 2]

private noncomputable def o8mTwoWord (a : Fin 2) : o8mW := o8mWordOfList (o8mTwoList a)

private def o8mTwoStd : Fin 2 → (Fin 3 → ℤ) :=
  ![![1, -1, 1], ![1, -1, -1]]

private theorem o8m_toStdB_two (a : Fin 2) :
    toStdB 3 (o8mAct (o8mTwoWord a) (o8mWt 2)) = o8mTwoStd a := by
  fin_cases a <;>
    (simp only [o8mTwoWord, o8mTwoList, o8m_toStdB_wordOfList, o8mStdWord, o8mWt,
      toStdB_ofStdB]
     decide)

private theorem o8mTwo_inj :
    Function.Injective (fun a => o8mAct (o8mTwoWord a) (o8mWt 2)) := by
  intro i j hij
  exact (by decide : Function.Injective o8mTwoStd) (by
    have h := congrArg (toStdB 3) hij
    simpa only [o8m_toStdB_two] using h)

private theorem o8mTwo_ne :
    ∀ i j, o8mAct (o8mTwoWord i) (o8mWt 2) ≠
      o8mAct (o8mSimple 0) (o8mAct (o8mTwoWord j) (o8mWt 2)) := by
  intro i j hij
  have h := congrArg (toStdB 3) hij
  fin_cases i <;> fin_cases j <;>
    (simp only [o8mTwoWord, o8mTwoList, o8m_toStdB_wordOfList, o8mStdWord, o8m_toStdB_simple,
      o8mWt, toStdB_ofStdB] at h
     exact absurd h (by decide))

private theorem o8mTwoOrbit :
    ∃ u : Fin 2 → (Fin 3 → ℤ), (∀ i, ∃ w : o8mW, u i = o8mAct w (o8mWt 2)) ∧
      Function.Injective u ∧ ∀ i j, u i ≠ o8mAct (o8mSimple 0) (u j) :=
  ⟨_, fun i => ⟨o8mTwoWord i, rfl⟩, o8mTwo_inj, o8mTwo_ne⟩

theorem exists_two_orbit_o8mWt_two :
    ∃ u : Fin 2 → (Fin 3 → ℤ), (∀ i, ∃ w : o8mW, u i = o8mAct w (o8mWt 2)) ∧
      Function.Injective u ∧ ∀ i j, u i ≠ o8mAct (o8mSimple 0) (u j) :=
  o8mTwoOrbit

private def o8mPairListZero : Fin 17 → List (Fin 3) :=
  ![[], [1], [2], [0, 1], [1, 2], [2, 1], [0, 1, 2], [1, 2, 1], [2, 0, 1], [2, 1, 2],
    [0, 1, 2, 1], [1, 2, 0, 1], [2, 0, 1, 2], [2, 1, 2, 1], [0, 1, 2, 0, 1],
    [1, 2, 0, 1, 2], [2, 0, 1, 2, 1]]

private noncomputable def o8mPairWordZero (a : Fin 17) : o8mW :=
  o8mWordOfList (o8mPairListZero a)

private def o8mPairStdZero : Fin 17 → (Fin 3 → ℤ) :=
  ![![3, 3, 1], ![3, 1, 3], ![3, 3, -1], ![1, 3, 3], ![3, -1, 3], ![3, 1, -3], ![-1, 3, 3],
    ![3, -3, 1], ![1, 3, -3], ![3, -1, -3], ![-3, 3, 1], ![1, -3, 3], ![-1, 3, -3],
    ![3, -3, -1], ![-3, 1, 3], ![-1, -3, 3], ![-3, 3, -1]]

private theorem o8m_toStdB_pairZero (a : Fin 17) :
    toStdB 3 (o8mAct (o8mPairWordZero a) (o8mWtPair 0)) = o8mPairStdZero a := by
  fin_cases a <;>
    (simp only [o8mPairWordZero, o8mPairListZero, o8m_toStdB_wordOfList, o8mWtPair,
      toStdB_ofStdB]
     decide)

private theorem o8mPairOrbitZero :
    ∃ u : Fin 17 → (Fin 3 → ℤ), (∀ a, ∃ w : o8mW, u a = o8mAct w (o8mWtPair 0)) ∧
      Function.Injective u := by
  refine ⟨fun a => o8mAct (o8mPairWordZero a) (o8mWtPair 0), ?_, ?_⟩
  · intro a; exact ⟨o8mPairWordZero a, rfl⟩
  · intro a b hab
    exact (by decide : Function.Injective o8mPairStdZero) (by
      have h := congrArg (toStdB 3) hab
      simpa only [o8m_toStdB_pairZero] using h)

private def o8mPairListOne : Fin 17 → List (Fin 3) :=
  ![[], [0], [2], [1, 0], [1, 2], [2, 0], [0, 1, 2], [1, 2, 0], [2, 1, 0], [2, 1, 2],
    [0, 1, 2, 0], [1, 2, 1, 0], [2, 0, 1, 2], [2, 1, 2, 0], [0, 1, 2, 1, 0],
    [1, 2, 0, 1, 2], [2, 0, 1, 2, 0]]

private noncomputable def o8mPairWordOne (a : Fin 17) : o8mW :=
  o8mWordOfList (o8mPairListOne a)

private def o8mPairStdOne : Fin 17 → (Fin 3 → ℤ) :=
  ![![3, 1, 1], ![1, 3, 1], ![3, 1, -1], ![1, 1, 3], ![3, -1, 1], ![1, 3, -1], ![-1, 3, 1],
    ![1, -1, 3], ![1, 1, -3], ![3, -1, -1], ![-1, 1, 3], ![1, -3, 1], ![-1, 3, -1],
    ![1, -1, -3], ![-3, 1, 1], ![-1, -1, 3], ![-1, 1, -3]]

private theorem o8m_toStdB_pairOne (a : Fin 17) :
    toStdB 3 (o8mAct (o8mPairWordOne a) (o8mWtPair 1)) = o8mPairStdOne a := by
  fin_cases a <;>
    (simp only [o8mPairWordOne, o8mPairListOne, o8m_toStdB_wordOfList, o8mWtPair,
      toStdB_ofStdB]
     decide)

private theorem o8mPairOrbitOne :
    ∃ u : Fin 17 → (Fin 3 → ℤ), (∀ a, ∃ w : o8mW, u a = o8mAct w (o8mWtPair 1)) ∧
      Function.Injective u := by
  refine ⟨fun a => o8mAct (o8mPairWordOne a) (o8mWtPair 1), ?_, ?_⟩
  · intro a; exact ⟨o8mPairWordOne a, rfl⟩
  · intro a b hab
    exact (by decide : Function.Injective o8mPairStdOne) (by
      have h := congrArg (toStdB 3) hab
      simpa only [o8m_toStdB_pairOne] using h)

private def o8mPairListTwo : Fin 17 → List (Fin 3) :=
  ![[], [0], [1], [0, 1], [1, 0], [2, 1], [0, 1, 0], [1, 2, 1], [2, 0, 1], [2, 1, 0],
    [0, 1, 2, 1], [1, 2, 0, 1], [1, 2, 1, 0], [2, 0, 1, 0], [0, 1, 2, 0, 1],
    [0, 1, 2, 1, 0], [1, 2, 0, 1, 0]]

private noncomputable def o8mPairWordTwo (a : Fin 17) : o8mW :=
  o8mWordOfList (o8mPairListTwo a)

private def o8mPairStdTwo : Fin 17 → (Fin 3 → ℤ) :=
  ![![2, 1, 0], ![1, 2, 0], ![2, 0, 1], ![0, 2, 1], ![1, 0, 2], ![2, 0, -1], ![0, 1, 2],
    ![2, -1, 0], ![0, 2, -1], ![1, 0, -2], ![-1, 2, 0], ![0, -1, 2], ![1, -2, 0],
    ![0, 1, -2], ![-1, 0, 2], ![-2, 1, 0], ![0, -2, 1]]

private theorem o8m_toStdB_pairTwo (a : Fin 17) :
    toStdB 3 (o8mAct (o8mPairWordTwo a) (o8mWtPair 2)) = o8mPairStdTwo a := by
  fin_cases a <;>
    (simp only [o8mPairWordTwo, o8mPairListTwo, o8m_toStdB_wordOfList, o8mWtPair,
      toStdB_ofStdB]
     decide)

private theorem o8mPairOrbitTwo :
    ∃ u : Fin 17 → (Fin 3 → ℤ), (∀ a, ∃ w : o8mW, u a = o8mAct w (o8mWtPair 2)) ∧
      Function.Injective u := by
  refine ⟨fun a => o8mAct (o8mPairWordTwo a) (o8mWtPair 2), ?_, ?_⟩
  · intro a; exact ⟨o8mPairWordTwo a, rfl⟩
  · intro a b hab
    exact (by decide : Function.Injective o8mPairStdTwo) (by
      have h := congrArg (toStdB 3) hab
      simpa only [o8m_toStdB_pairTwo] using h)

theorem exists_seventeen_orbit_o8mWtPair (i : Fin 3) :
    ∃ u : Fin 17 → (Fin 3 → ℤ), (∀ a, ∃ w : o8mW, u a = o8mAct w (o8mWtPair i)) ∧
      Function.Injective u := by
  fin_cases i
  · exact o8mPairOrbitZero
  · exact o8mPairOrbitOne
  · exact o8mPairOrbitTwo

private theorem o8mSimple121_inv :
    (o8mSimple 1 * o8mSimple 2 * o8mSimple 1)⁻¹ =
      o8mSimple 1 * o8mSimple 2 * o8mSimple 1 := by
  have h1 : o8mSimple 1 * o8mSimple 1 = 1 :=
    (coxeterMatrix (isFiniteType_cartanB 3)).toCoxeterSystem.simple_mul_simple_self 1
  have h2 : o8mSimple 2 * o8mSimple 2 = 1 :=
    (coxeterMatrix (isFiniteType_cartanB 3)).toCoxeterSystem.simple_mul_simple_self 2
  have i1 : (o8mSimple 1)⁻¹ = o8mSimple 1 := inv_eq_of_mul_eq_one_right h1
  have i2 : (o8mSimple 2)⁻¹ = o8mSimple 2 := inv_eq_of_mul_eq_one_right h2
  rw [mul_inv_rev, mul_inv_rev, i1, i2, ← mul_assoc]

theorem weylAction_theta_o8mWt_two_ne :
    o8mAct ((o8mSimple 1 * o8mSimple 2 * o8mSimple 1)⁻¹ * o8mSimple 0 *
      (o8mSimple 1 * o8mSimple 2 * o8mSimple 1)) (o8mWt 2) ≠ o8mWt 2 := by
  intro h
  rw [o8mSimple121_inv] at h
  have h' := congrArg (toStdB 3) h
  simp only [o8mAct, o8mSimple, weylAction_mul_apply, weylAction_simple, toStdB_reflection,
    o8mWt, toStdB_ofStdB] at h'
  exact absurd h' (by decide)

end CFSG.LocalAnalysis.WeakClosure81
