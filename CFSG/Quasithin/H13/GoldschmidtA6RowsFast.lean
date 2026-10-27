module

public import CFSG.Quasithin.H13.GoldschmidtA6RowsCode
public import Batteries.Data.Nat.Bitwise.Lemmas

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open Matrix

namespace CFSG.Quasithin.H13.A6.GR

@[expose] def appL : List ℕ → ℕ → ℕ
  | [], _ => 0
  | c :: cs, x => Nat.xor (Nat.mul (Nat.land x 1) c) (appL cs (Nat.shiftRight x 1))

theorem appAux_cons (c : ℕ) (cs : List ℕ) :
    ∀ (n x : ℕ), appAux (c :: cs) x (n + 1) = ((x &&& 1) * c) ^^^ appAux cs (x >>> 1) n := by
  intro n
  induction n with
  | zero =>
    intro x
    have h : (if x.testBit 0 then c else 0) = (x &&& 1) * c := by
      rw [Nat.testBit_zero, Nat.and_one_is_mod]
      rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h]
    have e : appAux (c :: cs) x (0 + 1) = (if x.testBit 0 then c else 0) ^^^ 0 := by
      simp only [appAux, List.getD_cons_zero]
    rw [e, Nat.xor_zero, h]
    simp [appAux]
  | succ n ih =>
    intro x
    have hb : (x >>> 1).testBit n = x.testBit (n + 1) := by
      rw [Nat.testBit_shiftRight, Nat.add_comm]
    have h1 : appAux (c :: cs) x (n + 1 + 1) =
        (if x.testBit (n + 1) then cs.getD n 0 else 0) ^^^ appAux (c :: cs) x (n + 1) := by
      simp only [appAux, List.getD_cons_succ]
    have h2 : appAux cs (x >>> 1) (n + 1) =
        (if x.testBit (n + 1) then cs.getD n 0 else 0) ^^^ appAux cs (x >>> 1) n := by
      simp only [appAux, hb]
    rw [h1, h2, ih x, Nat.xor_left_comm]

theorem appL_eq : ∀ (cs : List ℕ) (x : ℕ), appL cs x = appC cs.length cs x := by
  intro cs
  induction cs with
  | nil => intro x; rfl
  | cons c cs ih =>
    intro x
    have e := appAux_cons c cs cs.length x
    calc appL (c :: cs) x = ((x &&& 1) * c) ^^^ appL cs (x >>> 1) := rfl
      _ = ((x &&& 1) * c) ^^^ appC cs.length cs (x >>> 1) := by rw [ih]
      _ = appC (c :: cs).length (c :: cs) x := e.symm

@[expose] def mulL (a b : List ℕ) : List ℕ := b.map (appL a)

theorem mulL_eq (a b : List ℕ) : mulL a b = mulC a.length a b := by
  unfold mulL mulC
  exact List.map_congr_left fun x _ => appL_eq a x

theorem length_mulL (a b : List ℕ) : (mulL a b).length = b.length := by simp [mulL]

theorem length_mulC (d : ℕ) (a b : List ℕ) : (mulC d a b).length = b.length := by simp [mulC]

@[expose] def cubeL (cs : List ℕ) : List ℕ := mulL cs (mulL cs cs)

theorem cubeL_eq {cs : List ℕ} (h : cs.length = 6) : cubeL cs = cubeC 6 cs := by
  unfold cubeL cubeC
  rw [mulL_eq, mulL_eq, h]

@[expose] def sqIterL (cs : List ℕ) : ℕ → List ℕ
  | 0 => cs
  | a + 1 => sqIterL (mulL cs cs) a

theorem sqIter_succ' (d : ℕ) : ∀ (a : ℕ) (cs : List ℕ),
    sqIter d cs (a + 1) = sqIter d (mulC d cs cs) a := by
  intro a
  induction a with
  | zero => intro cs; rfl
  | succ a ih =>
    intro cs
    rw [sqIter, ih, sqIter]

theorem sqIterL_eq (d : ℕ) : ∀ (a : ℕ) (cs : List ℕ), cs.length = d →
    sqIterL cs a = sqIter d cs a := by
  intro a
  induction a with
  | zero => intro cs _; rfl
  | succ a ih =>
    intro cs h
    rw [sqIterL, sqIter_succ', mulL_eq, h]
    exact ih _ (by rw [length_mulC, h])

theorem length_sqIterL : ∀ (a : ℕ) (cs : List ℕ), (sqIterL cs a).length = cs.length := by
  intro a
  induction a with
  | zero => intro cs; rfl
  | succ a ih => intro cs; rw [sqIterL, ih, length_mulL]

@[expose] def conjL (gp : List (List ℕ × List ℕ)) (cs : List ℕ) : List (List ℕ) :=
  cs :: gp.flatMap fun p => [mulL (mulL p.1 cs) p.2, mulL (mulL p.2 cs) p.1]

theorem mulL_eq6 {a : List ℕ} (b : List ℕ) (ha : a.length = 6) : mulL a b = mulC 6 a b := by
  rw [mulL_eq, ha]

theorem conjL_eq {gp : List (List ℕ × List ℕ)} (hgp : ∀ p ∈ gp, p.1.length = 6 ∧ p.2.length = 6)
    {cs : List ℕ} (h : cs.length = 6) : conjL gp cs = conjC 6 gp cs := by
  unfold conjL conjC
  congr 1
  refine List.flatMap_congr fun p hp => ?_
  obtain ⟨h1, h2⟩ := hgp p hp
  have e1 : (mulC 6 p.1 cs).length = 6 := by rw [length_mulC, h]
  have e2 : (mulC 6 p.2 cs).length = 6 := by rw [length_mulC, h]
  rw [mulL_eq6 cs h1, mulL_eq6 p.2 e1, mulL_eq6 cs h2, mulL_eq6 p.1 e2]

@[expose] def isOneL (cs : List ℕ) : Bool := (cs.map fun x => x % 64) == [1, 2, 4, 8, 16, 32]

theorem normC_six {cs : List ℕ} (h : cs.length = 6) : normC 6 cs = cs.map fun x => x % 64 := by
  refine List.ext_getElem (by simp [normC, h]) fun i h1 h2 => ?_
  have hi : i < 6 := by simpa [normC] using h1
  simp only [normC, List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ _ (by omega)]
  norm_num

theorem isOne_eq {cs : List ℕ} (h : cs.length = 6) : isOne 6 cs = isOneL cs := by
  unfold isOne isOneL
  rw [normC_six h]
  have : normC 6 (oneC 6) = [1, 2, 4, 8, 16, 32] := by decide
  rw [this]


theorem appAux_pow (cs : List ℕ) (j : ℕ) :
    ∀ n, appAux cs (2 ^ j) n = if j < n then cs.getD j 0 else 0 := by
  intro n
  induction n with
  | zero => simp [appAux]
  | succ n ih =>
    rw [appAux, ih, Nat.testBit_two_pow]
    by_cases h1 : j = n
    · subst h1
      simp
    · by_cases h2 : j < n
      · have h3 : j < n + 1 := by omega
        simp [h1, h2, h3]
      · have h3 : ¬ j < n + 1 := by omega
        simp [h1, h2, h3]

theorem appC_pow (d : ℕ) (cs : List ℕ) {j : ℕ} (hj : j < d) :
    appC d cs (2 ^ j) = cs.getD j 0 := by
  unfold appC
  rw [appAux_pow]
  simp [hj]

@[expose] def parTab : ℕ := 7608434000728254870

@[expose] def parT (n : ℕ) : Bool := parTab.testBit n

@[expose] def spanF (L : List (List ℕ)) : Bool :=
  (List.range 64).all fun c => c == 0 || L.any fun q => (List.range 6).any fun j =>
    parT (Nat.land c (Nat.xor (q.getD j 0 % 64) (2 ^ j)))

theorem par_dot : ∀ c < 64, ∀ a < 64, ∀ j < 6,
    parT (c &&& (a ^^^ 2 ^ j)) = true → (dotC 6 c a != dotC 6 c (2 ^ j)) = true := by
  decide +kernel

theorem spanF_imp {L : List (List ℕ)} (h : spanF L = true) : spanC 6 L = true := by
  unfold spanF at h
  unfold spanC
  rw [List.all_eq_true] at h ⊢
  intro c hc
  have h1 := h c (by simpa using hc)
  simp only [Bool.or_eq_true, beq_iff_eq] at h1 ⊢
  rcases h1 with h1 | h1
  · exact Or.inl h1
  · right
    rw [List.any_eq_true] at h1 ⊢
    obtain ⟨q, hq, h2⟩ := h1
    rw [List.any_eq_true] at h2
    obtain ⟨j, hj, h3⟩ := h2
    refine ⟨q, hq, ?_⟩
    rw [List.any_eq_true]
    have hj6 : j < 6 := List.mem_range.mp hj
    have hlt : 2 ^ j < 2 ^ 6 := Nat.pow_lt_pow_right (by norm_num) hj6
    refine ⟨2 ^ j, List.mem_range.mpr hlt, ?_⟩
    rw [appC_pow 6 q hj6]
    exact par_dot c (by simpa using hc) _ (Nat.mod_lt _ (by norm_num)) j hj6 h3


theorem mulVec_vecN_pow {d : ℕ} (K : Matrix (Fin d) (Fin d) (ZMod 2)) (j : Fin d) :
    K *ᵥ vecN d (2 ^ (j : ℕ)) = fun r => K r j := by
  have : vecN d (2 ^ (j : ℕ)) = Pi.single j 1 := by
    funext r
    simp [vecN, bit, Nat.testBit_two_pow, Pi.single_apply, Fin.ext_iff, eq_comm]
  rw [this, Matrix.mulVec_single_one]
  rfl


@[expose] def commOk1 (d : ℕ) (Pc pre : List ℕ) : Bool :=
  (List.range pre.length).all fun i =>
    decide (2 ^ pre.length ≤ Pc.getD i 0) ||
      (decide (i + 1 < pre.length) && decide (Pc.getD i 0 < 2 ^ (pre.length - 1))) ||
      appC d pre (Pc.getD i 0) % 2 ^ d == appC d Pc (pre.getD i 0) % 2 ^ d

theorem commOk1_of_commOk {d : ℕ} {Pc pre : List ℕ} (h : commOk d Pc pre = true) :
    commOk1 d Pc pre = true := by
  unfold commOk commOk1 at *
  rw [List.all_eq_true] at h ⊢
  intro i hi
  have := h i hi
  simp only [Bool.or_eq_true] at this ⊢
  tauto

theorem bt_mono (d : ℕ) {ok ok' : List ℕ → ℕ → Bool}
    (h : ∀ pre c, ok pre c = true → ok' pre c = true) :
    ∀ n cs, cs ∈ bt d ok n → cs ∈ bt d ok' n := by
  intro n
  induction n with
  | zero => intro cs hcs; simpa [bt] using hcs
  | succ n ih =>
    intro cs hcs
    rw [bt, List.mem_flatMap] at hcs ⊢
    obtain ⟨pre, hpre, hc⟩ := hcs
    refine ⟨pre, ih pre hpre, ?_⟩
    rw [List.mem_map] at hc ⊢
    obtain ⟨c, hc1, hc2⟩ := hc
    refine ⟨c, ?_, hc2⟩
    rw [List.mem_filter] at hc1 ⊢
    exact ⟨hc1.1, h pre c hc1.2⟩

theorem length_of_mem_bt (d : ℕ) {ok : List ℕ → ℕ → Bool} :
    ∀ n cs, cs ∈ bt d ok n → cs.length = n := by
  intro n
  induction n with
  | zero => intro cs hcs; simp [bt] at hcs; simp [hcs]
  | succ n ih =>
    intro cs hcs
    rw [bt, List.mem_flatMap] at hcs
    obtain ⟨pre, hpre, hc⟩ := hcs
    rw [List.mem_map] at hc
    obtain ⟨c, -, rfl⟩ := hc
    simp [ih pre hpre]

@[expose] def leafF (gp : List (List ℕ × List ℕ)) (fullM : List ℕ → Bool) (a : ℕ)
    (cs : List ℕ) : Bool :=
  !(fullM cs) || (isOneL (sqIterL (cubeL cs) a) &&
    (!(isOneL (cubeL cs)) || isOneL cs || spanF (conjL gp cs)))

theorem leafF_imp {gp : List (List ℕ × List ℕ)} (hgp : ∀ p ∈ gp, p.1.length = 6 ∧ p.2.length = 6)
    {fullM : List ℕ → Bool} {a : ℕ} {cs : List ℕ} (hcs : cs.length = 6)
    (h : leafF gp fullM a cs = true) : leafC 6 gp fullM a cs = true := by
  have hc3 : (cubeL cs).length = 6 := by rw [cubeL, length_mulL, length_mulL, hcs]
  have hs : (sqIterL (cubeL cs) a).length = 6 := by rw [length_sqIterL, hc3]
  unfold leafF at h
  unfold leafC
  rw [← isOne_eq hs, ← isOne_eq hc3, ← isOne_eq hcs, sqIterL_eq 6 a _ hc3, cubeL_eq hcs,
    conjL_eq hgp hcs] at h
  have h' := spanF_imp (L := conjC 6 gp cs)
  cases hf : fullM cs
  · simp
  · simp only [hf, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true,
      Bool.not_eq_true'] at h ⊢
    refine ⟨h.1, ?_⟩
    rcases h.2 with (h2 | h2) | h2
    · exact Or.inl (Or.inl h2)
    · exact Or.inl (Or.inr h2)
    · exact Or.inr (h' h2)

end CFSG.Quasithin.H13.A6.GR
