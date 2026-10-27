module

public import CFSG.Sporadic.FischerOddCore.FischerOuterFi24CheckInputs

public section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.Sporadic.Fi24.Native

theorem ap_set (t : Table) (p : ℕ) (x : UInt32) (k : ℕ) :
    ap (t.set! p x) k = if k = p ∧ p < t.size then x.toNat else ap t k := by
  unfold ap
  by_cases hk : k = p
  · subst hk
    by_cases hp : k < t.size
    · rw [if_pos ⟨rfl, hp⟩, Array.set!, getElem!_pos _ k (by simpa using hp),
        Array.getElem_setIfInBounds_self]
    · rw [if_neg (fun h => hp h.2), Array.set!, Array.setIfInBounds, dif_neg hp]
  · rw [if_neg (fun h => hk h.1)]
    by_cases hk' : k < t.size
    · rw [Array.set!, getElem!_pos _ k (by simpa using hk'), getElem!_pos t k hk',
        Array.getElem_setIfInBounds_ne hk' (Ne.symm hk)]
    · rw [getElem!_neg _ k (by simpa using hk'), getElem!_neg t k hk']

theorem size_set (t : Table) (p : ℕ) (x : UInt32) : (t.set! p x).size = t.size := by
  simp [Array.set!]

theorem ap_lt (t : Table) (k : ℕ) : ap t k < 2 ^ 32 := (t[k]!).toNat_lt

@[expose] def tPStep (O : Enum) (tA tB : Table) (t : Table) (p : ℕ) : Table :=
  t.set! p (UInt32.ofNat (if ap O.lab p == 1 then ap tA (ap t (ap O.par p))
    else ap tB (ap t (ap O.par p))))

private theorem tPTable_eq_symbolic (n : Nat) (O : Enum) (tA tB : Table) :
    (Id.run do
      let mut t : Table := Array.replicate n 0
      for p in [1:n] do
        let q := ap t (ap O.par p)
        let v := if ap O.lab p == 1 then ap tA q else ap tB q
        t := t.set! p (UInt32.ofNat v)
      return t) =
      (List.range' 1 (n - 1)).foldl (tPStep O tA tB) (Array.replicate n 0) := by
  unfold tPStep
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size]
  simp only [Nat.div_one, bind_pure]
  rfl

theorem tPTable_eq (O : Enum) (tA tB : Table) :
    tPTable O tA tB = (List.range' 1 (nPts - 1)).foldl (tPStep O tA tB) (Array.replicate nPts 0) := by
  exact tPTable_eq_symbolic nPts O tA tB

@[expose] def tPT (O : Enum) (tA tB : Table) (s : ℕ) : Table :=
  (List.range' 1 s).foldl (tPStep O tA tB) (Array.replicate nPts 0)

theorem tPT_succ (O : Enum) (tA tB : Table) (s : ℕ) :
    tPT O tA tB (s + 1) = tPStep O tA tB (tPT O tA tB s) (1 + s) := by
  unfold tPT
  rw [List.range'_concat, List.foldl_append, Nat.one_mul]
  rfl

theorem tPT_size (O : Enum) (tA tB : Table) : ∀ s, (tPT O tA tB s).size = nPts
  | 0 => by simp [tPT]
  | s + 1 => by rw [tPT_succ, tPStep, size_set, tPT_size O tA tB s]

theorem tPT_zero_entry (O : Enum) (tA tB : Table) : ∀ s, ap (tPT O tA tB s) 0 = 0
  | 0 => by
    change ((Array.replicate nPts (0 : UInt32))[0]!).toNat = 0
    rw [getElem!_pos _ 0 (by simp; decide), Array.getElem_replicate]
    rfl
  | s + 1 => by
    rw [tPT_succ, tPStep, ap_set, if_neg (by omega)]
    exact tPT_zero_entry O tA tB s

theorem tPT_stable (O : Enum) (tA tB : Table) {s k : ℕ} (hk : k < 1 + s) :
    ∀ d, ap (tPT O tA tB (s + d)) k = ap (tPT O tA tB s) k
  | 0 => rfl
  | d + 1 => by
    rw [← Nat.add_assoc, tPT_succ, tPStep, ap_set, if_neg (by omega)]
    exact tPT_stable O tA tB hk d

theorem tPOK_tPTable (O : Enum) (tA tB : Table)
    (hpar : ∀ p, 0 < p → p < nPts → ap O.par p < p) :
    tPOK O tA tB (tPTable O tA tB) = true := by
  rw [tPTable_eq]
  change tPOK O tA tB (tPT O tA tB (nPts - 1)) = true
  unfold tPOK
  rw [Bool.and_eq_true, beq_iff_eq, CFSG.Sporadic.Th.allIn_eq_true]
  refine ⟨tPT_zero_entry _ _ _ _, fun p hp1 hp => ?_⟩
  rw [beq_iff_eq]
  obtain ⟨s, rfl⟩ : ∃ s, p = s + 1 := ⟨p - 1, by omega⟩
  have hfin : ∀ k < 1 + (s + 1), ap (tPT O tA tB (nPts - 1)) k = ap (tPT O tA tB (s + 1)) k :=
    fun k hk => by
      rw [show nPts - 1 = (s + 1) + (nPts - 1 - (s + 1)) by omega]
      exact tPT_stable O tA tB hk _
  have hq := hpar (s + 1) (by omega) hp
  have e : ap (tPT O tA tB (s + 1)) (ap O.par (s + 1)) = ap (tPT O tA tB s) (ap O.par (s + 1)) := by
    rw [tPT_succ, tPStep, ap_set, if_neg (by omega)]
  rw [hfin (s + 1) (by omega), hfin _ (by omega), e, tPT_succ, tPStep, ap_set,
    if_pos ⟨by omega, by rw [tPT_size]; omega⟩, show 1 + s = s + 1 by omega]
  split <;> exact UInt32.toNat_ofNat_of_lt' (ap_lt _ _)

theorem invT_eq_foldl24 (n : ℕ) (P : Table) :
    invT n P = (List.range' 0 n).foldl
      (fun r i => r.setIfInBounds (P[i]!).toNat (UInt32.ofNat i)) (Array.replicate n 0) := by
  unfold invT
  simp [Id.run]
  rfl

theorem invT_foldl_spec24 {n : ℕ} (P : Table) (hlt : ∀ i < n, (P[i]!).toNat < n)
    (hinj : ∀ i < n, ∀ i' < n, (P[i]!).toNat = (P[i']!).toNat → i = i') :
    ∀ m ≤ n, ((List.range' 0 m).foldl
        (fun r i => r.setIfInBounds (P[i]!).toNat (UInt32.ofNat i)) (Array.replicate n 0)).size = n ∧
      ∀ i < m, ((List.range' 0 m).foldl
        (fun r i => r.setIfInBounds (P[i]!).toNat (UInt32.ofNat i))
          (Array.replicate n 0))[(P[i]!).toNat]! = UInt32.ofNat i := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    obtain ⟨hs, hi⟩ := ih (by omega)
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [zero_add, one_mul]
    set r := (List.range' 0 m).foldl (fun r i => r.setIfInBounds (P[i]!).toNat (UInt32.ofNat i))
      (Array.replicate n 0) with hr
    refine ⟨by rw [Array.size_setIfInBounds, hs], fun i hi' => ?_⟩
    have hmn : m < n := by omega
    have hPm := hlt m hmn
    have hbound : (P[m]!).toNat < (r.setIfInBounds (P[m]!).toNat (UInt32.ofNat m)).size := by
      rw [Array.size_setIfInBounds, hs]; exact hPm
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with hlt' | heq
    · have hne : (P[m]!).toNat ≠ (P[i]!).toNat := fun h' => by
        have := hinj m hmn i (by omega) h'
        omega
      have hbi : (P[i]!).toNat < r.size := by rw [hs]; exact hlt i (by omega)
      have hbi' : (P[i]!).toNat < (r.setIfInBounds (P[m]!).toNat (UInt32.ofNat m)).size := by
        rw [Array.size_setIfInBounds]; exact hbi
      rw [getElem!_pos (r.setIfInBounds (P[m]!).toNat (UInt32.ofNat m)) (P[i]!).toNat hbi',
        Array.getElem_setIfInBounds_ne hbi hne, ← getElem!_pos r (P[i]!).toNat hbi]
      exact hi i hlt'
    · subst heq
      rw [getElem!_pos (r.setIfInBounds (P[i]!).toNat (UInt32.ofNat i)) (P[i]!).toNat hbound,
        Array.getElem_setIfInBounds_self]

theorem rep_invT24 {G : Type*} [Group G] [MulAction G (Fin 306936)] {T : Table} {g : G}
    (hT : Rep 306936 T g) : Rep 306936 (invT 306936 T) g⁻¹ := by
  have hlt : ∀ i < 306936, (T[i]!).toNat < 306936 := by
    intro i hi
    have := hT i hi
    unfold ap at this
    rw [this]
    exact idx_lt g hi
  have hinj : ∀ i < 306936, ∀ i' < 306936, (T[i]!).toNat = (T[i']!).toNat → i = i' := by
    intro i hi i' hi' h
    have h1 := hT i hi
    have h2 := hT i' hi'
    unfold ap at h1 h2
    rw [h1, h2] at h
    have := congrArg (idx 306936 g⁻¹) h
    rwa [idx_inv_idx, idx_inv_idx] at this
  refine Rep.inv_of_invOK hT ?_
  rw [invOK, CFSG.Sporadic.Th.allIn_eq_true]
  intro i _ hi
  have h := (invT_foldl_spec24 T hlt hinj 306936 le_rfl).2 i hi
  rw [← invT_eq_foldl24] at h
  rw [beq_iff_eq]
  unfold ap
  rw [h, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (hi.trans (by norm_num))]

theorem pack_facts {p l : ℕ} (hp : p < 2 ^ 30) (hl : l < 4) :
    treePar (p ||| (l <<< 30)) = p ∧ treeLab (p ||| (l <<< 30)) = l := by
  have hpb : ∀ i, 30 ≤ i → p.testBit i = false := fun i hi =>
    Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hp (Nat.pow_le_pow_right (by norm_num) hi))
  refine ⟨Nat.eq_of_testBit_eq fun i => ?_, Nat.eq_of_testBit_eq fun i => ?_⟩
  · unfold treePar
    rw [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftLeft,
      show (0x3FFFFFFF : ℕ) = 2 ^ 30 - 1 by norm_num, Nat.testBit_two_pow_sub_one]
    by_cases hi : i < 30
    · simp [hi, show ¬ 30 ≤ i by omega]
    · simp [hi, hpb i (by omega)]
  · unfold treeLab
    rw [Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_shiftLeft, hpb _ (by omega)]
    simp

theorem toNat_pack {a b : UInt32} (hb : b.toNat < 4) :
    (a ||| (b <<< 30)).toNat = a.toNat ||| (b.toNat <<< 30) := by
  have h30 : (30 : UInt32).toNat % 32 = 30 := by decide
  have hlt : b.toNat <<< 30 < 2 ^ 32 := by rw [Nat.shiftLeft_eq]; omega
  rw [UInt32.toNat_or, UInt32.toNat_shiftLeft, h30, Nat.mod_eq_of_lt hlt]

theorem fo24Packed_facts :
    ∀ i < 306936, 0 < i → treePar (ap (fo24Packed CFSG.Sporadic.Fi24.orb) i) =
        ap CFSG.Sporadic.Fi24.orb.par i ∧
      treeLab (ap (fo24Packed CFSG.Sporadic.Fi24.orb) i) = ap CFSG.Sporadic.Fi24.orb.lab i := by
  intro i hi hpos
  have hb : ap CFSG.Sporadic.Fi24.orb.par i < 2 ^ 30 ∧ ap CFSG.Sporadic.Fi24.orb.lab i < 4 := by
    obtain ⟨hlt, hc⟩ := CFSG.Sporadic.Fi24.tree_facts i hi hpos
    refine ⟨by omega, ?_⟩
    rcases hc with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  have e : ap (fo24Packed CFSG.Sporadic.Fi24.orb) i =
      ap CFSG.Sporadic.Fi24.orb.par i ||| (ap CFSG.Sporadic.Fi24.orb.lab i <<< 30) := by
    unfold fo24Packed ap
    rw [getElem!_pos _ i (by simp [CFSG.Sporadic.Fi24.nPts_eq]; exact hi), Array.getElem_ofFn]
    exact toNat_pack hb.2
  rw [e]
  exact pack_facts hb.1 hb.2

end CFSG.Sporadic.FischerOddCore

end
