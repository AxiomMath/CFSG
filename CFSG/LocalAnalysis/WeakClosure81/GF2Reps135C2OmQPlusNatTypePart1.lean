module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusNat

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.Quasithin.SmithCurtis CFSG.LieType.Steinberg
open scoped Matrix

variable {F : Type} [Field F] [Finite F] [CharP F 2] {k : Type} [Field k] [CharP k 2]

theorem c2slomqnt_rep_apply {n : ℕ} {F k : Type} [Field F] [Field k] (φ : F →+* k)
    (g : spinGroup (quadPlus n F)) (v : Fin n ⊕ Fin n → k) :
    (omPlusNatRep n φ) g v =
      ((spinMatrix (quadPlus n F) g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).map φ) *ᵥ v := by
  simp [omPlusNatRep, Matrix.toLin'_apply]

theorem c2slomqnt_mapVec {n : ℕ} {F k : Type} [Field F] [Field k] (φ : F →+* k)
    (g : spinGroup (quadPlus n F)) (v : Fin n ⊕ Fin n → F) :
    (omPlusNatRep n φ) g (fun a => φ (v a)) =
      fun a => φ (spinAction (quadPlus n F) g v a) := by
  rw [c2slomqnt_rep_apply]
  have hact : ((spinMatrix (quadPlus n F) g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ v) =
      spinAction (quadPlus n F) g v := spinMatrix_mulVec (quadPlus n F) g v
  rw [← hact]
  ext a
  rw [RingHom.map_mulVec]
  rfl

omit [Finite F] [CharP F 2] [CharP k 2] in
theorem c2slomqnt_phi_plusVec_true {n : ℕ} (φ : F →+* k) (i : Fin n) :
    (fun a => φ (plusVec n F i true a)) =
      (Pi.single (Sum.inl i) (1 : k) : Fin n ⊕ Fin n → k) := by
  funext a
  simp only [plusVec_true, Pi.single_apply]
  split_ifs <;> simp

theorem c2slomqnt_rootIdxD_val_ne_zero {n : ℕ} (hn : 3 ≤ n) {s : Fin n}
    (hs : s.val ≠ 0) : (rootIdxD n s).val ≠ 0 := by
  by_cases h : s.val + 1 < n
  · rw [rootIdxD_of_lt n h]; exact hs
  · rw [val_rootIdxD_of_not_lt n h]; omega

theorem c2slomqnt_rootIdxD'_val_ne_zero {n : ℕ} (hn : 3 ≤ n) (s : Fin n) :
    (rootIdxD' n s).val ≠ 0 := by
  by_cases h : s.val + 1 < n
  · rw [rootIdxD'_of_lt n h]; exact Nat.succ_ne_zero _
  · rw [val_rootIdxD'_of_not_lt n h]; omega

theorem c2slomqnt_sign_left {n : ℕ} (hn : 3 ≤ n) {γ : Fin n → ℤ} {i j : Fin n}
    (_hij : i ≠ j) {s t : Bool}
    (hstd : toStdD n γ = Pi.single i (boolSign s) + Pi.single j (boolSign t))
    (hpos : 0 < ht γ) (hlt : i.val < j.val) : s = true := by
  have hb : boolSign s = 1 :=
    (ht_pos_iff_of_toStdD_eq_add (n := n) (by omega) (i := i) (j := j) hlt
      (by cases s <;> simp [boolSign]) (by cases t <;> simp [boolSign]) hstd).mp hpos
  cases s
  · norm_num [boolSign] at hb
  · rfl

theorem c2slomqnt_sign_right {n : ℕ} (hn : 3 ≤ n) {γ : Fin n → ℤ} {i j : Fin n}
    (hij : i ≠ j) {s t : Bool}
    (hstd : toStdD n γ = Pi.single i (boolSign s) + Pi.single j (boolSign t))
    (hpos : 0 < ht γ) (hlt : j.val < i.val) : t = true :=
  c2slomqnt_sign_left hn hij.symm (by rw [hstd, add_comm]) hpos hlt

omit [Finite F] [CharP F 2] [Field k] [CharP k 2] in
theorem c2slomqnt_longRoot_fix_vec {n : ℕ} (hn : 3 ≤ n) {γ : Fin n → ℤ}
    {i j : Fin n} (hij : i ≠ j) {s t : Bool}
    (hstd : toStdD n γ = Pi.single i (boolSign s) + Pi.single j (boolSign t))
    (hpos : 0 < ht γ) (c : F) :
    spinAction (quadPlus n F) ((plusFrame n F hn).longRoot hij s t (.ofAdd c))
      (plusVec n F (⟨0, by omega⟩ : Fin n) true) =
      plusVec n F (⟨0, by omega⟩ : Fin n) true := by
  by_cases hi : i = (⟨0, by omega⟩ : Fin n)
  · have hne : j.val ≠ 0 := fun h0 => hij (hi.trans (Fin.ext h0.symm))
    have hlt : i.val < j.val := by
      rw [hi]; show (0 : ℕ) < j.val; omega
    have hs : s = true := c2slomqnt_sign_left hn hij hstd hpos hlt
    subst hi
    rw [hs]
    change spinAction (quadPlus n F)
        ((plusFrame n F hn).longRoot hij true t (.ofAdd c))
        ((plusFrame n F hn).vec (⟨0, by omega⟩ : Fin n) true) =
        (plusFrame n F hn).vec (⟨0, by omega⟩ : Fin n) true
    rw [HypFrame.spinAction_longRoot_vec_left]
  · by_cases hj : j = (⟨0, by omega⟩ : Fin n)
    · have hne : i.val ≠ 0 := fun h0 => hi (Fin.ext h0)
      have hlt : j.val < i.val := by
        rw [hj]; show (0 : ℕ) < i.val; omega
      have ht' : t = true := c2slomqnt_sign_right hn hij hstd hpos hlt
      subst hj
      rw [ht']
      change spinAction (quadPlus n F)
          ((plusFrame n F hn).longRoot hij s true (.ofAdd c))
          ((plusFrame n F hn).vec (⟨0, by omega⟩ : Fin n) true) =
          (plusFrame n F hn).vec (⟨0, by omega⟩ : Fin n) true
      rw [HypFrame.spinAction_longRoot_vec_right]
    · change spinAction (quadPlus n F)
          ((plusFrame n F hn).longRoot hij s t (.ofAdd c))
          ((plusFrame n F hn).vec (⟨0, by omega⟩ : Fin n) true) =
          (plusFrame n F hn).vec (⟨0, by omega⟩ : Fin n) true
      rw [HypFrame.spinAction_longRoot_vec_of_ne (F := plusFrame n F hn) hij s t c
        (fun h => hi h.symm) (fun h => hj h.symm) true]

omit [Finite F] [CharP F 2] [CharP k 2] in
theorem c2slomqnt_longRoot_fix_e0 {n : ℕ} (hn : 3 ≤ n) {γ : Fin n → ℤ}
    {i j : Fin n} (hij : i ≠ j) {s t : Bool}
    (hstd : toStdD n γ = Pi.single i (boolSign s) + Pi.single j (boolSign t))
    (hpos : 0 < ht γ) (φ : F →+* k) (c : F) :
    (omPlusNatRep n φ) ((plusFrame n F hn).longRoot hij s t (.ofAdd c))
      (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k)) =
      Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k) := by
  calc (omPlusNatRep n φ) ((plusFrame n F hn).longRoot hij s t (.ofAdd c))
        (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k))
      = (omPlusNatRep n φ) ((plusFrame n F hn).longRoot hij s t (.ofAdd c))
          (fun a => φ (plusVec n F (⟨0, by omega⟩ : Fin n) true a)) := by
          rw [c2slomqnt_phi_plusVec_true]
    _ = (fun a => φ (spinAction (quadPlus n F)
          ((plusFrame n F hn).longRoot hij s t (.ofAdd c))
          (plusVec n F (⟨0, by omega⟩ : Fin n) true) a)) :=
          c2slomqnt_mapVec φ _ _
    _ = (fun a => φ (plusVec n F (⟨0, by omega⟩ : Fin n) true a)) := by
          rw [c2slomqnt_longRoot_fix_vec hn hij hstd hpos c]
    _ = Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k) :=
          c2slomqnt_phi_plusVec_true φ (⟨0, by omega⟩ : Fin n)

def c2slomqnt_stab {n : ℕ} (φ : F →+* k) (v : Fin n ⊕ Fin n → k) :
    Subgroup (spinGroup (quadPlus n F)) where
  carrier := {g | (omPlusNatRep n φ) g v = v}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    have ha' : (omPlusNatRep n φ) a v = v := ha
    have hb' : (omPlusNatRep n φ) b v = v := hb
    change (omPlusNatRep n φ) (a * b) v = v
    rw [map_mul, Module.End.mul_apply, hb', ha']
  inv_mem' := by
    intro a ha
    have ha' : (omPlusNatRep n φ) a v = v := ha
    change (omPlusNatRep n φ) a⁻¹ v = v
    have h1 : (omPlusNatRep n φ) a⁻¹ * (omPlusNatRep n φ) a = 1 := by
      rw [← map_mul, inv_mul_cancel, map_one]
    have h2 : (omPlusNatRep n φ) a⁻¹ ((omPlusNatRep n φ) a v) = v := by
      rw [← Module.End.mul_apply, h1, Module.End.one_apply]
    rwa [ha'] at h2

omit [CharP k 2] in
theorem c2slomqnt_fixU {n : ℕ} (hn : 3 ≤ n) (φ : F →+* k) :
    (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k)) ∈
      (omPlusCurtisDatum n F hn).fixU (omPlusNatRep n φ) := by
  rw [CurtisDatum.mem_fixU, omPlusCurtisDatum_U]
  intro u hu
  change u ∈ c2slomqnt_stab (n := n) φ
    (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k))
  change u ∈ (⨆ γ ∈ {γ | γ ∈ (plusDatum n F hn).roots ∧ 0 < ht γ},
    (plusDatum n F hn).rootGroup γ) at hu
  have hle : (⨆ γ ∈ {γ | γ ∈ (plusDatum n F hn).roots ∧ 0 < ht γ},
      (plusDatum n F hn).rootGroup γ) ≤ c2slomqnt_stab (n := n) φ
      (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k)) := by
    refine iSup₂_le fun γ hγ => ?_
    intro x hx
    obtain ⟨hroot, hpos⟩ := hγ
    rw [plusDatum_roots] at hroot
    obtain ⟨i, j, hij, s, t, hstd, hX⟩ := exists_plusRootGroup_eq (K := F) hn hroot
    change x ∈ plusRootGroup n F hn γ at hx
    rw [hX] at hx
    obtain ⟨c, rfl⟩ := hx
    exact c2slomqnt_longRoot_fix_e0 hn hij hstd hpos φ c
  exact hle hu

theorem c2slomqnt_XEquiv_bijective {n : ℕ} (hn : 3 ≤ n) (s : Fin n) :
    Function.Bijective (fun c : F =>
      (⟨rootD F hn s (.ofAdd c), by
        rw [omPlusCurtisDatum_X, plusRootGroup_single hn s]
        exact ⟨.ofAdd c, rfl⟩⟩ : (omPlusCurtisDatum n F hn).X s)) := by
  refine ⟨fun a b h => ?_, fun x => ?_⟩
  · have h1 : rootD F hn s (.ofAdd a) = rootD F hn s (.ofAdd b) := congrArg Subtype.val h
    have h2 : Multiplicative.ofAdd a = Multiplicative.ofAdd b :=
      HypFrame.longRoot_injective (plusFrame n F hn) (rootIdxD_ne n (by omega) s) true
        (rootSignD n s) (by simpa only [rootD] using h1)
    simpa using h2
  · have hx : (x : spinGroup (quadPlus n F)) ∈ (rootD F hn s).range := by
      have hx' : (x : spinGroup (quadPlus n F)) ∈ plusRootGroup n F hn (Pi.single s 1) := by
        simpa only [omPlusCurtisDatum_X] using x.2
      simpa only [plusRootGroup_single hn s] using hx'
    obtain ⟨c, hc⟩ := hx
    exact ⟨c.toAdd, Subtype.ext (by simpa using hc)⟩

noncomputable def c2slomqnt_XEquiv {n : ℕ} (hn : 3 ≤ n) (s : Fin n) :
    F ≃ (omPlusCurtisDatum n F hn).X s :=
  Equiv.ofBijective _ (c2slomqnt_XEquiv_bijective hn s)

omit [Finite F] [CharP k 2] in
theorem c2slomqnt_weylD_zero_e0 {n : ℕ} (hn : 3 ≤ n) (φ : F →+* k) :
    (omPlusNatRep n φ) (weylD F hn (⟨0, by omega⟩ : Fin n))
      (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k)) =
      Pi.single (Sum.inl (⟨1, by omega⟩ : Fin n)) (1 : k) := by
  have hvec : spinAction (quadPlus n F) (weylD F hn (⟨0, by omega⟩ : Fin n))
      (plusVec n F (⟨0, by omega⟩ : Fin n) true) =
      plusVec n F (⟨1, by omega⟩ : Fin n) true := by
    rw [spinAction_weylD,
      rootIdxD_of_lt n (k := (⟨0, by omega⟩ : Fin n)) (by show (0 : ℕ) + 1 < n; omega),
      rootIdxD'_of_lt n (k := (⟨0, by omega⟩ : Fin n)) (by show (0 : ℕ) + 1 < n; omega),
      rootSignD_of_lt n (k := (⟨0, by omega⟩ : Fin n)) (by show (0 : ℕ) + 1 < n; omega)]
    simp [longWeylBool, longWeylSign, CharTwo.neg_eq]
  calc (omPlusNatRep n φ) (weylD F hn (⟨0, by omega⟩ : Fin n))
        (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k))
      = (omPlusNatRep n φ) (weylD F hn (⟨0, by omega⟩ : Fin n))
          (fun a => φ (plusVec n F (⟨0, by omega⟩ : Fin n) true a)) := by
          rw [c2slomqnt_phi_plusVec_true]
    _ = (fun a => φ (spinAction (quadPlus n F) (weylD F hn (⟨0, by omega⟩ : Fin n))
          (plusVec n F (⟨0, by omega⟩ : Fin n) true) a)) := c2slomqnt_mapVec φ _ _
    _ = (fun a => φ (plusVec n F (⟨1, by omega⟩ : Fin n) true a)) := by rw [hvec]
    _ = Pi.single (Sum.inl (⟨1, by omega⟩ : Fin n)) (1 : k) :=
          c2slomqnt_phi_plusVec_true φ (⟨1, by omega⟩ : Fin n)

omit [Finite F] [CharP F 2] [CharP k 2] in
theorem c2slomqnt_rootD_zero_e1 {n : ℕ} (hn : 3 ≤ n) (φ : F →+* k) (c : F) :
    (omPlusNatRep n φ) (rootD F hn (⟨0, by omega⟩ : Fin n) (.ofAdd c))
      (Pi.single (Sum.inl (⟨1, by omega⟩ : Fin n)) (1 : k)) =
      Pi.single (Sum.inl (⟨1, by omega⟩ : Fin n)) (1 : k) +
        φ c • Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k) := by
  have h1 : (plusVec n F (⟨1, by omega⟩ : Fin n) true) =
      (plusFrame n F hn).vec (rootIdxD' n (⟨0, by omega⟩ : Fin n))
        (!(rootSignD n (⟨0, by omega⟩ : Fin n))) := by
    rw [rootIdxD'_of_lt n (k := (⟨0, by omega⟩ : Fin n)) (by show (0 : ℕ) + 1 < n; omega),
      rootSignD_of_lt n (k := (⟨0, by omega⟩ : Fin n)) (by show (0 : ℕ) + 1 < n; omega)]
    rfl
  have h2 : (plusFrame n F hn).vec (rootIdxD n (⟨0, by omega⟩ : Fin n)) true =
      plusVec n F (⟨0, by omega⟩ : Fin n) true := by
    rw [rootIdxD_of_lt n (k := (⟨0, by omega⟩ : Fin n)) (by show (0 : ℕ) + 1 < n; omega)]
    rfl
  have hvec : spinAction (quadPlus n F) (rootD F hn (⟨0, by omega⟩ : Fin n) (.ofAdd c))
      (plusVec n F (⟨1, by omega⟩ : Fin n) true) =
      plusVec n F (⟨1, by omega⟩ : Fin n) true +
        c • plusVec n F (⟨0, by omega⟩ : Fin n) true := by
    rw [rootD]
    conv_lhs => rw [h1]
    rw [HypFrame.spinAction_longRoot_vec_not_right]
    rw [← h1, h2]
  calc (omPlusNatRep n φ) (rootD F hn (⟨0, by omega⟩ : Fin n) (.ofAdd c))
        (Pi.single (Sum.inl (⟨1, by omega⟩ : Fin n)) (1 : k))
      = (omPlusNatRep n φ) (rootD F hn (⟨0, by omega⟩ : Fin n) (.ofAdd c))
          (fun a => φ (plusVec n F (⟨1, by omega⟩ : Fin n) true a)) := by
          rw [c2slomqnt_phi_plusVec_true]
    _ = (fun a => φ (spinAction (quadPlus n F)
          (rootD F hn (⟨0, by omega⟩ : Fin n) (.ofAdd c))
          (plusVec n F (⟨1, by omega⟩ : Fin n) true) a)) := c2slomqnt_mapVec φ _ _
    _ = (fun a => φ ((plusVec n F (⟨1, by omega⟩ : Fin n) true +
          c • plusVec n F (⟨0, by omega⟩ : Fin n) true) a)) := by rw [hvec]
    _ = Pi.single (Sum.inl (⟨1, by omega⟩ : Fin n)) (1 : k) +
        φ c • Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k) := by
          rw [← c2slomqnt_phi_plusVec_true φ (⟨1, by omega⟩ : Fin n),
            ← c2slomqnt_phi_plusVec_true φ (⟨0, by omega⟩ : Fin n)]
          ext a
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]

omit [Finite F] [CharP F 2] [CharP k 2] in
theorem c2slomqnt_weylD_ne_zero_e0 {n : ℕ} (hn : 3 ≤ n) {s : Fin n}
    (hs : s.val ≠ 0) (φ : F →+* k) :
    (omPlusNatRep n φ) (weylD F hn s)
      (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k)) =
      Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k) := by
  have h0a : (⟨0, by omega⟩ : Fin n) ≠ rootIdxD n s := fun h =>
    c2slomqnt_rootIdxD_val_ne_zero hn hs (by simpa using congrArg Fin.val h.symm)
  have h0b : (⟨0, by omega⟩ : Fin n) ≠ rootIdxD' n s := fun h =>
    c2slomqnt_rootIdxD'_val_ne_zero hn s (by simpa using congrArg Fin.val h.symm)
  have hvec : spinAction (quadPlus n F) (weylD F hn s)
      (plusVec n F (⟨0, by omega⟩ : Fin n) true) =
      plusVec n F (⟨0, by omega⟩ : Fin n) true := by
    rw [spinAction_weylD, Equiv.swap_apply_of_ne_of_ne h0a h0b,
      longWeylBool_of_ne true (rootSignD n s) h0a h0b, longWeylSign_of_ne h0a]
    rw [one_smul]
  calc (omPlusNatRep n φ) (weylD F hn s)
        (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k))
      = (omPlusNatRep n φ) (weylD F hn s)
          (fun a => φ (plusVec n F (⟨0, by omega⟩ : Fin n) true a)) := by
          rw [c2slomqnt_phi_plusVec_true]
    _ = (fun a => φ (spinAction (quadPlus n F) (weylD F hn s)
          (plusVec n F (⟨0, by omega⟩ : Fin n) true) a)) := c2slomqnt_mapVec φ _ _
    _ = Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k) := by
          rw [hvec, c2slomqnt_phi_plusVec_true]

omit [Finite F] [CharP F 2] [CharP k 2] in
theorem c2slomqnt_rootD_ne_zero_e0 {n : ℕ} (hn : 3 ≤ n) {s : Fin n}
    (hs : s.val ≠ 0) (φ : F →+* k) (c : F) :
    (omPlusNatRep n φ) (rootD F hn s (.ofAdd c))
      (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k)) =
      Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k) := by
  have h0a : (⟨0, by omega⟩ : Fin n) ≠ rootIdxD n s := fun h =>
    c2slomqnt_rootIdxD_val_ne_zero hn hs (by simpa using congrArg Fin.val h.symm)
  have h0b : (⟨0, by omega⟩ : Fin n) ≠ rootIdxD' n s := fun h =>
    c2slomqnt_rootIdxD'_val_ne_zero hn s (by simpa using congrArg Fin.val h.symm)
  have hvec : spinAction (quadPlus n F) (rootD F hn s (.ofAdd c))
      (plusVec n F (⟨0, by omega⟩ : Fin n) true) =
      plusVec n F (⟨0, by omega⟩ : Fin n) true := by
    change spinAction (quadPlus n F)
        ((plusFrame n F hn).longRoot (rootIdxD_ne n (by omega) s) true (rootSignD n s) (.ofAdd c))
        ((plusFrame n F hn).vec (⟨0, by omega⟩ : Fin n) true) =
        (plusFrame n F hn).vec (⟨0, by omega⟩ : Fin n) true
    rw [HypFrame.spinAction_longRoot_vec_of_ne (F := plusFrame n F hn) (rootIdxD_ne n (by omega) s)
      true (rootSignD n s) c h0a h0b true]
  calc (omPlusNatRep n φ) (rootD F hn s (.ofAdd c))
        (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k))
      = (omPlusNatRep n φ) (rootD F hn s (.ofAdd c))
          (fun a => φ (plusVec n F (⟨0, by omega⟩ : Fin n) true a)) := by
          rw [c2slomqnt_phi_plusVec_true]
    _ = (fun a => φ (spinAction (quadPlus n F) (rootD F hn s (.ofAdd c))
          (plusVec n F (⟨0, by omega⟩ : Fin n) true) a)) := c2slomqnt_mapVec φ _ _
    _ = Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k) := by
          rw [hvec, c2slomqnt_phi_plusVec_true]

end CFSG.LocalAnalysis.WeakClosure81
