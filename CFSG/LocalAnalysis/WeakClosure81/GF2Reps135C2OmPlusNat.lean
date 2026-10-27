module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusCurtis
import CFSG.RankThree.GF2n.Stroth80.Sec78NatIrredOmega

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.Quasithin.SmithCurtis CFSG.LieType.Steinberg
open scoped Matrix

@[expose] noncomputable def omPlusNatRep (n : ℕ) {F k : Type} [Field F] [Field k] (φ : F →+* k) :
    Representation k (spinGroup (quadPlus n F)) (Fin n ⊕ Fin n → k) where
  toFun g := Matrix.toLin'
    ((spinMatrix (quadPlus n F) g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).map φ)
  map_one' := by simp; rfl
  map_mul' g h := by
    rw [map_mul, Units.val_mul, Matrix.map_mul, Matrix.toLin'_mul]
    rfl

theorem omPlusNat_rep_apply {n : ℕ} {F k : Type} [Field F] [Field k] (φ : F →+* k)
    (g : spinGroup (quadPlus n F)) (v : Fin n ⊕ Fin n → k) :
    (omPlusNatRep n φ) g v =
      ((spinMatrix (quadPlus n F) g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).map φ) *ᵥ v := by
  simp [omPlusNatRep, Matrix.toLin'_apply]

private theorem omPlusNat_mapVec {n : ℕ} {F k : Type} [Field F] [Field k] (φ : F →+* k)
    (g : spinGroup (quadPlus n F)) (v : Fin n ⊕ Fin n → F) :
    (omPlusNatRep n φ) g (fun a => φ (v a)) =
      fun a => φ (spinAction (quadPlus n F) g v a) := by
  rw [omPlusNat_rep_apply]
  have hact : ((spinMatrix (quadPlus n F) g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ v) =
      spinAction (quadPlus n F) g v := spinMatrix_mulVec (quadPlus n F) g v
  rw [← hact]
  ext a
  rw [RingHom.map_mulVec]
  rfl

private def omPlusNat_preimage {n : ℕ} {F k : Type} [Field F] [Field k] (φ : F ≃+* k)
    (W : Submodule k (Fin n ⊕ Fin n → k)) : Submodule F (Fin n ⊕ Fin n → F) :=
  { carrier := {v | (fun i => φ (v i)) ∈ W}
    zero_mem' := by
      change (fun i => φ ((0 : Fin n ⊕ Fin n → F) i)) ∈ W
      rw [show (fun i => φ ((0 : Fin n ⊕ Fin n → F) i)) = 0 by ext i; simp]
      exact W.zero_mem
    add_mem' := by
      intro a b ha hb
      change (fun i => φ ((a + b) i)) ∈ W
      rw [show (fun i => φ ((a + b) i)) =
          (fun i => φ (a i)) + (fun i => φ (b i)) by
        ext i; simp [Pi.add_apply, map_add]]
      exact W.add_mem ha hb
    smul_mem' := by
      intro c v hv
      change (fun i => φ ((c • v) i)) ∈ W
      rw [show (fun i => φ ((c • v) i)) = φ c • (fun i => φ (v i)) by
        ext i; simp [Pi.smul_apply, map_mul]]
      exact W.smul_mem (φ c) hv }

private theorem omPlusNat_preimage_natIrred {n : ℕ} (hn : 3 ≤ n) {F k : Type} [Field F]
    [Field k] (φ : F ≃+* k) (W : Submodule k (Fin n ⊕ Fin n → k))
    (hW : ∀ g, ∀ w ∈ W, (omPlusNatRep n (φ : F →+* k)) g w ∈ W) :
    omPlusNat_preimage (n := n) φ W = ⊥ ∨ omPlusNat_preimage (n := n) φ W = ⊤ := by
  have hW'mem : ∀ g ∈ CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus n F),
      ∀ v ∈ omPlusNat_preimage (n := n) φ W,
      (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ v ∈
        omPlusNat_preimage (n := n) φ W := by
    intro g hg v hv
    obtain ⟨u, rfl⟩ := (range_spinMatrix_quadPlus (K := F) hn).symm ▸ hg
    change (fun i => φ (((spinMatrix (quadPlus n F) u) *ᵥ v) i)) ∈ W
    have h1 : (omPlusNatRep n (φ : F →+* k)) u (fun i => φ (v i)) ∈ W := hW u _ hv
    have h2 : (omPlusNatRep n (φ : F →+* k)) u (fun i => φ (v i)) =
        (fun i => φ (((spinMatrix (quadPlus n F) u) *ᵥ v) i)) := by
      rw [omPlusNat_rep_apply]
      ext i
      exact (RingHom.map_mulVec (φ : F →+* k) (spinMatrix (quadPlus n F) u) v i).symm
    rwa [h2] at h1
  exact CFSG.RankThree.GF2n.Stroth80.natIrred_statedOmegaPlus (K := F) (m := n) hn _ hW'mem

theorem isSimpleRep_omPlusNatRep {n : ℕ} (hn : 3 ≤ n) {F k : Type} [Field F] [Field k]
    (φ : F ≃+* k) : IsSimpleRep (omPlusNatRep n (φ : F →+* k)) := by
  refine ⟨⟨fun _ => (1 : k), fun _ => (0 : k), fun h =>
    one_ne_zero (congrFun h (Sum.inl (⟨0, by omega⟩ : Fin n)))⟩, fun W hW => ?_⟩
  rcases omPlusNat_preimage_natIrred hn φ W hW with hbot | htop
  · left
    rw [Submodule.eq_bot_iff]
    intro w hw
    let v : Fin n ⊕ Fin n → F := fun i => φ.symm (w i)
    have hmv : (fun i => φ (v i)) = w := by ext i; simp [v]
    have hv : v ∈ omPlusNat_preimage (n := n) φ W := by
      change (fun i => φ (v i)) ∈ W
      rw [hmv]; exact hw
    have hv0 : v = 0 := by
      have : v ∈ (⊥ : Submodule F (Fin n ⊕ Fin n → F)) := hbot ▸ hv
      simpa using this
    rw [← hmv, hv0]
    ext i; simp
  · right
    rw [Submodule.eq_top_iff']
    intro w
    let v : Fin n ⊕ Fin n → F := fun i => φ.symm (w i)
    have hmv : (fun i => φ (v i)) = w := by ext i; simp [v]
    have hv : v ∈ omPlusNat_preimage (n := n) φ W := htop ▸ Submodule.mem_top
    have : (fun i => φ (v i)) ∈ W := hv
    rwa [hmv] at this

variable {F : Type} [Field F] [Finite F] [CharP F 2] {k : Type} [Field k] [CharP k 2]

omit [Finite F] [CharP F 2] [CharP k 2] in
private theorem omPlusNat_sum_field [Fintype F] (φ : F →+* k) (hF : Nat.card F = 2) :
    (∑ c : F, φ c) = 1 := by
  classical
  have hcard : (Finset.univ : Finset F).card = 2 := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact hF
  have hset : ({(0 : F), 1} : Finset F) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair zero_ne_one]
    exact hcard.symm
  rw [← hset, Finset.sum_pair zero_ne_one]
  simp

omit [Finite F] [CharP F 2] [CharP k 2] in
private theorem omPlusNat_phi_plusVec_true {n : ℕ} (φ : F →+* k) (i : Fin n) :
    (fun a => φ (plusVec n F i true a)) =
      (Pi.single (Sum.inl i) (1 : k) : Fin n ⊕ Fin n → k) := by
  funext a
  simp only [plusVec_true, Pi.single_apply]
  split_ifs <;> simp

private theorem omPlusNat_rootIdxD_val_ne_zero {n : ℕ} (hn : 3 ≤ n) {s : Fin n}
    (hs : s.val ≠ 0) : (rootIdxD n s).val ≠ 0 := by
  by_cases h : s.val + 1 < n
  · rw [rootIdxD_of_lt n h]; exact hs
  · rw [val_rootIdxD_of_not_lt n h]; omega

private theorem omPlusNat_rootIdxD'_val_ne_zero {n : ℕ} (hn : 3 ≤ n) (s : Fin n) :
    (rootIdxD' n s).val ≠ 0 := by
  by_cases h : s.val + 1 < n
  · rw [rootIdxD'_of_lt n h]; exact Nat.succ_ne_zero _
  · rw [val_rootIdxD'_of_not_lt n h]; omega

private theorem omPlusNat_sign_left {n : ℕ} (hn : 3 ≤ n) {γ : Fin n → ℤ} {i j : Fin n}
    (_hij : i ≠ j) {s t : Bool}
    (hstd : toStdD n γ = Pi.single i (boolSign s) + Pi.single j (boolSign t))
    (hpos : 0 < ht γ) (hlt : i.val < j.val) : s = true := by
  have hb : boolSign s = 1 :=
    (ht_pos_iff_of_toStdD_eq_add (n := n) (by omega) (i := i) (j := j) hlt
      (by cases s <;> simp [boolSign]) (by cases t <;> simp [boolSign]) hstd).mp hpos
  cases s
  · norm_num [boolSign] at hb
  · rfl

private theorem omPlusNat_sign_right {n : ℕ} (hn : 3 ≤ n) {γ : Fin n → ℤ} {i j : Fin n}
    (hij : i ≠ j) {s t : Bool}
    (hstd : toStdD n γ = Pi.single i (boolSign s) + Pi.single j (boolSign t))
    (hpos : 0 < ht γ) (hlt : j.val < i.val) : t = true :=
  omPlusNat_sign_left hn hij.symm (by rw [hstd, add_comm]) hpos hlt

omit [Finite F] [CharP F 2] [Field k] [CharP k 2] in
private theorem omPlusNat_longRoot_fix_vec {n : ℕ} (hn : 3 ≤ n) {γ : Fin n → ℤ}
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
    have hs : s = true := omPlusNat_sign_left hn hij hstd hpos hlt
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
      have ht' : t = true := omPlusNat_sign_right hn hij hstd hpos hlt
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
private theorem omPlusNat_longRoot_fix_e0 {n : ℕ} (hn : 3 ≤ n) {γ : Fin n → ℤ}
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
          rw [omPlusNat_phi_plusVec_true]
    _ = (fun a => φ (spinAction (quadPlus n F)
          ((plusFrame n F hn).longRoot hij s t (.ofAdd c))
          (plusVec n F (⟨0, by omega⟩ : Fin n) true) a)) :=
          omPlusNat_mapVec φ _ _
    _ = (fun a => φ (plusVec n F (⟨0, by omega⟩ : Fin n) true a)) := by
          rw [omPlusNat_longRoot_fix_vec hn hij hstd hpos c]
    _ = Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k) :=
          omPlusNat_phi_plusVec_true φ (⟨0, by omega⟩ : Fin n)

private def omPlusNat_stab {n : ℕ} (φ : F →+* k) (v : Fin n ⊕ Fin n → k) :
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
private theorem omPlusNat_fixU {n : ℕ} (hn : 3 ≤ n) (φ : F →+* k) :
    (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k)) ∈
      (omPlusCurtisDatum n F hn).fixU (omPlusNatRep n φ) := by
  rw [CurtisDatum.mem_fixU, omPlusCurtisDatum_U]
  intro u hu
  change u ∈ omPlusNat_stab (n := n) φ
    (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k))
  change u ∈ (⨆ γ ∈ {γ | γ ∈ (plusDatum n F hn).roots ∧ 0 < ht γ},
    (plusDatum n F hn).rootGroup γ) at hu
  have hle : (⨆ γ ∈ {γ | γ ∈ (plusDatum n F hn).roots ∧ 0 < ht γ},
      (plusDatum n F hn).rootGroup γ) ≤ omPlusNat_stab (n := n) φ
      (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k)) := by
    refine iSup₂_le fun γ hγ => ?_
    intro x hx
    obtain ⟨hroot, hpos⟩ := hγ
    rw [plusDatum_roots] at hroot
    obtain ⟨i, j, hij, s, t, hstd, hX⟩ := exists_plusRootGroup_eq (K := F) hn hroot
    change x ∈ plusRootGroup n F hn γ at hx
    rw [hX] at hx
    obtain ⟨c, rfl⟩ := hx
    exact omPlusNat_longRoot_fix_e0 hn hij hstd hpos φ c
  exact hle hu

private theorem omPlusNat_XEquiv_bijective {n : ℕ} (hn : 3 ≤ n) (s : Fin n) :
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

private noncomputable def omPlusNat_XEquiv {n : ℕ} (hn : 3 ≤ n) (s : Fin n) :
    F ≃ (omPlusCurtisDatum n F hn).X s :=
  Equiv.ofBijective _ (omPlusNat_XEquiv_bijective hn s)

private theorem omPlusNat_card_X {n : ℕ} (hn : 3 ≤ n) (hF : Nat.card F = 2) (s : Fin n) :
    Nat.card ((omPlusCurtisDatum n F hn).X s) = 2 := by
  rw [← Nat.card_congr (omPlusNat_XEquiv hn s)]
  exact hF

omit [Finite F] [CharP k 2] in
private theorem omPlusNat_weylD_zero_e0 {n : ℕ} (hn : 3 ≤ n) (φ : F →+* k) :
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
          rw [omPlusNat_phi_plusVec_true]
    _ = (fun a => φ (spinAction (quadPlus n F) (weylD F hn (⟨0, by omega⟩ : Fin n))
          (plusVec n F (⟨0, by omega⟩ : Fin n) true) a)) := omPlusNat_mapVec φ _ _
    _ = (fun a => φ (plusVec n F (⟨1, by omega⟩ : Fin n) true a)) := by rw [hvec]
    _ = Pi.single (Sum.inl (⟨1, by omega⟩ : Fin n)) (1 : k) :=
          omPlusNat_phi_plusVec_true φ (⟨1, by omega⟩ : Fin n)

omit [Finite F] [CharP F 2] [CharP k 2] in
private theorem omPlusNat_rootD_zero_e1 {n : ℕ} (hn : 3 ≤ n) (φ : F →+* k) (c : F) :
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
          rw [omPlusNat_phi_plusVec_true]
    _ = (fun a => φ (spinAction (quadPlus n F)
          (rootD F hn (⟨0, by omega⟩ : Fin n) (.ofAdd c))
          (plusVec n F (⟨1, by omega⟩ : Fin n) true) a)) := omPlusNat_mapVec φ _ _
    _ = (fun a => φ ((plusVec n F (⟨1, by omega⟩ : Fin n) true +
          c • plusVec n F (⟨0, by omega⟩ : Fin n) true) a)) := by rw [hvec]
    _ = Pi.single (Sum.inl (⟨1, by omega⟩ : Fin n)) (1 : k) +
        φ c • Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k) := by
          rw [← omPlusNat_phi_plusVec_true φ (⟨1, by omega⟩ : Fin n),
            ← omPlusNat_phi_plusVec_true φ (⟨0, by omega⟩ : Fin n)]
          ext a
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]

omit [Finite F] [CharP F 2] [CharP k 2] in
private theorem omPlusNat_weylD_ne_zero_e0 {n : ℕ} (hn : 3 ≤ n) {s : Fin n}
    (hs : s.val ≠ 0) (φ : F →+* k) :
    (omPlusNatRep n φ) (weylD F hn s)
      (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k)) =
      Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k) := by
  have h0a : (⟨0, by omega⟩ : Fin n) ≠ rootIdxD n s := fun h =>
    omPlusNat_rootIdxD_val_ne_zero hn hs (by simpa using congrArg Fin.val h.symm)
  have h0b : (⟨0, by omega⟩ : Fin n) ≠ rootIdxD' n s := fun h =>
    omPlusNat_rootIdxD'_val_ne_zero hn s (by simpa using congrArg Fin.val h.symm)
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
          rw [omPlusNat_phi_plusVec_true]
    _ = (fun a => φ (spinAction (quadPlus n F) (weylD F hn s)
          (plusVec n F (⟨0, by omega⟩ : Fin n) true) a)) := omPlusNat_mapVec φ _ _
    _ = Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k) := by
          rw [hvec, omPlusNat_phi_plusVec_true]

omit [Finite F] [CharP F 2] [CharP k 2] in
private theorem omPlusNat_rootD_ne_zero_e0 {n : ℕ} (hn : 3 ≤ n) {s : Fin n}
    (hs : s.val ≠ 0) (φ : F →+* k) (c : F) :
    (omPlusNatRep n φ) (rootD F hn s (.ofAdd c))
      (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k)) =
      Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k) := by
  have h0a : (⟨0, by omega⟩ : Fin n) ≠ rootIdxD n s := fun h =>
    omPlusNat_rootIdxD_val_ne_zero hn hs (by simpa using congrArg Fin.val h.symm)
  have h0b : (⟨0, by omega⟩ : Fin n) ≠ rootIdxD' n s := fun h =>
    omPlusNat_rootIdxD'_val_ne_zero hn s (by simpa using congrArg Fin.val h.symm)
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
          rw [omPlusNat_phi_plusVec_true]
    _ = (fun a => φ (spinAction (quadPlus n F) (rootD F hn s (.ofAdd c))
          (plusVec n F (⟨0, by omega⟩ : Fin n) true) a)) := omPlusNat_mapVec φ _ _
    _ = Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k) := by
          rw [hvec, omPlusNat_phi_plusVec_true]

private theorem omPlusNat_hecke {n : ℕ} (hn : 3 ≤ n) (hF : Nat.card F = 2) (φ : F →+* k)
    (s : Fin n) :
    (omPlusCurtisDatum n F hn).heckeT (omPlusNatRep n φ) s
      (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k)) =
      (if s.val = 0 then (1 : k) else 0) •
        Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k) := by
  classical
  have hFintype : Fintype F := Fintype.ofFinite F
  have : Fintype ((omPlusCurtisDatum n F hn).X s) := Fintype.ofFinite _
  have hcardF : Fintype.card F = 2 := by rw [← Nat.card_eq_fintype_card]; exact hF
  erw [CurtisDatum.heckeT_apply (omPlusCurtisDatum n F hn)]
  rw [← (omPlusNat_XEquiv_bijective (F := F) hn s).sum_comp]
  simp only [omPlusCurtisDatum_n]
  by_cases hs0 : s.val = 0
  · rw [if_pos hs0]
    have hterm : ∀ c : F, (omPlusNatRep n φ)
        (rootD F hn s (.ofAdd c) * weylD F hn s)
        (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k)) =
        Pi.single (Sum.inl (⟨1, by omega⟩ : Fin n)) (1 : k) +
          φ c • Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k) := by
      intro c
      have hs : s = (⟨0, by omega⟩ : Fin n) := Fin.ext hs0
      rw [hs, map_mul, Module.End.mul_apply, omPlusNat_weylD_zero_e0 hn φ,
        omPlusNat_rootD_zero_e1 hn φ c]
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hcardF,
      ← Finset.sum_smul, omPlusNat_sum_field φ hF, one_smul]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply]
    rw [CharTwo.two_nsmul, zero_add]
  · rw [if_neg hs0]
    have hterm : ∀ c : F, (omPlusNatRep n φ)
        (rootD F hn s (.ofAdd c) * weylD F hn s)
        (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k)) =
        Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k) := by
      intro c
      rw [map_mul, Module.End.mul_apply, omPlusNat_weylD_ne_zero_e0 hn hs0 φ,
        omPlusNat_rootD_ne_zero_e0 hn hs0 φ c]
    simp_rw [hterm]
    rw [Finset.sum_const, Finset.card_univ, hcardF, zero_smul]
    ext i
    simp only [Pi.smul_apply, Pi.zero_apply]
    rw [CharTwo.two_nsmul]

theorem isCurtisType_omPlus_two_natural (hF : Nat.card F = 2) {n : ℕ} (hn : 3 ≤ n)
    (φ : F →+* k) {χ : spinGroup (quadPlus n F) → k} (hχ : χ 1 = 1) :
    (omPlusCurtisDatum n F hn).IsCurtisType (omPlusNatRep n φ)
      (Pi.single (Sum.inl ⟨0, by omega⟩) 1) χ (fun s => if s.val = 0 then 1 else 0) := by
  refine ⟨omPlusNat_fixU hn φ, Pi.single_ne_zero_iff.mpr one_ne_zero, ?_, ?_⟩
  · intro h hh
    have h1 : h = 1 := by
      have hmem : h ∈ (omPlusCurtisDatum n F hn).H := hh
      rw [omPlusCurtisDatum_two_H hF hn] at hmem
      simpa using hmem
    subst h1
    rw [hχ]
    simp
  · intro s
    simpa using omPlusNat_hecke hn hF φ s

theorem isCurtisType_omPlus_two_trivial (hF : Nat.card F = 2) {n : ℕ} (hn : 3 ≤ n)
    {χ : spinGroup (quadPlus n F) → k} (hχ : χ 1 = 1) :
    (omPlusCurtisDatum n F hn).IsCurtisType
      (Representation.trivial k (spinGroup (quadPlus n F)) k) 1 χ 0 := by
  refine ⟨?_, one_ne_zero, ?_, ?_⟩
  · intro u _
    rw [Representation.trivial_apply]
  · intro h hh
    have h1 : h = 1 := by
      have hmem : h ∈ (omPlusCurtisDatum n F hn).H := hh
      rw [omPlusCurtisDatum_two_H hF hn] at hmem
      simpa using hmem
    subst h1
    rw [hχ]
    simp
  · intro s
    have : Fintype ((omPlusCurtisDatum n F hn).X s) := Fintype.ofFinite _
    erw [CurtisDatum.heckeT_apply (omPlusCurtisDatum n F hn)]
    simp only [Representation.trivial_apply]
    rw [Finset.sum_const, Finset.card_univ,
      show Fintype.card ((omPlusCurtisDatum n F hn).X s) = 2 by
        rw [← Nat.card_eq_fintype_card]; exact omPlusNat_card_X hn hF s]
    simp only [Pi.zero_apply, zero_smul, nsmul_eq_mul, mul_one]
    exact CharTwo.two_eq_zero

end CFSG.LocalAnalysis.WeakClosure81
