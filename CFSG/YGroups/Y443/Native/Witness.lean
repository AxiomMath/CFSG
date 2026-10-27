module

public import CFSG.Monster.AxisCount.DenseWord
public import CFSG.Monster.Griess.ThreeVectorSeparation
public import CFSG.Monster.Griess.Invariance.Diagonal
public import CFSG.Monster.Griess.Invariance.Octad.Basic
public import Certificates.Data.CFSGNative.YGroups.Y443.Witness
public import Certificates.Certificate10127
public meta import Certificates.Data.CFSGNative.YGroups.Y443.Witness
public import CFSG.Monster.Visible.SignCompat

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.YGroups.Y443

open CFSG.Monster CFSG.Monster.B CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.Monster.Spin CFSG.Monster.Code CFSG.Monster.SpinLattice CFSG.Monster.B.Rep4371
  CFSG.Monster.Griess.DiagonalInvariance CFSG.Monster.Griess.OctadInv
  CFSG.YGroups.Y443Native

theorem aV_e : (aV ()).e = 0 := rfl
theorem bV_e : (bV ()).e = 0 := rfl
theorem wV_e : (wV ()).e = 0 := rfl

theorem aV_getD (k : ℕ) (hk : k < 196884) :
    (aV ()).D.getD k 0 = if k < 300 then aTab[k]! else 0 := by
  unfold aV
  simp only []
  rw [Native.getD_ofFn _ k hk 0]

theorem bV_getD (k : ℕ) (hk : k < 196884) :
    (bV ()).D.getD k 0 = if 300 ≤ k ∧ k < 98580 then 1 else 0 := by
  unfold bV
  simp only []
  rw [Native.getD_ofFn _ k hk 0]

theorem wV_getD (k : ℕ) (hk : k < 196884) :
    (wV ()).D.getD k 0 = if k = 98580 then 1 else 0 := by
  unfold wV
  simp only []
  rw [Native.getD_ofFn _ k hk 0]

noncomputable abbrev a₀ : symMat := interpA (aV ())

theorem aIdx_lt
    (i j : Fin 24) : Native.aIdx i j < 300 := (Native.aIdx_spec i j i.2 j.2).1

theorem interpX_posOf_lt (c : ShortIdx) : 300 + posOf c < 98580 := by
  have := posOf_lt c
  omega

theorem interpW_idx_lt (s : SpinIdx) (j : Fin 24) : 98580 + 24 * rowOf s + j < 196884 := by
  have := rowOf_lt s
  have := j.2
  omega

theorem interp_aV : interp (aV ()) = inA a₀ := by
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · funext c
    show ((aV ()).D.getD (300 + posOf c) 0 : ℚ) / 2 ^ (aV ()).e = 0
    rw [aV_getD _ (by have := interpX_posOf_lt c; omega)]
    have h : ¬ (300 + posOf c < 300) := by omega
    simp [h]
  · ext s j
    show (((aV ()).D.getD (98580 + 24 * rowOf s + j) 0 : ℤ) : ℚ) / 2 ^ (aV ()).e = 0
    rw [aV_getD _ (interpW_idx_lt s j)]
    have h : ¬ (98580 + 24 * rowOf s + (j : ℕ) < 300) := by omega
    simp [h]


theorem sum_basisB_X : ∑ c : ShortIdx, (1 : ℚ) • basisB (Sum.inr (Sum.inl c)) =
    ((0 : symMat), (fun _ => (1 : ℚ)), (0 : SpaceW)) := by
  simp only [one_smul, basisB_inr_inl]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · rw [Prod.fst_sum]
    simp
  · rw [Prod.snd_sum, Prod.fst_sum]
    funext d
    rw [Finset.sum_apply]
    simp [Pi.single_apply]
  · rw [Prod.snd_sum, Prod.snd_sum]
    simp

theorem interp_bV :
    interp (bV ()) = ∑ c : ShortIdx, (1 : ℚ) • basisB (Sum.inr (Sum.inl c)) := by
  rw [sum_basisB_X]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · ext i j
    show (((bV ()).D.getD (Native.aIdx i j) 0 : ℤ) : ℚ) / 2 ^ (bV ()).e = 0
    have hlt := aIdx_lt i j
    rw [bV_getD _ (by omega)]
    have h : ¬ (300 ≤ Native.aIdx i j ∧ Native.aIdx i j < 98580) := by omega
    simp [h]
  · funext c
    show ((bV ()).D.getD (300 + posOf c) 0 : ℚ) / 2 ^ (bV ()).e = 1
    rw [bV_getD _ (by have := interpX_posOf_lt c; omega)]
    have h : 300 ≤ 300 + posOf c ∧ 300 + posOf c < 98580 := ⟨by omega, interpX_posOf_lt c⟩
    simp [h, bV_e]
  · ext s j
    show (((bV ()).D.getD (98580 + 24 * rowOf s + j) 0 : ℤ) : ℚ) / 2 ^ (bV ()).e = 0
    rw [bV_getD _ (interpW_idx_lt s j)]
    have h : ¬ (300 ≤ 98580 + 24 * rowOf s + (j : ℕ) ∧ 98580 + 24 * rowOf s + (j : ℕ) < 98580) := by
      omega
    simp [h]

noncomputable abbrev N₀ : SpaceW := interpW (wV ())

theorem interp_wV : interp (wV ()) = inW N₀ := by
  refine Prod.ext ?_ (Prod.ext ?_ rfl)
  · ext i j
    show (((wV ()).D.getD (Native.aIdx i j) 0 : ℤ) : ℚ) / 2 ^ (wV ()).e = 0
    have hlt := aIdx_lt i j
    rw [wV_getD _ (by omega)]
    have h : ¬ (Native.aIdx i j = 98580) := by omega
    simp [h]
  · funext c
    show ((wV ()).D.getD (300 + posOf c) 0 : ℚ) / 2 ^ (wV ()).e = 0
    rw [wV_getD _ (by have := interpX_posOf_lt c; omega)]
    have h : ¬ (300 + posOf c = 98580) := by have := interpX_posOf_lt c; omega
    simp [h]

theorem N₀_ne_zero : N₀ ≠ 0 := by
  intro h
  have h1 := congrFun (congrFun h (spinOfRow 0)) 0
  have e : rowOf (spinOfRow 0) = 0 := rowOf_spinOfRow (by norm_num)
  have h2 : ((wV ()).D.getD (98580 + 24 * rowOf (spinOfRow 0) + ((0 : Fin 24) : ℕ)) 0 : ℚ) /
      2 ^ (wV ()).e = 0 := h1
  rw [e] at h2
  rw [wV_getD _ (by norm_num)] at h2
  simp at h2


theorem bitLift_zero_val : bitLift (0 : ZMod 2) = 0 := rfl

theorem ofFn_getElem! (f : Fin 24 → ℤ) (k : Fin 24) : (Array.ofFn f)[(k : ℕ)]! = f k := by
  simp

theorem shortVecN_F1 (p : ℕ) (hp : p < 552) (k : Fin 24) :
    (shortVecN p)[(k : ℕ)]! =
      (if (k : ℕ) = (Native.pairTab[p / 2]!).1 then 4 else 0) +
        (if (k : ℕ) = (Native.pairTab[p / 2]!).2 then (if p % 2 = 0 then -4 else 4) else 0) := by
  unfold shortVecN
  rw [ite_eq_left hp]
  simp only []
  rw [ofFn_getElem!]

theorem shortVecN_F2 (p : ℕ) (h1 : 552 ≤ p) (h2 : p < 49704) (k : Fin 24) :
    (shortVecN p)[(k : ℕ)]! =
      (if (Native.wordN (2 * ((p - 552) / 24))).testBit k then -1 else 1) *
        (if (k : ℕ) = (p - 552) % 24 then -3 else 1) := by
  unfold shortVecN
  rw [ite_eq_right (by omega), ite_eq_left h2]
  simp only []
  rw [ofFn_getElem!]

theorem shortVecN_F3 (p : ℕ) (h1 : 49704 ≤ p) (k : Fin 24) :
    (shortVecN p)[(k : ℕ)]! =
      (if (Native.wordN Native.octTab[(p - 49704) / 64]!).testBit k then 2 else 0) -
        (if (Native.spreadG (Native.wordN Native.octTab[(p - 49704) / 64]!)
          Native.evenTab[(p - 49704) % 64]!).testBit k then 4 else 0) := by
  unfold shortVecN
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  simp only []
  rw [ofFn_getElem!]


def ShortBridge (p : ℕ) : Prop :=
  ∃ l : ShortLabel, (∃ h : p < 98280, shortOf ⟨p, h⟩ = labelIdx l) ∧
    ((∀ k : Fin 24, labelVec l k = (shortVecN p)[(k : ℕ)]!) ∨
      (∀ k : Fin 24, labelVec l k = -(shortVecN p)[(k : ℕ)]!))

theorem bridge_F1 (p : ℕ) (hp : p < 552) : ShortBridge p := by
  obtain ⟨hlt, h24, -⟩ := Native.pairTab_spec (p / 2) (by omega)
  have hi : (Native.pairTab[p / 2]!).1 < 24 := lt_trans hlt h24
  have hne : (⟨(Native.pairTab[p / 2]!).1, hi⟩ : Fin 24) ≠ ⟨(Native.pairTab[p / 2]!).2, h24⟩ :=
    fun e => by
      have := congrArg Fin.val e
      simp only at this
      omega
  have hlt' : (⟨(Native.pairTab[p / 2]!).1, hi⟩ : Fin 24) < ⟨(Native.pairTab[p / 2]!).2, h24⟩ :=
    Fin.mk_lt_mk.2 hlt
  by_cases hpar : p % 2 = 0
  · refine ⟨.inl ⟨(⟨(Native.pairTab[p / 2]!).1, hi⟩, ⟨(Native.pairTab[p / 2]!).2, h24⟩), hlt'⟩,
      ⟨by omega, ?_⟩, Or.inl fun k => ?_⟩
    · apply Subtype.ext
      show (toC (keyOf p).1, toD (keyOf p).2) = coordOf (labelElt _)
      rw [keyOf_pair p hp, ite_eq_left hpar]
      simp only [labelElt]
      rw [← pauliQ_minus hne, coordOf_pauliQ]
    · simp only [labelVec]
      rw [vMinus_apply, shortVecN_F1 p hp k, ite_eq_left hpar]
      simp only [Fin.ext_iff]
      split_ifs <;> omega
  · refine ⟨.inr (.inl ⟨(⟨(Native.pairTab[p / 2]!).1, hi⟩, ⟨(Native.pairTab[p / 2]!).2, h24⟩),
      hlt'⟩), ⟨by omega, ?_⟩, Or.inl fun k => ?_⟩
    · apply Subtype.ext
      show (toC (keyOf p).1, toD (keyOf p).2) = coordOf (labelElt _)
      rw [keyOf_pair p hp, ite_eq_right hpar]
      simp only [labelElt]
      rw [← pauliQ_plus hne, coordOf_pauliQ]
    · simp only [labelVec]
      rw [vPlus_apply, shortVecN_F1 p hp k, ite_eq_right hpar]
      simp only [Fin.ext_iff]
      split_ifs <;> omega


theorem bridge_F2
    (p : ℕ) (h1 : 552 ≤ p) (h2 : p < 49704) : ShortBridge p := by
  have hi : (p - 552) % 24 < 24 := Nat.mod_lt _ (by norm_num)
  have hn : (2 * ((p - 552) / 24)).testBit 0 = false := by simp [Nat.testBit_zero]
  have hc : ((π₀ (toC (2 * ((p - 552) / 24))) : C₀) : C) = toC (2 * ((p - 552) / 24)) := by
    rw [coe_π₀_toC]
    unfold Model.pi0N
    simp [hn]
  refine ⟨.inr (.inr (.inl (π₀ (toC (2 * ((p - 552) / 24))), ⟨(p - 552) % 24, hi⟩))),
    ⟨by omega, ?_⟩, Or.inl fun k => ?_⟩
  · apply Subtype.ext
    show (toC (keyOf p).1, toD (keyOf p).2) = coordOf (labelElt _)
    rw [keyOf_odd p h1 h2]
    simp only [labelElt]
    rw [← pauliQ_odd' _ hn ⟨(p - 552) % 24, hi⟩, coordOf_pauliQ]
  · simp only [labelVec]
    rw [hc, shortVecN_F2 p h1 h2 k, native_wordN]
    unfold oddMin
    rw [coe_toC]
    simp only [bvec_apply, Fin.ext_iff]
    cases hb : (Model.wordN (2 * ((p - 552) / 24))).testBit k <;>
      by_cases hk : (k : ℕ) = (p - 552) % 24 <;> simp [hk] <;> rfl


theorem bridge_oct (a m : ℕ) (hpop : Native.popcN 24 (Native.wordN a) = 8)
    (hsub : Native.spreadG (Native.wordN a) m &&& Native.wordN a =
      Native.spreadG (Native.wordN a) m)
    (hev : Native.popcN 24 (Native.spreadG (Native.wordN a) m) % 2 = 0) :
    ∃ l : ShortLabel,
      coordOf (labelElt l) = (toC (Native.octCodeG a m),
        toD (Model.thetaN (Native.octCodeG a m) ^^^
          Model.dualN (Native.spreadG (Model.wordN a) m))) ∧
      ((∀ k : Fin 24, labelVec l k = 2 * bitLift (bvec 24 (Model.wordN a) k) -
          4 * bitLift (bvec 24 (Native.spreadG (Model.wordN a) m) k)) ∨
        (∀ k : Fin 24, labelVec l k = -(2 * bitLift (bvec 24 (Model.wordN a) k) -
          4 * bitLift (bvec 24 (Native.spreadG (Model.wordN a) m) k)))) := by
  have hw := octadWord_of _ hpop
  let D : OctadWord := ⟨toC a, hw⟩
  have hsubset : octSetG a m ⊆ octSupp D := by
    intro i hi
    simp only [octSetG, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    have h1 : (Native.spreadG (Native.wordN a) m &&& Native.wordN a).testBit i =
        (Native.spreadG (Native.wordN a) m).testBit i := by
      rw [hsub]
    rw [Nat.testBit_and] at h1
    simp only [native_wordN] at h1 hi
    have h2 : (Model.wordN a).testBit i = true := by
      cases h : (Model.wordN a).testBit i
      · rw [h, Bool.and_false] at h1
        rw [hi] at h1
        exact absurd h1 (by simp)
      · rfl
    show i ∈ supp ((toC a : C) : Fin 24 → ZMod 2)
    rw [mem_supp_iff, coe_toC]
    simp [bvec, h2]
  have hevenc : Even (octSetG a m).card := by
    rw [card_octSetG, ← popcN_eq_popc, ← native_popcN, ← native_wordN, Nat.even_iff]
    exact hev
  have hD : ((D : C) : Fin 24 → ZMod 2) = bvec 24 (Model.wordN a) := coe_toC _
  have hv : vOct ((D : C) : Fin 24 → ZMod 2) (octSetG a m) =
      fun k => 2 * bitLift (bvec 24 (Model.wordN a) k) -
        4 * bitLift (bvec 24 (Native.spreadG (Model.wordN a) m) k) := by
    funext k
    simp only [vOct, liftℤ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [ind_octSetG, hD]
  refine ⟨.inr (.inr (.inr ⟨D, Octad.cls (octSupp D) (octSetG a m)⟩)), ?_, ?_⟩
  · simp only [labelElt]
    rw [rOctQ_cls hsubset hevenc, ← pauliQ_octG, coordOf_pauliQ]
  · rcases octRep_cls hsubset hevenc with h | h
    · refine Or.inl fun k => ?_
      simp only [labelVec, h]
      exact congrFun hv k
    · refine Or.inr fun k => ?_
      simp only [labelVec, h]
      rw [← neg_vOct hsubset, Pi.neg_apply]
      exact congrArg Neg.neg (congrFun hv k)


theorem bridge_F3
    (p : ℕ) (h1 : 49704 ≤ p) (h2 : p < 98280) : ShortBridge p := by
  have ho : (p - 49704) / 64 < 759 := by omega
  have hq : (p - 49704) % 64 < 64 := Nat.mod_lt _ (by norm_num)
  obtain ⟨ha, hpop⟩ := Native.octTab_spec ((p - 49704) / 64) ho
  obtain ⟨hm, hev⟩ := Native.evenTab_spec ((p - 49704) % 64) hq
  have hm256 : Native.evenTab[(p - 49704) % 64]! < 256 := by omega
  obtain ⟨hsub, hcard, -⟩ := (Native.octCheck_parts ((p - 49704) / 64) ho).1 _ hm256
  have hev' : Native.popcN 24 (Native.spreadG (Native.wordN Native.octTab[(p - 49704) / 64]!)
      Native.evenTab[(p - 49704) % 64]!) % 2 = 0 := by
    rw [hcard]
    exact hev
  obtain ⟨l, hl1, hl2⟩ := bridge_oct _ _ hpop hsub hev'
  refine ⟨l, ⟨h2, ?_⟩, ?_⟩
  · apply Subtype.ext
    show (toC (keyOf p).1, toD (keyOf p).2) = coordOf (labelElt l)
    rw [hl1, keyOf_oct p h1 h2]
  · rcases hl2 with h | h
    · refine Or.inl fun k => ?_
      rw [h k, shortVecN_F3 p h1 k, native_wordN]
      simp only [bvec_apply]
      cases (Model.wordN Native.octTab[(p - 49704) / 64]!).testBit k <;>
        cases (Native.spreadG (Model.wordN Native.octTab[(p - 49704) / 64]!)
          Native.evenTab[(p - 49704) % 64]!).testBit k <;> simp [bitLift_one, bitLift_zero_val]
    · refine Or.inr fun k => ?_
      rw [h k, shortVecN_F3 p h1 k, native_wordN]
      simp only [bvec_apply]
      cases (Model.wordN Native.octTab[(p - 49704) / 64]!).testBit k <;>
        cases (Native.spreadG (Model.wordN Native.octTab[(p - 49704) / 64]!)
          Native.evenTab[(p - 49704) % 64]!).testBit k <;> simp [bitLift_one, bitLift_zero_val]


theorem shortBridge (p : ℕ) (hp : p < 98280) : ShortBridge p := by
  by_cases h1 : p < 552
  · exact bridge_F1 p h1
  by_cases h2 : p < 49704
  · exact bridge_F2 p (by omega) h2
  · exact bridge_F3 p (by omega) hp

theorem qf_eq_sum (c : ShortIdx) (M : Matrix (Fin 24) (Fin 24) ℚ) :
    qf c M = ∑ i, ∑ j, M i j * (uQ c i * uQ c j) := by
  unfold qf
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem qf_shortOf (p : Fin 98280) (M : Matrix (Fin 24) (Fin 24) ℚ) :
    qf (shortOf p) M =
      ∑ i : Fin 24, ∑ j : Fin 24,
        M i j * (((shortVecN p)[(i : ℕ)]! * (shortVecN p)[(j : ℕ)]! : ℤ) : ℚ) := by
  obtain ⟨l, ⟨h, hl⟩, hv⟩ := shortBridge p p.2
  have hp : (⟨p.val, h⟩ : Fin 98280) = p := Fin.ext rfl
  rw [hp] at hl
  rw [hl, qf_eq_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [uQ_mul_uQ_label]
  congr 1
  rcases hv with hv | hv
  · rw [hv i, hv j]
    push_cast
    rfl
  · rw [hv i, hv j]
    push_cast
    ring

theorem sum_range_map (f : ℕ → ℤ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

theorem qfN_eq (A u : Array ℤ) :
    ((qfN A u : ℤ) : ℚ) = ∑ i : Fin 24, ∑ j : Fin 24,
      (A[24 * (i : ℕ) + (j : ℕ)]! : ℚ) * (((u[(i : ℕ)]! * u[(j : ℕ)]! : ℤ)) : ℚ) := by
  unfold qfN
  simp only [sum_range_map]
  rw [Finset.sum_range]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_range]


theorem aFull_get (D : Array ℤ) (i j : Fin 24) :
    (Native.aFull D)[24 * (i : ℕ) + (j : ℕ)]! = D[Native.aIdx i j]! := by
  have hlt : 24 * (i : ℕ) + (j : ℕ) < 576 := by have := i.2; have := j.2; omega
  unfold Native.aFull
  rw [Native.getElem!_eq_getD', Native.getD_ofFn _ _ hlt]
  have e1 : (24 * (i : ℕ) + (j : ℕ)) / 24 = i := by have := j.2; omega
  have e2 : (24 * (i : ℕ) + (j : ℕ)) % 24 = j := by have := j.2; omega
  simp only [e1, e2]

theorem a₀_apply (i j : Fin 24) :
    (a₀ : Matrix (Fin 24) (Fin 24) ℚ) i j = (((aV ()).D[Native.aIdx i j]! : ℤ) : ℚ) := by
  show (((aV ()).D.getD (Native.aIdx i j) 0 : ℤ) : ℚ) / 2 ^ (aV ()).e = _
  rw [aV_e, Native.getElem!_eq_getD']
  simp

theorem shortValsN_get (A : Array ℤ) (p : ℕ) (hp : p < 98280) :
    (shortValsN A)[p]! = qfN A (shortVecN p) := by
  unfold shortValsN
  rw [Native.getElem!_eq_getD_gen, Array.getD_eq_getD_getElem?, Array.getElem?_map,
    Array.getElem?_range]
  simp [hp]

theorem qf_shortOf_a (p : Fin 98280) :
    qf (shortOf p) (a₀ : Matrix (Fin 24) (Fin 24) ℚ) =
      (((shortValsN (Native.aFull (aV ()).D))[(p : ℕ)]! : ℤ) : ℚ) := by
  rw [shortValsN_get _ _ p.2, qfN_eq, qf_shortOf]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [a₀_apply, aFull_get]

theorem sorted_lt {vals : Array ℤ} {perm : Array ℕ} {n : ℕ}
    (hC : ∀ i, i < n - 1 → vals[perm[i]!]! < vals[perm[i + 1]!]!) :
    ∀ k i, i + k + 1 < n + 0 → vals[perm[i]!]! < vals[perm[i + k + 1]!]! := by
  intro k
  induction k with
  | zero => intro i hi; exact hC i (by omega)
  | succ k ih =>
    intro i hi
    exact lt_trans (ih i (by omega)) (hC (i + k + 1) (by omega))

theorem distinct_of_checks {vals : Array ℤ} {perm inv : Array ℕ} {n : ℕ}
    (hB : ∀ p, p < n → inv[p]! < n ∧ perm[inv[p]!]! = p)
    (hC : ∀ i, i < n - 1 → vals[perm[i]!]! < vals[perm[i + 1]!]!) :
    ∀ p q, p < n → q < n → vals[p]! = vals[q]! → p = q := by
  intro p q hp hq hpq
  obtain ⟨hip, hperm_p⟩ := hB p hp
  obtain ⟨hiq, hperm_q⟩ := hB q hq
  have hmono := sorted_lt (vals := vals) (perm := perm) (n := n) hC
  by_contra hne
  have hij : inv[p]! ≠ inv[q]! := fun e => hne (by rw [← hperm_p, ← hperm_q, e])
  rcases lt_or_gt_of_ne hij with h | h
  · have := hmono (inv[q]! - inv[p]! - 1) inv[p]! (by omega)
    rw [show inv[p]! + (inv[q]! - inv[p]! - 1) + 1 = inv[q]! by omega, hperm_p, hperm_q] at this
    rw [hpq] at this
    exact lt_irrefl _ this
  · have := hmono (inv[p]! - inv[q]! - 1) inv[q]! (by omega)
    rw [show inv[q]! + (inv[p]! - inv[q]! - 1) + 1 = inv[p]! by omega, hperm_p, hperm_q] at this
    rw [hpq] at this
    exact lt_irrefl _ this

theorem distinctCheck_sound {vals : Array ℤ} (h : distinctCheck vals = true) :
    ∀ p q, p < vals.size → q < vals.size → vals[p]! = vals[q]! → p = q := by
  unfold distinctCheck at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    beq_iff_eq] at h
  obtain ⟨hB, hC⟩ := h
  exact distinct_of_checks (perm := sortPerm vals) (inv := invTable (sortPerm vals))
    (fun p hp => hB p hp) (fun i hi => hC i hi)



theorem shortValsN_size (A : Array ℤ) : (shortValsN A).size = 98280 := by
  simp [shortValsN]

theorem shortEig_injective_of_check (hOK : shortValsOK () = true) :
    Function.Injective (shortEig a₀) := by
  have hd := distinctCheck_sound (vals := shortValsN (Native.aFull (aV ()).D)) hOK
  intro c d h
  have hq : qf c a₀ = qf d a₀ := by
    unfold shortEig at h
    linarith
  have hc := shortOf_posOf c
  have hd' := shortOf_posOf d
  rw [← hc, ← hd', qf_shortOf_a, qf_shortOf_a] at hq
  have h1 := Int.cast_injective hq
  have h2 := hd (posOf c) (posOf d) (by rw [shortValsN_size]; exact posOf_lt c)
    (by rw [shortValsN_size]; exact posOf_lt d) h1
  rw [← hc, ← hd']
  congr 1
  exact Fin.ext h2

theorem separation (hOK : shortValsOK () = true) :
    ∀ h ∈ Gmat, h (interp (aV ())) = interp (aV ()) → h (interp (bV ())) = interp (bV ()) →
      h (interp (wV ())) = interp (wV ()) → h = 1 :=
  (three_vector_separation_Gmat (shortEig_injective_of_check hOK) (β := fun _ => (1 : ℚ))
    (fun _ => one_ne_zero) N₀_ne_zero interp_aV interp_bV interp_wV).1

theorem shortValsOK_eq : shortValsOK () = true :=
  Certificates.certificate10127

theorem shortEig_injective :
    Function.Injective (shortEig a₀) :=
  shortEig_injective_of_check shortValsOK_eq

theorem separation_witnesses :
    ∀ h ∈ Gmat, h (interp (aV ())) = interp (aV ()) → h (interp (bV ())) = interp (bV ()) →
      h (interp (wV ())) = interp (wV ()) → h = 1 :=
  separation shortValsOK_eq

end CFSG.YGroups.Y443
