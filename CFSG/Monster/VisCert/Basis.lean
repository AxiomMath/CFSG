module

public import CFSG.Monster.Visible.SignFixed
import Mathlib.Data.Nat.Bitwise

public noncomputable section

namespace CFSG.Monster.VisCert

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.SpinLattice CFSG.Monster.ScalarKernel
  CFSG.Monster.Visible

@[expose] def sumTo (f : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => sumTo f n + f n

@[expose] def allTo (p : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | n + 1 => allTo p n && p n

theorem sumTo_eq (f : ℕ → ℤ) : ∀ n, sumTo f n = ∑ i ∈ Finset.range n, f i
  | 0 => rfl
  | n + 1 => by rw [sumTo, sumTo_eq f n, Finset.sum_range_succ]

theorem sum_fin_eq_sumTo (f : ℕ → ℤ) : ∑ i : Fin 24, f i = sumTo f 24 := by
  rw [sumTo_eq, Fin.sum_univ_eq_sum_range f 24]

theorem allTo_iff (p : ℕ → Bool) : ∀ n, allTo p n = true ↔ ∀ i < n, p i = true
  | 0 => by simp [allTo]
  | n + 1 => by
    rw [allTo, Bool.and_eq_true, allTo_iff p n]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
      · exact h1 i h
      · exact h2
    · intro h
      exact ⟨fun i hi => h i (Nat.lt_succ_of_lt hi), h n (Nat.lt_succ_self n)⟩

theorem allTo_spec {p : ℕ → Bool} {n : ℕ} (h : allTo p n = true) {i : ℕ} (hi : i < n) :
    p i = true :=
  (allTo_iff p n).1 h i hi

@[expose] def J : Fin 12 → Fin 24 := ![0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 16]

@[expose] def Jlist : List ℕ := [0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 16]

@[expose] def ellVec (j : Fin 24) : Fin 24 → ℤ :=
  if h : (j : ℕ) < 12 then fun i => 2 * bitLift (B ⟨j, h⟩ i) else lam (J ⟨j - 12, by omega⟩)

@[expose] def ellN (j i : ℕ) : ℤ :=
  if j < 12 then (if (Bmask j).testBit i then 2 else 0)
  else if i = Jlist.getD (j - 12) 0 then -3 else 1

theorem ellVec_apply : ∀ j i : Fin 24, ellVec j i = ellN j i := by decide +kernel

theorem ellVec_eq (j : Fin 24) : ellVec j = fun i : Fin 24 => ellN j i :=
  funext (ellVec_apply j)

theorem ellVec_mem (j : Fin 24) : ellVec j ∈ codeLattice C := by
  unfold ellVec
  split_ifs with h
  · exact two_bitLift_mem weight_mod_four' (B_mem_C _)
  · exact lam_mem _

@[expose] def ellCls (j : Fin 24) : L2 := cls (ellVec j) (ellVec_mem j)

@[expose] def gramList : List ℕ :=
  [13230272, 13505280, 15801344, 8986560, 4792256, 13180864, 49209, 41017, 262202, 131130, 2097212,
   1048636, 62, 129, 65, 193, 61, 514, 258, 59, 2052, 1028, 55, 47]

@[expose] def gramRow (j : ℕ) : ℕ := gramList.getD j 0

@[expose] def ginvList : List ℕ :=
  [57344, 126976, 585728, 4255744, 8450048, 13176832, 40960, 49152, 389120, 258048, 2682880,
   1634304, 28478, 4169567, 4169631, 3567583, 3171106, 582144, 581888, 420900, 124928, 123904, 40,
   48]

@[expose] def ginvRow (j : ℕ) : ℕ := ginvList.getD j 0

@[expose] def gramOK : Bool :=
  allTo (fun j => allTo (fun k =>
    (sumTo (fun i => ellN j i * ellN k i) 24 / 8) % 2 == if (gramRow j).testBit k then 1 else 0)
    24) 24

@[expose] def ginvOK : Bool :=
  allTo (fun j => allTo (fun l =>
    popc 24 (gramRow j &&& ginvRow l) % 2 == if j = l then 1 else 0) 24) 24

theorem gramOK_eq_true : gramOK = true := by decide +kernel

theorem ginvOK_eq_true : ginvOK = true := by decide +kernel

theorem hInt_eq_sumTo (u : ℕ → ℤ) (k : Fin 24) :
    hInt (fun i : Fin 24 => u i) (ellVec k) = sumTo (fun i => u i * ellN k i) 24 / 8 := by
  rw [hInt, ellVec_eq]
  exact congrArg (· / 8) (sum_fin_eq_sumTo fun i => u i * ellN k i)

theorem intCast_zmod_two_of_emod {x y : ℤ} (h : x % 2 = y) : ((x : ℤ) : ZMod 2) = (y : ZMod 2) := by
  rw [← h]
  simpa using (ZMod.intCast_mod x 2).symm

theorem bL_ellCls (j k : Fin 24) :
    QuadraticMap.polarBilin qL (ellCls j) (ellCls k) = bvec 24 (gramRow j) k := by
  rw [ellCls, ellCls, bL_cls, ellVec_eq j, hInt_eq_sumTo]
  have h := allTo_spec (allTo_spec gramOK_eq_true j.2) k.2
  rw [beq_iff_eq] at h
  rw [intCast_zmod_two_of_emod h, bvec_apply]
  split_ifs <;> simp

theorem bvec_gramRow_symm (j k : Fin 24) : bvec 24 (gramRow j) k = bvec 24 (gramRow k) j := by
  rw [← bL_ellCls, ← bL_ellCls, QuadraticMap.polarBilin_apply_apply,
    QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]

theorem bvec_dotProduct_ginv (j l : Fin 24) :
    bvec 24 (gramRow j) ⬝ᵥ bvec 24 (ginvRow l) = if j = l then 1 else 0 := by
  rw [bvec_dotProduct]
  have h := allTo_spec (allTo_spec ginvOK_eq_true j.2) l.2
  rw [beq_iff_eq] at h
  rw [← ZMod.natCast_mod, h]
  by_cases hjl : j = l
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (congrArg Fin.val hjl)),
      ite_eq_left_of_eq_true _ _ (eq_true hjl)]
    rfl
  · rw [ite_eq_right_of_eq_false _ _ (eq_false fun h' => hjl (Fin.ext h')),
      ite_eq_right_of_eq_false _ _ (eq_false hjl)]
    rfl

theorem linearIndependent_ellCls : LinearIndependent (ZMod 2) ellCls := by
  rw [Fintype.linearIndependent_iff]
  intro c hc l
  have hk : ∀ k : Fin 24, ∑ j, c j * bvec 24 (gramRow j) k = 0 := by
    intro k
    have h := congrArg (fun x => QuadraticMap.polarBilin qL x (ellCls k)) hc
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      bL_ellCls, smul_eq_mul, map_zero, LinearMap.zero_apply] at h
    exact h
  calc c l = ∑ j, c j * (if j = l then 1 else 0) := by simp
    _ = ∑ j, c j * ∑ k, bvec 24 (gramRow j) k * bvec 24 (ginvRow l) k := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← bvec_dotProduct_ginv]
        rfl
    _ = ∑ k, (∑ j, c j * bvec 24 (gramRow j) k) * bvec 24 (ginvRow l) k := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
    _ = 0 := by simp [hk]

theorem finrank_L2 : Module.finrank (ZMod 2) L2 = 24 :=
  finrank_codeLatticeModTwo allOnes_mem_C weight_mod_four' mem_C_iff_forall_dotProduct

@[expose] def ellBasis : Module.Basis (Fin 24) (ZMod 2) L2 :=
  basisOfLinearIndependentOfCardEqFinrank linearIndependent_ellCls
    (by rw [Fintype.card_fin, finrank_L2])

@[simp] theorem ellBasis_apply (j : Fin 24) : ellBasis j = ellCls j := by
  simp [ellBasis]

@[expose] def dec (v : ℕ) : L2 := ∑ i : Fin 24, bvec 24 v i • ellCls i

theorem dec_xor (a b : ℕ) : dec (a ^^^ b) = dec a + dec b := by
  simp only [dec, bvec_xor, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem dec_zero : dec 0 = 0 := by
  simp [dec, bvec_zero]

theorem dec_eq_ellBasis (v : ℕ) : dec v = ellBasis.equivFun.symm (bvec 24 v) := by
  rw [Module.Basis.equivFun_symm_apply, dec]
  simp

theorem bvec_injective {a b : ℕ} (ha : a < 2 ^ 24) (hb : b < 2 ^ 24) (h : bvec 24 a = bvec 24 b) :
    a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 24
  · have := congrFun h ⟨i, hi⟩
    simp only [bvec_apply] at this
    cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num)
      (by omega))), Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hb (Nat.pow_le_pow_right
      (by norm_num) (by omega)))]

theorem dec_injective {a b : ℕ} (ha : a < 2 ^ 24) (hb : b < 2 ^ 24) (h : dec a = dec b) :
    a = b := by
  rw [dec_eq_ellBasis, dec_eq_ellBasis] at h
  exact bvec_injective ha hb (ellBasis.equivFun.symm.injective h)

theorem bL_dec (r : ℕ) (k : Fin 24) :
    QuadraticMap.polarBilin qL (dec r) (ellCls k) = (popc 24 (r &&& gramRow k) : ZMod 2) := by
  rw [← bvec_dotProduct, dec]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    bL_ellCls, smul_eq_mul, dotProduct]
  exact Finset.sum_congr rfl fun j _ => by rw [bvec_gramRow_symm]

theorem bL_nondegenerate : (QuadraticMap.polarBilin qL).Nondegenerate :=
  polarBilin_codeQuadForm_nondegenerate allOnes_mem_C weight_mod_four' mem_C_iff_forall_dotProduct

theorem eq_of_bL_ellCls {x y : L2}
    (h : ∀ k, QuadraticMap.polarBilin qL x (ellCls k) = QuadraticMap.polarBilin qL y (ellCls k)) :
    x = y := by
  rw [← sub_eq_zero]
  refine bL_nondegenerate.1 _ fun z => ?_
  rw [← ellBasis.sum_repr z]
  simp only [map_sum, map_smul, ellBasis_apply, map_sub, LinearMap.sub_apply, h, sub_self,
    smul_zero, Finset.sum_const_zero]

@[expose] def rowCheck (w : ℕ → ℤ) (r : ℕ) : Bool :=
  allTo (fun k => (sumTo (fun i => w i * ellN k i) 24 / 8) % 2 ==
    ((popc 24 (r &&& gramRow k) % 2 : ℕ) : ℤ)) 24

theorem cls_eq_dec_of_rowCheck {w : ℕ → ℤ} (hw : (fun i : Fin 24 => w i) ∈ codeLattice C)
    {r : ℕ} (h : rowCheck w r = true) : cls (fun i : Fin 24 => w i) hw = dec r := by
  refine eq_of_bL_ellCls fun k => ?_
  rw [bL_dec, ellCls, bL_cls, hInt_eq_sumTo]
  have hk := allTo_spec h k.2
  rw [beq_iff_eq] at hk
  rw [intCast_zmod_two_of_emod hk, ← ZMod.natCast_mod]
  push_cast
  rfl

@[expose] def actGo (rows : Array ℕ) (v : ℕ) : ℕ → ℕ → ℕ
  | 0, acc => acc
  | i + 1, acc => actGo rows v i (if v.testBit i then acc ^^^ rows[i]! else acc)

@[expose] def actRows (rows : Array ℕ) (v : ℕ) : ℕ := actGo rows v 24 0

@[expose] def actWord (gens : Array (Array ℕ)) : List ℕ → ℕ → ℕ
  | [], v => v
  | g :: w, v => actWord gens w (actRows gens[g]! v)

theorem dec_actGo (rows : Array ℕ) (v : ℕ) :
    ∀ n acc, n ≤ 24 → dec (actGo rows v n acc) =
      dec acc + ∑ i : Fin 24, (if (i : ℕ) < n then bvec 24 v i else 0) • dec rows[(i : ℕ)]!
  | 0, acc, _ => by simp [actGo]
  | n + 1, acc, hn => by
    rw [actGo, dec_actGo rows v n _ (by omega)]
    have hsplit : ∀ i : Fin 24, (if (i : ℕ) < n + 1 then bvec 24 v i else 0) =
        (if (i : ℕ) < n then bvec 24 v i else 0) + (if (i : ℕ) = n then bvec 24 v i else 0) := by
      intro i
      split_ifs <;> first | omega | simp
    simp only [hsplit, add_smul, Finset.sum_add_distrib]
    have hn' : n < 24 := by omega
    have hlast : ∑ i : Fin 24, (if (i : ℕ) = n then bvec 24 v i else 0) • dec rows[(i : ℕ)]! =
        if v.testBit n = true then dec rows[n]! else 0 := by
      rw [Finset.sum_eq_single (⟨n, hn'⟩ : Fin 24)]
      · simp [bvec_apply]
      · intro i _ hi
        have : (i : ℕ) ≠ n := fun h => hi (Fin.ext h)
        simp [this]
      · simp
    rw [hlast]
    by_cases h : v.testBit n = true
    · simp only [h, ite_true, dec_xor]
      abel
    · simp [h]

theorem dec_actRows (rows : Array ℕ) (v : ℕ) :
    dec (actRows rows v) = ∑ i : Fin 24, bvec 24 v i • dec rows[(i : ℕ)]! := by
  rw [actRows, dec_actGo rows v 24 0 le_rfl, dec_zero, zero_add]
  simp

theorem dec_seed : dec 63 = twoΩCls :=
  (cls_eq_dec_of_rowCheck (w := fun _ => 2) twoΩ_mem (by decide +kernel)).symm

end CFSG.Monster.VisCert
