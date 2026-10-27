module

public import CFSG.Monster.B.Pinned.Primes.Data
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Monster.B.Pinned

open scoped Matrix

@[expose] def lvecMul (p k : ℕ) (v : List ℕ) (M : List (List ℕ)) : List ℕ :=
  (List.range k).map fun j =>
    ((List.range k).map fun i => v.getD i 0 * (M.getD i []).getD j 0).sum % p

theorem lvecMul_length (p k : ℕ) (v : List ℕ) (M : List (List ℕ)) :
    (lvecMul p k v M).length = k := by
  simp [lvecMul]

theorem lvecMul_lt {p k : ℕ} (hp : 0 < p) (v : List ℕ) (M : List (List ℕ)) :
    ∀ d ∈ lvecMul p k v M, d < p := by
  intro d hd
  simp only [lvecMul, List.mem_map, List.mem_range] at hd
  obtain ⟨j, -, rfl⟩ := hd
  exact Nat.mod_lt _ hp

theorem sum_range_list (k : ℕ) (f : ℕ → ℕ) :
    (((List.range k).map f).sum : ℕ) = ∑ i ∈ Finset.range k, f i := by
  induction k with
  | zero => simp
  | succ k ih => rw [List.sum_range_succ, Finset.sum_range_succ, ih]

theorem rowsVec_lvecMul (p k : ℕ) (v : List ℕ) (M : List (List ℕ)) :
    rowsVec p k (lvecMul p k v M) = rowsVec p k v ᵥ* rowsMat p k M := by
  funext j
  simp only [rowsVec, lvecMul, Matrix.vecMul, dotProduct, rowsMat, Matrix.of_apply]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range j.2, Option.map_some,
    Option.getD_some, ZMod.natCast_mod, sum_range_list, Nat.cast_sum, Finset.sum_range]
  simp only [Nat.cast_mul]

@[expose] def lcode (v : List ℕ) : ℕ := v.foldr (fun d acc => d + 3 * acc) 0

theorem lcode_inj : ∀ {v w : List ℕ}, (∀ d ∈ v, d < 3) → (∀ d ∈ w, d < 3) →
    v.length = w.length → lcode v = lcode w → v = w
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, h, _ => absurd h (by simp)
  | _ :: _, [], _, _, h, _ => absurd h (by simp)
  | a :: v, b :: w, hv, hw, hl, h => by
    simp only [lcode, List.foldr_cons] at h
    have ha := hv a (List.mem_cons_self ..)
    have hb := hw b (List.mem_cons_self ..)
    have hab : a = b := by omega
    have hvw : lcode v = lcode w := by unfold lcode; omega
    rw [hab, lcode_inj (fun d hd => hv d (List.mem_cons_of_mem _ hd))
      (fun d hd => hw d (List.mem_cons_of_mem _ hd)) (by simpa using hl) hvw]

@[expose] def bfsAdd (st : ℕ × List (List ℕ)) (w : List ℕ) : ℕ × List (List ℕ) :=
  if st.1.testBit (lcode w) then st else (st.1 ||| 1 <<< lcode w, w :: st.2)

@[expose] def bfsLayer (gens : List (List (List ℕ))) (bm : ℕ) (F : List (List ℕ)) :
    ℕ × List (List ℕ) :=
  F.foldl (fun st u => gens.foldl (fun st' G => bfsAdd st' (lvecMul 3 8 u G)) st) (bm, [])

@[expose] def bfs (gens : List (List (List ℕ))) : ℕ → ℕ → List (List ℕ) → List (List ℕ) →
    List (List ℕ)
  | 0, _, F, acc => F ++ acc
  | fuel + 1, bm, F, acc =>
    match F with
    | [] => acc
    | _ :: _ =>
      let r := bfsLayer gens bm F
      bfs gens fuel r.1 r.2 (F ++ acc)

@[expose] def distinctBits : List (List ℕ) → ℕ → Option ℕ
  | [], bm => some bm
  | w :: L, bm => if bm.testBit (lcode w) then none else distinctBits L (bm ||| 1 <<< lcode w)

@[expose] def orbitOK (gens : List (List (List ℕ))) (L : List (List ℕ)) : Bool :=
  match distinctBits L 0 with
  | none => false
  | some bm => L.all fun w => gens.all fun G => bm.testBit (lcode (lvecMul 3 8 w G))

@[expose] def orbitBase : List ℕ := [1, 0, 1, 0, 0, 0, 0, 0]

@[expose] def orbitList : List (List ℕ) :=
  bfs [threeXRows, threeYRows] 20 (1 <<< lcode orbitBase) [orbitBase] []

theorem orbitList_facts :
    (orbitList.length == 1440 && orbitOK [threeXRows, threeYRows] orbitList) = true := by
  decide +kernel

theorem orbitList_ok :
    orbitList.length = 1440 ∧ orbitOK [threeXRows, threeYRows] orbitList = true := by
  have h := orbitList_facts
  rw [Bool.and_eq_true, beq_iff_eq] at h
  exact h

theorem testBit_or_shift (bm c c' : ℕ) :
    (bm ||| 1 <<< c).testBit c' = (bm.testBit c' || decide (c = c')) := by
  rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]

theorem distinctBits_spec : ∀ (L : List (List ℕ)) (bm bm' : ℕ), distinctBits L bm = some bm' →
    (∀ c, bm'.testBit c = true ↔ bm.testBit c = true ∨ ∃ w ∈ L, lcode w = c) ∧
      (L.map lcode).Nodup ∧ ∀ w ∈ L, bm.testBit (lcode w) = false
  | [], bm, bm', h => by
    simp only [distinctBits, Option.some.injEq] at h
    subst h
    simp
  | w :: L, bm, bm', h => by
    simp only [distinctBits] at h
    split_ifs at h with hw
    obtain ⟨h1, h2, h3⟩ := distinctBits_spec L _ _ h
    simp only [Bool.not_eq_true] at hw
    refine ⟨fun c => ?_, ?_, ?_⟩
    · rw [h1, testBit_or_shift]
      simp only [Bool.or_eq_true, decide_eq_true_eq, List.mem_cons, exists_eq_or_imp]
      tauto
    · refine List.nodup_cons.2 ⟨fun hmem => ?_, h2⟩
      obtain ⟨w', hw', he⟩ := List.mem_map.1 hmem
      have := h3 w' hw'
      rw [he, testBit_or_shift] at this
      simp at this
    · intro w' hw'
      rcases List.mem_cons.1 hw' with rfl | hw'
      · exact hw
      · have := h3 w' hw'
        rw [testBit_or_shift] at this
        simp only [Bool.or_eq_false_iff] at this
        exact this.1

theorem orbitOK_spec {gens : List (List (List ℕ))} {L : List (List ℕ)}
    (h : orbitOK gens L = true) :
    (L.map lcode).Nodup ∧ ∀ w ∈ L, ∀ G ∈ gens, ∃ w' ∈ L, lcode w' = lcode (lvecMul 3 8 w G) := by
  unfold orbitOK at h
  split at h
  · exact absurd h (by simp)
  · rename_i bm hbm
    obtain ⟨h1, h2, -⟩ := distinctBits_spec L 0 bm hbm
    refine ⟨h2, fun w hw G hG => ?_⟩
    have := List.all_eq_true.1 (List.all_eq_true.1 h w hw) G hG
    rcases (h1 _).1 this with h0 | h0
    · simp at h0
    · exact h0

theorem mem_bfsAdd {st : ℕ × List (List ℕ)} {w w' : List ℕ} (h : w' ∈ (bfsAdd st w).2) :
    w' = w ∨ w' ∈ st.2 := by
  unfold bfsAdd at h
  split_ifs at h
  · exact Or.inr h
  · exact List.mem_cons.1 h

theorem bfsLayer_inv {P : List ℕ → Prop} {gens : List (List (List ℕ))}
    (hP : ∀ u, P u → ∀ G ∈ gens, P (lvecMul 3 8 u G)) :
    ∀ (F : List (List ℕ)) (st : ℕ × List (List ℕ)), (∀ w ∈ st.2, P w) → (∀ u ∈ F, P u) →
      ∀ w ∈ (F.foldl (fun st u => gens.foldl (fun st' G => bfsAdd st' (lvecMul 3 8 u G)) st)
        st).2, P w
  | [], st, hst, _ => hst
  | u :: F, st, hst, hF => by
    rw [List.foldl_cons]
    refine bfsLayer_inv hP F _ ?_ (fun u' hu' => hF u' (List.mem_cons_of_mem _ hu'))
    have hu := hF u (List.mem_cons_self ..)
    have key : ∀ (gs : List (List (List ℕ))) (st' : ℕ × List (List ℕ)), (∀ G ∈ gs, G ∈ gens) →
        (∀ w ∈ st'.2, P w) →
        ∀ w ∈ (gs.foldl (fun st' G => bfsAdd st' (lvecMul 3 8 u G)) st').2, P w := by
      intro gs
      induction gs with
      | nil => intro st' _ h; exact h
      | cons G gs ih =>
        intro st' hgs h
        rw [List.foldl_cons]
        refine ih _ (fun G' hG' => hgs G' (List.mem_cons_of_mem _ hG')) ?_
        intro w hw
        rcases mem_bfsAdd hw with rfl | hw
        · exact hP u hu G (hgs G (List.mem_cons_self ..))
        · exact h w hw
    exact key gens st (fun G hG => hG) hst

theorem bfs_inv {P : List ℕ → Prop} {gens : List (List (List ℕ))}
    (hP : ∀ u, P u → ∀ G ∈ gens, P (lvecMul 3 8 u G)) :
    ∀ (fuel bm : ℕ) (F acc : List (List ℕ)), (∀ w ∈ F, P w) → (∀ w ∈ acc, P w) →
      ∀ w ∈ bfs gens fuel bm F acc, P w
  | 0, bm, F, acc, hF, hacc => by
    intro w hw
    rcases List.mem_append.1 hw with hw | hw
    · exact hF w hw
    · exact hacc w hw
  | fuel + 1, bm, [], acc, _, hacc => by
    intro w hw
    simp only [bfs] at hw
    exact hacc w hw
  | fuel + 1, bm, u :: F, acc, hF, hacc => by
    intro w hw
    simp only [bfs] at hw
    refine bfs_inv hP fuel _ _ _ (bfsLayer_inv hP (u :: F) (bm, []) (by simp) hF) ?_ w hw
    intro w hw
    rcases List.mem_append.1 hw with hw | hw
    · exact hF w hw
    · exact hacc w hw

theorem mem_bfs (gens : List (List (List ℕ))) :
    ∀ (fuel bm : ℕ) (F acc : List (List ℕ)), ∀ w ∈ F ++ acc, w ∈ bfs gens fuel bm F acc
  | 0, bm, F, acc => fun w hw => hw
  | fuel + 1, bm, [], acc => fun w hw => by simpa [bfs] using hw
  | fuel + 1, bm, u :: F, acc => fun w hw => by
    simp only [bfs]
    exact mem_bfs gens fuel _ _ _ w (List.mem_append_right _ hw)

@[expose] def lmul (A B : List (List ℕ)) : List (List ℕ) := A.map fun r => lvecMul 3 8 r B

@[expose] def lpow (A : List (List ℕ)) : ℕ → List (List ℕ)
  | 0 => (List.range 8).map fun i => (List.range 8).map fun j => if i = j then 1 else 0
  | e + 1 => lmul (lpow A e) A

theorem rowsMat_lmul {A : List (List ℕ)} (hA : A.length = 8) (B : List (List ℕ)) :
    rowsMat 3 8 (lmul A B) = rowsMat 3 8 A * rowsMat 3 8 B := by
  ext i j
  have hi : (i : ℕ) < A.length := lt_of_lt_of_eq i.2 hA.symm
  have e : (lmul A B).getD i [] = lvecMul 3 8 (A.getD i []) B := by
    rw [lmul, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
      List.getD_eq_getElem _ _ hi]
  have := congrFun (rowsVec_lvecMul 3 8 (A.getD i []) B) j
  simp only [rowsVec] at this
  simp only [rowsMat, Matrix.of_apply, e, this, Matrix.mul_apply, Matrix.vecMul, dotProduct,
    rowsVec]

theorem lmul_length (A B : List (List ℕ)) : (lmul A B).length = A.length := by simp [lmul]

theorem lpow_length (A : List (List ℕ)) : ∀ e, (lpow A e).length = 8
  | 0 => by simp [lpow]
  | e + 1 => by rw [lpow, lmul_length, lpow_length A e]

theorem rowsMat_lpow (A : List (List ℕ)) : ∀ e, rowsMat 3 8 (lpow A e) = rowsMat 3 8 A ^ e
  | 0 => by
    ext i j
    simp only [lpow, rowsMat, Matrix.of_apply, pow_zero, Matrix.one_apply,
      List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range i.2,
      List.getElem?_range j.2, Option.map_some, Option.getD_some]
    by_cases h : i = j
    · subst h; simp
    · have h' : (i : ℕ) ≠ j := fun e => h (Fin.ext e)
      simp [h, h']
  | e + 1 => by rw [lpow, rowsMat_lmul (lpow_length A e), rowsMat_lpow A e, pow_succ]

@[expose] def threeXiRows : List (List ℕ) :=
  [[0, 2, 0, 2, 0, 2, 1, 2], [1, 0, 0, 0, 0, 0, 0, 0], [1, 1, 1, 1, 2, 2, 2, 0],
    [0, 1, 0, 0, 0, 0, 0, 0], [2, 1, 1, 0, 0, 2, 0, 2], [0, 0, 1, 0, 0, 0, 0, 0],
    [0, 1, 2, 2, 1, 1, 0, 1], [0, 0, 0, 1, 0, 0, 0, 0]]

@[expose] def threeYiRows : List (List ℕ) :=
  [[1, 0, 0, 0, 0, 0, 1, 0], [2, 0, 0, 1, 1, 0, 2, 1], [1, 0, 0, 0, 0, 0, 0, 0],
    [2, 1, 2, 2, 1, 1, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [1, 0, 2, 1, 0, 1, 2, 1],
    [0, 0, 1, 0, 0, 0, 0, 0], [2, 2, 1, 2, 1, 0, 1, 0]]

theorem XThree_mul_inv : XThree * rowsMat 3 8 threeXiRows = 1 := by decide +kernel
theorem XThree_inv_mul : rowsMat 3 8 threeXiRows * XThree = 1 := by decide +kernel
theorem YThree_mul_inv : YThree * rowsMat 3 8 threeYiRows = 1 := by decide +kernel
theorem YThree_inv_mul : rowsMat 3 8 threeYiRows * YThree = 1 := by decide +kernel

@[expose] def XThreeU : GL (Fin 8) (ZMod 3) :=
  ⟨XThree, rowsMat 3 8 threeXiRows, XThree_mul_inv, XThree_inv_mul⟩

@[expose] def YThreeU : GL (Fin 8) (ZMod 3) :=
  ⟨YThree, rowsMat 3 8 threeYiRows, YThree_mul_inv, YThree_inv_mul⟩

@[expose] def KThree : Subgroup (GL (Fin 8) (ZMod 3)) := Subgroup.closure {XThreeU, YThreeU}

@[expose] def vThree : Fin 8 → ZMod 3 := ![1, 0, 1, 0, 0, 0, 0, 0]

@[expose] def sThree : GL (Fin 8) (ZMod 3) :=
  XThreeU⁻¹ * YThreeU * XThreeU⁻¹ * YThreeU * XThreeU * YThreeU⁻¹

@[expose] def sRows : List (List ℕ) :=
  lmul (lmul (lmul (lmul (lmul threeXiRows threeYRows) threeXiRows) threeYRows) threeXRows)
    threeYiRows

theorem coe_sThree : (sThree : Matrix (Fin 8) (Fin 8) (ZMod 3)) = rowsMat 3 8 sRows := by
  have h8 : ∀ A B : List (List ℕ), A.length = 8 → (lmul A B).length = 8 := fun A B h => by
    rw [lmul_length, h]
  simp only [sThree, sRows, Units.val_mul]
  rw [rowsMat_lmul (h8 _ _ (h8 _ _ (h8 _ _ (h8 _ _ rfl)))),
    rowsMat_lmul (h8 _ _ (h8 _ _ (h8 _ _ rfl))), rowsMat_lmul (h8 _ _ (h8 _ _ rfl)),
    rowsMat_lmul (h8 _ _ rfl), rowsMat_lmul rfl]
  rfl

theorem sRows_facts : lpow sRows 12 = lpow sRows 0 ∧ lvecMul 3 8 orbitBase sRows = orbitBase ∧
    rowsMat 3 8 (lpow sRows 6) ≠ 1 ∧ rowsMat 3 8 (lpow sRows 4) ≠ 1 := by
  refine ⟨by decide +kernel, by decide +kernel, ?_, ?_⟩ <;> decide +kernel

theorem vThree_eq : vThree = rowsVec 3 8 orbitBase := by decide +kernel

@[expose] def Valid3 (w : List ℕ) : Prop := w.length = 8 ∧ ∀ d ∈ w, d < 3

theorem valid_lvecMul (v : List ℕ) (M : List (List ℕ)) : Valid3 (lvecMul 3 8 v M) :=
  ⟨lvecMul_length 3 8 v M, lvecMul_lt (by norm_num) v M⟩

theorem rowsVec_inj {v w : List ℕ} (hv : Valid3 v) (hw : Valid3 w)
    (h : rowsVec 3 8 v = rowsVec 3 8 w) : v = w := by
  apply List.ext_getElem (hv.1.trans hw.1.symm)
  intro i hi hi'
  have hi8 : i < 8 := hv.1 ▸ hi
  have e := congrFun h ⟨i, hi8⟩
  simp only [rowsVec, List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi'] at e
  have h1 := hv.2 _ (List.getElem_mem hi)
  have h2 := hw.2 _ (List.getElem_mem hi')
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at e
  exact e

@[expose] def Reach3 (w : List ℕ) : Prop :=
  Valid3 w ∧ ∃ g ∈ KThree, rowsVec 3 8 w = vThree ᵥ* (g : Matrix (Fin 8) (Fin 8) (ZMod 3))

theorem reach3_step (u : List ℕ) (hu : Reach3 u) :
    ∀ G ∈ [threeXRows, threeYRows], Reach3 (lvecMul 3 8 u G) := by
  obtain ⟨-, g, hg, hgu⟩ := hu
  have key : ∀ (t : GL (Fin 8) (ZMod 3)) (G : List (List ℕ)), t ∈ KThree →
      (t : Matrix (Fin 8) (Fin 8) (ZMod 3)) = rowsMat 3 8 G → Reach3 (lvecMul 3 8 u G) := by
    intro t G ht htG
    refine ⟨valid_lvecMul u G, g * t, mul_mem hg ht, ?_⟩
    rw [rowsVec_lvecMul, hgu, Units.val_mul, ← Matrix.vecMul_vecMul, htG]
  intro G hG
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hG
  rcases hG with rfl | rfl
  · exact key XThreeU _ (Subgroup.subset_closure (Set.mem_insert _ _)) rfl
  · exact key YThreeU _ (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)) rfl

theorem reach3_orbitList : ∀ w ∈ orbitList, Reach3 w := by
  refine bfs_inv reach3_step 20 _ [orbitBase] [] ?_ (by simp)
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  subst hw
  exact ⟨⟨rfl, by decide⟩, 1, one_mem _, by rw [vThree_eq, Units.val_one, Matrix.vecMul_one]⟩

theorem orbitBase_mem : orbitBase ∈ orbitList :=
  mem_bfs _ 20 _ [orbitBase] [] orbitBase (by simp)

@[expose] def orbitSet3 : Set (Fin 8 → ZMod 3) := {u | ∃ w ∈ orbitList, u = rowsVec 3 8 w}

theorem orbitSet3_closed : ∀ u ∈ orbitSet3, ∀ G ∈ [threeXRows, threeYRows],
    u ᵥ* rowsMat 3 8 G ∈ orbitSet3 := by
  rintro u ⟨w, hw, rfl⟩ G hG
  obtain ⟨w', hw', he⟩ := (orbitOK_spec orbitList_ok.2).2 w hw G hG
  have := lcode_inj (reach3_orbitList w' hw').1.2 (valid_lvecMul w G).2
    ((reach3_orbitList w' hw').1.1.trans (valid_lvecMul w G).1.symm) he
  exact ⟨w', hw', by rw [this, rowsVec_lvecMul]⟩

theorem orbitSet3_invariant : ∀ g ∈ KThree, ∀ u ∈ orbitSet3,
    u ᵥ* (g : Matrix (Fin 8) (Fin 8) (ZMod 3)) ∈ orbitSet3 := by
  intro g hg
  have hg' : g ∈ Submonoid.closure ({XThreeU, YThreeU} : Set (GL (Fin 8) (ZMod 3))) := by
    rw [← Subgroup.closure_toSubmonoid_of_finite]
    exact hg
  clear hg
  induction hg' using Submonoid.closure_induction with
  | mem t ht =>
    intro u hu
    rcases ht with rfl | rfl
    · exact orbitSet3_closed u hu threeXRows (by simp)
    · exact orbitSet3_closed u hu threeYRows (by simp)
  | one => intro u hu; rwa [Units.val_one, Matrix.vecMul_one]
  | mul a b _ _ iha ihb =>
    intro u hu
    rw [Units.val_mul, ← Matrix.vecMul_vecMul]
    exact ihb _ (iha u hu)

theorem orbit_eq : {w : Fin 8 → ZMod 3 | ∃ g ∈ KThree, w = vThree ᵥ* (g : Matrix (Fin 8) (Fin 8)
    (ZMod 3))} = orbitSet3 := by
  ext u
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact orbitSet3_invariant g hg _ ⟨orbitBase, orbitBase_mem, vThree_eq⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨-, g, hg, e⟩ := reach3_orbitList w hw
    exact ⟨g, hg, e⟩

theorem ncard_orbitSet3 : orbitSet3.ncard = 1440 := by
  have hnd : orbitList.Nodup := (orbitOK_spec orbitList_ok.2).1.of_map _
  have hnd' : (orbitList.map (rowsVec 3 8)).Nodup :=
    hnd.map_on fun v hv w hw h => rowsVec_inj (reach3_orbitList v hv).1 (reach3_orbitList w hw).1 h
  have e : orbitSet3 = ↑(orbitList.map (rowsVec 3 8)).toFinset := by
    ext u
    simp only [orbitSet3, Set.mem_ofPred_eq, List.coe_toFinset, List.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩; exact ⟨w, hw, rfl⟩
    · rintro ⟨w, hw, rfl⟩; exact ⟨w, hw, rfl⟩
  rw [e, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd', List.length_map]
  exact orbitList_ok.1

theorem coe_sThree_pow (e : ℕ) :
    ((sThree ^ e : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) =
      rowsMat 3 8 (lpow sRows e) := by
  rw [Units.val_pow_eq_pow_val, coe_sThree, rowsMat_lpow]

theorem sThree_pow_twelve : sThree ^ 12 = 1 := by
  apply Units.ext
  rw [coe_sThree_pow, sRows_facts.1, ← coe_sThree_pow, pow_zero]

theorem sThree_pow_ne (e : ℕ) (h : rowsMat 3 8 (lpow sRows e) ≠ 1) : sThree ^ e ≠ 1 := by
  intro h'
  apply h
  rw [← coe_sThree_pow, h', Units.val_one]

theorem orderOf_sThree : orderOf sThree = 12 := by
  refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num) sThree_pow_twelve fun r hr hr12 => ?_
  have hr' : r ∈ ({2, 3} : Finset ℕ) := by
    have hle : r ≤ 12 := Nat.le_of_dvd (by norm_num) hr12
    interval_cases r <;> simp_all <;> norm_num at hr
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr'
  rcases hr' with rfl | rfl
  · exact sThree_pow_ne 6 sRows_facts.2.2.1
  · exact sThree_pow_ne 4 sRows_facts.2.2.2

theorem vThree_sThree : vThree ᵥ* (sThree : Matrix (Fin 8) (Fin 8) (ZMod 3)) = vThree := by
  rw [coe_sThree, vThree_eq, ← rowsVec_lvecMul, sRows_facts.2.1]

theorem sThree_mem : sThree ∈ KThree := by
  have hX : XThreeU ∈ KThree := Subgroup.subset_closure (Set.mem_insert _ _)
  have hY : YThreeU ∈ KThree := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  unfold sThree
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (inv_mem hX) hY) (inv_mem hX)) hY) hX)
    (inv_mem hY)

theorem vThree_sThree_pow (e : ℕ) :
    vThree ᵥ* ((sThree ^ e : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) = vThree := by
  rw [Units.val_pow_eq_pow_val]
  induction e with
  | zero => rw [pow_zero, Matrix.vecMul_one]
  | succ k ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih, vThree_sThree]

theorem orderOf_sThree_pow_four : orderOf (sThree ^ 4) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  refine orderOf_eq_prime ?_ (sThree_pow_ne 4 sRows_facts.2.2.2)
  rw [← pow_mul]
  exact sThree_pow_twelve

@[ext] structure RowV where
  vec : Fin 8 → ZMod 3

instance rowAction : MulAction (GL (Fin 8) (ZMod 3)) RowV where
  smul g w := ⟨w.vec ᵥ* ((g⁻¹ : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3))⟩
  one_smul w := RowV.ext (by
    show w.vec ᵥ* (((1 : GL (Fin 8) (ZMod 3))⁻¹ : GL (Fin 8) (ZMod 3)) :
      Matrix (Fin 8) (Fin 8) (ZMod 3)) = w.vec
    rw [inv_one, Units.val_one, Matrix.vecMul_one])
  mul_smul g h w := RowV.ext (by
    show w.vec ᵥ* (((g * h)⁻¹ : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) =
      (w.vec ᵥ* ((h⁻¹ : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3))) ᵥ*
        ((g⁻¹ : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3))
    rw [mul_inv_rev, Units.val_mul, Matrix.vecMul_vecMul])

theorem vec_smul (g : KThree) (w : RowV) :
    (g • w).vec = w.vec ᵥ* ((((g : GL (Fin 8) (ZMod 3))⁻¹ : GL (Fin 8) (ZMod 3))) :
      Matrix (Fin 8) (Fin 8) (ZMod 3)) :=
  rfl

@[expose] def vRow : RowV := ⟨vThree⟩

theorem image_orbit_vRow :
    RowV.vec '' MulAction.orbit KThree vRow = orbitSet3 := by
  rw [← orbit_eq]
  ext u
  constructor
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨(g : GL (Fin 8) (ZMod 3))⁻¹, inv_mem g.2, vec_smul g vRow⟩
  · rintro ⟨g, hg, rfl⟩
    refine ⟨(⟨g, hg⟩⁻¹ : KThree) • vRow, ⟨_, rfl⟩, ?_⟩
    rw [vec_smul, Subgroup.coe_inv, inv_inv]
    rfl

theorem ncard_orbit_vRow : (MulAction.orbit KThree vRow).ncard = 1440 := by
  rw [← Set.ncard_image_of_injective _ (fun a b h => RowV.ext h), image_orbit_vRow]
  exact ncard_orbitSet3

theorem card_KThree_dvd : 4320 ∣ Nat.card KThree := by
  have hidx := MulAction.index_stabilizer KThree vRow
  rw [ncard_orbit_vRow] at hidx
  have hcard := (MulAction.stabilizer KThree vRow).card_mul_index
  rw [hidx] at hcard
  have hs4 : sThree ^ 4 ∈ KThree := pow_mem sThree_mem 4
  have hfix := vThree_sThree_pow 4
  have hstab : (⟨sThree ^ 4, hs4⟩ : KThree) ∈ MulAction.stabilizer KThree vRow := by
    rw [MulAction.mem_stabilizer_iff]
    apply RowV.ext
    rw [vec_smul]
    show vThree ᵥ* (((sThree ^ 4)⁻¹ : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) =
      vThree
    conv_lhs => rw [← hfix]
    rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
  have h3 : orderOf (⟨⟨sThree ^ 4, hs4⟩, hstab⟩ : MulAction.stabilizer KThree vRow) = 3 := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, orderOf_sThree_pow_four]
  have hd := orderOf_dvd_natCard (⟨⟨sThree ^ 4, hs4⟩, hstab⟩ : MulAction.stabilizer KThree vRow)
  rw [h3] at hd
  rw [← hcard, show (4320 : ℕ) = 3 * 1440 by norm_num]
  exact Nat.mul_dvd_mul_right hd 1440

theorem pinned_B_three_primary_action_image_divisor :
    IsUnit XThree ∧ IsUnit YThree ∧
      (XThreeU : Matrix (Fin 8) (Fin 8) (ZMod 3)) = XThree ∧
      (YThreeU : Matrix (Fin 8) (Fin 8) (ZMod 3)) = YThree ∧
      KThree = Subgroup.closure {XThreeU, YThreeU} ∧ vThree = ![1, 0, 1, 0, 0, 0, 0, 0] ∧
      Set.ncard {w : Fin 8 → ZMod 3 |
        ∃ g ∈ KThree, w = vThree ᵥ* (g : Matrix (Fin 8) (Fin 8) (ZMod 3))} = 1440 ∧
      sThree = XThreeU⁻¹ * YThreeU * XThreeU⁻¹ * YThreeU * XThreeU * YThreeU⁻¹ ∧
      sThree ∈ KThree ∧ vThree ᵥ* (sThree : Matrix (Fin 8) (Fin 8) (ZMod 3)) = vThree ∧
      orderOf sThree = 12 ∧ sThree ^ 4 ∈ KThree ∧
      vThree ᵥ* ((sThree ^ 4 : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) = vThree ∧
      orderOf (sThree ^ 4) = 3 ∧ 4320 ∣ Nat.card KThree ∧ 3 ^ 3 ∣ Nat.card KThree := by
  refine ⟨XThreeU.isUnit, YThreeU.isUnit, rfl, rfl, rfl, rfl, by rw [orbit_eq, ncard_orbitSet3],
    rfl, sThree_mem, vThree_sThree, orderOf_sThree, pow_mem sThree_mem 4, vThree_sThree_pow 4,
    orderOf_sThree_pow_four, card_KThree_dvd, (show 3 ^ 3 ∣ 4320 by norm_num).trans card_KThree_dvd⟩

end CFSG.Monster.B.Pinned
