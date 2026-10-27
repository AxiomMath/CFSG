module

public import Mathlib
public import Certificates.Data.CFSGNative.Th.Certificate
import Certificates.Data.CFSGNative.Th.Core
import Certificates.Data.CFSGNative.Th.Orbit
import Certificates.Data.CFSGNative.Th.Tables
import Certificates.Data.CFSGNative.Th.Sift
import Certificates.Data.CFSGNative.Th.Suborbits

public section

namespace CFSG.Sporadic.Th

open Native

theorem allIn_eq_true {lo hi : ℕ} {p : ℕ → Bool} :
    allIn lo hi p = true ↔ ∀ i, lo ≤ i → i < hi → p i = true := by
  unfold allIn
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  constructor
  · intro h i hlo hhi
    have := h ⟨i - lo, by omega⟩ (List.mem_finRange _)
    simpa [Nat.add_sub_cancel' hlo] using this
  · rintro h ⟨k, hk⟩ _
    exact h (lo + k) (by omega) (by omega)

theorem nat_all_eq_true_imp {n : ℕ} {f : (k : ℕ) → k < n → Bool} (h : Nat.all n f = true)
    (k : ℕ) (hk : k < n) : f k hk = true := by
  rw [Nat.all_eq_finRange_all, List.all_eq_true] at h
  exact h ⟨k, hk⟩ (List.mem_finRange _)

theorem parAll_eq_true {n chunks : ℕ} {p : ℕ → Bool} (h : parAll n chunks p = true) :
    ∀ i < n, p i = true := by
  intro i hi
  unfold parAll at h
  simp only [List.all_map, List.all_eq_true, List.mem_range, Function.comp_apply] at h
  have hcpos : 0 < chunks + 1 := Nat.succ_pos _
  have hstep := h (i % (chunks + 1)) (Nat.mod_lt _ hcpos)
  change allStep (i % (chunks + 1)) (chunks + 1) n p = true at hstep
  unfold allStep at hstep
  have hdiv := Nat.mod_add_div i (chunks + 1)
  have hk : i / (chunks + 1) < (n + (chunks + 1) - 1 - i % (chunks + 1)) / (chunks + 1) := by
    apply Nat.lt_of_succ_le
    rw [Nat.le_div_iff_mul_le hcpos]
    have hmod := Nat.mod_lt i hcpos
    have e : (i / (chunks + 1) + 1) * (chunks + 1) =
        (chunks + 1) * (i / (chunks + 1)) + (chunks + 1) := by ring
    rw [e]
    generalize (chunks + 1) * (i / (chunks + 1)) = X at hdiv ⊢
    omega
  have := nat_all_eq_true_imp hstep _ hk
  rwa [hdiv] at this

theorem readU32_lt (b : ByteArray) (i : ℕ) : readU32 b i < 2 ^ 32 := by
  unfold readU32
  have hb : ∀ o, (b.get! o).toNat < 2 ^ 8 := fun o => (b.get! o).toNat_lt
  have hs : ∀ o k, k ≤ 24 → (b.get! o).toNat <<< k < 2 ^ 32 := by
    intro o k hk
    rw [Nat.shiftLeft_eq]
    calc (b.get! o).toNat * 2 ^ k < 2 ^ 8 * 2 ^ k :=
          Nat.mul_lt_mul_of_pos_right (hb o) (Nat.two_pow_pos k)
      _ = 2 ^ (8 + k) := (Nat.pow_add 2 8 k).symm
      _ ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine Nat.or_lt_two_pow (Nat.or_lt_two_pow (Nat.or_lt_two_pow ?_ ?_) ?_) ?_
  · exact lt_of_lt_of_le (hb _) (by norm_num)
  · exact hs _ _ (by norm_num)
  · exact hs _ _ (by norm_num)
  · exact hs _ _ (by norm_num)

theorem ap_ofFn {n i : ℕ} (f : Fin n → UInt32) (hi : i < n) :
    ap (Array.ofFn f) i = (f ⟨i, hi⟩).toNat := by
  unfold ap
  rw [getElem!_pos _ _ (by simpa using hi), Array.getElem_ofFn]

theorem ap_tblOfBytes {n i : ℕ} (b : ByteArray) (hi : i < n) :
    ap (tblOfBytes n b) i = readU32 b i := by
  unfold tblOfBytes
  rw [ap_ofFn _ hi, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (readU32_lt b i)]

section Rep

variable {G : Type*} [Group G] {n : ℕ} [MulAction G (Fin n)]

@[expose] def idx (n : ℕ) [MulAction G (Fin n)] (g : G) (i : ℕ) : ℕ :=
  if h : i < n then (g • (⟨i, h⟩ : Fin n)).val else i

theorem idx_of_lt (g : G) {i : ℕ} (hi : i < n) : idx n g i = (g • (⟨i, hi⟩ : Fin n)).val :=
  dite_eq_left hi

theorem idx_of_not_lt (g : G) {i : ℕ} (hi : ¬i < n) : idx n g i = i :=
  dite_eq_right hi

theorem idx_lt (g : G) {i : ℕ} (hi : i < n) : idx n g i < n := by
  rw [idx_of_lt g hi]
  exact (g • (⟨i, hi⟩ : Fin n)).isLt

theorem idx_mul (g h : G) (i : ℕ) : idx n (g * h) i = idx n g (idx n h i) := by
  by_cases hi : i < n
  · have e : (⟨idx n h i, idx_lt h hi⟩ : Fin n) = h • ⟨i, hi⟩ := Fin.ext (idx_of_lt h hi)
    rw [idx_of_lt g (idx_lt h hi), idx_of_lt (g * h) hi, e, mul_smul]
  · rw [idx_of_not_lt _ hi, idx_of_not_lt _ hi, idx_of_not_lt _ hi]

theorem idx_one (i : ℕ) : idx n (1 : G) i = i := by
  by_cases hi : i < n
  · rw [idx_of_lt _ hi, one_smul]
  · rw [idx_of_not_lt _ hi]

theorem idx_inv_idx (g : G) (i : ℕ) : idx n g⁻¹ (idx n g i) = i := by
  rw [← idx_mul, inv_mul_cancel, idx_one]

theorem idx_idx_inv (g : G) (i : ℕ) : idx n g (idx n g⁻¹ i) = i := by
  rw [← idx_mul, mul_inv_cancel, idx_one]

@[expose] def Rep (n : ℕ) [MulAction G (Fin n)] (T : Table) (g : G) : Prop :=
  ∀ i < n, ap T i = idx n g i

theorem Rep.idT (hn : n < 2 ^ 32) : Rep n (idT n) (1 : G) := by
  intro i hi
  rw [idx_one]
  unfold Native.idT
  rw [ap_ofFn _ hi, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (hi.trans hn)]

theorem Rep.compT {P Q : Table} {g h : G} (hP : Rep n P g) (hQ : Rep n Q h) :
    Rep n (compT n P Q) (g * h) := by
  intro i hi
  unfold Native.compT
  rw [ap_ofFn _ hi, idx_mul, ← hQ i hi, ← hP _ (by rw [hQ i hi]; exact idx_lt h hi)]
  rfl

theorem Rep.powT (hn : n < 2 ^ 32) {P : Table} {g : G} (hP : Rep n P g) (e : ℕ) :
    Rep n (powT n e P) (g ^ e) := by
  induction e with
  | zero => rw [pow_zero]; exact Rep.idT hn
  | succ e ih => rw [pow_succ']; exact Rep.compT hP ih

theorem Rep.inv_of_invOK {P R : Table} {g : G} (hP : Rep n P g) (h : invOK n P R = true) :
    Rep n R g⁻¹ := by
  intro i hi
  have hj := idx_lt g⁻¹ hi
  have := allIn_eq_true.1 h (idx n g⁻¹ i) (Nat.zero_le _) hj
  rw [beq_iff_eq, hP _ hj, idx_idx_inv] at this
  exact this

theorem idx_sq_of_invoOK {P : Table} {g : G} (hP : Rep n P g) (h : invoOK n P = true) :
    ∀ i < n, idx n (g ^ 2) i = i := by
  intro i hi
  have := allIn_eq_true.1 h i (Nat.zero_le _) hi
  rw [beq_iff_eq, hP i hi, hP _ (idx_lt g hi)] at this
  rw [pow_two, idx_mul, this]

theorem Rep.inv_of_invoOK {P : Table} {g : G} (hP : Rep n P g) (h : invoOK n P = true) :
    Rep n P g⁻¹ :=
  Rep.inv_of_invOK hP h

theorem idx_cube_of_order3OK {P : Table} {g : G} (hP : Rep n P g) (h : order3OK n P = true) :
    ∀ i < n, idx n (g ^ 3) i = i := by
  intro i hi
  have := allIn_eq_true.1 h i (Nat.zero_le _) hi
  rw [beq_iff_eq, hP i hi, hP _ (idx_lt g hi), hP _ (idx_lt g (idx_lt g hi))] at this
  rw [pow_three, idx_mul, idx_mul, this]

@[expose] def stepG (regs : ℕ → G) : Instr → ℕ → G
  | .mu i j k => Function.update regs k (regs i * regs j)
  | .pwr e i k => Function.update regs k (regs i ^ e)
  | .iv i k => Function.update regs k (regs i)⁻¹

@[expose] def runSLPG (prog : List Instr) (regs : ℕ → G) : ℕ → G :=
  prog.foldl stepG regs

@[expose] def instrRegsLt (r : ℕ) : Instr → Prop
  | .mu i j k => i < r ∧ j < r ∧ k < r
  | .pwr _ i k => i < r ∧ k < r
  | .iv i k => i < r ∧ k < r

private theorem getElem!_set! {α : Type*} [Inhabited α] (a : Array α) (k r : ℕ) (v : α)
    (hr : r < a.size) : (a.set! k v)[r]! = if k = r then v else a[r]! := by
  rw [Array.set!_eq_setIfInBounds, getElem!_pos (a.setIfInBounds k v) r (by simpa using hr),
    Array.getElem_setIfInBounds hr, getElem!_pos a r hr]

private theorem foldl_stepT_flag (n : ℕ) (prog : List Instr) (st : Array Table × Bool)
    (h : (prog.foldl (stepT n) st).2 = true) : st.2 = true := by
  induction prog generalizing st with
  | nil => exact h
  | cons ins prog ih =>
    have h' := ih _ h
    cases ins with
    | mu i j k => exact h'
    | pwr e i k => exact h'
    | iv i k => exact (Bool.and_eq_true_iff.1 h').1

private theorem foldl_stepT_rep (hn : n < 2 ^ 32) (prog : List Instr) (st : Array Table × Bool)
    (regsG : ℕ → G) (hprog : ∀ ins ∈ prog, instrRegsLt st.1.size ins)
    (hregs : ∀ r < st.1.size, Rep n st.1[r]! (regsG r))
    (hok : (prog.foldl (stepT n) st).2 = true) :
    (prog.foldl (stepT n) st).1.size = st.1.size ∧
      ∀ r < st.1.size, Rep n (prog.foldl (stepT n) st).1[r]! (runSLPG prog regsG r) := by
  induction prog generalizing st regsG with
  | nil => exact ⟨rfl, hregs⟩
  | cons ins prog ih =>
    rw [List.foldl_cons] at hok ⊢
    have hflag := foldl_stepT_flag n prog _ hok
    have hins := hprog ins List.mem_cons_self
    have hsz : (stepT n st ins).1.size = st.1.size := by
      cases ins <;> simp [stepT]
    have hstep : ∀ r < st.1.size, Rep n (stepT n st ins).1[r]! (stepG regsG ins r) := by
      intro r hr
      cases ins with
      | mu i j k =>
        simp only [stepT, stepG, getElem!_set! _ _ _ _ hr, Function.update_apply]
        by_cases hkr : k = r
        · subst hkr
          rw [ite_eq_left rfl, ite_eq_left rfl]
          exact Rep.compT (hregs i hins.1) (hregs j hins.2.1)
        · rw [ite_eq_right hkr, ite_eq_right (Ne.symm hkr)]
          exact hregs r hr
      | pwr e i k =>
        simp only [stepT, stepG, getElem!_set! _ _ _ _ hr, Function.update_apply]
        by_cases hkr : k = r
        · subst hkr
          rw [ite_eq_left rfl, ite_eq_left rfl]
          exact Rep.powT hn (hregs i hins.1) e
        · rw [ite_eq_right hkr, ite_eq_right (Ne.symm hkr)]
          exact hregs r hr
      | iv i k =>
        simp only [stepT] at hflag
        simp only [stepT, stepG, getElem!_set! _ _ _ _ hr, Function.update_apply]
        by_cases hkr : k = r
        · subst hkr
          rw [ite_eq_left rfl, ite_eq_left rfl]
          exact Rep.inv_of_invOK (hregs i hins.1) (Bool.and_eq_true_iff.1 hflag).2
        · rw [ite_eq_right hkr, ite_eq_right (Ne.symm hkr)]
          exact hregs r hr
    have := ih (stepT n st ins) (stepG regsG ins)
      (fun ins' hins' => hsz ▸ hprog ins' (List.mem_cons_of_mem _ hins'))
      (fun r hr => hstep r (hsz ▸ hr)) hok
    refine ⟨this.1.trans hsz, fun r hr => ?_⟩
    exact this.2 r (hsz.symm ▸ hr)

theorem runSLP_rep (hn : n < 2 ^ 32) (prog : List Instr) (regsT : Array Table) (regsG : ℕ → G)
    (hprog : ∀ ins ∈ prog, instrRegsLt regsT.size ins)
    (hregs : ∀ r < regsT.size, Rep n regsT[r]! (regsG r))
    (hok : (runSLP n prog regsT).2 = true) :
    (runSLP n prog regsT).1.size = regsT.size ∧
      ∀ r < regsT.size, Rep n (runSLP n prog regsT).1[r]! (runSLPG prog regsG r) :=
  foldl_stepT_rep hn prog (regsT, true) regsG hprog hregs hok

@[expose] def wordG (gensG : ℤ → G) (w : List ℤ) : G := (w.map gensG).prod

theorem wordT_size (n : ℕ) (gens : ℤ → Table) (w : List ℤ) : (wordT n gens w).size = n := by
  induction w with
  | nil => simp [wordT, Native.idT]
  | cons l w ih =>
    simp only [wordT, List.foldr_cons, Array.size_map] at ih ⊢
    exact ih

theorem Rep.wordT (hn : n < 2 ^ 32) {gens : ℤ → Table} {gensG : ℤ → G} (w : List ℤ)
    (h : ∀ l ∈ w, Rep n (gens l) (gensG l)) : Rep n (wordT n gens w) (wordG gensG w) := by
  induction w with
  | nil => simpa [Native.wordT, wordG] using Rep.idT (G := G) hn
  | cons l w ih =>
    have ih := ih (fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))
    intro i hi
    have hsz := wordT_size n gens w
    have e : Native.wordT n gens (l :: w) =
        (Native.wordT n gens w).map (fun t => (gens l)[t.toNat]!) := rfl
    have hw : wordG gensG (l :: w) = gensG l * wordG gensG w := by
      simp only [wordG, List.map_cons, List.prod_cons]
    rw [e, hw, idx_mul, ← ih i hi, ← h l List.mem_cons_self _ (by rw [ih i hi]; exact idx_lt _ hi)]
    unfold ap
    rw [getElem!_pos (Array.map _ (Native.wordT n gens w)) i (by simp [hsz, hi]),
      Array.getElem_map, getElem!_pos (Native.wordT n gens w) i (by simp [hsz, hi])]

private theorem foldl_set_ap (T : Table) (q : Array ℕ) (m : ℕ) :
    ∀ (s : ℕ) (a : Array ℕ), a.size = q.size → s + m = q.size →
      (∀ j < s, a[j]! = ap T q[j]!) → (∀ j, s ≤ j → j < q.size → a[j]! = q[j]!) →
      (List.range' s m).foldl (fun b k => b.set! k (ap T b[k]!)) a = q.map (ap T) := by
  induction m with
  | zero =>
    intro s a ha hs h1 _
    rw [List.range'_zero, List.foldl_nil]
    refine Array.ext (by simp [ha]) fun j hj₁ hj₂ => ?_
    have := h1 j (by omega)
    rw [getElem!_pos a j hj₁, getElem!_pos q j (by omega)] at this
    rw [this, Array.getElem_map]
  | succ m ih =>
    intro s a ha hs h1 h2
    rw [List.range'_succ, List.foldl_cons]
    apply ih (s + 1) _ (by simp [ha]) (by omega)
    · intro j hj
      rw [getElem!_set! _ _ _ _ (by omega)]
      by_cases hjs : s = j
      · subst hjs
        rw [ite_eq_left rfl, h2 s le_rfl (by omega)]
      · rw [ite_eq_right hjs]
        exact h1 j (by omega)
    · intro j hj hjq
      rw [getElem!_set! _ _ _ _ (by omega), ite_eq_right (by omega)]
      exact h2 j (by omega) hjq

theorem apT_eq_map (T : Table) (q : Array ℕ) : apT T q = q.map (ap T) := by
  unfold apT
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size]
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, bind_pure]
  exact foldl_set_ap T q q.size 0 q rfl (by omega) (fun j hj => absurd hj (Nat.not_lt_zero _))
    (fun _ _ _ => rfl)

theorem apT_size (T : Table) (q : Array ℕ) : (apT T q).size = q.size := by
  rw [apT_eq_map, Array.size_map]

theorem apT_get (T : Table) (q : Array ℕ) {k : ℕ} (hk : k < q.size) :
    (apT T q)[k]! = ap T q[k]! := by
  rw [apT_eq_map, getElem!_pos (q.map (ap T)) k (by simpa using hk), Array.getElem_map,
    getElem!_pos q k hk]

@[expose] def treeElt (pl : Table) (gensG : ℕ → G) (k : ℕ) : G :=
  if _h : 0 < k ∧ treePar (pl[k]!).toNat < k then
    gensG (treeLab (pl[k]!).toNat) * treeElt pl gensG (treePar (pl[k]!).toNat)
  else 1
termination_by k

theorem treeElt_mem (K : Subgroup G) (pl : Table) {gensG : ℕ → G} (h : ∀ s, gensG s ∈ K)
    (k : ℕ) : treeElt pl gensG k ∈ K := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [treeElt.eq_def]
    split_ifs with hk
    · exact K.mul_mem (h _) (ih _ hk.2)
    · exact K.one_mem

theorem applyTree_spec {gens : ℕ → Table} {gensG : ℕ → G} (hgens : ∀ s, Rep n (gens s) (gensG s))
    (pl : Table) (k : ℕ) (q : Array ℕ) (hq : ∀ j < q.size, q[j]! < n) :
    (applyTree pl gens k q).size = q.size ∧
      ∀ j < q.size, (applyTree pl gens k q)[j]! = idx n (treeElt pl gensG k) q[j]! := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [applyTree.eq_def, treeElt.eq_def]
    split_ifs with hk
    · obtain ⟨hs, he⟩ := ih _ hk.2
      refine ⟨by rw [apT_size, hs], fun j hj => ?_⟩
      rw [apT_get _ _ (by rwa [hs]), he j hj, hgens _ _ (idx_lt _ (hq j hj)), idx_mul]
    · exact ⟨rfl, fun j _ => by rw [idx_one]⟩

theorem applyTreeInv_spec {gensInv : ℕ → Table} {gensG : ℕ → G}
    (hgens : ∀ s, Rep n (gensInv s) (gensG s)⁻¹)
    (pl : Table) (k : ℕ) (q : Array ℕ) (hq : ∀ j < q.size, q[j]! < n) :
    (applyTreeInv pl gensInv k q).size = q.size ∧
      ∀ j < q.size, (applyTreeInv pl gensInv k q)[j]! = idx n (treeElt pl gensG k)⁻¹ q[j]! := by
  induction k using Nat.strong_induction_on generalizing q with
  | _ k ih =>
    rw [applyTreeInv.eq_def, treeElt.eq_def]
    split_ifs with hk
    · have hq' : ∀ j < (apT (gensInv (treeLab (pl[k]!).toNat)) q).size,
          (apT (gensInv (treeLab (pl[k]!).toNat)) q)[j]! < n := by
        intro j hj
        rw [apT_size] at hj
        rw [apT_get _ _ hj, hgens _ _ (hq j hj)]
        exact idx_lt _ (hq j hj)
      obtain ⟨hs, he⟩ := ih _ hk.2 _ hq'
      refine ⟨by rw [hs, apT_size], fun j hj => ?_⟩
      rw [he j (by rwa [apT_size]), apT_get _ _ hj, hgens _ _ (hq j hj), ← idx_mul, mul_inv_rev]
    · exact ⟨rfl, fun j _ => by rw [inv_one, idx_one]⟩

@[expose] def lettersG (x y : G) (s : ℕ) : G := if s = 1 then x else y

theorem Rep.letters {P₁ P₂ : Table} {x y : G} (h₁ : Rep n P₁ x) (h₂ : Rep n P₂ y) (s : ℕ) :
    Rep n (letters P₁ P₂ s) (lettersG x y s) := by
  unfold Native.letters lettersG
  split_ifs
  · exact h₁
  · exact h₂

theorem treeOK_spec {g1 g2 : Table} {x y : G} (h1 : Rep n g1 x) (h2 : Rep n g2 y)
    {m root : ℕ} {pts pl : Table} {lk : ℕ → ℕ}
    (h : treeOK n m root pts pl lk g1 g2 = true) :
    0 < m ∧ ap pts 0 = root ∧
      (∀ k < m, ap pts k < n ∧ lk (ap pts k) = k) ∧
      (∀ k < m, lk (idx n x (ap pts k)) < m ∧
        ap pts (lk (idx n x (ap pts k))) = idx n x (ap pts k)) ∧
      (∀ k < m, lk (idx n y (ap pts k)) < m ∧
        ap pts (lk (idx n y (ap pts k))) = idx n y (ap pts k)) ∧
      (∀ k < m, idx n (treeElt pl (lettersG x y) k) root = ap pts k) := by
  unfold treeOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨hm, h0⟩, hall⟩ := h
  have hc : ∀ k < m, ap pts k < n ∧ lk (ap pts k) = k ∧
      (lk (ap g1 (ap pts k)) < m ∧ ap pts (lk (ap g1 (ap pts k))) = ap g1 (ap pts k)) ∧
      (lk (ap g2 (ap pts k)) < m ∧ ap pts (lk (ap g2 (ap pts k))) = ap g2 (ap pts k)) ∧
      (k = 0 ∨ (treePar (pl[k]!).toNat < k ∧
        ((treeLab (pl[k]!).toNat = 1 ∧ ap g1 (ap pts (treePar (pl[k]!).toNat)) = ap pts k) ∨
          (treeLab (pl[k]!).toNat = 2 ∧
            ap g2 (ap pts (treePar (pl[k]!).toNat)) = ap pts k)))) := by
    intro k hk
    have := allIn_eq_true.1 hall k (Nat.zero_le _) hk
    simp only [treeCheckAt, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
      beq_iff_eq] at this
    obtain ⟨⟨⟨⟨⟨⟨hp, hlk⟩, ha1⟩, ha2⟩, hb1⟩, hb2⟩, ht⟩ := this
    exact ⟨hp, hlk, ⟨ha1, ha2⟩, ⟨hb1, hb2⟩, ht⟩
  refine ⟨hm, h0, fun k hk => ⟨(hc k hk).1, (hc k hk).2.1⟩, fun k hk => ?_, fun k hk => ?_,
    fun k hk => ?_⟩
  · rw [← h1 _ (hc k hk).1]
    exact (hc k hk).2.2.1
  · rw [← h2 _ (hc k hk).1]
    exact (hc k hk).2.2.2.1
  · induction k using Nat.strong_induction_on with
    | _ k ih =>
      rcases (hc k hk).2.2.2.2 with hk0 | ⟨hpar, hlab⟩
      · subst hk0
        rw [treeElt.eq_def, dite_eq_right (fun h => absurd h.1 (lt_irrefl 0)), idx_one, h0]
      · have hk0 : 0 < k := lt_of_le_of_lt (Nat.zero_le _) hpar
        rw [treeElt.eq_def, dite_eq_left ⟨hk0, hpar⟩, idx_mul, ih _ hpar (hpar.trans hk)]
        have hlt := (hc _ (hpar.trans hk)).1
        rcases hlab with ⟨hl, he⟩ | ⟨hl, he⟩
        · rw [hl, lettersG, ite_eq_left rfl, ← h1 _ hlt, he]
        · rw [hl, lettersG, ite_eq_right (by norm_num), ← h2 _ hlt, he]

theorem reqTwo_cover (pl : Table) (P : ℕ → ℕ) (s i : ℕ) (hinv : P (P i) = i) :
    (reqTwo pl P s i = true ∨ treeEdge pl s i (P i) = true) ∨
      (P i ≠ i ∧ (reqTwo pl P s (P i) = true ∨ treeEdge pl s (P i) (P (P i)) = true)) := by
  simp only [reqTwo, hinv]
  generalize treeEdge pl s i (P i) = a
  generalize treeEdge pl s (P i) i = b
  generalize P i = j
  cases a <;> cases b <;> simp <;> omega

theorem reqThree_cover (pl : Table) (P : ℕ → ℕ) (s i : ℕ) (h3 : P (P (P i)) = i) :
    (reqThree pl P s i = true ∨ treeEdge pl s i (P i) = true) ∨
      (P i ≠ i ∧ (reqThree pl P s (P i) = true ∨ treeEdge pl s (P i) (P (P i)) = true) ∧
        (reqThree pl P s (P (P i)) = true ∨
          treeEdge pl s (P (P i)) (P (P (P i))) = true)) := by
  have hkj : P (P i) = P i → P i = i := fun h => by
    have := congrArg P h
    rw [h3, h] at this
    exact this.symm
  have hki : P (P i) = i → P i = i := fun h => by
    have := congrArg P h
    rw [h3] at this
    exact this.symm
  simp only [reqThree, h3]
  generalize treeEdge pl s i (P i) = a at *
  generalize treeEdge pl s (P i) (P (P i)) = b at *
  generalize treeEdge pl s (P (P i)) i = c at *
  generalize P (P i) = k at *
  generalize P i = j at *
  cases a <;> cases b <;> cases c <;> simp <;> omega

theorem treeElt_of_treeEdge (pl : Table) (gensG : ℕ → G) {s i j : ℕ}
    (h : treeEdge pl s i j = true) (hij : i < j) :
    treeElt pl gensG j = gensG s * treeElt pl gensG i := by
  simp only [treeEdge, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨hj, hp⟩, hl⟩ := h
  rw [treeElt.eq_def, dite_eq_left ⟨hj, hp ▸ hij⟩, hp, hl]

theorem tuple0_spec : tuple0.size = 124 ∧ ∀ j < 124, tuple0[j]! = j := by
  refine ⟨by simp [tuple0], fun j hj => ?_⟩
  unfold tuple0
  rw [getElem!_pos _ _ (by simpa using hj), Array.getElem_ofFn]

private def TupRep (n m : ℕ) [MulAction G (Fin n)] (q : Array ℕ) (g : G) : Prop :=
  q.size = m ∧ ∀ j < m, q[j]! = idx n g j

private theorem tupRep_tuple0 : TupRep n 124 tuple0 (1 : G) :=
  ⟨tuple0_spec.1, fun j hj => by rw [tuple0_spec.2 j hj, idx_one]⟩

private theorem TupRep.lt {m : ℕ} (hm : m ≤ n) {q : Array ℕ} {g : G} (h : TupRep n m q g) :
    ∀ j < q.size, q[j]! < n := by
  intro j hj
  rw [h.1] at hj
  rw [h.2 j hj]
  exact idx_lt g (by omega)

private theorem TupRep.apT {m : ℕ} (hm : m ≤ n) {q : Array ℕ} {g h : G} (hq : TupRep n m q g)
    {T : Table} (hT : Rep n T h) : TupRep n m (apT T q) (h * g) := by
  refine ⟨by rw [apT_size, hq.1], fun j hj => ?_⟩
  rw [apT_get _ _ (by rw [hq.1]; exact hj), hq.2 j hj, hT _ (idx_lt g (by omega)), idx_mul]

private theorem TupRep.applyTree {m : ℕ} (hm : m ≤ n) {q : Array ℕ} {g : G} (hq : TupRep n m q g)
    {gens : ℕ → Table} {gensG : ℕ → G} (hgens : ∀ s, Rep n (gens s) (gensG s)) (pl : Table)
    (k : ℕ) : TupRep n m (applyTree pl gens k q) (treeElt pl gensG k * g) := by
  obtain ⟨hs, he⟩ := applyTree_spec hgens pl k q (hq.lt hm)
  refine ⟨by rw [hs, hq.1], fun j hj => ?_⟩
  rw [he j (by rw [hq.1]; exact hj), hq.2 j hj, idx_mul]

private theorem TupRep.applyTreeInv {m : ℕ} (hm : m ≤ n) {q : Array ℕ} {g : G} (hq : TupRep n m q g)
    {gensInv : ℕ → Table} {gensG : ℕ → G} (hgens : ∀ s, Rep n (gensInv s) (gensG s)⁻¹)
    (pl : Table) (k : ℕ) :
    TupRep n m (applyTreeInv pl gensInv k q) ((treeElt pl gensG k)⁻¹ * g) := by
  obtain ⟨hs, he⟩ := applyTreeInv_spec hgens pl k q (hq.lt hm)
  refine ⟨by rw [hs, hq.1], fun j hj => ?_⟩
  rw [he j (by rw [hq.1]; exact hj), hq.2 j hj, idx_mul]

private theorem TupRep.fix_of_eq {q : Array ℕ} {g : G} (hq : TupRep n 124 q g)
    (h : (q == tuple0) = true) : ∀ j < 124, idx n g j = j := by
  intro j hj
  rw [beq_iff_eq] at h
  rw [← hq.2 j hj, h, tuple0_spec.2 j hj]

private theorem strip_eq_some {c : Chain} {q q' : Array ℕ} (h : strip c q = some q') :
    ∃ k0 k1, q' = applyTreeInv c.pl1 c.inv1 k1 (applyTreeInv c.pl0 c.inv0 k0 q) := by
  unfold strip at h
  simp only at h
  split_ifs at h
  exact ⟨_, _, (Option.some.inj h).symm⟩

private theorem strip1_eq_some {c : Chain} {q q' : Array ℕ} (h : strip1 c q = some q') :
    ∃ k1, q' = applyTreeInv c.pl1 c.inv1 k1 q := by
  unfold strip1 at h
  simp only at h
  split_ifs at h
  exact ⟨_, (Option.some.inj h).symm⟩

theorem globalTest_spec (hn : 124 ≤ n) {gens gensInv : ℕ → Table} {gG : ℕ → G}
    (hg : ∀ s, Rep n (gens s) (gG s)) (hgi : ∀ s, Rep n (gensInv s) (gG s)⁻¹)
    {c : Chain} {hG lG : ℕ → G} (h0 : ∀ s, Rep n (c.inv0 s) (hG s)⁻¹)
    (h1 : ∀ s, Rep n (c.inv1 s) (lG s)⁻¹) {pl : Table} {s i : ℕ} (hi : i < n)
    (h : globalTest pl gens gensInv c s i = true) :
    ∃ k0 k1, ∀ j < 124,
      idx n ((treeElt c.pl1 lG k1)⁻¹ * (treeElt c.pl0 hG k0)⁻¹ *
        ((treeElt pl gG (idx n (gG s) i))⁻¹ * gG s * treeElt pl gG i)) j = j := by
  have hX : TupRep n 124 (schreierTuple pl gens gensInv s i)
      ((treeElt pl gG (idx n (gG s) i))⁻¹ * gG s * treeElt pl gG i) := by
    have := ((tupRep_tuple0.applyTree hn hg pl i).apT hn (hg s)).applyTreeInv hn hgi pl
      (ap (gens s) i)
    have e : (treeElt pl gG (ap (gens s) i))⁻¹ * (gG s * (treeElt pl gG i * 1)) =
        (treeElt pl gG (idx n (gG s) i))⁻¹ * gG s * treeElt pl gG i := by
      rw [hg s i hi, mul_one, mul_assoc]
    rw [e] at this
    exact this
  unfold globalTest at h
  split at h
  · rename_i q' hq'
    obtain ⟨k0, k1, rfl⟩ := strip_eq_some hq'
    refine ⟨k0, k1, ?_⟩
    have := (hX.applyTreeInv hn h0 c.pl0 k0).applyTreeInv hn h1 c.pl1 k1
    rw [← mul_assoc (treeElt c.pl1 lG k1)⁻¹] at this
    exact this.fix_of_eq h
  · exact absurd h (by simp)

theorem levelOneTest_spec (hn : 124 ≤ n) {pts0 : Table} {c : Chain} {gens : ℕ → Table}
    {hG lG : ℕ → G} (hg : ∀ s, Rep n (gens s) (hG s)) (h0 : ∀ s, Rep n (c.inv0 s) (hG s)⁻¹)
    (h1 : ∀ s, Rep n (c.inv1 s) (lG s)⁻¹) {s k : ℕ} (hk : ap pts0 k < n)
    (h : levelOneTest pts0 c gens s k = true) :
    ∃ k1, ∀ j < 124,
      idx n ((treeElt c.pl1 lG k1)⁻¹ *
        ((treeElt c.pl0 hG (ap c.pos0 (idx n (hG s) (ap pts0 k))))⁻¹ * hG s *
          treeElt c.pl0 hG k)) j = j := by
  have hX := ((tupRep_tuple0.applyTree hn hg c.pl0 k).apT hn (hg s)).applyTreeInv hn h0 c.pl0
    (ap c.pos0 (ap (gens s) (ap pts0 k)))
  have e : (treeElt c.pl0 hG (ap c.pos0 (ap (gens s) (ap pts0 k))))⁻¹ *
      (hG s * (treeElt c.pl0 hG k * 1)) =
      (treeElt c.pl0 hG (ap c.pos0 (idx n (hG s) (ap pts0 k))))⁻¹ * hG s * treeElt c.pl0 hG k := by
    rw [hg s _ hk, mul_one, mul_assoc]
  rw [e] at hX
  unfold levelOneTest at h
  dsimp only at h
  split at h
  · rename_i q' hq'
    obtain ⟨k1, rfl⟩ := strip1_eq_some hq'
    exact ⟨k1, (hX.applyTreeInv hn h1 c.pl1 k1).fix_of_eq h⟩
  · exact absurd h (by simp)

theorem levelTwoTest_spec (hn : 124 ≤ n) {c : Chain} {gens : ℕ → Table} {lG : ℕ → G}
    (hg : ∀ s, Rep n (gens s) (lG s)) (h1 : ∀ s, Rep n (c.inv1 s) (lG s)⁻¹) {s k : ℕ}
    (hk : ap c.pts1 k < n) (h : levelTwoTest c gens s k = true) :
    ∀ j < 124,
      idx n ((treeElt c.pl1 lG (findPt c.pts1 (idx n (lG s) (ap c.pts1 k))))⁻¹ * lG s *
        treeElt c.pl1 lG k) j = j := by
  have hX := ((tupRep_tuple0.applyTree hn hg c.pl1 k).apT hn (hg s)).applyTreeInv hn h1 c.pl1
    (findPt c.pts1 (ap (gens s) (ap c.pts1 k)))
  have e : (treeElt c.pl1 lG (findPt c.pts1 (ap (gens s) (ap c.pts1 k))))⁻¹ *
      (lG s * (treeElt c.pl1 lG k * 1)) =
      (treeElt c.pl1 lG (findPt c.pts1 (idx n (lG s) (ap c.pts1 k))))⁻¹ * lG s *
        treeElt c.pl1 lG k := by
    rw [hg s _ hk, mul_one, mul_assoc]
  rw [e] at hX
  exact hX.fix_of_eq h

theorem compOK_spec {g1 g2 : Table} {x y : G} (h1 : Rep n g1 x) (h2 : Rep n g2 y) {c : Comps}
    (h : compOK n c g1 g2 = true) :
    (∀ p < n, c.labelOf (idx n x p) = c.labelOf p ∧ c.labelOf (idx n y p) = c.labelOf p ∧
      c.labelOf p < c.reps.size) ∧
      ∀ p < n, ∃ h ∈ Subgroup.closure ({x, y} : Set G), idx n h c.reps[c.labelOf p]! = p := by
  have hc : ∀ t < n, ap c.ord t < n ∧ ap c.posOf (ap c.ord t) = t ∧
      c.labelOf (ap g1 t) = c.labelOf t ∧ c.labelOf (ap g2 t) = c.labelOf t ∧
      c.labelOf t < c.reps.size ∧
      (if treeLab (c.opl[t]!).toNat = 0 then c.reps[c.labelOf (ap c.ord t)]! = ap c.ord t
       else treePar (c.opl[t]!).toNat < t ∧
        c.labelOf (ap c.ord (treePar (c.opl[t]!).toNat)) = c.labelOf (ap c.ord t) ∧
        ((treeLab (c.opl[t]!).toNat = 1 ∧
            ap g1 (ap c.ord (treePar (c.opl[t]!).toNat)) = ap c.ord t) ∨
          (treeLab (c.opl[t]!).toNat = 2 ∧
            ap g2 (ap c.ord (treePar (c.opl[t]!).toNat)) = ap c.ord t))) := by
    intro t ht
    have := allIn_eq_true.1 h t (Nat.zero_le _) ht
    simp only [compCheckAt, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    obtain ⟨⟨⟨⟨⟨hp, hpos⟩, hl1⟩, hl2⟩, hrep⟩, htr⟩ := this
    refine ⟨hp, hpos, hl1, hl2, hrep, ?_⟩
    split_ifs at htr ⊢ with hlab
    · simpa using htr
    · simpa [and_assoc] using htr
  refine ⟨fun p hp => ?_, fun p hp => ?_⟩
  · obtain ⟨-, -, hl1, hl2, hrep, -⟩ := hc p hp
    rw [← h1 p hp, ← h2 p hp]
    exact ⟨hl1, hl2, hrep⟩
  ·
    have hconn : ∀ t < n, ∃ h ∈ Subgroup.closure ({x, y} : Set G),
        idx n h c.reps[c.labelOf (ap c.ord t)]! = ap c.ord t := by
      intro t ht
      induction t using Nat.strong_induction_on with
      | _ t ih =>
        obtain ⟨-, -, -, -, -, htr⟩ := hc t ht
        split_ifs at htr with hlab
        · exact ⟨1, Subgroup.one_mem _, by rw [htr, idx_one]⟩
        · obtain ⟨hpar, hlp, hg⟩ := htr
          obtain ⟨h', hh', he⟩ := ih _ hpar (hpar.trans ht)
          have hlt := (hc _ (hpar.trans ht)).1
          rw [hlp] at he
          rcases hg with ⟨-, hg⟩ | ⟨-, hg⟩
          · refine ⟨x * h', Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) hh', ?_⟩
            rw [idx_mul, he, ← h1 _ hlt, hg]
          · refine ⟨y * h', Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) hh', ?_⟩
            rw [idx_mul, he, ← h2 _ hlt, hg]
    let f : Fin n → Fin n := fun t => ⟨ap c.ord t, (hc t t.isLt).1⟩
    have hinj : Function.Injective f := by
      intro t t' htt
      have e := congrArg (fun u : Fin n => ap c.posOf u.val) htt
      simp only [f, (hc t t.isLt).2.1, (hc t' t'.isLt).2.1] at e
      exact Fin.ext e
    obtain ⟨t, ht⟩ := Finite.surjective_of_injective hinj ⟨p, hp⟩
    have htp : ap c.ord t = p := congrArg Fin.val ht
    obtain ⟨h, hh, he⟩ := hconn t t.isLt
    rw [htp] at he
    exact ⟨h, hh, he⟩

private theorem fold_countLabels (k : ℕ) (c : Comps) (m : ℕ) :
    (Nat.fold m (fun p _ acc => acc.modify (c.labelOf p) (· + 1))
        (Array.replicate k 0)).size = k ∧
      ∀ i < k, (Nat.fold m (fun p _ acc => acc.modify (c.labelOf p) (· + 1))
        (Array.replicate k 0))[i]! = ((Finset.range m).filter (fun p => c.labelOf p = i)).card := by
  induction m with
  | zero =>
    refine ⟨by simp, fun i hi => ?_⟩
    rw [Nat.fold_zero, getElem!_pos _ _ (by simpa using hi)]
    simp
  | succ m ih =>
    obtain ⟨hs, he⟩ := ih
    rw [Nat.fold_succ]
    refine ⟨by rw [Array.size_modify, hs], fun i hi => ?_⟩
    rw [getElem!_pos _ _ (by rw [Array.size_modify, hs]; exact hi), Array.getElem_modify,
      Finset.range_add_one, Finset.filter_insert]
    have hcur := he i hi
    rw [getElem!_pos _ _ (by rw [hs]; exact hi)] at hcur
    split_ifs with hm
    · rw [hcur, Finset.card_insert_of_notMem (by simp)]
    · exact hcur

theorem countLabels_spec {k : ℕ} {c : Comps} (_hlab : ∀ p < n, c.labelOf p < k) (i : ℕ)
    (hi : i < k) :
    (countLabels n k c)[i]! = ((Finset.range n).filter (fun p => c.labelOf p = i)).card :=
  (fold_countLabels k c n).2 i hi

end Rep

end CFSG.Sporadic.Th
