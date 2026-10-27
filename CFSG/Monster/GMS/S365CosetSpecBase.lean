
module

public import CFSG.Monster.GMS.Leech.Linear
public import CFSG.Monster.GMS.S365Native
public import CFSG.Monster.GMS.S365Facts
public import Certificates.Data.CFSGNative.Co1.S365CentPath
public import CFSG.Monster.GMS.S365CosetInputs

@[expose] public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

namespace S365

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.Module
  CFSG.Sporadic.Co1.Module.Pairs CFSG.Sporadic.Co1.S365Native CFSG.Sporadic.Co1.InvNative
  CFSG.Sporadic.Co1.S365CentNative

@[expose] def InK (x y κ : Fin 24 → ZMod 2) : Prop := κ = 0 ∨ κ = x ∨ κ = y ∨ κ = x + y

theorem vec_add_add_left (u v : Fin 24 → ZMod 2) : u + (u + v) = v := by
  rw [← add_assoc, vec_add_self, zero_add]

theorem vec_add_add_right (u v : Fin 24 → ZMod 2) : u + v + v = u := by
  rw [add_assoc, vec_add_self, add_zero]

theorem InK.add {x y a b : Fin 24 → ZMod 2} (ha : InK x y a) (hb : InK x y b) :
    InK x y (a + b) := by
  unfold InK at *
  rcases ha with h | h | h | h <;> rcases hb with h' | h' | h' | h' <;> rw [h, h']
  · left; rw [add_zero]
  · right; left; rw [zero_add]
  · right; right; left; rw [zero_add]
  · right; right; right; rw [zero_add]
  · right; left; rw [add_zero]
  · left; exact vec_add_self _
  · right; right; right; rfl
  · right; right; left; exact vec_add_add_left _ _
  · right; right; left; rw [add_zero]
  · right; right; right; rw [add_comm]
  · left; exact vec_add_self _
  · right; left; rw [add_comm x y, vec_add_add_left]
  · right; right; right; rw [add_zero]
  · right; right; left; rw [add_comm x y, vec_add_add_right]
  · right; left; exact vec_add_add_right _ _
  · left; exact vec_add_self _

theorem InK.smul {x y κ : Fin 24 → ZMod 2} {g : Co1} (hx : g • x = x)
    (hy : g • y = y) (h : InK x y κ) : InK x y (g • κ) := by
  unfold InK at *
  rcases h with rfl | rfl | rfl | rfl
  · left; exact smul_zero g
  · right; left; exact hx
  · right; right; left; exact hy
  · right; right; right; rw [smul_add, hx, hy]

@[expose] def CosetEq (x y u w : Fin 24 → ZMod 2) : Prop := InK x y (u + w)

theorem CosetEq.refl (x y w : Fin 24 → ZMod 2) : CosetEq x y w w := by
  unfold CosetEq InK
  left
  exact vec_add_self w

theorem CosetEq.symm {x y u w : Fin 24 → ZMod 2} (h : CosetEq x y u w) : CosetEq x y w u := by
  unfold CosetEq at *
  rw [add_comm]
  exact h

theorem CosetEq.trans {x y u w z : Fin 24 → ZMod 2} (h : CosetEq x y u w) (h' : CosetEq x y w z) :
    CosetEq x y u z := by
  unfold CosetEq at *
  have : u + z = (u + w) + (w + z) := by rw [add_assoc, vec_add_add_left]
  rw [this]
  exact h.add h'

theorem CosetEq.smul {x y u w : Fin 24 → ZMod 2} {g : Co1} (hx : g • x = x)
    (hy : g • y = y) (h : CosetEq x y u w) : CosetEq x y (g • u) (g • w) := by
  unfold CosetEq at *
  rw [← smul_add]
  exact h.smul hx hy

theorem InK.map {x y κ : Fin 24 → ZMod 2} (g : Co1) (h : InK x y κ) :
    InK (g • x) (g • y) (g • κ) := by
  unfold InK at *
  rcases h with rfl | rfl | rfl | rfl
  · left; exact smul_zero g
  · right; left; rfl
  · right; right; left; rfl
  · right; right; right; rw [smul_add]

theorem CosetEq.map {x y u w : Fin 24 → ZMod 2} (g : Co1) (h : CosetEq x y u w) :
    CosetEq (g • x) (g • y) (g • u) (g • w) := by
  unfold CosetEq at *
  rw [← smul_add]
  exact h.map g

theorem CosetEq.add_klein {x y w κ : Fin 24 → ZMod 2} (h : InK x y κ) : CosetEq x y (w + κ) w := by
  unfold CosetEq
  rw [add_comm w κ, vec_add_add_right]
  exact h

theorem CosetEq.cases {x y u w : Fin 24 → ZMod 2} (h : CosetEq x y u w) :
    u = w ∨ u = w + x ∨ u = w + y ∨ u = w + x + y := by
  have key : ∀ κ, u + w = κ → u = w + κ := by
    intro κ hκ
    rw [← hκ, add_comm u w, ← add_assoc, vec_add_self, zero_add]
  unfold CosetEq InK at h
  rcases h with h | h | h | h
  · left
    have := key _ h
    rwa [add_zero] at this
  · right; left; exact key _ h
  · right; right; left; exact key _ h
  · right; right; right
    have := key _ h
    rwa [← add_assoc] at this

theorem canon4_cases (x y v : ℕ) :
    canon4 x y v = v ∨ canon4 x y v = v ^^^ x ∨ canon4 x y v = v ^^^ y ∨
      canon4 x y v = v ^^^ x ^^^ y := by
  unfold canon4
  rcases min_choice (min v (v ^^^ x)) (min (v ^^^ y) (v ^^^ x ^^^ y)) with h3 | h3
  · rw [h3]
    rcases min_choice v (v ^^^ x) with h1 | h1
    · left; exact h1
    · right; left; exact h1
  · rw [h3]
    rcases min_choice (v ^^^ y) (v ^^^ x ^^^ y) with h2 | h2
    · right; right; left; exact h2
    · right; right; right; exact h2

theorem coset_canon4 (x y v : ℕ) :
    CosetEq (toVecD 24 x) (toVecD 24 y) (toVecD 24 (canon4 x y v)) (toVecD 24 v) := by
  unfold CosetEq InK
  rcases canon4_cases x y v with h | h | h | h <;> rw [h]
  · left; exact vec_add_self _
  · right; left
    rw [toVecD_xor, add_comm (toVecD 24 v) (toVecD 24 x), vec_add_add_right]
  · right; right; left
    rw [toVecD_xor, add_comm (toVecD 24 v) (toVecD 24 y), vec_add_add_right]
  · right; right; right
    rw [toVecD_xor, toVecD_xor, add_assoc (toVecD 24 v) (toVecD 24 x) (toVecD 24 y),
      add_comm (toVecD 24 v) (toVecD 24 x + toVecD 24 y), vec_add_add_right]

theorem xorK_cancel (v k : ℕ) : v ^^^ k ^^^ k = v := by
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem canon4_xor_two (v : ℕ) : canon4 2 4 (v ^^^ 2) = canon4 2 4 v := by
  unfold canon4
  rw [xorK_cancel]
  omega

theorem canon4_xor_four (v : ℕ) : canon4 2 4 (v ^^^ 4) = canon4 2 4 v := by
  unfold canon4
  have e1 : v ^^^ 4 ^^^ 2 = v ^^^ 2 ^^^ 4 := by
    rw [Nat.xor_assoc, Nat.xor_comm 4 2, ← Nat.xor_assoc]
  rw [xorK_cancel, e1, xorK_cancel]
  omega

theorem canon4_xor {v k : ℕ} (hk : k = 0 ∨ k = 2 ∨ k = 4 ∨ k = 6) :
    canon4 2 4 (v ^^^ k) = canon4 2 4 v := by
  rcases hk with rfl | rfl | rfl | rfl
  · rw [Nat.xor_zero]
  · exact canon4_xor_two v
  · exact canon4_xor_four v
  · rw [show (6 : ℕ) = 2 ^^^ 4 by decide, ← Nat.xor_assoc, canon4_xor_four, canon4_xor_two]

theorem canon4_idem (v : ℕ) : canon4 2 4 (canon4 2 4 v) = canon4 2 4 v := by
  have key : ∀ k, (k = 0 ∨ k = 2 ∨ k = 4 ∨ k = 6) → canon4 2 4 v = v ^^^ k →
      canon4 2 4 (canon4 2 4 v) = canon4 2 4 v := by
    intro k hk h
    rw [h, canon4_xor hk]
    exact h
  rcases canon4_cases 2 4 v with h | h | h | h
  · exact key 0 (Or.inl rfl) (by rw [Nat.xor_zero]; exact h)
  · exact key 2 (Or.inr (Or.inl rfl)) h
  · exact key 4 (Or.inr (Or.inr (Or.inl rfl))) h
  · exact key 6 (Or.inr (Or.inr (Or.inr rfl))) (by rw [h, Nat.xor_assoc]; rfl)

theorem canon4_le (v : ℕ) : canon4 2 4 v ≤ v :=
  (min_le_left _ _).trans (min_le_left _ _)

theorem inK_of_mem {k : ℕ} (hk : k = 0 ∨ k = 2 ∨ k = 4 ∨ k = 6) :
    InK (toVecD 24 2) (toVecD 24 4) (toVecD 24 k) := by
  rcases hk with rfl | rfl | rfl | rfl
  · left; exact toVecD_zero 24
  · right; left; rfl
  · right; right; left; rfl
  · right; right; right
    rw [show (6 : ℕ) = 2 ^^^ 4 by decide, toVecD_xor]

@[expose] def canonPatSet (P : ℕ → Bool) (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter fun r => P r = true ∧ canon4 2 4 r = r

theorem mem_canonPatSet (P : ℕ → Bool) (n r : ℕ) :
    r ∈ canonPatSet P n ↔ r < n ∧ P r = true ∧ canon4 2 4 r = r := by
  unfold canonPatSet
  rw [Finset.mem_filter, Finset.mem_range]

theorem card_canonPatSet_le (P : ℕ → Bool) (n : ℕ)
    (hP : ∀ c k, (k = 0 ∨ k = 2 ∨ k = 4 ∨ k = 6) → c < n → P c = true →
      c ^^^ k < n ∧ P (c ^^^ k) = true) :
    (canonPatSet P n).card * 4 ≤ ((Finset.range n).filter fun r => P r = true).card := by
  have hKm : ∀ k ∈ ({0, 2, 4, 6} : Finset ℕ), k = 0 ∨ k = 2 ∨ k = 4 ∨ k = 6 := by
    intro k hk
    simpa using hk
  have hK4 : ({0, 2, 4, 6} : Finset ℕ).card = 4 := by decide
  rw [← hK4, ← Finset.card_product]
  refine Finset.card_le_card_of_injOn (fun p => p.1 ^^^ p.2) ?_ ?_
  · intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.1 (Finset.mem_coe.1 hp)
    obtain ⟨hc, hpc, -⟩ := (mem_canonPatSet P n p.1).1 hp1
    obtain ⟨hlt, hpk⟩ := hP p.1 p.2 (hKm _ hp2) hc hpc
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    exact ⟨hlt, hpk⟩
  · intro p hp q hq e
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.1 (Finset.mem_coe.1 hp)
    obtain ⟨hq1, hq2⟩ := Finset.mem_product.1 (Finset.mem_coe.1 hq)
    have ep := ((mem_canonPatSet P n p.1).1 hp1).2.2
    have eq := ((mem_canonPatSet P n q.1).1 hq1).2.2
    have e' : p.1 ^^^ p.2 = q.1 ^^^ q.2 := e
    have h1 : p.1 = q.1 := by
      have := congrArg (canon4 2 4) e'
      rwa [canon4_xor (hKm _ hp2), canon4_xor (hKm _ hq2), ep, eq] at this
    have h2 : p.2 = q.2 := by
      have := congrArg (fun t => p.1 ^^^ t) e'
      simp only [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] at this
      rw [this, h1, Nat.xor_self, Nat.zero_xor]
    exact Prod.ext h1 h2

theorem treeCheckK_spec {Mts : Array (Array ℕ)} {x y : ℕ} {L par lab : Array ℕ}
    (h : treeCheckK Mts x y L par lab = true) :
    0 < L.size ∧ ∀ k < L.size, k = 0 ∨ (par[k]! < k ∧ lab[k]! < Mts.size ∧
      L[k]! = canon4 x y (vecMulN 24 Mts[lab[k]!]! L[par[k]!]!)) := by
  unfold treeCheckK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, beq_iff_eq] at h
  refine ⟨h.1, fun k hk => ?_⟩
  rcases h.2 k hk with h0 | ⟨⟨h1, h2⟩, h3⟩
  · exact Or.inl h0
  · exact Or.inr ⟨h1, h2, h3⟩

theorem tyLabN_eq (pts : Array ℕ) (pos : Array UInt32) (n w : ℕ) :
    tyLabN qRows pts pos n w = tyLab pts pos n w := rfl

theorem exists_cosetElems :
    ∃ gl : ℕ → Co1, ∀ l < cosetRowsT.size, ∀ u,
    gl l • toVecD 24 u = toVecD 24 (vecMulN 24 cosetRowsT[l]! u) := by
  have hmem : ∀ l < cosetRowsT.size, ∃ w : List Bool,
      cosetRowsT[l]! = transposeRows 24 (wordRows w) := by
    intro l hl
    have hm : cosetRowsT[l]! ∈ cosetRowsT := by
      rw [getElem!_pos cosetRowsT l hl]
      exact Array.getElem_mem hl
    simp only [cosetRowsT, List.mem_toArray, List.mem_map] at hm
    obtain ⟨s, -, hs⟩ := hm
    exact ⟨invWord s, hs.symm⟩
  have hex : ∀ l : ℕ, ∃ g : Co1, l < cosetRowsT.size → ∀ u,
      g • toVecD 24 u = toVecD 24 (vecMulN 24 cosetRowsT[l]! u) := by
    intro l
    by_cases hl : l < cosetRowsT.size
    · obtain ⟨w, hw⟩ := hmem l hl
      obtain ⟨g, hg⟩ := exists_co1_wordMat w
      refine ⟨g, fun _ u => ?_⟩
      have hg' : (g.val.val : Matrix (Fin 24) (Fin 24) (ZMod 2)) = rowsMatrix 24 (wordRows w) :=
        hg.trans (rowsMatrix_wordRows w).symm
      rw [hw]
      exact act_packed g (wordRows w) hg' u
    · exact ⟨1, fun h => absurd h hl⟩
  choose gl hgl using hex
  exact ⟨gl, fun l hl => hgl l hl⟩

@[expose] def pathElem (gl : ℕ → Co1) : List ℕ → Co1
  | [] => 1
  | l :: p => pathElem gl p * gl l

theorem pathElem_smul {gl : ℕ → Co1}
    (hgl : ∀ l < cosetRowsT.size, ∀ u, gl l • toVecD 24 u =
      toVecD 24 (vecMulN 24 cosetRowsT[l]! u)) :
    ∀ (path : List ℕ), (∀ l ∈ path, l < cosetRowsT.size) → ∀ u : ℕ,
      pathElem gl path • toVecD 24 u = toVecD 24 (applyPath cosetRowsT path u) := by
  intro path
  induction path with
  | nil => intro _ u; rw [pathElem, one_smul]; rfl
  | cons l p ih =>
    intro hp u
    rw [pathElem, mul_smul, hgl l (hp l (List.mem_cons_self ..)) u]
    exact ih (fun l' hl' => hp l' (List.mem_cons_of_mem _ hl')) _

theorem pathElem_fix {gl : ℕ → Co1} {v : Fin 24 → ZMod 2}
    (hfix : ∀ l < cosetRowsT.size, gl l • v = v) :
    ∀ (path : List ℕ), (∀ l ∈ path, l < cosetRowsT.size) → pathElem gl path • v = v := by
  intro path
  induction path with
  | nil => intro _; rw [pathElem, one_smul]
  | cons l p ih =>
    intro hp
    rw [pathElem, mul_smul, hfix l (hp l (List.mem_cons_self ..))]
    exact ih (fun l' hl' => hp l' (List.mem_cons_of_mem _ hl'))

@[expose] def PatSet (a b : Fin 24 → ZMod 2) : Set (Fin 24 → ZMod 2) :=
  {v | v ∈ co1Orbit 2 ∧ v + a ∈ co1Orbit 2 ∧ v + b ∈ co1Orbit 2 ∧ v + a + b ∈ co1Orbit 2}

theorem PatSet.map {a b t : Fin 24 → ZMod 2} (g : Co1) (ht : t ∈ PatSet a b) :
    g • t ∈ PatSet (g • a) (g • b) := by
  obtain ⟨h1, h2, h3, h4⟩ := ht
  have m : ∀ {u : Fin 24 → ZMod 2}, u ∈ co1Orbit 2 → g • u ∈ co1Orbit 2 :=
    fun hu => Leech.co1Act_mem_co1Orbit hu g
  refine ⟨m h1, ?_, ?_, ?_⟩
  · rw [← smul_add]; exact m h2
  · rw [← smul_add]; exact m h3
  · rw [← smul_add, ← smul_add]; exact m h4

theorem PatSet.smul_mem {a b t : Fin 24 → ZMod 2} {g : Co1} (ha : g • a = a) (hb : g • b = b)
    (ht : t ∈ PatSet a b) : g • t ∈ PatSet a b := by
  have := PatSet.map g ht
  rwa [ha, hb] at this

theorem PatSet.add_klein {x y v κ : Fin 24 → ZMod 2} (hκ : InK x y κ) (hv : v ∈ PatSet x y) :
    v + κ ∈ PatSet x y := by
  obtain ⟨h1, h2, h3, h4⟩ := hv
  unfold InK at hκ
  rcases hκ with h | h | h | h <;> rw [h]
  · rw [add_zero]
    exact ⟨h1, h2, h3, h4⟩
  · refine ⟨h2, ?_, h4, ?_⟩
    · rw [add_assoc, vec_add_self, add_zero]; exact h1
    · rw [add_assoc v x x, vec_add_self, add_zero]; exact h3
  · refine ⟨h3, ?_, ?_, ?_⟩
    · rw [add_right_comm]; exact h4
    · rw [add_assoc, vec_add_self, add_zero]; exact h1
    · rw [add_right_comm v y x, add_assoc (v + x) y y, vec_add_self, add_zero]; exact h2
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← add_assoc]; exact h4
    · rw [← add_assoc, add_right_comm, add_assoc v x x, vec_add_self, add_zero]; exact h3
    · rw [← add_assoc, add_assoc (v + x) y y, vec_add_self, add_zero]; exact h2
    · rw [← add_assoc, add_right_comm (v + x) y x, add_assoc v x x, vec_add_self, add_zero,
        add_assoc v y y, vec_add_self, add_zero]
      exact h1

theorem lbl_one_iff
    {w : ℕ} (hw : w < 2 ^ 24) :
    tyLab (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 w = 1 ↔
      toVecD 24 w ∈ co1Orbit 2 := by
  rw [co1Orbit_two, orbit_Co1_eq]
  exact tyLab_spec w hw 1 (by norm_num)

theorem pat4_iff
    {x : ℕ} (hx : x < 2 ^ 24) :
    pat4 qRows (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 2 4 x = true ↔
      toVecD 24 x ∈ PatSet (toVecD 24 2) (toVecD 24 4) := by
  unfold pat4 PatSet
  simp only [Bool.and_eq_true, beq_iff_eq, tyLabN_eq, Set.mem_ofPred_eq]
  rw [lbl_one_iff hx, lbl_one_iff (Nat.xor_lt_two_pow hx (by norm_num)),
    lbl_one_iff (Nat.xor_lt_two_pow hx (by norm_num)),
    lbl_one_iff (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow hx (by norm_num)) (by norm_num)),
    toVecD_xor, toVecD_xor, toVecD_xor, toVecD_xor]
  tauto

theorem refPair :
    toVecD 24 2 ∈ co1Orbit 0 ∧ toVecD 24 4 ∈ co1Orbit 0 ∧
    toVecD 24 2 + toVecD 24 4 ∈ co1Orbit 0 := by
  have h := eightCheck_ok
  simp only [eightCheck, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  obtain ⟨h2, h4, h6, -⟩ := h
  refine ⟨mem_co1Orbit_zero_of_lbl (by norm_num) h2, mem_co1Orbit_zero_of_lbl (by norm_num) h4, ?_⟩
  have := mem_co1Orbit_zero_of_lbl (w := 6) (by norm_num) h6
  rw [show (6 : ℕ) = 2 ^^^ 4 by decide, toVecD_xor] at this
  exact this

theorem FourPattern.map {a b ω : Fin 24 → ZMod 2} (g : Co1) (h : FourPattern a b ω) :
    FourPattern (g • a) (g • b) (g • ω) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have m0 : ∀ {u : Fin 24 → ZMod 2}, u ∈ co1Orbit 0 → g • u ∈ co1Orbit 0 :=
    fun hu => Leech.co1Act_mem_co1Orbit hu g
  have m2 : ∀ {u : Fin 24 → ZMod 2}, u ∈ co1Orbit 2 → g • u ∈ co1Orbit 2 :=
    fun hu => Leech.co1Act_mem_co1Orbit hu g
  refine ⟨m0 h1, m0 h2, ?_, m2 h4, ?_, ?_, ?_⟩
  · rw [← smul_add]; exact m0 h3
  · rw [← smul_add]; exact m2 h5
  · rw [← smul_add]; exact m2 h6
  · rw [← smul_add, ← smul_add]; exact m2 h7

end S365

end CFSG.Monster.GMS
