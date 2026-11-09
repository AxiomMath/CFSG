module

public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCharDataE8

public section

namespace CertificateChecks.KernelDirect.C13691

open CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.Blueprint.Chevalley

variable {τ : Tag}

def packL256 (l : List ℕ) : ℕ :=
  List.rec 0 (fun a _ acc => a + acc <<< 256) l

theorem getD_eq_packL256 : ∀ (l : List ℕ), (∀ y ∈ l, y < 2 ^ 256) →
    ∀ k, l.getD k 0 = packL256 l >>> (256 * k) % 2 ^ 256
  | [], _, k => by simp [packL256]
  | a :: l, h, k => by
    have ha := h a (by simp)
    have e : packL256 (a :: l) = a + packL256 l * 2 ^ 256 := by
      change a + packL256 l <<< 256 = _
      rw [Nat.shiftLeft_eq]
    rw [Nat.shiftRight_eq_div_pow, e]
    rcases k with _ | k
    · simp only [List.getD_cons_zero, Nat.mul_zero, pow_zero, Nat.div_one]
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha]
    · rw [List.getD_cons_succ, getD_eq_packL256 l (fun y hy => h y (by simp [hy])) k,
        Nat.shiftRight_eq_div_pow, Nat.mul_add, Nat.mul_one, pow_add, Nat.mul_comm (2 ^ (256 * k)),
        ← Nat.div_div_eq_div_mul, Nat.add_mul_div_right _ _ (by positivity),
        Nat.div_eq_of_lt ha, Nat.zero_add]

def getR3 (l : List ℕ) : ℕ → ℕ :=
  List.rec (fun _ => 0) (fun a _ ih k => if k = 0 then a else ih (k - 1)) l

theorem getR3_eq : ∀ (l : List ℕ) (k : ℕ), getR3 l k = l.getD k 0
  | [], _ => rfl
  | a :: l, k => by
    change (if k = 0 then a else getR3 l (k - 1)) = _
    rcases k with _ | k
    · rfl
    · simp [getR3_eq l k]

def chunksP : ℕ → List ℕ → List ℕ
  | 0, _ => []
  | f + 1, l => packL256 (l.take 81) :: chunksP f (l.drop 81)

def lookP (Q : List ℕ) (m : ℕ) : ℕ := getR3 Q (m / 81) >>> (256 * (m % 81)) % 2 ^ 256

theorem getD_eq_lookP : ∀ (f : ℕ) (l : List ℕ), (∀ y ∈ l, y < 2 ^ 256) → l.length ≤ 81 * f →
    ∀ m, l.getD m 0 = lookP (chunksP f l) m
  | 0, l, _, hl, m => by
    obtain rfl : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp [lookP, chunksP, getR3_eq]
  | f + 1, l, h, hl, m => by
    unfold lookP
    rw [getR3_eq]
    by_cases hm : m < 81
    · rw [Nat.div_eq_of_lt hm, Nat.mod_eq_of_lt hm, chunksP, List.getD_cons_zero,
        ← getD_eq_packL256 _ (fun y hy => h y (List.mem_of_mem_take hy))]
      simp [List.getD_eq_getElem?_getD, hm]
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 81 := ⟨m - 81, by omega⟩
      rw [Nat.add_div_right _ (by norm_num), Nat.add_mod_right, chunksP, List.getD_cons_succ]
      have := getD_eq_lookP f (l.drop 81) (fun y hy => h y (List.mem_of_mem_drop hy))
        (by simp; omega) k
      unfold lookP at this
      rw [getR3_eq] at this
      rw [← this]
      simp [List.getD_eq_getElem?_getD, Nat.add_comm k]

def digR3 : ℕ → ℕ → List ℕ
  | 0, _ => []
  | r + 1, n => n % 3 :: digR3 r (n / 3)

theorem digits3_eq_digR3 : ∀ (r n : ℕ), (List.range r).map (fun j => n / 3 ^ j % 3) = digR3 r n
  | 0, _ => rfl
  | r + 1, n => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, digR3, ← digits3_eq_digR3 r (n / 3)]
    congr 1
    · simp
    · refine List.map_congr_left fun j _ => ?_
      simp [Function.comp, pow_succ', Nat.div_div_eq_div_mul]

def reflIdx3 : List ℕ → ℕ → ℕ → ℕ
  | [], _, _ => 0
  | c :: cs, x, n => (n % 3 + c * x) % 3 + 3 * reflIdx3 cs x (n / 3)

theorem digR3_reflIdx3 (x : ℕ) : ∀ (row : List ℕ) (n : ℕ),
    digR3 row.length (reflIdx3 row x n) = reflAux x (digR3 row.length n) row
  | [], _ => rfl
  | c :: cs, n => by
    simp only [List.length_cons, digR3, reflIdx3, reflAux, List.zipWith_cons_cons]
    have h := digR3_reflIdx3 x cs (n / 3)
    simp only [reflAux] at h
    rw [← h]
    have ha : (n % 3 + c * x) % 3 < 3 := Nat.mod_lt _ (by norm_num)
    generalize (n % 3 + c * x) % 3 = a at ha ⊢
    congr 2 <;> omega

theorem reflAux_getD3 (x : ℕ) : ∀ (b row : List ℕ) (k : ℕ), k < b.length → k < row.length →
    (reflAux x b row).getD k 0 = (b.getD k 0 + row.getD k 0 * x) % 3
  | [], _, _, hk, _ => absurd hk (by simp)
  | _ :: _, [], _, _, hk => absurd hk (by simp)
  | v :: b, c :: row, 0, _, _ => by simp [reflAux]
  | v :: b, c :: row, k + 1, hb, hr => by
    have := reflAux_getD3 x b row k (by simpa using hb) (by simpa using hr)
    simp only [reflAux] at this
    simpa [reflAux] using this

theorem reflAux_twice3 {x : ℕ} (hx : x < 3) : ∀ (b row : List ℕ), (∀ v ∈ b, v < 3) →
    (∀ c ∈ row, c < 3) → b.length = row.length →
    reflAux ((x + x) % 3) (reflAux x b row) row = b
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => absurd h (by simp)
  | _ :: _, [], _, _, h => absurd h (by simp)
  | v :: b, c :: row, hb, hc, h => by
    have key : ∀ v < 3, ∀ c < 3, ∀ x < 3, ((v + c * x) % 3 + c * ((x + x) % 3)) % 3 = v := by
      decide
    have ih := reflAux_twice3 hx b row (fun y hy => hb y (by simp [hy]))
      (fun y hy => hc y (by simp [hy])) (by simpa using h)
    simp only [reflAux, List.zipWith_cons_cons] at ih ⊢
    rw [ih, key v (hb v (by simp)) c (hc c (by simp)) x hx]

theorem reflL_twice3 {rows : List (List ℕ)} {i : ℕ} {b : List ℕ}
    (hl : (rows.getD i []).length = b.length) (hi : i < b.length)
    (h3 : ∀ c ∈ rows.getD i [], c < 3) (hb : ∀ v ∈ b, v < 3) (h1 : (rows.getD i []).getD i 0 = 1) :
    reflL rows i (reflL rows i b) = b := by
  have hx : b.getD i 0 < 3 := by
    rw [List.getD_eq_getElem _ _ hi]
    exact hb _ (List.getElem_mem hi)
  have hy : (reflAux (b.getD i 0) b (rows.getD i [])).getD i 0 = (b.getD i 0 + b.getD i 0) % 3 := by
    rw [reflAux_getD3 _ _ _ _ hi (by omega), h1, Nat.one_mul]
  unfold reflL
  rw [hy]
  exact reflAux_twice3 hx _ _ hb h3 hl.symm

def rowsOk3 (τ : Tag) (rows : List (List ℕ)) : Bool :=
  (List.range τ.rank).all fun i =>
    ((rows.getD i []).length == τ.rank) && (rows.getD i []).all (fun c => decide (c < 3)) &&
      ((rows.getD i []).getD i 0 == 1)

theorem rowsOk3_spec {rows : List (List ℕ)} (h : rowsOk3 τ rows = true) {i : ℕ} (hi : i < τ.rank) :
    (rows.getD i []).length = τ.rank ∧ (∀ c ∈ rows.getD i [], c < 3) ∧
      (rows.getD i []).getD i 0 = 1 := by
  simp only [rowsOk3, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  exact ⟨(h i hi).1.1, (h i hi).1.2, (h i hi).2⟩

def treeStep3 (τ : Tag) (rows : List (List ℕ)) (reps : List (List ℕ)) (Q : List ℕ) (N n e : ℕ) :
    Bool :=
  decide (e < 2 ^ 256) &&
  if e / 8 = 0 then decide (e % 8 < reps.length) && (reps.getD (e % 8) [] == digits3 τ n)
  else
    decide (0 < e / 8 % 9) && decide (e / 8 % 9 - 1 < τ.rank) && decide (e / 8 < 9 ^ 128) &&
      decide (reflIdx3 (rows.getD (e / 8 % 9 - 1) []) (n / 3 ^ (e / 8 % 9 - 1) % 3) n < N) &&
      (lookP Q (reflIdx3 (rows.getD (e / 8 % 9 - 1) []) (n / 3 ^ (e / 8 % 9 - 1) % 3) n) ==
        e % 8 + 8 * (e / 8 / 9))

def treeAux3 (τ : Tag) (rows : List (List ℕ)) (reps : List (List ℕ)) (Q : List ℕ) (N : ℕ) :
    ℕ → List ℕ → Bool
  | _, [] => true
  | n, e :: es => treeStep3 τ rows reps Q N n e && treeAux3 τ rows reps Q N (n + 1) es

def treeCheck3 (τ : Tag) (reps : List (List ℕ)) (E : List ℕ) : Bool :=
  decide (E.length = 3 ^ τ.rank) && reps.all (fun b => decide (b.length = τ.rank)) &&
    decide (3 ^ τ.rank ≤ 81 * 81) && rowsOk3 τ (negCartanRows τ) && treeAux3 τ (negCartanRows τ) reps (chunksP 81 E) (3 ^ τ.rank) 0 E

theorem decodeWord9_stable : ∀ f q, q < 9 ^ f → decodeWord9 (f + 1) q = decodeWord9 f q
  | 0, q, h => by
    obtain rfl : q = 0 := by simpa using h
    rfl
  | f + 1, q, h => by
    change (if q = 0 then [] else (q % 9 - 1) :: decodeWord9 (f + 1) (q / 9)) =
      (if q = 0 then [] else (q % 9 - 1) :: decodeWord9 f (q / 9))
    rw [decodeWord9_stable f (q / 9) (by rw [pow_succ] at h; omega)]

theorem treeAux3_spec {rows reps : List (List ℕ)} {P : List ℕ} {N : ℕ} :
    ∀ (es : List ℕ) (m : ℕ), treeAux3 τ rows reps P N m es = true →
      ∀ k < es.length, treeStep3 τ rows reps P N (m + k) (es.getD k 0) = true
  | [], _, _, k, hk => absurd hk (by simp)
  | e :: es, m, h, k, hk => by
    simp only [treeAux3, Bool.and_eq_true] at h
    rcases k with _ | k
    · simpa using h.1
    · have := treeAux3_spec es (m + 1) h.2 k (by simpa using hk)
      simpa [Nat.add_assoc, Nat.add_comm 1 k] using this

def orbitCond3 (τ : Tag) (reps : List (List ℕ)) (e n : ℕ) : Prop :=
  entryRep e < reps.length ∧ (∀ i ∈ entryWord e, i < τ.rank) ∧
    actL (negCartanRows τ) (entryWord e) (reps.getD (entryRep e) []) = digits3 τ n

theorem orbitAux3_of_cond {reps : List (List ℕ)} :
    ∀ (es : List ℕ) (m : ℕ), (∀ k < es.length, orbitCond3 τ reps (es.getD k 0) (m + k)) →
      orbitAux3 τ (negCartanRows τ) reps m es = true
  | [], _, _ => rfl
  | e :: es, m, h => by
    obtain ⟨h1, h2, h3⟩ := h 0 (by simp)
    simp only [orbitAux3, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true]
    refine ⟨⟨⟨h1, h2⟩, by simpa using h3⟩, orbitAux3_of_cond es (m + 1) fun k hk => ?_⟩
    have := h (k + 1) (by simpa using hk)
    simpa [Nat.add_assoc, Nat.add_comm 1 k] using this

theorem orbitCond3_of_treeAux3 {reps : List (List ℕ)} {E : List ℕ}
    (hE : E.length ≤ 81 * 81) (hrows : rowsOk3 τ (negCartanRows τ) = true)
    (h : treeAux3 τ (negCartanRows τ) reps (chunksP 81 E) E.length 0 E = true) :
    ∀ L n, n < E.length → (entryWord (E.getD n 0)).length = L → orbitCond3 τ reps (E.getD n 0) n := by
  have hbd : ∀ y ∈ E, y < 2 ^ 256 := by
    intro y hy
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy
    have hs := treeAux3_spec E 0 h k hk
    rw [List.getD_eq_getElem _ _ hk] at hs
    unfold treeStep3 at hs
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
    exact hs.1
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
  intro n hn hL
  have hs := treeAux3_spec E 0 h n hn
  rw [Nat.zero_add] at hs
  generalize E.getD n 0 = e at hs hL ⊢
  unfold treeStep3 at hs
  rw [Bool.and_eq_true] at hs
  replace hs := hs.2
  split_ifs at hs with hq
  · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hs
    have hw : entryWord e = [] := by
      simp only [entryWord, hq]
      rfl
    refine ⟨hs.1, by simp [hw], ?_⟩
    rw [hw]
    exact hs.2
  · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
      ← getD_eq_lookP 81 E hbd hE] at hs
    obtain ⟨⟨⟨⟨h0, hi⟩, hb⟩, hm⟩, hc⟩ := hs
    set i := e / 8 % 9 - 1
    set m := reflIdx3 ((negCartanRows τ).getD i []) (n / 3 ^ i % 3) n
    obtain ⟨hl, h3, h1⟩ := rowsOk3_spec hrows hi
    have hd : ∀ k, digits3 τ k = digR3 τ.rank k := fun k => digits3_eq_digR3 _ _
    have hdi : (digits3 τ n).getD i 0 = n / 3 ^ i % 3 := getD_range_map' _ _ hi
    have hdm : digits3 τ m = reflL (negCartanRows τ) i (digits3 τ n) := by
      rw [reflL, hdi, hd, hd, ← hl]
      exact digR3_reflIdx3 _ _ _
    have hr : reflL (negCartanRows τ) i (digits3 τ m) = digits3 τ n := by
      rw [hdm]
      refine reflL_twice3 (by rw [hl, length_digits3]) (by rw [length_digits3]; exact hi) h3 ?_ h1
      intro v hv
      simp only [digits3, List.mem_map] at hv
      obtain ⟨j, _, rfl⟩ := hv
      exact Nat.mod_lt _ (by norm_num)
    have hcw : entryWord (e % 8 + 8 * (e / 8 / 9)) = decodeWord9 128 (e / 8 / 9) := by
      simp only [entryWord]
      congr 1
      omega
    have hcr : entryRep (e % 8 + 8 * (e / 8 / 9)) = e % 8 := by
      simp only [entryRep]
      omega
    have hw : entryWord e = i :: entryWord (e % 8 + 8 * (e / 8 / 9)) := by
      have hst := decodeWord9_stable 127 (e / 8 / 9)
        ((Nat.div_lt_iff_lt_mul (by norm_num)).2 (by rw [← pow_succ]; exact hb))
      rw [hcw]
      change _ = i :: decodeWord9 (127 + 1) (e / 8 / 9)
      rw [hst]
      change (if e / 8 = 0 then [] else (e / 8 % 9 - 1) :: decodeWord9 127 (e / 8 / 9)) = _
      simp only [hq, ↓reduceIte]
      rfl
    have := ih (entryWord (e % 8 + 8 * (e / 8 / 9))).length (by rw [← hL, hw]; simp) m hm
      (by rw [hc])
    obtain ⟨c1, c2, c3⟩ := this
    rw [hc] at c1 c2 c3
    rw [hcr] at c1 c3
    have her : entryRep e = e % 8 := rfl
    refine ⟨her ▸ c1, ?_, ?_⟩
    · rw [hw]
      intro j hj
      rcases List.mem_cons.1 hj with rfl | hj
      · exact hi
      · exact c2 j hj
    · rw [hw, her]
      change reflL (negCartanRows τ) i (actL (negCartanRows τ) _ _) = _
      rw [c3, hr]

theorem orbitCheck3_of_treeCheck3 {reps : List (List ℕ)} {E : List ℕ}
    (h : treeCheck3 τ reps E = true) : orbitCheck3 τ reps E = true := by
  simp only [treeCheck3, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hlen, hreps⟩, h81⟩, hrows⟩, ht⟩ := h
  simp only [orbitCheck3, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨hlen, hreps⟩, orbitAux3_of_cond E 0 fun k hk => ?_⟩
  rw [Nat.zero_add]
  rw [← hlen] at ht h81
  exact orbitCond3_of_treeAux3 h81 hrows ht _ k hk rfl

set_option maxRecDepth 100000 in
theorem e8ThreeTree_ok : treeCheck3 .E8 e8ThreeReps e8ThreeOrbit = true := by
  decide +kernel

theorem e8ThreeOrbit_ok : orbitCheck3 .E8 e8ThreeReps e8ThreeOrbit = true :=
  orbitCheck3_of_treeCheck3 e8ThreeTree_ok

end CertificateChecks.KernelDirect.C13691
