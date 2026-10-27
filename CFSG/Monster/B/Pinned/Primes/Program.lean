module

public import Certificates.Data.CFSGNative.MonsterB.Primes
public import CFSG.Monster.B.Pinned.Primes.Extraspecial
public import CFSG.Monster.B.Pinned.Primes.Data
public import CFSG.Monster.B.Intertwiner.ArithSpec
public import CFSG.Monster.B.Max2.Prog
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Monster.B.Pinned

open Bin Primes.Native

section Programs

variable {G : Type*} [Group G]

@[expose] def insStepG (r : ℕ → G) : Ins → ℕ → G
  | .mu i j k => Function.update r k (r i * r j)
  | .iv i k => Function.update r k (r i)⁻¹
  | .pwr e i k => Function.update r k (r i ^ e)

@[expose] def runG (prog : List Ins) (a b : G) : ℕ → G := prog.foldl insStepG (progInit a b)

theorem map_insStepG {H : Type*} [Group H] (f : G →* H) (r : ℕ → G) (ins : Ins) :
    (fun i => f (insStepG r ins i)) = insStepG (fun i => f (r i)) ins := by
  funext i
  cases ins with
  | mu a b k =>
    simp only [insStepG]
    by_cases h : i = k
    · subst h; simp
    · simp [Function.update_of_ne h]
  | iv a k =>
    simp only [insStepG]
    by_cases h : i = k
    · subst h; simp
    · simp [Function.update_of_ne h]
  | pwr e a k =>
    simp only [insStepG]
    by_cases h : i = k
    · subst h; simp
    · simp [Function.update_of_ne h]

theorem map_foldl_insStepG {H : Type*} [Group H] (f : G →* H) :
    ∀ (l : List Ins) (r : ℕ → G) (k : ℕ),
      f (l.foldl insStepG r k) = l.foldl insStepG (fun i => f (r i)) k
  | [], r, k => rfl
  | ins :: l, r, k => by
    rw [List.foldl_cons, List.foldl_cons, map_foldl_insStepG f l, map_insStepG]

theorem map_runG {H : Type*} [Group H] (f : G →* H) (prog : List Ins) (a b : G) (k : ℕ) :
    f (runG prog a b k) = runG prog (f a) (f b) k := by
  unfold runG
  rw [map_foldl_insStepG]
  have e : (fun i => f (progInit a b i)) = progInit (f a) (f b) := by
    funext i
    unfold progInit
    split_ifs <;> simp
  rw [e]

@[expose] def insReads : Ins → List ℕ
  | .mu i j _ => [i, j]
  | .iv i _ => [i]
  | .pwr _ i _ => [i]

@[expose] def insOut : Ins → ℕ
  | .mu _ _ k => k
  | .iv _ k => k
  | .pwr _ _ k => k

@[expose] def initOK : List Ins → List ℕ → Bool
  | [], _ => true
  | ins :: l, S => (insReads ins).all (S.contains ·) && initOK l (insOut ins :: S)

theorem insStepG_congr {r r' : ℕ → G} {S : List ℕ} {ins : Ins}
    (hread : (insReads ins).all (S.contains ·) = true) (h : ∀ i ∈ S, r i = r' i) :
    ∀ i ∈ insOut ins :: S, insStepG r ins i = insStepG r' ins i := by
  have hr : ∀ i ∈ insReads ins, r i = r' i := fun i hi =>
    h i (by simpa using List.all_eq_true.1 hread i hi)
  intro i hi
  cases ins with
  | mu a b k =>
    simp only [insStepG]
    by_cases e : i = k
    · subst e
      rw [Function.update_self, Function.update_self, hr a (by simp [insReads]),
        hr b (by simp [insReads])]
    · rw [Function.update_of_ne e, Function.update_of_ne e]
      exact h i (by simpa [insOut, e] using hi)
  | iv a k =>
    simp only [insStepG]
    by_cases e : i = k
    · subst e
      rw [Function.update_self, Function.update_self, hr a (by simp [insReads])]
    · rw [Function.update_of_ne e, Function.update_of_ne e]
      exact h i (by simpa [insOut, e] using hi)
  | pwr d a k =>
    simp only [insStepG]
    by_cases e : i = k
    · subst e
      rw [Function.update_self, Function.update_self, hr a (by simp [insReads])]
    · rw [Function.update_of_ne e, Function.update_of_ne e]
      exact h i (by simpa [insOut, e] using hi)

theorem foldl_insStepG_congr :
    ∀ (l : List Ins) (S : List ℕ) (r r' : ℕ → G), initOK l S = true → (∀ i ∈ S, r i = r' i) →
      ∀ k ∈ S, l.foldl insStepG r k = l.foldl insStepG r' k
  | [], _, _, _, _, h => h
  | ins :: l, S, r, r', hok, h => by
    simp only [initOK, Bool.and_eq_true] at hok
    intro k hk
    rw [List.foldl_cons, List.foldl_cons]
    exact foldl_insStepG_congr l (insOut ins :: S) _ _ hok.2 (insStepG_congr hok.1 h) k
      (List.mem_cons_of_mem _ hk)

theorem runG_of_initOK {prog : List Ins} (hok : initOK prog [1, 2] = true) {a b : G}
    (r : ℕ → G) (h1 : r 1 = a) (h2 : r 2 = b) :
    prog.foldl insStepG r 1 = runG prog a b 1 ∧ prog.foldl insStepG r 2 = runG prog a b 2 := by
  have h : ∀ i ∈ [1, 2], r i = progInit a b i := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · rw [h1]; rfl
    · rw [h2]; rfl
  exact ⟨foldl_insStepG_congr prog [1, 2] r _ hok h 1 (by simp),
    foldl_insStepG_congr prog [1, 2] r _ hok h 2 (by simp)⟩

end Programs

@[expose] def wordG {M : Type*} [Monoid M] (a b : M) (w : List Char) : M :=
  (w.map fun c => if c = 'a' then a else if c = 'b' then b else 1).prod

theorem wordG_append {M : Type*} [Monoid M] (a b : M) (v w : List Char) :
    wordG a b (v ++ w) = wordG a b v * wordG a b w := by
  simp [wordG, List.prod_append]

theorem map_wordG {M N : Type*} [Monoid M] [Monoid N] (f : M →* N) (a b : M) (w : List Char) :
    f (wordG a b w) = wordG (f a) (f b) w := by
  simp only [wordG, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro c _
  simp only [Function.comp_apply]
  split_ifs <;> simp

section RepMonoid

variable {M : Type*} [Monoid M] {n : ℕ} (f : M →* Matrix (Fin n) (Fin n) (ZMod 2))

@[expose] def Rep (X : Mat) (g : M) : Prop := X.size ≤ n ∧ cmat n X = f g

variable {f}

theorem Rep.of_eq {X : Mat} {g g' : M} (h : Rep f X g) (e : g = g') : Rep f X g' := e ▸ h

theorem rep_mul {X Y : Mat} {g h : M} (hX : Rep f X g) (hY : Rep f Y h) :
    Rep f (mulP n X Y) (g * h) :=
  ⟨by rw [mulP_size]; exact hX.1, by rw [cmat_mulP _ _ _ hY.1, hX.2, hY.2, map_mul]⟩

theorem rep_pow {X : Mat} {g : M} (hX : Rep f X g) (e : ℕ) : Rep f (powM n X e) (g ^ e) :=
  ⟨powM_size hX.1 e, by rw [cmat_powM hX.1, hX.2, map_pow]⟩

theorem rep_one : Rep f (idMat n) (1 : M) := ⟨(idMat_size n).le, by rw [cmat_idMat, map_one]⟩

theorem eq_of_rep (hf : Function.Injective f) {X Y : Mat} {g h : M} (hX : Rep f X g)
    (hY : Rep f Y h) (he : (X == Y) = true) : g = h :=
  hf (hX.2.symm.trans ((cmat_eq_of_beq he).trans hY.2))

theorem ne_one_of_rep {X : Mat} {g : M} (hX : Rep f X g) (h : neM n X (idMat n) = true) :
    g ≠ 1 := by
  intro hg
  apply cmat_ne_of_neM h
  rw [hX.2, hg, map_one, cmat_idMat]

theorem rep_wordFrom {A B : Mat} {a b : M} (hA : Rep f A a) (hB : Rep f B b) :
    ∀ (w : List Char) {X : Mat} {g : M}, Rep f X g → Rep f (wordFrom n A B X w) (g * wordG a b w)
  | [], X, g, hX => by simpa [wordFrom, wordG] using hX
  | c :: w, X, g, hX => by
    rw [wordFrom]
    have e : g * wordG a b (c :: w) =
        (g * if c = 'a' then a else if c = 'b' then b else 1) * wordG a b w := by
      simp [wordG, mul_assoc]
    rw [e]
    apply rep_wordFrom hA hB w
    split_ifs
    · exact rep_mul hX hA
    · exact rep_mul hX hB
    · simpa using hX

theorem ordOK_spec (hf : Function.Injective f) {p : ℕ} {X : Mat} {g : M} (hX : Rep f X g)
    (h : ordOK n p X = true) : g ^ p = 1 ∧ g ≠ 1 := by
  simp only [ordOK, Bool.and_eq_true] at h
  exact ⟨eq_of_rep hf (rep_pow hX p) rep_one h.1, ne_one_of_rep hX h.2⟩

theorem ordExactOK_spec (hf : Function.Injective f) {e : ℕ} {rs : List ℕ} {X : Mat} {g : M}
    (hX : Rep f X g) (h : ordExactOK n e rs X = true) :
    g ^ e = 1 ∧ ∀ r ∈ rs, g ^ (e / r) ≠ 1 := by
  simp only [ordExactOK, Bool.and_eq_true, List.all_eq_true] at h
  exact ⟨eq_of_rep hf (rep_pow hX e) rep_one h.1,
    fun r hr => ne_one_of_rep (rep_pow hX (e / r)) (h.2 r hr)⟩

theorem orderOf_eq_of_exact {g : M} {e : ℕ} {rs : List ℕ} (he : 0 < e) (h1 : g ^ e = 1)
    (h2 : ∀ r ∈ rs, g ^ (e / r) ≠ 1) (hcov : ∀ r ≤ e, r.Prime → r ∣ e → r ∈ rs) :
    orderOf g = e :=
  orderOf_eq_of_pow_and_pow_div_prime he h1 fun r hr hre =>
    h2 r (hcov r (Nat.le_of_dvd he hre) hr hre)

theorem rep_powTable {p : ℕ} {X : Mat} {g : M} (hX : Rep f X g) {e : ℕ} (he : e < p) :
    Rep f ((powTable n p X).getD e #[]) (g ^ e) := by
  rw [powTable, List.getD_eq_getElem _ _ (by simpa using he), List.getElem_map,
    List.getElem_range]
  exact rep_pow hX e

theorem rep_prodPows {p : ℕ} :
    ∀ (T : List (List Mat)) (qs : List M) (es : List ℕ), T.length = qs.length →
      es.length = qs.length →
      (∀ j < qs.length, ∀ e < p, Rep f ((T.getD j []).getD e #[]) (qs.getD j 1 ^ e)) →
      (∀ e ∈ es, e < p) → Rep f (prodPows n T es) (List.zipWith (· ^ ·) qs es).prod
  | [], [], [], _, _, _, _ => by simpa [prodPows] using rep_one
  | T :: Ts, q :: qs, e :: es, hT, he, h, hes => by
    have hT' : Ts.length = qs.length := by simpa using hT
    have he' : es.length = qs.length := by simpa using he
    have h' : ∀ j < qs.length, ∀ e < p, Rep f ((Ts.getD j []).getD e #[]) (qs.getD j 1 ^ e) :=
      fun j hj e he => by simpa using h (j + 1) (by simpa using hj) e he
    have ih := rep_prodPows Ts qs es hT' he' h' (fun e' he' => hes e' (List.mem_cons_of_mem _ he'))
    rw [prodPows, List.zipWith_cons_cons, List.prod_cons]
    split_ifs with h0
    · subst h0; simpa using ih
    · have hq := h 0 (by simp) e (hes e (List.mem_cons_self ..))
      simp only [List.getD_cons_zero] at hq
      exact rep_mul hq ih
  | [], _ :: _, _, hT, _, _, _ => absurd hT (by simp)
  | _ :: _, [], _, hT, _, _, _ => absurd hT (by simp)
  | [], [], _ :: _, _, he, _, _ => absurd he (by simp)
  | _ :: _, _ :: _, [], _, he, _, _ => absurd he (by simp)

theorem rep_mulTab {p : ℕ} {P zN : Mat} {g z : M} (hP : Rep f P g) (hz : Rep f zN z) {c : ℕ}
    (hc : c < p) : Rep f (mulTab n P (powTable n p zN) c) (g * z ^ c) := by
  unfold mulTab
  split_ifs with h0
  · subst h0; simpa using hP
  · exact rep_mul hP (rep_powTable hz hc)

theorem zipWith_ofFn {k : ℕ} (q : Fin k → M) (l : List ℕ) (hl : l.length = k) :
    List.zipWith (· ^ ·) (List.ofFn q) l = List.ofFn fun j => q j ^ l.getD j 0 := by
  apply List.ext_getElem (by simp [hl])
  intro i h1 h2
  simp only [List.getElem_zipWith, List.getElem_ofFn]
  rw [List.getD_eq_getElem _ _ (by simpa [hl] using h2)]

end RepMonoid

section RepGroup

variable {G : Type*} [Group G] {n : ℕ} {f : G →* Matrix (Fin n) (Fin n) (ZMod 2)}

theorem rep_inv {X Y : Mat} {g : G} (hX : Rep f X g) (hY : Y.size ≤ n)
    (h : (mulP n X Y == idMat n) = true) : Rep f Y g⁻¹ := by
  refine ⟨hY, ?_⟩
  have e := cmat_eq_of_beq (n := n) h
  rw [cmat_mulP _ _ _ hY, cmat_idMat, hX.2] at e
  calc cmat n Y = f (g⁻¹ * g) * cmat n Y := by rw [inv_mul_cancel, map_one, one_mul]
    _ = f g⁻¹ * (f g * cmat n Y) := by rw [map_mul, mul_assoc]
    _ = f g⁻¹ := by rw [e, mul_one]

theorem regStep_flag (ins : List Ins) :
    ∀ R : Array Mat, (ins.foldl (regStep n) (R, false)).2 = false := by
  induction ins with
  | nil => intro R; rfl
  | cons ins l ih =>
    intro R
    rw [List.foldl_cons]
    cases ins with
    | mu i j k => exact ih _
    | iv i k => simpa [regStep] using ih _
    | pwr e i k => exact ih _

theorem getD_set!_self (R : Array Mat) {k : ℕ} (v : Mat) (hk : k < R.size) :
    (R.set! k v).getD k #[] = v := by
  rw [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  simp [hk]

theorem getD_set!_ne (R : Array Mat) {k i : ℕ} (v : Mat) (h : k ≠ i) :
    (R.set! k v).getD i #[] = R.getD i #[] := by
  rw [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  simp [h, Array.getD_eq_getD_getElem?]

theorem foldl_regStep (N : ℕ) :
    ∀ (l : List Ins) (R : Array Mat) (b : Bool) (r : ℕ → G),
      (∀ ins ∈ l, ins.lt N = true) → R.size = N → (∀ i < N, Rep f (R.getD i #[]) (r i)) →
      (l.foldl (regStep n) (R, b)).2 = true →
      (l.foldl (regStep n) (R, b)).1.size = N ∧
        ∀ i < N, Rep f ((l.foldl (regStep n) (R, b)).1.getD i #[]) (l.foldl insStepG r i)
  | [], R, b, r, _, hR, h, _ => ⟨hR, h⟩
  | ins :: l, R, b, r, hl, hR, h, hflag => by
    rw [List.foldl_cons] at hflag ⊢
    rw [List.foldl_cons]
    have hins := hl ins (List.mem_cons_self ..)
    have hl' : ∀ ins' ∈ l, ins'.lt N = true := fun ins' h' => hl ins' (List.mem_cons_of_mem _ h')
    cases ins with
    | mu i j k =>
      simp only [Ins.lt, Bool.and_eq_true, decide_eq_true_eq] at hins
      obtain ⟨⟨hi, hj⟩, hk⟩ := hins
      refine foldl_regStep N l _ _ _ hl' (by simp [hR]) ?_ hflag
      intro i' hi'
      simp only [insStepG]
      by_cases e : k = i'
      · subst e
        rw [getD_set!_self _ _ (hR ▸ hk), Function.update_self]
        exact rep_mul (h i hi) (h j hj)
      · rw [getD_set!_ne _ _ e, Function.update_of_ne (Ne.symm e)]
        exact h i' hi'
    | iv i k =>
      simp only [Ins.lt, Bool.and_eq_true, decide_eq_true_eq] at hins
      obtain ⟨hi, hk⟩ := hins
      have hchk : (mulP n (R.getD i #[]) (invM n (R.getD i #[])) == idMat n) = true := by
        by_contra hc
        rw [Bool.not_eq_true] at hc
        simp only [regStep, hc, Bool.and_false] at hflag
        rw [regStep_flag] at hflag
        exact absurd hflag (by simp)
      have hb : b = true := by
        by_contra hc
        rw [Bool.not_eq_true] at hc
        simp only [regStep, hc, Bool.false_and] at hflag
        rw [regStep_flag] at hflag
        exact absurd hflag (by simp)
      refine foldl_regStep N l _ _ _ hl' (by simp [hR]) ?_ hflag
      intro i' hi'
      simp only [insStepG]
      by_cases e : k = i'
      · subst e
        rw [getD_set!_self _ _ (hR ▸ hk), Function.update_self]
        exact rep_inv (h i hi) (invM_size n _).le hchk
      · rw [getD_set!_ne _ _ e, Function.update_of_ne (Ne.symm e)]
        exact h i' hi'
    | pwr e i k =>
      simp only [Ins.lt, Bool.and_eq_true, decide_eq_true_eq] at hins
      obtain ⟨hi, hk⟩ := hins
      refine foldl_regStep N l _ _ _ hl' (by simp [hR]) ?_ hflag
      intro i' hi'
      simp only [insStepG]
      by_cases e' : k = i'
      · subst e'
        rw [getD_set!_self _ _ (hR ▸ hk), Function.update_self]
        exact rep_pow (h i hi) e
      · rw [getD_set!_ne _ _ e', Function.update_of_ne (Ne.symm e')]
        exact h i' hi'

theorem regRun_rep (N : ℕ) (prog : List Ins) (hprog : ∀ ins ∈ prog, ins.lt N = true)
    {A B : Mat} {a b : G} (hA : Rep f A a) (hB : Rep f B b)
    (hflag : (regRun n N prog A B).2 = true) :
    ∀ i < N, Rep f ((regRun n N prog A B).1.getD i #[]) (runG prog a b i) := by
  refine (foldl_regStep N prog _ true _ hprog (by simp [regsInit]) ?_ hflag).2
  intro i hi
  have e : (regsInit n N A B).getD i #[] =
      if i = 1 then A else if i = 2 then B else idMat n := by
    simp [regsInit, Array.getD_eq_getD_getElem?, hi]
  rw [e]
  unfold progInit
  split_ifs
  · exact hA
  · exact hB
  · exact rep_one

theorem commDataOK_spec (hf : Function.Injective f) {p k : ℕ} (hp : 0 < p) {qsN : List Mat}
    {q : Fin k → G} (hlen : qsN.length = k) (hq : ∀ i : Fin k, Rep f (qsN.getD i #[]) (q i))
    {zN : Mat} {z : G} (hz : Rep f zN z) {Mr : List (List ℕ)}
    (hM : ∀ i j : Fin k, (Mr.getD i []).getD j 0 < p)
    (h : commDataOK n p qsN zN (powTable n p zN) Mr = true) :
    (∀ i, q i ^ p = 1 ∧ q i ≠ 1) ∧ z ^ p = 1 ∧ z ≠ 1 ∧ (∀ i, q i * z = z * q i) ∧
      ∀ i j : Fin k, i < j → bcomm (q i) (q j) = z ^ ((Mr.getD i []).getD j 0) := by
  simp only [commDataOK, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨hord, hzord⟩, hcomm⟩, hpairs⟩ := h
  have hmem : ∀ i : Fin k, qsN.getD i #[] ∈ qsN := fun i => by
    rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact i.2)]
    exact List.getElem_mem _
  have hqp : ∀ i, q i ^ p = 1 ∧ q i ≠ 1 := fun i => ordOK_spec hf (hq i) (hord _ (hmem i))
  have hzp := ordOK_spec hf hz hzord
  refine ⟨hqp, hzp.1, hzp.2, fun i => ?_, fun i j hij => ?_⟩
  · have := hcomm _ (hmem i)
    exact eq_of_rep hf (rep_mul (hq i) hz) (rep_mul hz (hq i)) this
  · have hinv : ∀ i : Fin k, Rep f ((qsN.map (powM n · (p - 1))).getD i #[]) (q i)⁻¹ := by
      intro i
      rw [List.getD_eq_getElem _ _ (by simp [hlen]), List.getElem_map]
      rw [← List.getD_eq_getElem _ #[] (by rw [hlen]; exact i.2)]
      have e : q i ^ (p - 1) = (q i)⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, ← pow_succ, Nat.sub_add_cancel hp, (hqp i).1]
      rw [← e]
      exact rep_pow (hq i) _
    have hpair := hpairs i (by rw [List.mem_range, hlen]; exact i.2) j
      (by rw [List.mem_range, hlen]; exact j.2)
    simp only [Fin.lt_def] at hij
    simp only [hij, decide_true, Bool.not_true, Bool.false_or] at hpair
    exact eq_of_rep hf (rep_mul (rep_mul (rep_mul (hinv i) (hinv j)) (hq i)) (hq j))
      (rep_powTable hz (hM i j)) hpair

theorem actOK_spec (hf : Function.Injective f) {p k : ℕ} {qsN : List Mat} {q : Fin k → G}
    (hlen : qsN.length = k) (hq : ∀ i : Fin k, Rep f (qsN.getD i #[]) (q i)) {zN : Mat} {z : G}
    (hz : Rep f zN z) {bN biN : Mat} {b : G} (hb : Rep f bN b) (hbi : Rep f biN b⁻¹)
    {R : List (List ℕ)} {c : List ℕ} (hRl : ∀ i : Fin k, (R.getD i []).length = k)
    (hR : ∀ i j : Fin k, (R.getD i []).getD j 0 < p) (hc : ∀ i : Fin k, c.getD i 0 < p)
    (h : actOK n qsN (qsN.map (powTable n p)) (powTable n p zN) bN biN R c = true) :
    ∀ i : Fin k, b⁻¹ * q i * b =
      (List.ofFn fun j => q j ^ (R.getD i []).getD j 0).prod * z ^ c.getD i 0 := by
  intro i
  simp only [actOK, List.all_eq_true] at h
  have hi := h i (by rw [List.mem_range, hlen]; exact i.2)
  have hprod : Rep f (prodPows n (qsN.map (powTable n p)) (R.getD i []))
      (List.zipWith (· ^ ·) (List.ofFn q) (R.getD i [])).prod := by
    refine rep_prodPows (p := p) _ _ _ (by simp [hlen]) (by rw [List.length_ofFn]; exact hRl i)
      ?_ ?_
    · intro j hj e he
      have hj' : j < k := by simpa using hj
      have hjq : j < qsN.length := hlen ▸ hj'
      have e1 : (qsN.map (powTable n p)).getD j [] = powTable n p (qsN.getD j #[]) := by
        rw [List.getD_eq_getElem _ _ (by simpa using hjq), List.getElem_map,
          List.getD_eq_getElem _ _ hjq]
      have e2 : (List.ofFn q).getD j 1 = q ⟨j, hj'⟩ := by
        rw [List.getD_eq_getElem _ _ (by simpa using hj'), List.getElem_ofFn]
      rw [e1, e2]
      exact rep_powTable (hq ⟨j, hj'⟩) he
    · intro e he
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
      have hj' : j < k := by rw [← hRl i]; exact hj
      have := hR i ⟨j, hj'⟩
      rwa [List.getD_eq_getElem _ _ hj] at this
  have hlhs := rep_mul (rep_mul hbi (hq i)) hb
  have e := eq_of_rep hf hlhs (rep_mulTab hprod hz (hc i)) hi
  rw [e, zipWith_ofFn q _ (hRl i)]

end RepGroup

theorem rowsMat_val {p k : ℕ} [NeZero p] {Mr : List (List ℕ)} {i j : Fin k}
    (h : (Mr.getD i []).getD j 0 < p) : (rowsMat p k Mr i j).val = (Mr.getD i []).getD j 0 := by
  rw [rowsMat, Matrix.of_apply, ZMod.val_natCast, Nat.mod_eq_of_lt h]

theorem bcomm_all {G : Type*} [Group G] {p k : ℕ} [NeZero p] {q : Fin k → G} {z : G}
    (hz : z ^ p = 1)
    {Mr : List (List ℕ)} (hlt : ∀ i j : Fin k, (Mr.getD i []).getD j 0 < p)
    (hdiag : ∀ i : Fin k, (Mr.getD i []).getD i 0 = 0)
    (hanti : ∀ i j : Fin k, ((Mr.getD i []).getD j 0 + (Mr.getD j []).getD i 0) % p = 0)
    (h : ∀ i j : Fin k, i < j → bcomm (q i) (q j) = z ^ ((Mr.getD i []).getD j 0)) :
    ∀ i j, bcomm (q i) (q j) = z ^ (rowsMat p k Mr i j).val := by
  intro i j
  rw [rowsMat_val (hlt i j)]
  rcases lt_trichotomy i j with hij | rfl | hij
  · exact h i j hij
  · rw [hdiag, pow_zero, bcomm_eq_one_iff]
  · rw [bcomm_swap (q j) (q i), h j i hij, eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_add]
    obtain ⟨t, ht⟩ := Nat.dvd_of_mod_eq_zero (hanti i j)
    rw [ht, pow_mul, hz, one_pow]

end CFSG.Monster.B.Pinned
