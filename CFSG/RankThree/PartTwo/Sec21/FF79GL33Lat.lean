module

public import CFSG.RankThree.PartTwo.Sec21.FF79GL33Code

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.GL33

@[expose] def TabLt (T : Array ℕ) : Prop := ∀ i : ℕ, T[i]! < 27

theorem ofFn_get!_lt {n : ℕ} (f : Fin n → ℕ) (hf : ∀ k, f k < 27) (i : ℕ) :
    (Array.ofFn f)[i]! < 27 := by
  by_cases h : i < n
  · rw [ofFn_get! f i h]; exact hf _
  · have hs : ¬ i < (Array.ofFn f).size := by rw [Array.size_ofFn]; exact h
    rw [getElem!_neg (Array.ofFn f) i hs]
    decide

theorem tabLt_vmTab : TabLt (vmTab ()) := by
  intro i
  unfold vmTab
  exact ofFn_get!_lt _ (fun k => vmRaw_lt _ _) i

theorem mulc_lt' {T : Array ℕ} (hT : TabLt T) (a b : ℕ) : mulc T a b < N := by
  have h0 := hT ((a % 27) * 19683 + b)
  have h1 := hT ((a / 27 % 27) * 19683 + b)
  have h2 := hT ((a / 729 % 27) * 19683 + b)
  unfold mulc act N
  omega

@[expose] def Struct (st : Array ℕ × Array Bool) : Prop :=
  st.2.size = N ∧ (∀ c ∈ st.1, c < N ∧ st.2[c]! = true) ∧
    (∀ c : ℕ, st.2[c]! = true → c ∈ st.1) ∧ st.1.toList.Nodup

@[expose] def MemIn (Xc : Set ℕ) (st : Array ℕ × Array Bool) : Prop := ∀ c ∈ st.1, c ∈ Xc

@[expose] def stepF (T : Array ℕ) (x : ℕ) (st : Array ℕ × Array Bool) (g : ℕ) :
    Array ℕ × Array Bool :=
  if st.2[mulc T x g]! then st else (st.1.push (mulc T x g), st.2.set! (mulc T x g) true)

theorem stepF_struct {T : Array ℕ} (hT : TabLt T) (x g : ℕ) {st : Array ℕ × Array Bool}
    (h : Struct st) : Struct (stepF T x st g) := by
  obtain ⟨hsz, hel, hbit, hnd⟩ := h
  unfold stepF
  by_cases hb : st.2[mulc T x g]! = true
  · simp only [hb, if_true]; exact ⟨hsz, hel, hbit, hnd⟩
  · have hbf : st.2[mulc T x g]! = false := by simpa using hb
    simp only [hbf]
    set c := mulc T x g with hc
    have hcN : c < N := mulc_lt' hT x g
    have hcs : c < st.2.size := by rw [hsz]; exact hcN
    simp only [Bool.false_eq_true, if_false]
    refine ⟨by simpa using hsz, ?_, ?_, ?_⟩
    · intro d hd
      rw [Array.mem_push] at hd
      rcases hd with hd | rfl
      · obtain ⟨h1, h2⟩ := hel d hd
        refine ⟨h1, ?_⟩
        by_cases hcd : c = d
        · subst hcd; exact Array.getElem!_set!_self _ _ _ hcs
        · rw [Array.getElem!_set!_ne _ _ _ _ hcd]; exact h2
      · exact ⟨hcN, Array.getElem!_set!_self _ _ _ hcs⟩
    · intro d hd
      rw [Array.mem_push]
      by_cases hcd : c = d
      · exact Or.inr hcd.symm
      · rw [Array.getElem!_set!_ne _ _ _ _ hcd] at hd
        exact Or.inl (hbit d hd)
    · simp only [Array.toList_push]
      rw [List.nodup_append]
      refine ⟨hnd, List.nodup_singleton _, ?_⟩
      intro a ha b hb' hab
      simp only [List.mem_singleton] at hb'
      have := (hel a (Array.mem_toList_iff.mp ha)).2
      rw [hab, hb'] at this
      exact hb this

theorem stepF_mem {T : Array ℕ} {Xc : Set ℕ}
    (hmul : ∀ a b, a ∈ Xc → b ∈ Xc → mulc T a b ∈ Xc) {x g : ℕ} (hx : x ∈ Xc) (hg : g ∈ Xc)
    {st : Array ℕ × Array Bool} (h : MemIn Xc st) : MemIn Xc (stepF T x st g) := by
  unfold stepF
  by_cases hb : st.2[mulc T x g]! = true
  · simp only [hb, if_true]; exact h
  · simp only [hb, Bool.false_eq_true, if_false]
    intro d hd
    rw [Array.mem_push] at hd
    rcases hd with hd | rfl
    · exact h d hd
    · exact hmul x g hx hg

theorem foldl_step {T : Array ℕ} (hT : TabLt T) {Xc : Set ℕ}
    (hmul : ∀ a b, a ∈ Xc → b ∈ Xc → mulc T a b ∈ Xc) {x : ℕ} (hx : x ∈ Xc) :
    ∀ (gs : List ℕ), (∀ g ∈ gs, g ∈ Xc) → ∀ st : Array ℕ × Array Bool, Struct st →
      MemIn Xc st → Struct (gs.foldl (stepF T x) st) ∧ MemIn Xc (gs.foldl (stepF T x) st) := by
  intro gs
  induction gs with
  | nil => intro _ st h1 h2; exact ⟨h1, h2⟩
  | cons g gs ih =>
    intro hgs st h1 h2
    exact ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) _
      (stepF_struct hT x g h1) (stepF_mem hmul hx (hgs g (List.mem_cons_self ..)) h2)

theorem expand_eq (T : Array ℕ) (gens : List ℕ) (x : ℕ) (st : Array ℕ × Array Bool) :
    expand T gens x st = gens.foldl (stepF T x) st := rfl

theorem bfsLoop_spec {T : Array ℕ} (hT : TabLt T) {Xc : Set ℕ}
    (hmul : ∀ a b, a ∈ Xc → b ∈ Xc → mulc T a b ∈ Xc) {gens : List ℕ}
    (hg : ∀ g ∈ gens, g ∈ Xc) :
    ∀ (fuel i : ℕ) (st : Array ℕ × Array Bool), Struct st → MemIn Xc st →
      Struct (bfsLoop T gens fuel i st) ∧ MemIn Xc (bfsLoop T gens fuel i st) := by
  intro fuel
  induction fuel with
  | zero => intro i st h1 h2; exact ⟨h1, h2⟩
  | succ fuel ih =>
    intro i st h1 h2
    unfold bfsLoop
    by_cases hi : i < st.1.size
    · rw [dif_pos hi]
      have hx : st.1[i] ∈ Xc := h2 _ (Array.getElem_mem hi)
      obtain ⟨a, b⟩ := foldl_step hT hmul hx gens hg st h1 h2
      exact ih _ _ (by rw [expand_eq]; exact a) (by rw [expand_eq]; exact b)
    · rw [dif_neg hi]; exact ⟨h1, h2⟩

theorem replicate_false_get (n i : ℕ) : (Array.replicate n false)[i]! = false := by
  by_cases hcs : i < (Array.replicate n false).size
  · rw [getElem!_pos (Array.replicate n false) i hcs]; simp
  · rw [getElem!_neg (Array.replicate n false) i hcs]; rfl

theorem bfs_spec {T : Array ℕ} (hT : TabLt T) {Xc : Set ℕ} (hone : oneC ∈ Xc)
    (hmul : ∀ a b, a ∈ Xc → b ∈ Xc → mulc T a b ∈ Xc) {gens : List ℕ}
    (hg : ∀ g ∈ gens, g ∈ Xc) : Struct (bfs T gens) ∧ MemIn Xc (bfs T gens) := by
  unfold bfs
  have hA := replicate_false_get 19683
  have hAs : (Array.replicate 19683 false).size = 19683 := Array.size_replicate ..
  generalize Array.replicate 19683 false = A at hA hAs
  have hone' : oneC < 19683 := by unfold oneC; omega
  have hs : oneC < A.size := by rw [hAs]; exact hone'
  refine bfsLoop_spec hT hmul hg _ _ _ ?_ ?_
  · refine ⟨by rw [Array.size_set!, hAs]; rfl, ?_, ?_, by simp⟩
    · intro c hc
      simp only [Array.mem_singleton] at hc
      subst hc
      exact ⟨hone', Array.getElem!_set!_self _ _ _ hs⟩
    · intro c hc
      by_cases hcd : oneC = c
      · simp [hcd]
      · rw [Array.getElem!_set!_ne _ _ _ _ hcd, hA] at hc
        exact absurd hc (by simp)
  · intro c hc
    simp only [Array.mem_singleton] at hc
    subst hc
    exact hone

theorem bfs_struct {T : Array ℕ} (hT : TabLt T) (gens : List ℕ) : Struct (bfs T gens) :=
  (bfs_spec hT (Xc := Set.univ) trivial (fun _ _ _ _ => trivial) (fun _ _ => trivial)).1

theorem minMul_aux (T : Array ℕ) (x : ℕ) (l : List ℕ) :
    ∀ b : ℕ, l.foldl (fun b s => min b (mulc T s x)) b ≤ b ∧
      (l.foldl (fun b s => min b (mulc T s x)) b = b ∨
        ∃ s ∈ l, l.foldl (fun b s => min b (mulc T s x)) b = mulc T s x) := by
  induction l with
  | nil => intro b; exact ⟨le_refl _, Or.inl rfl⟩
  | cons y l ih =>
    intro b
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih (min b (mulc T y x))
    refine ⟨h1.trans (min_le_left _ _), ?_⟩
    rcases h2 with h2 | ⟨s, hs, h2⟩
    · rcases min_choice b (mulc T y x) with h3 | h3
      · exact Or.inl (h2.trans h3)
      · exact Or.inr ⟨y, List.mem_cons_self .., h2.trans h3⟩
    · exact Or.inr ⟨s, List.mem_cons_of_mem _ hs, h2⟩

theorem minMul_le (T : Array ℕ) (es : Array ℕ) (x : ℕ) : minMul T es x ≤ x := by
  unfold minMul
  rw [← Array.foldl_toList]
  exact (minMul_aux T x es.toList x).1

theorem minMul_cases (T : Array ℕ) (es : Array ℕ) (x : ℕ) :
    minMul T es x = x ∨ ∃ s ∈ es, minMul T es x = mulc T s x := by
  unfold minMul
  rw [← Array.foldl_toList]
  rcases (minMul_aux T x es.toList x).2 with h | ⟨s, hs, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨s, Array.mem_toList_iff.mp hs, h⟩

theorem set!_true_get (mk : Array Bool) (j i : ℕ) (h : mk[i]! = true) :
    (mk.set! j true)[i]! = true := by
  by_cases hji : j = i
  · subst hji
    by_cases hs : j < mk.size
    · exact Array.getElem!_set!_self _ _ _ hs
    · exfalso
      rw [getElem!_neg mk j hs] at h
      exact absurd h (by decide)
  · rw [Array.getElem!_set!_ne _ _ _ _ hji]; exact h

theorem foldl_mark (m : ℕ → ℕ) (hm : ∀ x, m x ≤ x) (seen : Array Bool) :
    ∀ (L : List ℕ) (mk : Array Bool), mk.size = N → (∀ x ∈ L, x < N) →
      (L.foldl (fun mk x => if seen[x]! then mk else mk.set! (m x) true) mk).size = N ∧
      (∀ i : ℕ, mk[i]! = true →
        (L.foldl (fun mk x => if seen[x]! then mk else mk.set! (m x) true) mk)[i]! = true) ∧
      ∀ x ∈ L, seen[x]! = false →
        (L.foldl (fun mk x => if seen[x]! then mk else mk.set! (m x) true) mk)[m x]! = true := by
  intro L
  induction L with
  | nil => intro mk hsz _; exact ⟨hsz, fun i h => h, fun x hx => absurd hx (by simp)⟩
  | cons y L ih =>
    intro mk hsz hL
    simp only [List.foldl_cons]
    have hy := hL y (List.mem_cons_self ..)
    have hL' : ∀ x ∈ L, x < N := fun x hx => hL x (List.mem_cons_of_mem _ hx)
    by_cases hs : seen[y]! = true
    · simp only [hs, if_true]
      obtain ⟨a, b, c⟩ := ih mk hsz hL'
      refine ⟨a, b, ?_⟩
      intro x hx hxs
      rcases List.mem_cons.mp hx with rfl | hx
      · rw [hs] at hxs; exact absurd hxs (by simp)
      · exact c x hx hxs
    · have hsf : seen[y]! = false := by simpa using hs
      simp only [hs, Bool.false_eq_true, if_false]
      have hsz' : (mk.set! (m y) true).size = N := by rw [Array.size_set!]; exact hsz
      obtain ⟨a, b, c⟩ := ih (mk.set! (m y) true) hsz' hL'
      refine ⟨a, fun i hi => b i (set!_true_get mk _ i hi), ?_⟩
      intro x hx hxs
      rcases List.mem_cons.mp hx with rfl | hx
      · apply b
        have : m x < mk.size := by rw [hsz]; exact lt_of_le_of_lt (hm x) hy
        exact Array.getElem!_set!_self _ _ _ this
      · exact c x hx hxs

theorem repsOf_lt {T : Array ℕ} {U es : Array ℕ} {seen : Array Bool} {g : ℕ}
    (h : g ∈ repsOf T U es seen) : g < N := by
  unfold repsOf at h
  rw [Array.mem_filter, Array.mem_range] at h
  exact h.1

theorem repsOf_mem {T : Array ℕ} {U es : Array ℕ} {seen : Array Bool}
    (hU : ∀ x ∈ U, x < N) {x : ℕ} (hx : x ∈ U) (hs : seen[x]! = false) :
    minMul T es x ∈ repsOf T U es seen := by
  unfold repsOf
  rw [Array.mem_filter, Array.mem_range]
  have hsz : (Array.replicate 19683 false).size = N := Array.size_replicate ..
  rw [← Array.foldl_toList]
  obtain ⟨_, _, h3⟩ := foldl_mark (minMul T es) (minMul_le T es) seen U.toList
    (Array.replicate 19683 false) hsz (fun y hy => hU y (Array.mem_toList_iff.mp hy))
  refine ⟨lt_of_le_of_lt (minMul_le T es x) (hU x hx), ?_⟩
  exact h3 x (Array.mem_toList_iff.mpr hx) hs

theorem entry_eq {T : Array ℕ} {e : Entry} (h : e = mkEntry T e.gens) :
    e.es = (bfs T e.gens).1 ∧ e.seen = (bfs T e.gens).2 := by
  constructor
  · simpa [mkEntry] using congrArg Entry.es h
  · simpa [mkEntry] using congrArg Entry.seen h

theorem lat_complete {T : Array ℕ} (hT : TabLt T) {Xc : Set ℕ} (U : Array ℕ) (E : Array Entry)
    (hone : oneC ∈ Xc) (hmul : ∀ a b, a ∈ Xc → b ∈ Xc → mulc T a b ∈ Xc)
    (hU : ∀ x ∈ U, x < N)
    (hE : ∀ j, j < E.size → E[j]! = mkEntry T E[j]!.gens)
    (h0 : 0 < E.size) (hbase : ∀ g ∈ E[0]!.gens, g ∈ Xc)
    (hchk : latCheck T U E = true) :
    ∃ j < E.size, (∀ c ∈ E[j]!.es, c ∈ Xc) ∧ ∀ x ∈ U, x ∈ Xc → x ∈ E[j]!.es := by
  classical
  have hstruct : ∀ j, j < E.size → Struct (E[j]!.es, E[j]!.seen) := by
    intro j hj
    obtain ⟨h1, h2⟩ := entry_eq (hE j hj)
    rw [h1, h2]
    exact bfs_struct hT _
  let G : Finset ℕ := (Finset.range E.size).filter fun j => ∀ c ∈ E[j]!.es, c ∈ Xc
  have hG0 : 0 ∈ G := by
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨h0, ?_⟩
    obtain ⟨h1, h2⟩ := entry_eq (hE 0 h0)
    rw [h1]
    exact (bfs_spec hT hone hmul hbase).2
  obtain ⟨j, hjG, hjmax⟩ := Finset.exists_max_image G
    (fun j => (E[j]!.es.toList.toFinset).card) ⟨0, hG0⟩
  rw [Finset.mem_filter, Finset.mem_range] at hjG
  obtain ⟨hj, hjX⟩ := hjG
  refine ⟨j, hj, hjX, ?_⟩
  intro x hxU hxX
  by_contra hxn
  obtain ⟨hsz, hel, hbit, hnd⟩ := hstruct j hj
  have hseen : E[j]!.seen[x]! = false := by
    by_contra hb
    exact hxn (hbit x (by simpa using hb))
  have hok : entryOK T U E j = true := by
    have := hchk
    unfold latCheck at this
    rw [List.all_eq_true] at this
    exact this j (List.mem_range.mpr hj)
  unfold entryOK at hok
  simp only [Bool.and_eq_true] at hok
  obtain ⟨hgens, hreps⟩ := hok
  have hgensX : ∀ g ∈ E[j]!.gens, g ∈ Xc := by
    intro g hg
    rw [List.all_eq_true] at hgens
    exact hjX g (hbit g (hgens g hg))
  have hr : minMul T E[j]!.es x ∈ repsOf T U E[j]!.es E[j]!.seen := repsOf_mem hU hxU hseen
  have hrX : minMul T E[j]!.es x ∈ Xc := by
    rcases minMul_cases T E[j]!.es x with h | ⟨s, hs, h⟩
    · rw [h]; exact hxX
    · rw [h]; exact hmul s x (hjX s hs) hxX
  rw [Array.all_eq_true_iff_forall_mem] at hreps
  have h1 := hreps _ hr
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h1
  obtain ⟨hnc, hany⟩ := h1
  rw [List.any_eq_true] at hany
  obtain ⟨j', hj'mem, hj'⟩ := hany
  have hj'E : j' < E.size := List.mem_range.mp hj'mem
  simp only [Bool.and_eq_true, beq_iff_eq] at hj'
  obtain ⟨⟨⟨hsize, hfD⟩, hef⟩, hfr⟩ := hj'
  set D := bfs T (E[j]!.gens ++ [minMul T E[j]!.es x]) with hD
  have hDs : Struct D ∧ MemIn Xc D := bfs_spec hT hone hmul (by
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hgensX g hg
    · rw [List.mem_singleton.mp hg]; exact hrX)
  obtain ⟨⟨hDsz, hDel, hDbit, hDnd⟩, hDmem⟩ := hDs
  obtain ⟨hfsz, hfel, hfbit, hfnd⟩ := hstruct j' hj'E
  rw [Array.all_eq_true_iff_forall_mem] at hfD hef
  have hfX : ∀ c ∈ E[j']!.es, c ∈ Xc := fun c hc => hDmem c (hDbit c (hfD c hc))
  have hj'G : j' ∈ G := by
    rw [Finset.mem_filter, Finset.mem_range]; exact ⟨hj'E, hfX⟩
  have hsub : E[j]!.es.toList.toFinset ⊆ E[j']!.es.toList.toFinset := by
    intro c hc
    simp only [List.mem_toFinset, Array.mem_toList_iff] at hc ⊢
    exact hfbit c (hef c hc)
  have hrf : minMul T E[j]!.es x ∈ E[j']!.es := hfbit _ hfr
  have hrn : minMul T E[j]!.es x ∉ E[j]!.es := by
    intro h
    have := Array.contains_eq_true_of_mem h
    rw [this] at hnc
    exact absurd hnc (by simp)
  have hlt : (E[j]!.es.toList.toFinset).card < (E[j']!.es.toList.toFinset).card := by
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset hsub]
    exact ⟨minMul T E[j]!.es x, by simpa using hrf, by simpa using hrn⟩
  exact absurd (hjmax j' hj'G) (not_le.mpr hlt)

theorem entry_struct {T : Array ℕ} (hT : TabLt T) {E : Array Entry}
    (hE : ∀ j, j < E.size → E[j]! = mkEntry T E[j]!.gens) {j : ℕ} (hj : j < E.size) :
    Struct (E[j]!.es, E[j]!.seen) := by
  obtain ⟨h1, h2⟩ := entry_eq (hE j hj)
  rw [h1, h2]
  exact bfs_struct hT _

theorem latCheck_gens_mem {T : Array ℕ} (hT : TabLt T) {U : Array ℕ} {E : Array Entry}
    (hE : ∀ j, j < E.size → E[j]! = mkEntry T E[j]!.gens)
    (hchk : latCheck T U E = true) {j : ℕ} (hj : j < E.size) :
    ∀ g ∈ E[j]!.gens, g ∈ E[j]!.es := by
  obtain ⟨_, _, hbit, _⟩ := entry_struct hT hE hj
  have hok : entryOK T U E j = true := by
    have := hchk
    unfold latCheck at this
    rw [List.all_eq_true] at this
    exact this j (List.mem_range.mpr hj)
  unfold entryOK at hok
  simp only [Bool.and_eq_true] at hok
  intro g hg
  rw [List.all_eq_true] at hok
  exact hbit g (hok.1 g hg)

theorem mkEntries_size (T : Array ℕ) (lat : List (List ℕ)) :
    (mkEntries T lat).size = lat.length := by
  simp [mkEntries]

theorem mkEntries_get (T : Array ℕ) (lat : List (List ℕ)) {j : ℕ} (hj : j < lat.length) :
    (mkEntries T lat)[j]! = mkEntry T lat[j] := by
  have hs : j < (mkEntries T lat).size := by rw [mkEntries_size]; exact hj
  rw [getElem!_pos (mkEntries T lat) j hs]
  simp [mkEntries]

theorem mkEntries_gens (T : Array ℕ) (lat : List (List ℕ)) {j : ℕ} (hj : j < lat.length) :
    (mkEntries T lat)[j]!.gens = lat[j] := by
  rw [mkEntries_get T lat hj]; rfl

theorem mkEntries_hE (T : Array ℕ) (lat : List (List ℕ)) :
    ∀ j, j < (mkEntries T lat).size →
      (mkEntries T lat)[j]! = mkEntry T (mkEntries T lat)[j]!.gens := by
  intro j hj
  rw [mkEntries_size] at hj
  rw [mkEntries_gens T lat hj]
  exact mkEntries_get T lat hj

end CFSG.RankThree.PartTwo.Sec21.FF79.GL33

end
