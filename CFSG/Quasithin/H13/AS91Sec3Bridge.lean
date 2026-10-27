module

public import CFSG.Quasithin.H13.AS91Sec3Lists
public import CFSG.Quasithin.H13.AS91Sec3Invariance

public section

open scoped Pointwise

namespace CFSG.Quasithin.H13.AS91.M24G

open CFSG.ASVolI.ChH

theorem mem_toFinset_map_maskFin {L : List ℕ} (hL : ∀ x ∈ L, x < 2 ^ 24) {o : ℕ}
    (ho : o < 2 ^ 24) : maskFin o ∈ (L.map maskFin).toFinset ↔ o ∈ L := by
  rw [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨x, hx, h⟩
    rwa [← maskFin_inj (hL x hx) ho h]
  · intro h
    exact ⟨o, h, rfl⟩

theorem card_filter_toFinset_map {L : List ℕ} (hnd : L.Nodup) (hL : ∀ x ∈ L, x < 2 ^ 24)
    (P : Finset (Fin 24) → Prop) [DecidablePred P] (Q : ℕ → Bool)
    (hPQ : ∀ x ∈ L, (P (maskFin x) ↔ Q x = true)) :
    ((L.map maskFin).toFinset.filter P).card = (L.filter Q).length := by
  have hM : (L.map maskFin).Nodup :=
    hnd.map_on fun x hx y hy h => maskFin_inj (hL x hx) (hL y hy) h
  rw [hM.card_eq_countP, List.countP_map, List.countP_eq_length_filter]
  congr 1
  apply List.filter_congr
  intro x hx
  rw [Function.comp_apply, Bool.eq_iff_iff, decide_eq_true_eq]
  exact hPQ x hx

theorem trioOf_eq_toFinset (t : ℕ × ℕ × ℕ) :
    trioOf t = ((Native.octsT t).map maskFin).toFinset := by
  simp [trioOf, Native.octsT]

theorem trioFin_eq_toFinset (p : ℕ) :
    trioFin p = ((Native.octsT (Native.trioList ())[p]!).map maskFin).toFinset :=
  trioOf_eq_toFinset _

theorem mem_octsS {s : List ℕ} {o : ℕ} :
    o ∈ Native.octsS s ↔ ∃ B ∈ s, ∃ B' ∈ s, B < B' ∧ B ||| B' = o := by
  simp only [Native.octsS, List.mem_flatMap, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨B, hB, B', ⟨hB', hlt⟩, rfl⟩
    exact ⟨B, hB, B', hB', hlt, rfl⟩
  · rintro ⟨B, hB, B', hB', hlt, rfl⟩
    exact ⟨B, hB, B', ⟨hB', hlt⟩, rfl⟩

theorem octsS_lt {s : List ℕ} (hs : ∀ x ∈ s, x < 2 ^ 24) : ∀ o ∈ Native.octsS s, o < 2 ^ 24 := by
  intro o ho
  obtain ⟨B, hB, B', hB', -, rfl⟩ := mem_octsS.1 ho
  exact Nat.or_lt_two_pow (hs B hB) (hs B' hB')

theorem mem_octsOf_sextOfL {s : List ℕ} (hs : ∀ x ∈ s, x < 2 ^ 24) {X : Finset (Fin 24)} :
    X ∈ octsOf (sextOfL s) ↔ X ∈ ((Native.octsS s).map maskFin).toFinset := by
  rw [mem_octsOf, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨a, ha, b, hb, hne, rfl⟩
    obtain ⟨B, hB, rfl⟩ := mem_sextOfL.1 ha
    obtain ⟨B', hB', rfl⟩ := mem_sextOfL.1 hb
    have hBB' : B ≠ B' := fun h => hne (by rw [h])
    rcases Nat.lt_or_gt_of_ne hBB' with h | h
    · exact ⟨B ||| B', mem_octsS.2 ⟨B, hB, B', hB', h, rfl⟩, maskFin_or B B'⟩
    · exact ⟨B' ||| B, mem_octsS.2 ⟨B', hB', B, hB, h, rfl⟩, by rw [maskFin_or, Finset.union_comm]⟩
  · rintro ⟨o, ho, rfl⟩
    obtain ⟨B, hB, B', hB', hlt, rfl⟩ := mem_octsS.1 ho
    exact ⟨maskFin B, mem_sextOfL.2 ⟨B, hB, rfl⟩, maskFin B', mem_sextOfL.2 ⟨B', hB', rfl⟩,
      fun h => (ne_of_lt hlt) (maskFin_inj (hs B hB) (hs B' hB') h), (maskFin_or B B').symm⟩

theorem maskFin_mem_octsOf_sextOfL {s : List ℕ} (hs : ∀ x ∈ s, x < 2 ^ 24) {o : ℕ}
    (ho : o < 2 ^ 24) : maskFin o ∈ octsOf (sextOfL s) ↔ o ∈ Native.octsS s := by
  rw [mem_octsOf_sextOfL hs, mem_toFinset_map_maskFin (octsS_lt hs) ho]

theorem and_or_self_right (x b : ℕ) : x &&& (b ||| x) = x := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_or]
  cases x.testBit i <;> simp

theorem and_or_self_left (x b : ℕ) : x &&& (x ||| b) = x := by
  rw [Nat.or_comm, and_or_self_right]

theorem eq_of_and_or_eq {s : List ℕ} (h4 : ∀ x ∈ s, Native.pop x = 4)
    (hd : ∀ x ∈ s, ∀ y ∈ s, x = y ∨ x &&& y = 0) {X B B' : ℕ} (hX : X ∈ s) (hB : B ∈ s)
    (hB' : B' ∈ s) (hsub : X &&& (B ||| B') = X) : X = B ∨ X = B' := by
  by_contra hcon
  obtain ⟨hne1, hne2⟩ := not_or.1 hcon
  have e1 : X &&& B = 0 := (hd X hX B hB).resolve_left hne1
  have e2 : X &&& B' = 0 := (hd X hX B' hB').resolve_left hne2
  have hX0 : X = 0 := by
    rw [← hsub, Nat.and_or_distrib_left, e1, e2]
    rfl
  have h := h4 X hX
  rw [hX0] at h
  exact absurd h (by decide)

theorem octsS_nodup {s : List ℕ} (hpw : s.Pairwise (· < ·)) (h4 : ∀ x ∈ s, Native.pop x = 4)
    (hd : ∀ x ∈ s, ∀ y ∈ s, x = y ∨ x &&& y = 0) : (Native.octsS s).Nodup := by
  unfold Native.octsS
  rw [List.nodup_flatMap]
  refine ⟨fun B hB => ?_, ?_⟩
  · apply List.Nodup.map_on
    · intro x hx y hy hxy
      rw [List.mem_filter, decide_eq_true_eq] at hx hy
      have hsub : x &&& (B ||| y) = x := by rw [← hxy]; exact and_or_self_right x B
      rcases eq_of_and_or_eq h4 hd hx.1 hB hy.1 hsub with h | h
      · exact absurd hx.2 (by rw [h]; exact lt_irrefl _)
      · exact h
    · exact (hpw.nodup).filter _
  · refine hpw.imp_of_mem ?_
    intro a b ha hb hab x hxa hxb
    simp only [List.mem_map, List.mem_filter, decide_eq_true_eq] at hxa hxb
    obtain ⟨a', ⟨ha', haa'⟩, rfl⟩ := hxa
    obtain ⟨b', ⟨hb', hbb'⟩, hb''⟩ := hxb
    have hsub : a &&& (b ||| b') = a := by rw [hb'']; exact and_or_self_left a a'
    rcases eq_of_and_or_eq h4 hd ha hb hb' hsub with h | h
    · exact absurd hab (by rw [h]; exact lt_irrefl _)
    · exact absurd (hab.trans hbb') (by rw [h]; exact lt_irrefl _)

theorem trioSexts_getElem {p : ℕ} (hp : p < 3795) :
    (Native.trioSexts ())[p]! = (List.range 1771).filter fun q =>
      Native.trioIn (Native.trioList ())[p]! (Native.sextList ())[q]! := by
  unfold Native.trioSexts
  simp [Native.nTrio, Native.nSext, hp]

theorem reachOK_smul {X : Type*} [MulAction S24 X] (f : ℕ → X) (n : ℕ) (steps : List (ℕ → ℕ))
    {m : ℕ} (hm : steps.length = m) (P : Fin m → S24) (hPm : ∀ j, P j ∈ M24g)
    (hstep : ∀ (j : Fin m) (i : ℕ), i < n → (steps.getD j id) i < n →
      f ((steps.getD j id) i) = P j • f i)
    {p : ℕ} {c : List ℕ} (h : Native.reachOK n steps p c = true) (hp : p < n) :
    ∀ q ∈ c, ∃ σ ∈ M24g, σ • f p = f q := by
  unfold Native.reachOK at h
  generalize Native.bfs (fun i => i) steps p 5000 = r at h
  obtain ⟨L, par, gen⟩ := r
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Native.allLt_iff, Bool.or_eq_true,
    List.all_eq_true, Array.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨⟨-, hL0⟩, -⟩, -⟩, hall⟩, hc⟩ := h
  have key : ∀ j, j < L.size → ∃ σ ∈ M24g, σ • f p = f L[j]! := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      rcases (hall j hj).2 with rfl | ⟨⟨hpar, hgen⟩, hstp⟩
      · exact ⟨1, one_mem _, by rw [one_smul, hL0]⟩
      · obtain ⟨σ, hσ, hσf⟩ := ih par[j]! hpar (lt_trans hpar hj)
        have hlt : L[par[j]!]! < n := (hall par[j]! (lt_trans hpar hj)).1
        have hjn : L[j]! < n := (hall j hj).1
        have hgm : gen[j]! < m := hm ▸ hgen
        have hs : steps.getD gen[j]! id L[par[j]!]! < n →
            f (steps.getD gen[j]! id L[par[j]!]!) = P ⟨gen[j]!, hgm⟩ • f L[par[j]!]! :=
          hstep ⟨gen[j]!, hgm⟩ L[par[j]!]! hlt
        rw [hstp] at hs
        exact ⟨P ⟨gen[j]!, hgm⟩ * σ, mul_mem (hPm _) hσ, by rw [mul_smul, hσf, hs hjn]⟩
  intro q hq
  obtain ⟨j, hj, hjq⟩ := Array.mem_iff_getElem.1 (hc q hq)
  obtain ⟨σ, hσ, hσf⟩ := key j hj
  exact ⟨σ, hσ, by rw [hσf, getElem!_pos L j hj, hjq]⟩

section Cert

theorem octsT_lt {p : ℕ} (hp : p < 3795) :
    ∀ o ∈ Native.octsT (Native.trioList ())[p]!, o < 2 ^ 24 := by
  obtain ⟨-, -, h3, h4, h5, -⟩ := trioList_get hp rfl
  intro o ho
  simp only [Native.octsT, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl
  exacts [(isOctad_maskFin_of_octIdx h3).2, (isOctad_maskFin_of_octIdx h4).2,
    (isOctad_maskFin_of_octIdx h5).2]

theorem octsT_nodup {p : ℕ} (hp : p < 3795) :
    (Native.octsT (Native.trioList ())[p]!).Nodup := by
  obtain ⟨h1, h2, -⟩ := trioList_get hp rfl
  simp only [Native.octsT, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, not_false_eq_true, and_true]
  omega

theorem maskFin_mem_trioFin {p : ℕ} (hp : p < 3795) {o : ℕ} (ho : o < 2 ^ 24) :
    maskFin o ∈ trioFin p ↔ o ∈ Native.octsT (Native.trioList ())[p]! := by
  rw [trioFin_eq_toFinset, mem_toFinset_map_maskFin (octsT_lt hp) ho]

theorem sextList_lt {q : ℕ} (hq : q < 1771) : ∀ x ∈ (Native.sextList ())[q]!, x < 2 ^ 24 :=
  fun _ hx => ((sextList_get hq rfl).2.2.1 _ hx).2

theorem octsS_nodup_sextList {q : ℕ} (hq : q < 1771) :
    (Native.octsS (Native.sextList ())[q]!).Nodup := by
  obtain ⟨-, h2, h3, -, h5, -⟩ := sextList_get hq rfl
  refine octsS_nodup h2 (fun x hx => (h3 x hx).1) fun x hx y hy => ?_
  rcases h5 x hx y hy with h | ⟨h, -⟩
  exacts [Or.inl h, Or.inr h]

theorem octsOf_sextFin {q : ℕ} (hq : q < 1771) :
    octsOf (sextFin q) = ((Native.octsS (Native.sextList ())[q]!).map maskFin).toFinset :=
  Finset.ext fun _ => mem_octsOf_sextOfL (sextList_lt hq)

theorem maskFin_mem_octsOf_sextFin {q : ℕ} (hq : q < 1771) {o : ℕ} (ho : o < 2 ^ 24) :
    maskFin o ∈ octsOf (sextFin q) ↔ o ∈ Native.octsS (Native.sextList ())[q]! :=
  maskFin_mem_octsOf_sextOfL (sextList_lt hq) ho

theorem trioIn_iff {p q : ℕ} (hp : p < 3795) (hq : q < 1771) :
    Native.trioIn (Native.trioList ())[p]! (Native.sextList ())[q]! = true ↔
      TrioIn (trioFin p) (sextFin q) := by
  unfold TrioIn Native.trioIn
  rw [List.all_eq_true, trioFin_eq_toFinset, Finset.subset_iff]
  constructor
  · intro h X hX
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hX)
    rw [maskFin_mem_octsOf_sextFin hq (octsT_lt hp o ho)]
    simpa using h o ho
  · intro h o ho
    have h1 := h (List.mem_toFinset.2 (List.mem_map.2 ⟨o, ho, rfl⟩))
    rw [maskFin_mem_octsOf_sextFin hq (octsT_lt hp o ho)] at h1
    simpa using h1

theorem mem_trioSexts {p q : ℕ} (hp : p < 3795) :
    q ∈ (Native.trioSexts ())[p]! ↔ q < 1771 ∧ TrioIn (trioFin p) (sextFin q) := by
  rw [trioSexts_getElem hp, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨hq, h⟩
    exact ⟨hq, (trioIn_iff hp hq).1 h⟩
  · rintro ⟨hq, h⟩
    exact ⟨hq, (trioIn_iff hp hq).2 h⟩

theorem sextTrios_iff {p q : ℕ} (hq : q < 1771) :
    p ∈ Native.sextTrios (Native.trioSexts ()) q ↔ p < 3795 ∧ TrioIn (trioFin p) (sextFin q) := by
  unfold Native.sextTrios
  rw [List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨hp, h⟩
    exact ⟨hp, ((mem_trioSexts hp).1 (by simpa using h)).2⟩
  · rintro ⟨hp, h⟩
    exact ⟨hp, by simpa using (mem_trioSexts hp).2 ⟨hq, h⟩⟩

theorem coplanar_iff {p p' : ℕ} (hp : p < 3795) (hp' : p' < 3795) :
    Native.coplanar (Native.trioSexts ()) p p' = true ↔ Coplanar (trioFin p) (trioFin p') := by
  unfold Native.coplanar Coplanar
  simp only [List.any_eq_true, List.contains_eq_mem, decide_eq_true_eq]
  constructor
  · rintro ⟨q, hq, hq'⟩
    obtain ⟨hq1, hq2⟩ := (mem_trioSexts hp).1 hq
    exact ⟨sextFin q, isSextet_sextFin hq1, hq2, ((mem_trioSexts hp').1 hq').2⟩
  · rintro ⟨S, hS, h1, h2⟩
    obtain ⟨q, hq, rfl⟩ := (isSextet_iff S).1 hS
    exact ⟨q, (mem_trioSexts hp).2 ⟨hq, h1⟩, (mem_trioSexts hp').2 ⟨hq, h2⟩⟩

theorem meets_iff {p p' : ℕ} (hp : p < 3795) (hp' : p' < 3795) :
    Native.meets (Native.trioList ())[p]! (Native.trioList ())[p']! = true ↔
      ¬ Disjoint (trioFin p') (trioFin p) := by
  rw [Finset.not_disjoint_iff]
  unfold Native.meets
  simp only [List.any_eq_true, List.contains_eq_mem, decide_eq_true_eq]
  constructor
  · rintro ⟨o, ho', ho⟩
    have hlt := octsT_lt hp' o ho'
    exact ⟨maskFin o, (maskFin_mem_trioFin hp' hlt).2 ho', (maskFin_mem_trioFin hp hlt).2 ho⟩
  · rintro ⟨X, hX', hX⟩
    rw [trioFin_eq_toFinset, List.mem_toFinset, List.mem_map] at hX'
    obtain ⟨o, ho', rfl⟩ := hX'
    exact ⟨o, ho', (maskFin_mem_trioFin hp (octsT_lt hp' o ho')).1 hX⟩

theorem inZeta_iff {p : ℕ} (hp : p < 3795) {o : ℕ} (ho : o < 2 ^ 24) :
    Native.inZeta (Native.trioList ())[p]! o = true ↔ InZeta (trioFin p) (maskFin o) := by
  unfold Native.inZeta InZeta
  simp only [Bool.or_eq_true, List.contains_eq_mem, decide_eq_true_eq, List.any_eq_true,
    beq_iff_eq]
  rw [← maskFin_mem_trioFin hp ho]
  refine or_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨u, hu, h0⟩
    refine ⟨maskFin u, (maskFin_mem_trioFin hp (octsT_lt hp u hu)).2 hu, ?_⟩
    rw [disjoint_maskFin, h0, maskFin_zero]
  · rintro ⟨X, hX, hd⟩
    rw [trioFin_eq_toFinset, List.mem_toFinset, List.mem_map] at hX
    obtain ⟨u, hu, rfl⟩ := hX
    refine ⟨u, hu, ?_⟩
    rw [disjoint_maskFin] at hd
    exact (maskFin_eq_empty (Nat.and_lt_two_pow _ (octsT_lt hp u hu))).1 hd

theorem zc_eq {p p' : ℕ} (hp : p < 3795) (hp' : p' < 3795) :
    Native.zc (Native.trioList ())[p]! (Native.trioList ())[p']! =
      ((trioFin p').filter (InZeta (trioFin p))).card := by
  rw [trioFin_eq_toFinset p', card_filter_toFinset_map (octsT_nodup hp') (octsT_lt hp') _
    (Native.inZeta (Native.trioList ())[p]!)
    (fun o ho => (inZeta_iff hp (octsT_lt hp' o ho)).symm)]
  rfl

theorem deltaB_iff {p p' : ℕ} (hp : p < 3795) (hp' : p' < 3795) (i : Fin 5) :
    (Native.deltaB (Native.trioSexts ()) p p').getD i false = true ↔
      Delta (trioFin p) (trioFin p') i := by
  simp only [Native.deltaB]
  match i with
  | 0 =>
    show (p' == p) = true ↔ trioFin p' = trioFin p
    rw [beq_iff_eq]
    exact ⟨fun h => by rw [h], trioFin_injective hp' hp⟩
  | 1 =>
    show (p' != p && Native.meets (Native.trioList ())[p]! (Native.trioList ())[p']!) = true ↔
      trioFin p' ≠ trioFin p ∧ ¬ Disjoint (trioFin p') (trioFin p)
    rw [Bool.and_eq_true, meets_iff hp hp', bne_iff_ne, ne_eq, ne_eq]
    exact and_congr ⟨fun h h' => h (trioFin_injective hp' hp h'), fun h h' => h (by rw [h'])⟩
      Iff.rfl
  | 2 =>
    show (!Native.meets (Native.trioList ())[p]! (Native.trioList ())[p']! &&
        Native.coplanar (Native.trioSexts ()) p p') = true ↔
      Disjoint (trioFin p') (trioFin p) ∧ Coplanar (trioFin p) (trioFin p')
    rw [Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true, meets_iff hp hp',
      coplanar_iff hp hp', not_not]
  | 3 =>
    show (Native.zc (Native.trioList ())[p]! (Native.trioList ())[p']! == 1) = true ↔
      ((trioFin p').filter (InZeta (trioFin p))).card = 1
    rw [beq_iff_eq, zc_eq hp hp']
  | 4 =>
    show (Native.zc (Native.trioList ())[p]! (Native.trioList ())[p']! == 0) = true ↔
      ((trioFin p').filter (InZeta (trioFin p))).card = 0
    rw [beq_iff_eq, zc_eq hp hp']

theorem commonOcts_eq {q q' : ℕ} (hq : q < 1771) (hq' : q' < 1771) :
    Native.commonOcts (Native.sextList ())[q]! (Native.sextList ())[q']! =
      (octsOf (sextFin q') ∩ octsOf (sextFin q)).card := by
  rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, octsOf_sextFin hq,
    card_filter_toFinset_map (octsS_nodup_sextList hq) (octsS_lt (sextList_lt hq)) _
      (fun o => (Native.octsS (Native.sextList ())[q']!).contains o)]
  · rfl
  · intro o ho
    show maskFin o ∈ octsOf (sextFin q') ↔ _
    rw [maskFin_mem_octsOf_sextFin hq' (octsS_lt (sextList_lt hq) o ho)]
    simp

theorem xiB_iff {q q' : ℕ} (hq : q < 1771) (hq' : q' < 1771) (i : Fin 4) :
    (Native.xiB q q').getD i false = true ↔ Xi (sextFin q) (sextFin q') i := by
  simp only [Native.xiB]
  match i with
  | 0 =>
    show (q' == q) = true ↔ sextFin q' = sextFin q
    rw [beq_iff_eq]
    exact ⟨fun h => by rw [h], sextFin_injective hq' hq⟩
  | 1 =>
    show (Native.commonOcts (Native.sextList ())[q]! (Native.sextList ())[q']! == 3) = true ↔
      (octsOf (sextFin q') ∩ octsOf (sextFin q)).card = 3
    rw [beq_iff_eq, commonOcts_eq hq hq']
  | 2 =>
    show (Native.commonOcts (Native.sextList ())[q]! (Native.sextList ())[q']! == 1) = true ↔
      (octsOf (sextFin q') ∩ octsOf (sextFin q)).card = 1
    rw [beq_iff_eq, commonOcts_eq hq hq']
  | 3 =>
    show (Native.commonOcts (Native.sextList ())[q]! (Native.sextList ())[q']! == 0) = true ↔
      Disjoint (octsOf (sextFin q')) (octsOf (sextFin q))
    rw [beq_iff_eq, commonOcts_eq hq hq', Finset.card_eq_zero, Finset.disjoint_iff_inter_eq_empty]

theorem kappaCount_eq {p q : ℕ} (hp : p < 3795) (hq : q < 1771) :
    ((Native.octsT (Native.trioList ())[p]!).filter fun o =>
      (Native.octsS (Native.sextList ())[q]!).contains o).length =
        (trioFin p ∩ octsOf (sextFin q)).card := by
  rw [← Finset.filter_mem_eq_inter, trioFin_eq_toFinset p,
    card_filter_toFinset_map (octsT_nodup hp) (octsT_lt hp) _
      (fun o => (Native.octsS (Native.sextList ())[q]!).contains o)]
  intro o ho
  show maskFin o ∈ octsOf (sextFin q) ↔ _
  rw [maskFin_mem_octsOf_sextFin hq (octsT_lt hp o ho)]
  simp

theorem oneIn_iff {p q : ℕ} (hp : p < 3795) (hq : q < 1771) :
    Native.oneIn p q = true ↔ Kappa (sextFin q) (trioFin p) 1 := by
  unfold Native.oneIn
  rw [beq_iff_eq, kappaCount_eq hp hq]
  rfl

theorem inXi1_iff {q p : ℕ} (hq : q < 1771) (hp : p < 3795) :
    ((Native.trioSexts ())[p]!.any fun q' => (Native.xiB q q').getD 1 false) = true ↔
      ∃ W, IsSextet W ∧ Xi (sextFin q) W 1 ∧ TrioIn (trioFin p) W := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨q', hq', hx⟩
    obtain ⟨hq1, hq2⟩ := (mem_trioSexts hp).1 hq'
    exact ⟨sextFin q', isSextet_sextFin hq1, (xiB_iff hq hq1 1).1 hx, hq2⟩
  · rintro ⟨W, hW, hx, hin⟩
    obtain ⟨q', hq1, rfl⟩ := (isSextet_iff W).1 hW
    exact ⟨q', (mem_trioSexts hp).2 ⟨hq1, hin⟩, (xiB_iff hq hq1 1).2 hx⟩

theorem kappaB_iff {q p : ℕ} (hq : q < 1771) (hp : p < 3795) (i : Fin 4) :
    (Native.kappaB (Native.trioSexts ()) q p).getD i false = true ↔
      Kappa (sextFin q) (trioFin p) i := by
  simp only [Native.kappaB]
  match i with
  | 0 => exact trioIn_iff hp hq
  | 1 =>
    show (_ == 1) = true ↔ (trioFin p ∩ octsOf (sextFin q)).card = 1
    rw [beq_iff_eq, kappaCount_eq hp hq]
  | 2 =>
    show (_ == 0 && _) = true ↔ Disjoint (trioFin p) (octsOf (sextFin q)) ∧
      ∃ W, IsSextet W ∧ Xi (sextFin q) W 1 ∧ TrioIn (trioFin p) W
    rw [Bool.and_eq_true, beq_iff_eq, kappaCount_eq hp hq, inXi1_iff hq hp, Finset.card_eq_zero,
      ← Finset.disjoint_iff_inter_eq_empty]
  | 3 =>
    show (_ == 0 && !_) = true ↔ Disjoint (trioFin p) (octsOf (sextFin q)) ∧
      ¬ ∃ W, IsSextet W ∧ Xi (sextFin q) W 1 ∧ TrioIn (trioFin p) W
    rw [Bool.and_eq_true, beq_iff_eq, kappaCount_eq hp hq, Bool.not_eq_true', ← Bool.not_eq_true,
      inXi1_iff hq hp, Finset.card_eq_zero, ← Finset.disjoint_iff_inter_eq_empty]

end Cert

end CFSG.Quasithin.H13.AS91.M24G
