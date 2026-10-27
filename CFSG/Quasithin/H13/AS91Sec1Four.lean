module

public import CFSG.Quasithin.H13.AS91Sec1Rotate
public import CFSG.Quasithin.H13.AS91Sec1Square
public import CFSG.Quasithin.H13.AS91Sec1Three
public import CFSG.Quasithin.H13.AS91Sec1Two

public section

namespace CFSG.Quasithin.H13.AS91

open CFSG.Quasithin.Asc94

universe u

variable {V : Type u} {Δ : SimpleGraph V} {N : ℕ} {R : ℕ → V → V → V → Prop}

theorem comp_refl {x u y : V} (hxu : Δ.Adj x u) (hyu : Δ.Adj y u) : comp Δ x u y u :=
  ⟨⟨hxu, hyu⟩, ⟨hxu, hyu⟩, SimpleGraph.Reachable.refl _⟩

theorem comp_mem_right {x u y w : V} (h : comp Δ x u y w) : Δ.Adj x w ∧ Δ.Adj y w := by
  obtain ⟨_, hw, _⟩ := h
  exact hw

theorem comp_symm {x u y w : V} (h : comp Δ x u y w) : comp Δ x w y u := by
  obtain ⟨hu, hw, hr⟩ := h
  exact ⟨hw, hu, hr.symm⟩

theorem comp_trans {x u y v w : V} (h₁ : comp Δ x u y v) (h₂ : comp Δ x v y w) :
    comp Δ x u y w := by
  obtain ⟨hu, _, hr₁⟩ := h₁
  obtain ⟨_, hw, hr₂⟩ := h₂
  exact ⟨hu, hw, hr₁.trans hr₂⟩

theorem comp_of_adj {x u y w : V} (hu : Δ.Adj x u ∧ Δ.Adj y u) (hw : Δ.Adj x w ∧ Δ.Adj y w)
    (huw : Δ.Adj u w) : comp Δ x u y w :=
  ⟨hu, hw, SimpleGraph.Adj.reachable
    (show (Δ.induce {z | Δ.Adj x z ∧ Δ.Adj y z}).Adj ⟨u, hu⟩ ⟨w, hw⟩ from huw)⟩

theorem comp_swap {x u y w : V} (h : comp Δ x u y w) : comp Δ y u x w := by
  obtain ⟨hu, hw, hr⟩ := h
  refine ⟨⟨hu.2, hu.1⟩, ⟨hw.2, hw.1⟩, ?_⟩
  have hle : {z | Δ.Adj x z ∧ Δ.Adj y z} ≤ {z | Δ.Adj y z ∧ Δ.Adj x z} :=
    fun z hz => ⟨hz.2, hz.1⟩
  exact hr.map (SimpleGraph.induceHomOfLE Δ hle).toHom

theorem moves_middle_of_comp (l₁ l₂ : List V) {a b c b' : V} (h : comp Δ a b c b') :
    Moves Δ {p | IsNGon Δ 3 p} (l₁ ++ a :: b :: c :: l₂) (l₁ ++ a :: b' :: c :: l₂) := by
  obtain ⟨hb, hb', hr⟩ := h
  exact moves_middle_of_reachable l₁ l₂ hb hb' hr

theorem moves_square_replace {a b c d b' d' : V} (hb : comp Δ a b c b') (hd : comp Δ a d c d') :
    Moves Δ {p | IsNGon Δ 3 p} [a, b, c, d, a] [a, b', c, d', a] := by
  have m1 : Moves Δ {p | IsNGon Δ 3 p} [a, b, c, d, a] [a, b', c, d, a] := by
    simpa using moves_middle_of_comp [] [d, a] hb
  have m2 : Moves Δ {p | IsNGon Δ 3 p} [a, b', c, d, a] [a, b', c, d', a] := by
    simpa using moves_middle_of_comp [a, b'] [] (comp_swap hd)
  exact m1.trans m2

theorem HypB.le_top (h : HypB Δ N R) {k : ℕ} (hk : k ≤ N) {x u y : V} (hR : R k x u y) :
    R N x u y := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  have key : ∀ i ≤ j, R (k + i) x u y := by
    intro i
    induction i with
    | zero => intro _; exact hR
    | succ i ih => intro hi; exact h.mono (k + i) (by omega) x u y (ih (by omega))
  exact key j le_rfl

theorem HypB.adj_of_le (h : HypB Δ N R) {k : ℕ} (hk : k ≤ N) {x u y : V} (hR : R k x u y) :
    Δ.Adj x u ∧ Δ.Adj u y ∧ x ≠ y :=
  (h.top x u y).mp (h.le_top hk hR)

theorem comp_of_R_one (h : HypB Δ N R) (hN : 1 ≤ N) {x u y v : V} (hR : R 1 x u y)
    (hna : ¬ Δ.Adj x y) (hv : Δ.Adj x v ∧ Δ.Adj y v) : comp Δ x u y v := by
  obtain ⟨hxu, huy, hxy⟩ := h.adj_of_le hN hR
  have hRv : R N x v y := (h.top x v y).mpr ⟨hv.1, hv.2.symm, hxy⟩
  have hR0u : ¬ R 0 x u y := fun h0 => hna ((h.zero x u y).mp h0).2.2
  have hR0v : ¬ R 0 x v y := fun h0 => hna ((h.zero x v y).mp h0).2.2
  obtain ⟨a, b, ha, hb, hab⟩ := h.b2 0 (by omega) x u y v y hR hR0u hRv hR0v
  have hu : Δ.Adj x u ∧ Δ.Adj y u := ⟨hxu, huy.symm⟩
  have hca : comp Δ x u y a := by
    rcases ha with ha | ⟨hxa, c, hc, hR0⟩
    · exact ha
    · obtain ⟨_, hcac, hyac⟩ := (h.zero y c a).mp hR0
      exact comp_trans hc (comp_of_adj (comp_mem_right hc) ⟨hxa, hyac⟩ hcac)
  have hbmem := comp_mem_right hb
  have hamem := comp_mem_right hca
  have hab' : comp Δ x a y b := by
    simp only [Nat.zero_min, induced] at hab
    rcases hab with (rfl | hab) | ⟨e, he⟩
    · exact comp_refl hbmem.1 hbmem.2
    · exact comp_of_adj hamem hbmem hab
    · exact comp_of_adj hamem hbmem ((h.zero a e b).mp he).2.2
  exact comp_trans (comp_trans hca hab') (comp_symm hb)

theorem reachable_of_induced_one (h : HypB Δ N R) (hN : 1 ≤ N) {x y u v : V}
    (hi : induced Δ R 1 x y) (hp : ¬ Perp Δ x y) (hu : Δ.Adj x u ∧ Δ.Adj y u)
    (hv : Δ.Adj x v ∧ Δ.Adj y v) :
    (Δ.induce {z | Δ.Adj x z ∧ Δ.Adj y z}).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
  obtain ⟨u₀, hu₀⟩ : ∃ u₀, R 1 x u₀ y := hi.resolve_left hp
  have hna : ¬ Δ.Adj x y := fun hxy => hp (Or.inr hxy)
  obtain ⟨_, _, hr⟩ := comp_trans (comp_symm (comp_of_R_one h hN hu₀ hna hu))
    (comp_of_R_one h hN hu₀ hna hv)
  exact hr

theorem isCycle_square {a b c d : V} (hab : Δ.Adj a b) (hbc : Δ.Adj b c) (hcd : Δ.Adj c d)
    (hda : Δ.Adj d a) : IsCycle Δ [a, b, c, d, a] := by
  refine ⟨⟨List.cons_ne_nil _ _, ?_⟩, rfl⟩
  simp [List.isChain_cons_cons, hab, hbc, hcd, hda]

theorem inClosure_square_rotate {C : Set (List V)} {a b c d : V} (hab : Δ.Adj a b)
    (hbc : Δ.Adj b c) (hcd : Δ.Adj c d) (hda : Δ.Adj d a) (h : InClosure Δ C [a, b, c, d, a]) :
    InClosure Δ C [b, c, d, a, b] :=
  InClosure.of_isRotation (isCycle_square hab hbc hcd hda) ⟨[a, b], [c, d, a], b, rfl, rfl, rfl⟩ h

theorem inClosure_square_rotate' {C : Set (List V)} {a b c d : V} (hab : Δ.Adj a b)
    (hbc : Δ.Adj b c) (hcd : Δ.Adj c d) (hda : Δ.Adj d a) (h : InClosure Δ C [b, c, d, a, b]) :
    InClosure Δ C [a, b, c, d, a] :=
  InClosure.of_isRotation (isCycle_square hbc hcd hda hab) ⟨[b, c, d, a], [b], a, rfl, rfl, rfl⟩ h

theorem inClosure_square_of_perp_ac {a b c d : V} (hab : Δ.Adj a b) (hbc : Δ.Adj b c)
    (hcd : Δ.Adj c d) (hda : Δ.Adj d a) (h : Perp Δ a c) :
    InClosure Δ {p | IsNGon Δ 3 p} [a, b, c, d, a] := by
  rcases h with h | hac
  ·
    subst h
    refine ⟨a, ?_⟩
    have m1 : Moves Δ {p | IsNGon Δ 3 p} [a, b, a, d, a] [a, d, a] := by
      simpa using Moves.backDel (C := {p | IsNGon Δ 3 p}) [] [d, a] hab
    have m2 : Moves Δ {p | IsNGon Δ 3 p} [a, d, a] [a] := by
      simpa using Moves.backDel (C := {p | IsNGon Δ 3 p}) [] [] hda.symm
    exact m1.trans m2
  ·
    refine ⟨a, ?_⟩
    have m1 : Moves Δ {p | IsNGon Δ 3 p} [a, b, c, d, a] [a, b, c, a, c, d, a] := by
      simpa using Moves.backIns (C := {p | IsNGon Δ 3 p}) [a, b] [d, a] hac.symm
    have m2 : Moves Δ {p | IsNGon Δ 3 p} [a, b, c, a, c, d, a] [a, c, d, a] := by
      simpa using Moves.cycDel_mem (C := {p | IsNGon Δ 3 p}) [] [c, d, a] [a, b, c, a]
        (isNGon_three hab hbc hac.symm) rfl rfl
    have m3 : Moves Δ {p | IsNGon Δ 3 p} [a, c, d, a] [a] := by
      simpa using Moves.cycDel_mem (C := {p | IsNGon Δ 3 p}) [] [] [a, c, d, a]
        (isNGon_three hac hcd hda) rfl rfl
    exact m1.trans (m2.trans m3)

theorem inClosure_square_of_perp_bd {a b c d : V} (hab : Δ.Adj a b) (hbc : Δ.Adj b c)
    (hcd : Δ.Adj c d) (hda : Δ.Adj d a) (h : Perp Δ b d) :
    InClosure Δ {p | IsNGon Δ 3 p} [a, b, c, d, a] :=
  inClosure_square_rotate' hab hbc hcd hda (inClosure_square_of_perp_ac hbc hcd hda hab h)

@[expose] def SqLevel (Δ : SimpleGraph V) (R : ℕ → V → V → V → Prop) (t : ℕ) : Prop :=
  ∀ a b c d : V, Δ.Adj a b → Δ.Adj b c → Δ.Adj c d → Δ.Adj d a → R t a b c →
    InClosure Δ {p | IsNGon Δ 3 p} [a, b, c, d, a]

theorem inClosure_of_moves_of_inClosure {C : Set (List V)} {p q : List V} (hm : Moves Δ C p q)
    (hq : InClosure Δ C q) : InClosure Δ C p :=
  let ⟨w, hw⟩ := hq
  ⟨w, hm.trans hw⟩

theorem inClosure_square_of_caseA (h : HypB Δ N R) (hN : 1 ≤ N) {a b c d b' d' : V}
    (hb : comp Δ a b c b') (hd : comp Δ a d c d') (hi : induced Δ R 1 b' d') :
    InClosure Δ {p | IsNGon Δ 3 p} [a, b, c, d, a] := by
  obtain ⟨hab', hcb'⟩ := comp_mem_right hb
  obtain ⟨had', hcd'⟩ := comp_mem_right hd
  refine inClosure_of_moves_of_inClosure (moves_square_replace hb hd) ?_
  by_cases hp : Perp Δ b' d'
  · exact inClosure_square_of_perp_bd hab' hcb'.symm hcd' had'.symm hp
  · refine inClosure_square_rotate' hab' hcb'.symm hcd' had'.symm ?_
    exact inClosure_square_of_reachable hcb'.symm hcd' had'.symm hab'
      (reachable_of_induced_one h hN hi hp ⟨hcb'.symm, hcd'.symm⟩ ⟨hab'.symm, had'.symm⟩)

theorem inClosure_pentagon (h : HypB Δ N R) (hN : 1 ≤ N) {s : ℕ} (hs : s ≤ N)
    (ih : SqLevel Δ R s) {a b c d w : V} (hbc : Δ.Adj b c) (hcd : Δ.Adj c d) (hda : Δ.Adj d a)
    (haw : Δ.Adj a w) (hcw : ¬ Δ.Adj c w) (hR : R s w b c) (hi : induced Δ R 1 w d) :
    InClosure Δ {p | IsNGon Δ 3 p} [d, a, w, b, c, d] := by
  obtain ⟨hwb, -, hwc⟩ := h.adj_of_le hs hR
  by_cases hwd : w = d
  ·
    subst hwd
    refine ⟨w, ?_⟩
    have m1 : Moves Δ {p | IsNGon Δ 3 p} [w, a, w, b, c, w] [w, b, c, w] := by
      simpa using Moves.backDel (C := {p | IsNGon Δ 3 p}) [] [b, c, w] hda
    have m2 : Moves Δ {p | IsNGon Δ 3 p} [w, b, c, w] [w] := by
      simpa using Moves.cycDel_mem (C := {p | IsNGon Δ 3 p}) [] [] [w, b, c, w]
        (isNGon_three hwb hbc hcd) rfl rfl
    exact m1.trans m2
  by_cases hadj : Δ.Adj w d
  ·
    have m1 : Moves Δ {p | IsNGon Δ 3 p} [d, a, w, b, c, d] [d, a, w, d, w, b, c, d] := by
      simpa using Moves.backIns (C := {p | IsNGon Δ 3 p}) [d, a] [b, c, d] hadj
    have m2 : Moves Δ {p | IsNGon Δ 3 p} [d, a, w, d, w, b, c, d] [d, w, b, c, d] := by
      simpa using Moves.cycDel_mem (C := {p | IsNGon Δ 3 p}) [] [w, b, c, d] [d, a, w, d]
        (isNGon_three hda haw hadj) rfl rfl
    refine inClosure_of_moves_of_inClosure (m1.trans m2) ?_
    exact inClosure_square_rotate' hadj.symm hwb hbc hcd (ih w b c d hwb hbc hcd hadj.symm hR)
  ·
    have hD2d : Dist2 Δ w d := ⟨hwd, hadj, a, haw.symm, hda.symm⟩
    have hD2c : Dist2 Δ w c := ⟨hwc, fun e => hcw e.symm, b, hwb, hbc⟩
    obtain ⟨x, hwx, hdx, hxc⟩ := h.b3 w d c hi hD2d hcd.symm hD2c
    have hxc' : Δ.Adj x c := by
      rcases hxc with e | e
      · exact absurd (e ▸ hwx) (fun e' => hcw e'.symm)
      · exact e
    have hsq : InClosure Δ {p | IsNGon Δ 3 p} [w, b, c, x, w] :=
      ih w b c x hwb hbc hxc'.symm hwx.symm hR
    have hp : IsPath Δ [w, b, c] :=
      ⟨List.cons_ne_nil _ _, by simp [List.isChain_cons_cons, hwb, hbc]⟩
    have hq : IsPath Δ [w, x, c] :=
      ⟨List.cons_ne_nil _ _, by simp [List.isChain_cons_cons, hwx, hxc']⟩
    have hcl : InClosure Δ {p | IsNGon Δ 3 p} ([w, x, c] ++ [w, b, c].reverse.tail) := by
      have := InClosure.reverse (isCycle_square hwb hbc hxc'.symm hwx.symm) hsq
      simpa using this
    have m1 : Moves Δ {p | IsNGon Δ 3 p} [d, a, w, b, c, d] [d, a, w, x, c, d] := by
      simpa using moves_context_of_inClosure hp hq rfl rfl hcl [d, a] [d]
    have m2 : Moves Δ {p | IsNGon Δ 3 p} [d, a, w, x, c, d] [d, a, w, x, d] := by
      simpa using moves_triangle_shortcut (C := {p | IsNGon Δ 3 p}) (fun p hp => hp) [d, a, w] []
        hxc' hcd hdx.symm
    refine inClosure_of_moves_of_inClosure (m1.trans m2) ?_
    have hnp : ¬ Perp Δ w d := fun hp => hp.elim hwd hadj
    have hsq' : InClosure Δ {p | IsNGon Δ 3 p} [w, x, d, a, w] :=
      inClosure_square_of_reachable hwx hdx.symm hda haw
        (reachable_of_induced_one h hN hi hnp ⟨hwx, hdx⟩ ⟨haw.symm, hda⟩)
    exact inClosure_square_rotate hdx.symm hda haw hwx
      (inClosure_square_rotate hwx hdx.symm hda haw hsq')

theorem inClosure_square_of_caseB (h : HypB Δ N R) (hN : 1 ≤ N) {s : ℕ} (hs : s ≤ N)
    (ih : SqLevel Δ R s) {a b c d b' d' w : V} (hb : comp Δ a b c b') (hd : comp Δ a d c d')
    (haw : Δ.Adj a w) (hcw : ¬ Δ.Adj c w) (hR : R s w b' c) (hi : induced Δ R 1 w d') :
    InClosure Δ {p | IsNGon Δ 3 p} [a, b, c, d, a] := by
  obtain ⟨hab', hcb'⟩ := comp_mem_right hb
  obtain ⟨had', hcd'⟩ := comp_mem_right hd
  refine inClosure_of_moves_of_inClosure (moves_square_replace hb hd) ?_
  have hwb : Δ.Adj w b' := (h.adj_of_le hs hR).1
  have hpent := inClosure_pentagon h hN hs ih hcb'.symm hcd' had'.symm haw hcw hR hi
  have m : Moves Δ {p | IsNGon Δ 3 p} [d', a, b', c, d'] [d', a, w, b', c, d'] := by
    simpa using (moves_triangle_shortcut (C := {p | IsNGon Δ 3 p}) (fun p hp => hp) [d'] [c, d']
      haw hwb hab').symm
  exact inClosure_square_rotate had'.symm hab' hcb'.symm hcd'
    (inClosure_of_moves_of_inClosure m hpent)

theorem sqLevel_succ_succ (h : HypB Δ N R) {s : ℕ} (hs : s + 2 ≤ N) (ih : SqLevel Δ R (s + 1)) :
    SqLevel Δ R (s + 2) := by
  intro a b c d hab hbc hcd hda hR
  have hN : 1 ≤ N := by omega
  by_cases hac : Perp Δ a c
  · exact inClosure_square_of_perp_ac hab hbc hcd hda hac
  by_cases hbd : Perp Δ b d
  · exact inClosure_square_of_perp_bd hab hbc hcd hda hbd
  have hac' : a ≠ c := fun e => hac (Or.inl e)
  have hna : ¬ Δ.Adj a c := fun e => hac (Or.inr e)
  have hR0b : ¬ R 0 a b c := fun h0 => hna ((h.zero a b c).mp h0).2.2
  have hRd : R N a d c := (h.top a d c).mpr ⟨hda.symm, hcd.symm, hac'⟩
  have hR0d : ¬ R 0 a d c := fun h0 => hna ((h.zero a d c).mp h0).2.2
  obtain ⟨w, d', hw, hd', hi⟩ := h.b2 (s + 1) (by omega) a b c d c hR hR0b hRd hR0d
  rw [Nat.min_eq_right (by omega : 1 ≤ s + 1)] at hi
  rcases hw with hwb | ⟨haw, b', hb', hRw⟩
  · exact inClosure_square_of_caseA h hN hwb hd' hi
  · obtain ⟨-, hb'w, -⟩ := h.adj_of_le (by omega) hRw
    by_cases hcw : Δ.Adj c w
    · exact inClosure_square_of_caseA h hN
        (comp_trans hb' (comp_of_adj (comp_mem_right hb') ⟨haw, hcw⟩ hb'w)) hd' hi
    · exact inClosure_square_of_caseB h hN (by omega) ih hb' hd' haw hcw (h.symm _ _ _ _ hRw) hi

theorem sqLevel_zero (h : HypB Δ N R) : SqLevel Δ R 0 := fun a b c d hab hbc hcd hda hR =>
  inClosure_square_of_perp_ac hab hbc hcd hda (Or.inr ((h.zero a b c).mp hR).2.2)

theorem sqLevel_one (h : HypB Δ N R) (hN : 1 ≤ N) : SqLevel Δ R 1 := by
  intro a b c d hab hbc hcd hda hR
  by_cases hp : Perp Δ a c
  · exact inClosure_square_of_perp_ac hab hbc hcd hda hp
  · exact inClosure_square_of_reachable hab hbc hcd hda
      (reachable_of_induced_one h hN (Or.inr ⟨b, hR⟩) hp ⟨hab, hbc.symm⟩ ⟨hda.symm, hcd⟩)

theorem sqLevel_le (h : HypB Δ N R) : ∀ t, t ≤ N → SqLevel Δ R t
  | 0, _ => sqLevel_zero h
  | 1, ht => sqLevel_one h ht
  | s + 2, ht => sqLevel_succ_succ h ht (sqLevel_le h (s + 1) (by omega))

theorem inClosure_square_of_hypB (h : HypB Δ N R) {a b c d : V} (hab : Δ.Adj a b)
    (hbc : Δ.Adj b c) (hcd : Δ.Adj c d) (hda : Δ.Adj d a) :
    InClosure Δ {p | IsNGon Δ 3 p} [a, b, c, d, a] := by
  by_cases hac : a = c
  · exact inClosure_square_of_perp_ac hab hbc hcd hda (Or.inl hac)
  · exact sqLevel_le h N le_rfl a b c d hab hbc hcd hda ((h.top a b c).mpr ⟨hab, hbc, hac⟩)

theorem triangulable_of_fourGenerated (h4 : FourGenerated Δ)
    (hsq : ∀ a b c d : V, Δ.Adj a b → Δ.Adj b c → Δ.Adj c d → Δ.Adj d a →
      InClosure Δ {p | IsNGon Δ 3 p} [a, b, c, d, a]) : Triangulable Δ := by
  intro c hc
  refine (h4 c hc).of_rotRev ?_
  have key : ∀ d, (IsNGon Δ 3 d ∨ IsNGon Δ 4 d) → ∀ w, d.head? = some w →
      Moves Δ {p | IsNGon Δ 3 p} d [w] := by
    rintro d (hd | hd) w hw
    · simpa using Moves.cycDel_mem (C := {p | IsNGon Δ 3 p}) [] [] d hd hw
        (by rw [← hd.1.2, hw])
    · obtain ⟨a, b, c', d', rfl, hab, hbc, hcd, hda, -, -⟩ := hd.four
      exact (hsq a b c' d' hab hbc hcd hda).moves_head hw
  rintro d ⟨e, he, hr | hr⟩ w hw -
  · rcases he with he | he
    · exact key d (Or.inl (he.rotation hr)) w hw
    · exact key d (Or.inr (he.rotation hr)) w hw
  · rcases he with he | he
    · exact key d (Or.inl (he.reverse.rotation hr)) w hw
    · exact key d (Or.inr (he.reverse.rotation hr)) w hw

theorem triangulable_of_hypB_of_fourGenerated (h : HypB Δ N R) (h4 : FourGenerated Δ) :
    Triangulable Δ :=
  triangulable_of_fourGenerated h4 fun _ _ _ _ hab hbc hcd hda =>
    inClosure_square_of_hypB h hab hbc hcd hda

theorem triangulable_of_hypB (h : HypB Δ N R) : Triangulable Δ :=
  triangulable_of_hypB_of_fourGenerated h (fourGenerated_of_hypA (hypA_of_hypB h))

end CFSG.Quasithin.H13.AS91
