module

public import CFSG.Certificates.PresentationLetters

public section

namespace CFSG.Timmesfeld.Moufang.Exc

open CFSG.Certificates.CosetEnumeration

variable {G : Type*} [Group G]

@[expose] def coverWalk (L : ℕ) (fx fy ffi : ℕ → ℕ) : ℕ → List ℕ → ℕ
  | cur, [] => cur
  | cur, c :: w => coverWalk L fx fy ffi (refNext fx fy (ffi (cur * L + c))) w

@[expose] noncomputable def fElt (gen : ℕ → G) (L' : ℕ) (pl fx fc fy : ℕ → ℕ) (f : ℕ) : G :=
  rep gen L' pl (fx f) * gen (fc f) * (rep gen L' pl (fy f))⁻¹

section Walk

variable {gen : ℕ → G} {L' : ℕ} {pl fx fc fy inv refs : ℕ → ℕ}

private theorem walk_cons_eq' (gen : ℕ → G) (L' : ℕ) (pl : ℕ → ℕ) (cur c y s : ℕ) (w : List ℕ) :
    rep gen L' pl cur * evalWord gen (c :: w) * (rep gen L' pl s)⁻¹ =
      (rep gen L' pl cur * gen c * (rep gen L' pl y)⁻¹) *
        (rep gen L' pl y * evalWord gen w * (rep gen L' pl s)⁻¹) := by
  rw [evalWord_cons]; group

theorem ref_mem' {H : Subgroup G} {f r cur c : ℕ}
    (htrue : ∀ g < f, fElt gen L' pl fx fc fy g ∈ H) (hc : gen (inv c) = (gen c)⁻¹)
    (h : refOK fx fc fy inv f r cur c = true) :
    rep gen L' pl cur * gen c * (rep gen L' pl (refNext fx fy r))⁻¹ ∈ H := by
  unfold refOK at h
  rw [Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨hlt, h⟩ := h
  have hg := htrue _ hlt
  unfold refNext
  rcases Nat.mod_two_eq_zero_or_one r with hr | hr
  · have hb : Nat.beq (Nat.mod r 2) 0 = true := by rw [Nat.beq_eq]; exact hr
    rw [hb, Bool.cond_true, Bool.and_eq_true] at h
    rw [hb, Bool.cond_true]
    rw [fElt, Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2] at hg
    exact hg
  · have hb : Nat.beq (Nat.mod r 2) 0 = false := by
      cases hh : Nat.beq (Nat.mod r 2) 0 with
      | false => rfl
      | true =>
        have : r % 2 = 0 := Nat.eq_of_beq_eq_true hh
        omega
    rw [hb, Bool.cond_false, Bool.and_eq_true] at h
    rw [hb, Bool.cond_false]
    have := H.inv_mem hg
    rw [fElt, Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2, hc] at this
    simpa [mul_assoc] using this

theorem walk_mem_of_lt' {H : Subgroup G} {f t o s : ℕ}
    (htrue : ∀ g < f, fElt gen L' pl fx fc fy g ∈ H) :
    ∀ (w : List ℕ) (q cur : ℕ), (∀ c ∈ w, gen (inv c) = (gen c)⁻¹) →
      walkOK fx fc fy inv refs f t o s q cur w = true → t < q →
      rep gen L' pl cur * evalWord gen w * (rep gen L' pl s)⁻¹ ∈ H := by
  intro w
  induction w with
  | nil =>
    intro q cur _ h _
    have hcur : cur = s := Nat.eq_of_beq_eq_true h
    subst hcur
    simp
  | cons c w ih =>
    intro q cur hw h htq
    simp only [walkOK] at h
    have hb : Nat.beq q t = false := by
      cases hh : Nat.beq q t with
      | false => rfl
      | true => exact absurd (Nat.eq_of_beq_eq_true hh) (by omega)
    rw [hb, Bool.cond_false, Bool.and_eq_true] at h
    obtain ⟨href, hrest⟩ := h
    rw [walk_cons_eq' gen L' pl cur c (refNext fx fy (refs (Nat.add o q))) s w]
    exact H.mul_mem (ref_mem' htrue (hw c (by simp)) href)
      (ih (Nat.succ q) _ (fun c' hc' => hw c' (by simp [hc'])) (by simpa using hrest) (by omega))

theorem walk_mem_iff' {H : Subgroup G} {f t o s : ℕ}
    (htrue : ∀ g < f, fElt gen L' pl fx fc fy g ∈ H) :
    ∀ (w : List ℕ) (q cur : ℕ), (∀ c ∈ w, gen (inv c) = (gen c)⁻¹) →
      walkOK fx fc fy inv refs f t o s q cur w = true → q ≤ t → t < q + w.length →
      (rep gen L' pl cur * evalWord gen w * (rep gen L' pl s)⁻¹ ∈ H ↔
        fElt gen L' pl fx fc fy f ∈ H) := by
  intro w
  induction w with
  | nil => intro q cur _ _ h1 h2; simp at h2; omega
  | cons c w ih =>
    intro q cur hw h hqt htl
    have hw' : ∀ c' ∈ w, gen (inv c') = (gen c')⁻¹ := fun c' hc' => hw c' (by simp [hc'])
    simp only [walkOK] at h
    rcases Nat.eq_or_lt_of_le hqt with rfl | hlt'
    · rw [show Nat.beq q q = true from Nat.beq_refl q, Bool.cond_true] at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨hx, hc⟩, hrest⟩ := h
      have hx' := Nat.eq_of_beq_eq_true hx
      have hc' := Nat.eq_of_beq_eq_true hc
      have hr := walk_mem_of_lt' (H := H) htrue w (Nat.succ q) (fy f) hw' (by simpa using hrest)
        (Nat.lt_succ_self q)
      rw [walk_cons_eq' gen L' pl cur c (fy f) s w]
      have hfe : rep gen L' pl cur * gen c * (rep gen L' pl (fy f))⁻¹ =
          fElt gen L' pl fx fc fy f := by rw [fElt, hx', hc']
      rw [hfe]
      exact ⟨fun hm => by
        have h2 := H.mul_mem hm (H.inv_mem hr)
        rwa [mul_inv_cancel_right] at h2, fun hm => H.mul_mem hm hr⟩
    · have hb : Nat.beq q t = false := by
        cases hh : Nat.beq q t with
        | false => rfl
        | true => exact absurd (Nat.eq_of_beq_eq_true hh) (by omega)
      rw [hb, Bool.cond_false, Bool.and_eq_true] at h
      obtain ⟨href, hrest⟩ := h
      have hg := ref_mem' htrue (hw c (by simp)) href
      rw [walk_cons_eq' gen L' pl cur c (refNext fx fy (refs (Nat.add o q))) s w,
        ← ih (Nat.succ q) _ hw' (by simpa using hrest) hlt' (by simp at htl; omega)]
      exact ⟨fun hm => by
        have h2 := H.mul_mem (H.inv_mem hg) hm
        rwa [inv_mul_cancel_left] at h2, fun hm => H.mul_mem hg hm⟩

end Walk

theorem factElt_mem_of_factsOK {H : Subgroup G} {gen : ℕ → G} {L N F : ℕ}
    {fx fc fy kind wi fs ft fo refs pl inv : ℕ → ℕ} {rels subs : List (List ℕ)}
    (hinv : ∀ c ≤ L, gen (inv c) = (gen c)⁻¹)
    (hlet : ∀ w ∈ rels ++ subs, ∀ c ∈ w, c ≤ L)
    (hrels : ∀ w ∈ rels, evalWord gen w = 1) (hsubs : ∀ w ∈ subs, evalWord gen w ∈ H)
    (hfacts : factsOK N (L + 1) fx fc fy kind wi fs ft fo refs pl inv rels subs 0 F = true) :
    ∀ f < F, fElt gen (L + 1) pl fx fc fy f ∈ H := by
  set L' := L + 1
  have hok : ∀ f < F, factOK N L' fx fc fy kind wi fs ft fo refs pl inv rels subs f = true :=
    fun f hf => factOK_of_factsOK hfacts f (Nat.zero_le f) (by simpa using hf)
  have hwinv : ∀ w ∈ rels ++ subs, ∀ c ∈ w, gen (inv c) = (gen c)⁻¹ :=
    fun w hw c hc => hinv c (hlet w hw c hc)
  intro f
  induction f using Nat.strong_induction_on with
  | _ f ih =>
    intro hf
    have h := hok f hf
    unfold factOK at h
    simp only [Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨_, _, h⟩ := h
    have ih' : ∀ g < f, fElt gen L' pl fx fc fy g ∈ H :=
      fun g hg => ih g hg (lt_trans hg hf)
    split at h
    · simp only [Bool.and_eq_true, Nat.blt_eq] at h
      obtain ⟨hpl, hcL, hxy⟩ := h
      have hpl' : pl (fy f) = fx f * L' + fc f := by simpa using Nat.eq_of_beq_eq_true hpl
      have hL0 : 0 < L' := by omega
      have hdiv : pl (fy f) / L' = fx f := by
        rw [hpl', Nat.add_comm, Nat.add_mul_div_right _ _ hL0, Nat.div_eq_of_lt hcL,
          Nat.zero_add]
      have hmod : pl (fy f) % L' = fc f := by
        rw [hpl', Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hcL]
      have hy0 : 0 < fy f := lt_of_le_of_lt (Nat.zero_le _) hxy
      rw [fElt, rep_eq gen L' pl hy0 (by rw [hdiv]; exact hxy), hdiv, hmod]
      simp
    · simp only [Bool.and_eq_true, Nat.blt_eq] at h
      obtain ⟨h1, h2, h3⟩ := h
      have hwm := wordAt_mem h1
      rw [← walk_mem_iff' (H := H) ih' _ 0 (fs f) (hwinv _ (List.mem_append_left _ hwm)) h3
        (Nat.zero_le _) (by simpa using h2), hrels _ hwm]
      simp
    · simp only [Bool.and_eq_true, Nat.blt_eq] at h
      obtain ⟨h1, h2, h3⟩ := h
      have hwm := wordAt_mem h1
      rw [← walk_mem_iff' (H := H) ih' _ 0 0 (hwinv _ (List.mem_append_right _ hwm)) h3
        (Nat.zero_le _) (by simpa using h2), rep_zero]
      simpa using hsubs _ hwm
    · exact absurd h (by simp)

theorem walk_mem_of_coverOK {H : Subgroup G} {gen : ℕ → G} {L N F : ℕ}
    {fx fc fy pl inv ffi : ℕ → ℕ} {live : ℕ → Bool}
    (hinv : ∀ c ≤ L, gen (inv c) = (gen c)⁻¹)
    (htrue : ∀ f < F, fElt gen (L + 1) pl fx fc fy f ∈ H)
    (hcover : coverOK N L F fx fc fy inv ffi live 0 (N * L) = true) :
    ∀ (w : List ℕ) (cur : ℕ), (∀ c ∈ w, c < L) → cur < N → live cur = true →
      rep gen (L + 1) pl cur * evalWord gen w *
        (rep gen (L + 1) pl (coverWalk L fx fy ffi cur w))⁻¹ ∈ H := by
  intro w
  induction w with
  | nil => intro cur _ _ _; simp [coverWalk]
  | cons c w ih =>
    intro cur hw hcur hl
    have hc : c < L := hw c (by simp)
    have hL : 0 < L := lt_of_le_of_lt (Nat.zero_le c) hc
    have he : cur * L + c < N * L := by
      calc cur * L + c < cur * L + L := by omega
        _ = (cur + 1) * L := by ring
        _ ≤ N * L := Nat.mul_le_mul_right _ hcur
    have hdiv : (cur * L + c) / L = cur := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hL, Nat.div_eq_of_lt hc, Nat.zero_add]
    have hmod : (cur * L + c) % L = c := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]
    obtain ⟨h1, h2, h3⟩ := cover_of_coverOK hcover (cur * L + c) (Nat.zero_le _)
      (by simpa using he) (by rw [hdiv]; exact hl)
    rw [hdiv, hmod] at h1
    have hfe := ref_mem' htrue (hinv c (Nat.le_of_lt hc)) h1
    have hrest := ih _ (fun c' hc' => hw c' (by simp [hc'])) h3 h2
    have key := H.mul_mem hfe hrest
    simp only [coverWalk, evalWord_cons]
    convert key using 1
    group

theorem evalWord_mem_of_coverWalk {H : Subgroup G} {gen : ℕ → G} {L N F : ℕ}
    {fx fc fy kind wi fs ft fo refs pl ffi inv : ℕ → ℕ} {live : ℕ → Bool}
    {rels subs : List (List ℕ)}
    (hinv : ∀ c ≤ L, gen (inv c) = (gen c)⁻¹)
    (hlet : ∀ w ∈ rels ++ subs, ∀ c ∈ w, c ≤ L)
    (hrels : ∀ w ∈ rels, evalWord gen w = 1) (hsubs : ∀ w ∈ subs, evalWord gen w ∈ H)
    (hlive0 : live 0 = true) (hN : 0 < N)
    (hfacts : factsOK N (L + 1) fx fc fy kind wi fs ft fo refs pl inv rels subs 0 F = true)
    (hcover : coverOK N L F fx fc fy inv ffi live 0 (N * L) = true)
    {w : List ℕ} (hw : ∀ c ∈ w, c < L) (hwalk : coverWalk L fx fy ffi 0 w = 0) :
    evalWord gen w ∈ H := by
  have htrue := factElt_mem_of_factsOK hinv hlet hrels hsubs hfacts
  have := walk_mem_of_coverOK hinv htrue hcover w 0 hw hN hlive0
  rwa [hwalk, rep_zero, one_mul, inv_one, mul_one] at this

theorem mk_eq_one_of_coverWalk {m : ℕ} {rels : Set (FreeGroup (Fin m))} {N F : ℕ}
    {fx fc fy kind wi fs ft fo refs pl ffi : ℕ → ℕ} {live : ℕ → Bool}
    (relWords : List (List (Fin m × Bool))) (ws : List (List ℕ))
    (hrels : ∀ w ∈ relWords, FreeGroup.mk w ∈ rels)
    (hws : derivedOK (2 * m) (invLetter m) (codes relWords) ws = true)
    (hlive0 : live 0 = true) (hN : 0 < N)
    (hfacts : factsOK N (2 * m + 1) fx fc fy kind wi fs ft fo refs pl (invLetter m) ws [] 0 F =
      true)
    (hcover : coverOK N (2 * m) F fx fc fy (invLetter m) ffi live 0 (N * (2 * m)) = true)
    (w : List (Fin m × Bool))
    (hwalk : coverWalk (2 * m) fx fy ffi 0 (w.map letterCode) = 0) :
    PresentedGroup.mk rels (FreeGroup.mk w) = 1 := by
  have hbase : ∀ r ∈ codes relWords, evalWord (presLetter rels) r = 1 := by
    intro r hr
    simp only [codes, List.mem_map] at hr
    obtain ⟨v, hv, rfl⟩ := hr
    rw [evalWord_presLetter]
    exact PresentedGroup.one_of_mem (hrels v hv)
  have hlet : ∀ v ∈ ws ++ [], ∀ c ∈ v, c ≤ 2 * m := by
    intro v hv c hc
    rw [List.append_nil] at hv
    simp only [derivedOK, List.all_eq_true, Bool.and_eq_true, Nat.blt_eq] at hws
    exact Nat.lt_succ_iff.mp ((hws v hv).1 c hc)
  have hw : ∀ c ∈ w.map letterCode, c < 2 * m := by
    intro c hc
    obtain ⟨⟨i, b⟩, -, rfl⟩ := List.mem_map.mp hc
    simp only [letterCode]
    have := i.isLt
    split <;> omega
  have h := evalWord_mem_of_coverWalk (H := ⊥) (gen := presLetter rels) (inv := invLetter m)
    (fun c hc => presLetter_invLetter rels hc) hlet
    (evalWord_of_derivedOK (presLetter_eps rels)
      (fun c hc => presLetter_invLetter rels (Nat.le_of_lt hc)) hbase hws)
    (by simp) hlive0 hN hfacts hcover hw hwalk
  rwa [evalWord_presLetter, Subgroup.mem_bot] at h

end CFSG.Timmesfeld.Moufang.Exc
