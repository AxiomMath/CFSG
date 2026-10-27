module

public import Certificates.Certificate21168
public import Certificates.Certificate21169
public import Certificates.Certificate21245
public import Certificates.Certificate21246
public import Certificates.Certificate21247
public import Certificates.Certificate21248
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native

theorem glNJ1_check : Native.glNJ1OK = true :=
  Certificates.certificate21168

theorem glNJ2_check : Native.glNJ2OK = true :=
  Certificates.certificate21169

theorem glNJ3_check : Native.glNJ3OK = true :=
  Certificates.certificate21245

theorem glNJChain_check : Native.glNJChainOK = true :=
  Certificates.certificate21246

theorem glNJ4_check : Native.glNJ4OK = true :=
  Certificates.certificate21247

theorem glNJFix_check : Native.glNJFixOK = true :=
  Certificates.certificate21248

theorem list_getElem!_mem {l : List ℕ} {k : ℕ} (hk : k < l.length) : l[k]! ∈ l := by
  rw [getElem!_pos l k hk]
  exact List.getElem_mem hk

section One

theorem glNJ1_parts : Native.glNJGenOK = true ∧ Native.glNJInjOK = true ∧
    Native.glNJOmOK = true := by
  have h := glNJ1_check
  simp only [Native.glNJ1OK, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem glNJGen_spec : (∀ k < 3, ∀ l ∈ Native.glNJGw[k]!, l < 22) ∧
    (∀ k < 3, Native.glNJTw[k]! < 1024) ∧
    Native.commRows (Native.glNJG 0) Native.glZ = true ∧
    Native.commRows (Native.glNJG 1) Native.glZ = true ∧
    ∀ k < 3, Native.glWTabOK (Native.glNJG k) Native.glNJTab[k]! = true ∧
      Native.glWTabOK (Native.glNJGt k) Native.glNJTab[k]! = true := by
  have h := glNJ1_parts.1
  simp only [Native.glNJGenOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq, Array.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hs, hw⟩, -⟩, hl⟩, htw⟩, h0⟩, h1⟩, ht⟩ := h
  refine ⟨fun k hk l hl' => ?_, fun k hk => htw _ (list_getElem!_mem (by rw [hl]; exact hk)),
    h0, h1, ht⟩
  rw [getElem!_pos Native.glNJGw k (by rw [hs]; exact hk)] at hl'
  exact hw k (by rw [hs]; exact hk) l hl'

theorem glNJOm_spec : Native.glNJOm.length = 77 ∧
    (∀ k < 77, 0 < Native.glNJOm[k]! ∧ Native.glNJOm[k]! < 1024) ∧
    Native.glNJOm[0]! = 1 ∧
    (∀ i < 77, ∀ j < 77, Native.glNJOm[i]! = Native.glNJOm[j]! → i = j) ∧
    Native.glNJPerm.size = 3 ∧
    (∀ i < 3, (Native.glNJPerm[i]!).size = 77 ∧ ∀ k < 77, (Native.glNJPerm[i]!)[k]! < 77 ∧
      Native.glNJT i Native.glNJOm[k]! = Native.glNJOm[(Native.glNJPerm[i]!)[k]!]!) ∧
    (∀ k < 77, (∀ l ∈ Native.glNJConj[k]!, l < 3) ∧
      (Native.glNJWordP Native.glNJConj[k]!)[0]! = k) ∧
    ∀ i < 10, (∀ k ∈ Native.glNJSpan[i]!, k < 77) ∧
      Native.glNJSpan[i]!.foldl (fun acc k => acc ^^^ Native.glNJOm[k]!) 0 = 2 ^ i := by
  have h := glNJ1_parts.2.2
  simp only [Native.glNJOmOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq, Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hl, hlt⟩, h0⟩, hnd⟩, hps⟩, hp⟩, -⟩, hc⟩, -⟩, hsp⟩ := h
  refine ⟨hl, fun k hk => hlt _ (list_getElem!_mem (by rw [hl]; exact hk)), h0, ?_, hps, hp,
    hc, hsp⟩
  intro i hi j hj e
  by_contra hij
  exact (hnd i hi j hj).resolve_left hij e

end One

theorem glNJFix_spec {m : ℕ} (hm : m < 1024) (h0 : m ≠ 0)
    (hmem : m ∉ Native.glNJOm) : Native.glNJFixR (Native.glJcR m) ≠ 284 := by
  have h := glNJFix_check
  simp only [Native.glNJFixOK, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    bne_iff_ne, ne_eq, List.contains_iff_mem] at h
  exact (h m hm).resolve_left (by rintro (e | e); exacts [h0 e, hmem e])

theorem glNJJT_get {m : ℕ} (hm : m < 1024) :
    Native.glNJJT[m]! = transposeRows 22 (Native.glJcR m) := by
  rw [Native.glNJJT, getElem!_pos _ m (by rw [Array.size_ofFn]; exact hm), Array.getElem_ofFn]

theorem colActT_glNJJT {m : ℕ} (hm : m < 1024) (v : ℕ) :
    Native.colActT Native.glNJJT[m]! v = Native.colAct (Native.glJcR m) v := by
  rw [glNJJT_get hm]
  rfl

section Two

theorem glNJ2_parts : Native.glNJPtOK Native.glNJJT = true ∧
    Native.glNJO77OK Native.glNJJT = true := by
  have h := glNJ2_check
  simp only [Native.glNJ2OK, Bool.and_eq_true] at h
  exact h

theorem glNJPt_spec : (∀ k < 3, Native.glMaps (Native.glNJG k) 1 1 = true) ∧
    (∀ m < 1024, m ≠ 0 →
      Native.colAct (Native.glJcR m) CFSG.Sporadic.Co2Cert.co2PackedVecs[1]! ≠
        CFSG.Sporadic.Co2Cert.co2PackedVecs[1]!) ∧
    (∀ x < 2300, Native.glNJPtJ[x]! < 1024 ∧
      (Native.glMaps (Native.glJcR Native.glNJPtJ[x]!) 1 x = true ∨
        Native.glNJPtJ[x]! ≠ 0 ∧ Native.glMaps (Native.glJcR Native.glNJPtJ[x]!) x x = true)) ∧
    Native.glNJBasis.length = 22 ∧
    (∀ x ∈ Native.glNJBasis, x < 2300 ∧
      Native.glMaps (Native.glJcR Native.glNJPtJ[x]!) 1 x = true) ∧
    mulRows 22 (Native.glNJBasis.toArray.map fun x => CFSG.Sporadic.Co2Cert.co2PackedVecs[x]!)
      Native.glNJBasisInv = idRows 22 := by
  have h := glNJ2_parts.1
  simp only [Native.glNJPtOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.mem_range, decide_eq_true_eq, Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, -⟩, h4⟩, h5⟩, h6⟩, -⟩, h8⟩ := h
  refine ⟨h1, fun m hm h0 => ?_, fun x hx => ⟨(h4 x hx).1, ?_⟩, h5, fun x hx => ?_, h8⟩
  · have e := (h2 m hm).resolve_left h0
    rwa [colActT_glNJJT hm] at e
  · have hlt := (h4 x hx).1
    rcases (h4 x hx).2 with e | ⟨e0, e⟩
    · left
      rw [Native.glMaps, beq_iff_eq, ← colActT_glNJJT hlt]
      exact e
    · right
      refine ⟨e0, ?_⟩
      rw [Native.glMaps, beq_iff_eq, ← colActT_glNJJT hlt]
      exact e
  · obtain ⟨hx2, e⟩ := h6 x hx
    refine ⟨hx2, ?_⟩
    have hlt : Native.glNJPtJ[x]! < 1024 := (h4 x hx2).1
    rw [Native.glMaps, beq_iff_eq, ← colActT_glNJJT hlt]
    exact e

theorem glNJO77_spec : (∀ x ∈ Native.glNJO77, x < 2300) ∧
    (∀ k < 3, Native.glPermOK (Native.glNJGt k) (Native.glNJPermR (Native.glNJGt k)) = true ∧
      ∀ x ∈ Native.glNJO77, (Native.glNJPermR (Native.glNJGt k))[x]! ∈ Native.glNJO77) ∧
    ∀ m < 1024, m ≠ 0 → Native.glNJO77Wx[m]! ∈ Native.glNJO77 ∧
      Native.glNJO77Wy[m]! < 2300 ∧ Native.glNJO77Wy[m]! ∉ Native.glNJO77 ∧
      Native.glMaps (Native.glJcR m) Native.glNJO77Wx[m]! Native.glNJO77Wy[m]! = true := by
  have h := glNJ2_parts.2
  simp only [Native.glNJO77OK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.mem_range, decide_eq_true_eq, Bool.or_eq_true, List.contains_iff_mem,
    Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, -⟩, -⟩, h5⟩ := h
  refine ⟨h1, h2, fun m hm h0 => ?_⟩
  obtain ⟨⟨⟨hx, hy⟩, hny⟩, e⟩ := (h5 m hm).resolve_left h0
  refine ⟨hx, hy, ?_, ?_⟩
  · intro hmem
    have := List.contains_iff_mem.2 hmem
    rw [hny] at this
    exact Bool.false_ne_true this
  · rw [Native.glMaps, beq_iff_eq, ← colActT_glNJJT hm]
    exact e

end Two

theorem glNJ3_spec : Native.glNJNbr.size = 77 ∧
    Native.glNJBase.length = 8 ∧ Native.glNJBounds.length = 8 ∧
    (∀ s ∈ Native.glNJBase, s < 77) ∧
    (∀ a < 77, (∀ b ∈ Native.glNJNbr[a]!, b < 77) ∧
      CFSG.Certificates.Native.strictIncr Native.glNJNbr[a]! = true) ∧
    (∀ s < 8, Native.glNJClassCount (Native.glNJColour Native.glNJNbr s) Native.glNJBase[s]! =
      Native.glNJBounds[s]!) ∧
    (Native.glNJColour Native.glNJNbr 8).size = 77 ∧
    (Native.glNJColour Native.glNJNbr 8).toList.Nodup := by
  have h := glNJ3_check
  simp only [Native.glNJ3OK, Native.glNJRefOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.mem_range, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

section Four

theorem glNJ4_parts : Native.glNJH1OK = true ∧ Native.glNJFusOK = true := by
  have h := glNJ4_check
  simp only [Native.glNJ4OK, Bool.and_eq_true] at h
  exact h

theorem glNJWord_congr {g g' : ℕ → Array ℕ} :
    ∀ w : List ℕ, (∀ k ∈ w, g k = g' k) → Native.glNJWord g w = Native.glNJWord g' w
  | [], _ => rfl
  | k :: w, hw => by
    have ih := glNJWord_congr w fun j hj => hw j (List.mem_cons_of_mem _ hj)
    simp only [Native.glNJWord, List.foldr_cons] at ih ⊢
    rw [hw k List.mem_cons_self, ih]

theorem glNJH1_spec : (∀ r ∈ Native.glNJRels, (∀ k ∈ r, k < 2) ∧
      Native.glNJWord Native.glNJG r = idRows 22) ∧
    (∀ x < 1024, Native.glNJNrm[x]! < 1024 ∧
      (x ^^^ Native.glNJNrm[x]! ^^^ Native.glNJT 0 Native.glNJNrm[x]! = 0 ∨
        x ^^^ Native.glNJNrm[x]! ^^^ Native.glNJT 0 Native.glNJNrm[x]! = 64)) ∧
    ∀ c₁, (c₁ = 0 ∨ c₁ = 64) → ∀ c₂ < 1024, (∀ r ∈ Native.glNJRels, Native.glNJF c₁ c₂ r = 0) →
      c₁ = 0 ∧ (c₂ = 0 ∨ c₂ = 18 ∨ c₂ = 76 ∨ c₂ = 94) := by
  have h := glNJ4_parts.1
  simp only [Native.glNJH1OK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true', List.contains_iff_mem,
    List.mem_cons, List.not_mem_nil, or_false] at h
  obtain ⟨⟨⟨hr, -⟩, hn⟩, hc⟩ := h
  refine ⟨fun r hr' => ⟨(hr r hr').1, ?_⟩, hn, fun c₁ hc₁ c₂ hc₂ hrel => ?_⟩
  · rw [← (hr r hr').2]
    refine glNJWord_congr r fun k hk => ?_
    have := (hr r hr').1 k hk
    rcases Nat.lt_succ_iff_lt_or_eq.1 this with h0 | h1
    · rw [Nat.lt_one_iff.1 h0]
      rfl
    · subst h1
      rfl
  · rcases (hc c₁ hc₁ c₂ hc₂) with e | e
    · exfalso
      rw [Bool.eq_false_iff] at e
      apply e
      simp only [List.all_eq_true, beq_iff_eq]
      exact hrel
    · exact e

theorem glNJFus_spec : (∀ k ∈ Native.glNJFusA, k < 3) ∧ (∀ k ∈ Native.glNJFusX, k < 2) ∧
    (∀ k ∈ Native.glNJFusXp, k < 2) ∧
    mulRows 22 (Native.glNJWord Native.glNJG Native.glNJFusX)
        (Native.glNJWord Native.glNJG Native.glNJFusX) = idRows 22 ∧
    Native.glNJWord Native.glNJG Native.glNJFusX ≠ idRows 22 ∧
    mulRows 22 (Native.glNJWord Native.glNJG Native.glNJFusA)
        (Native.glNJWord Native.glNJG Native.glNJFusXp) =
      mulRows 22 (Native.glNJWord Native.glNJG Native.glNJFusX)
        (Native.glNJWord Native.glNJG Native.glNJFusA) ∧
    ∀ s ∈ [18, 94], Native.glNJFixR (Native.glNJWord (Native.glNJGs s) Native.glNJFusX) ≠
      Native.glNJFixR (Native.glNJWord (Native.glNJGs s) Native.glNJFusXp) := by
  have h := glNJ4_parts.2
  simp only [Native.glNJFusOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    bne_iff_ne, ne_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, -⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  refine ⟨h1, h2, h3, h5, h6, h7, fun s hs => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · obtain ⟨⟨e1, e2⟩, e3⟩ := h8 0 (by norm_num)
    simp only [List.getElem!_cons_zero, Nat.mul_zero, Nat.zero_add] at e1 e2 e3
    rw [e1, e2]
    exact e3
  · obtain ⟨⟨e1, e2⟩, e3⟩ := h8 1 (by norm_num)
    simp only [List.getElem!_cons_succ, List.getElem!_cons_zero, Nat.mul_one] at e1 e2 e3
    rw [e1, e2]
    exact e3

end Four

end CFSG.Sporadic.Co2Smith
