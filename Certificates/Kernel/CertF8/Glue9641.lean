module

public import Certificates.Data.Kernel.CertF8.D48
public import CFSG.Certificates.Kernel.CertF8.F512Sound
import Certificates.Kernel.CertF8.Check9641

public section

namespace Certificates.Kernel.CertF8.C9641

open CFSG.KC.CertF8 CFSG.KC.CertF8.D48 CFSG.AGLEmbedding.ChevOuterD48

theorem ch9641Let : ∀ k : Fin 24, codeA (letterArr k.val) = letK.getD k.val oneK := by
  decide +kernel

theorem ch9641One : codeA oneArr = oneK := by
  decide +kernel

theorem letV_eq {β : Sort _} (y : ℕ) (k : ℕ → β) : letV y k = k y := by
  cases y <;> rfl

theorem letQ_eq {β : Sort _} (p : ℕ × ℕ) (k : ℕ × ℕ → β) : letQ p k = k p := by
  simp only [letQ, letV_eq]

theorem eqQ_eq (x y : ℕ × ℕ) : eqQ x y = decide (x = y) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  simp only [eqQ, Bool.and_eq_true, Nat.beq_eq, Prod.ext_iff]

theorem eq_code {p q : Pr} (hp : p.1.size = 64) (hq : q.1.size = 64) :
    p = q ↔ codePr p = codePr q :=
  ⟨fun h => h ▸ rfl, codePr_inj hp hq⟩

theorem codePr_oneP : codePr oneP = oneQ := by
  simp only [codePr, oneP, oneQ, ch9641One]

theorem codeA_letterArr (k : ℕ) : codeA (letterArr k) = letK.getD k oneK := by
  by_cases hk : k < 24
  · exact ch9641Let ⟨k, hk⟩
  · have h1 : letterArr k = oneArr := by
      rw [letterArr, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by simp [letterTable]; omega)]
      rfl
    have h2 : letK.getD k oneK = oneK := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [letK]; omega)]
      rfl
    rw [h1, h2, ch9641One]

theorem codePr_symP (s : ℕ) : codePr (symP s) = symQ s := by
  unfold symP symQ
  split_ifs
  · simp only [codePr, codeA_letterArr]
  · simp only [codePr, ch9641One]

theorem codePr_wordP (w : List ℕ) : codePr (wordP w) = wordQ w := by
  induction w with
  | nil => exact codePr_oneP
  | cons s w ih =>
    change codePr (mulP (symP s) (wordP w)) = mulPr (symQ s) (wordQ w)
    rw [codePr_mulP, codePr_symP, ih]

theorem codePr_powP (p : Pr) (n : ℕ) : codePr (powP p n) = powQ (codePr p) n := by
  induction n with
  | zero => exact codePr_oneP
  | succ n ih =>
    change codePr (mulP p (powP p n)) = mulPr (codePr p) (powQ (codePr p) n)
    rw [codePr_mulP, ih]

theorem codePr_eP (i : ℕ) : codePr (eP i) = ePQ i := codePr_wordP _

theorem codePr_hypX (h : ℕ) : codePr (hypX h) = hypXQ (ePQ 0) (ePQ 1) h := by
  rcases h with _ | _ | _ | _ | h
  · simp [hypX, hypXQ, codePr_eP]
  · simp [hypX, hypXQ, codePr_eP]
  · simp [hypX, hypXQ, codePr_eP]
  · simp [hypX, hypXQ, codePr_eP, codePr_mulP]
  · simp [hypX, hypXQ, codePr_eP, codePr_mulP, codePr_powP]

theorem codePr_hypY (h : ℕ) : codePr (hypY h) = hypYQ (ePQ 1) (ePQ 2) h := by
  rcases h with _ | h
  · simp [hypY, hypYQ, codePr_eP]
  · simp [hypY, hypYQ, codePr_eP]

theorem size_hypX (h : ℕ) : (hypX h).1.size = 64 := by
  rcases h with _ | _ | _ | _ | h
  · exact size_wordP _
  · exact size_wordP _
  · exact size_wordP _
  · exact size_mulP _ _
  · exact size_mulP _ _

theorem size_hypY (h : ℕ) : (hypY h).1.size = 64 := by
  rcases h with _ | h
  · exact size_wordP _
  · exact size_wordP _

theorem size_eP (i : ℕ) : (eP i).1.size = 64 := size_wordP _

theorem size_foldl (f : ℕ → Pr) (w : List ℕ) (acc : Pr) (hacc : acc.1.size = 64) :
    (w.foldl (fun acc s => mulP acc (f s)) acc).1.size = 64 := by
  induction w generalizing acc with
  | nil => exact hacc
  | cons s w ih =>
    rw [List.foldl_cons]
    exact ih _ (size_mulP _ _)

theorem size_slpP (ids : List ℕ) : (slpP ids).1.size = 64 := size_foldl _ ids oneP size_oneP

theorem codePr_foldl (f : ℕ → Pr) (g : ℕ → ℕ × ℕ) (h : ∀ s, codePr (f s) = g s) (w : List ℕ)
    (acc : Pr) : codePr (w.foldl (fun acc s => mulP acc (f s)) acc) =
      w.foldl (fun acc s => mulPr acc (g s)) (codePr acc) := by
  induction w generalizing acc with
  | nil => rfl
  | cons s w ih =>
    simp only [List.foldl_cons]
    rw [ih, codePr_mulP, h]

theorem codePr_getD (L : List Pr) (k : ℕ) :
    codePr (L.getD k oneP) = (L.map codePr).getD k oneQ := by
  rw [← codePr_oneP, List.getD_map]

theorem nList_code : nList.map codePr = nListQ := by
  rw [nList, nListQ, List.map_map]
  congr 1
  funext j
  exact codePr_wordP _

theorem nInvList_code : nInvList.map codePr = nInvListQ := by
  rw [nInvList, nInvListQ, List.map_map]
  congr 1
  funext j
  exact codePr_wordP _

theorem codePr_slpElt (i : ℕ) : codePr (slpElt i) = slpEltQ i := by
  unfold slpElt slpEltQ
  split_ifs
  · rw [codePr_getD, nList_code]
  · rw [codePr_getD, nInvList_code]
  · simp only [codePr, codeA_letterArr]

theorem codePr_slpP (ids : List ℕ) : codePr (slpP ids) = slpPQ ids := by
  rw [slpP, slpPQ, codePr_foldl _ _ codePr_slpElt, codePr_oneP]

theorem checkE : D48CheckE := by
  have h := ch9641E
  rw [d48EQ, letQ_eq, letQ_eq, letQ_eq] at h
  simp only [chkEQ, eqQ_eq, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_false_iff_not, and_assoc] at h
  obtain ⟨h0, h1, h2, h01, h02, h12, habc⟩ := h
  unfold D48CheckE
  simp only [List.mem_range, ne_eq, eq_code (size_powP _ _) size_oneP,
    eq_code (size_mulP _ _) (size_mulP _ _), eq_code (size_mulP _ _) size_oneP, codePr_mulP,
    codePr_powP, codePr_oneP, codePr_eP]
  refine ⟨fun i hi => ?_, h01, h02, h12, habc⟩
  interval_cases i
  · exact h0
  · exact h1
  · exact h2

theorem checkHyp : D48CheckHyp := by
  have h := ch9641Hyp
  rw [d48HypQ, letQ_eq, letQ_eq, letQ_eq, chkHypQ] at h
  simp only [letQ_eq, hypChkQ, eqQ_eq, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_false_iff_not,
    and_assoc] at h
  unfold D48CheckHyp
  simp only [List.mem_range, ne_eq, eq_code (size_powP _ _) size_oneP,
    eq_code (size_mulP _ _) (size_mulP _ _), eq_code (size_mulP _ _) size_oneP, codePr_mulP,
    codePr_powP, codePr_oneP, codePr_hypX, codePr_hypY]
  exact h

theorem checkN : D48CheckN := by
  have h := ch9641N
  rw [d48NQ, letQ_eq, letQ_eq, letQ_eq, chkNQ] at h
  simp only [letQ_eq, nChkQ, eqQ_eq, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, List.any_eq_true, and_assoc] at h
  unfold D48CheckN
  intro j hj
  obtain ⟨hn, hg⟩ := h j (List.mem_range.1 hj)
  refine ⟨ch9641NHyp j hj, ?_, ?_⟩
  · rw [eq_code (size_mulP _ _) size_oneP, codePr_mulP, codePr_oneP, nP, nInvP, codePr_wordP,
      codePr_wordP]
    exact hn
  · intro g hgm
    have hgs : g.1.size = 64 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hgm
      rcases hgm with rfl | rfl
      · exact size_hypX _
      · exact size_hypY _
    have hgc : codePr g ∈ [hypXQ (ePQ 0) (ePQ 1) (nHyp j), hypYQ (ePQ 1) (ePQ 2) (nHyp j)] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hgm ⊢
      rcases hgm with rfl | rfl
      · exact Or.inl (codePr_hypX _)
      · exact Or.inr (codePr_hypY _)
    obtain ⟨s, hs, t, ht, he⟩ := hg _ hgc
    refine ⟨s, List.mem_range.2 hs, t, List.mem_range.2 ht, ?_⟩
    rw [eq_code (size_mulP _ _) (size_mulP _ _), codePr_mulP, codePr_mulP, codePr_mulP,
      codePr_powP, codePr_powP, codePr_hypX, codePr_hypY, nP, nInvP, codePr_wordP, codePr_wordP]
    exact he

theorem checkSlp : D48CheckSlp := by
  have h := ch9641Slp
  simp only [d48SlpQ, eqQ_eq, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨h1, h2, h3⟩, hs1, hs2⟩ := And.intro ch9641SlpIdx h
  have key : ∀ x : ℕ × List ℕ, slpPQ x.2 = (letK.getD x.1 oneK, 0) →
      slpP x.2 = (letterArr x.1, 0) := fun x hx => by
    rw [eq_code (size_slpP _) (size_letterArr _), codePr_slpP]
    simpa only [codePr, codeA_letterArr] using hx
  refine ⟨fun x hx => ⟨(h1 x hx).1, (h1 x hx).2, key x (hs1 x hx)⟩,
    fun x hx => ⟨(h2 x hx).1, (h2 x hx).2, key x (hs2 x hx)⟩, h3⟩

theorem d48Check : D48Check := ⟨checkE, checkHyp, checkN, checkSlp⟩

end Certificates.Kernel.CertF8.C9641

end
