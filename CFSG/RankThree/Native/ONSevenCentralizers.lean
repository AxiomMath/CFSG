module

public import CFSG.RankThree.Native.ONSevenCheck
public import CFSG.RankThree.Native.ONSevenCheckBound
public import CFSG.RankThree.Native.ONSevenCheckKernel
public import CFSG.RankThree.Native.ONSevenRestrict
public import CFSG.RankThree.Native.PrimeLines
public import CFSG.Monster.B.Mathieu.SylowSound
public import CFSG.RankThree.Native.ONSevenDefs

public noncomputable section

namespace CFSG.RankThree.Native

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native CFSG.Certificates
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
open CFSG.Monster.B.Mathieu (powArr rep_powArr)

theorem onSeven_letters :
    (∀ k < onSevenSylowWords.size, plettersOK 7 onSevenSylowWords[k]! = true) ∧
    (∀ k < onSevenLineWords.size, plettersOK 7 onSevenLineWords[k]! = true) ∧
    (∀ r < 5, ∀ k < onSevenCentWords[r]!.size, plettersOK 7 (onSevenCentWords[r]!)[k]! = true) ∧
    (∀ r < 3, ∀ k < onSevenNormalWords[r]!.size,
      plettersOK 7 (onSevenNormalWords[r]!)[k]! = true) ∧
    (∀ r < 5, ∀ t ∈ onSevenTransporterData[r]!.toList, plettersOK 7 t.word = true) ∧
    (∀ r < 5, plettersOK 7 onSevenConjWords[r]! = true) ∧
    (∀ r < 5, ∀ k < onSevenBadData[r]!.size, plettersOK 7 (onSevenBadData[r]!)[k]!.2 = true) := by
  decide

theorem onSevenLineWords_size : onSevenLineWords.size = 57 := by decide

theorem onSeven_getElem!_append_left {a b : Array (Array ℕ)} {k : ℕ} (hk : k < a.size) :
    (a ++ b)[k]! = a[k]! := by
  rw [getElem!_pos (a ++ b) k (by simp; omega), getElem!_pos a k hk,
    Array.getElem_append_left hk]

theorem onSeven_getElem!_append_right {a b : Array (Array ℕ)} {k : ℕ} (hk : k < b.size) :
    (a ++ b)[a.size + k]! = b[k]! := by
  rw [getElem!_pos (a ++ b) _ (by simp; omega), getElem!_pos b k hk,
    Array.getElem_append_right (by omega)]
  simp

theorem onSeven_getElem!_push_lt {a : Array (Array ℕ)} {x : Array ℕ} {k : ℕ} (hk : k < a.size) :
    (a.push x)[k]! = a[k]! := by
  rw [getElem!_pos (a.push x) k (by simp; omega), getElem!_pos a k hk, Array.getElem_push_lt hk]

theorem onSeven_getElem!_push_eq {a : Array (Array ℕ)} {x : Array ℕ} :
    (a.push x)[a.size]! = x := by
  rw [getElem!_pos (a.push x) a.size (by simp), Array.getElem_push_eq]

theorem onSevenResOK_spec {R : Array ℕ} {gs : Array (Array ℕ)} (h : onSevenResOK R gs = true) :
    pointsOK nPts R (posArr nPts R) = true ∧ 3 ≤ R.size ∧ R[0]! = 0 ∧ R[1]! = 227759 ∧
      R[2]! = 100817 ∧ ∀ k < gs.size, restrictOK gs[k]! R (onSevenTab R gs[k]!) = true := by
  simp only [onSevenResOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, fun k hk => allBelowN_spec h6 hk⟩

theorem onSevenRes_of_append {R : Array ℕ} {ws : Array (List ℤ)} {extra : Array (Array ℕ)}
    (h : onSevenResOK R (ws.map onSevenArr ++ extra) = true)
    (hl : ∀ k < ws.size, plettersOK 7 ws[k]! = true) :
    ONSevenRes R ws ∧ ∀ k < extra.size, restrictOK extra[k]! R (onSevenTab R extra[k]!) = true := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := onSevenResOK_spec h
  have hsz : (ws.map onSevenArr).size = ws.size := by simp
  refine ⟨⟨h1, h2, h3, h4, h5, hl, fun k hk => ?_⟩, fun k hk => ?_⟩
  · have := h6 k (by simp; omega)
    rwa [onSeven_getElem!_append_left (by rw [hsz]; exact hk),
      getElem!_map_onSeven _ _ hk] at this
  · have := h6 ((ws.map onSevenArr).size + k) (by simp; omega)
    rwa [onSeven_getElem!_append_right hk] at this

theorem onSevenRes_of_push {R : Array ℕ} {ws : Array (List ℤ)} {x : Array ℕ}
    (h : onSevenResOK R ((ws.map onSevenArr).push x) = true)
    (hl : ∀ k < ws.size, plettersOK 7 ws[k]! = true) :
    ONSevenRes R ws ∧ restrictOK x R (onSevenTab R x) = true := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := onSevenResOK_spec h
  have hsz : (ws.map onSevenArr).size = ws.size := by simp
  refine ⟨⟨h1, h2, h3, h4, h5, hl, fun k hk => ?_⟩, ?_⟩
  · have := h6 k (by simp; omega)
    rwa [onSeven_getElem!_push_lt (by rw [hsz]; exact hk), getElem!_map_onSeven _ _ hk] at this
  · have := h6 (ws.map onSevenArr).size (by simp)
    rwa [onSeven_getElem!_push_eq] at this

theorem onSevenRes_of_map {R : Array ℕ} {ws : Array (List ℤ)}
    (h : onSevenResOK R (ws.map onSevenArr) = true)
    (hl : ∀ k < ws.size, plettersOK 7 ws[k]! = true) : ONSevenRes R ws := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := onSevenResOK_spec h
  refine ⟨h1, h2, h3, h4, h5, hl, fun k hk => ?_⟩
  have := h6 k (by simp; omega)
  rwa [getElem!_map_onSeven _ _ hk] at this

theorem onSevenLineArrs_get {j : ℕ} (hj : j < 57) :
    onSevenLineArrs[j]! = onSevenArr onSevenLineWords[j]! :=
  getElem!_map_onSeven _ _ (by rw [onSevenLineWords_size]; exact hj)

theorem prep_onSevenLine (j : Fin 57) : PRep N onSevenLineArrs[j.val]! (onSevenLine j) := by
  rw [onSevenLineArrs_get j.isLt]
  exact prep_onSevenArr (onSeven_letters.2.1 j (by rw [onSevenLineWords_size]; exact j.isLt))

theorem prep_onSevenRepArr {r : ℕ} (hr : r < 5) :
    PRep N (onSevenRepArr r) (onSevenLine (onSevenRep ⟨r, hr⟩)) := by
  have h := prep_onSevenLine (onSevenRep ⟨r, hr⟩)
  rwa [onSevenRep_val] at h

structure ONSevenQFacts : Prop where
  res : onSevenResOK onSevenQR (onSevenQArrs ++ onSevenLineArrs) = true
  enum : enumOK onSevenQR.size onSevenQTabs onSevenKeys onSevenQCert = true
  size : onSevenQCert.pts.size = 343
  lsize : onSevenLineTabs.size = 57
  pow : allLt 343 (fun k => eqA onSevenQR.size (powArr onSevenQR.size onSevenQCert.pts[k]! 7)
    (idA onSevenQR.size)) = true
  cover : allLt 343 (fun k => eqA onSevenQR.size onSevenQCert.pts[k]! (idA onSevenQR.size) ||
    (List.range 57).any fun j => (List.range 7).any fun e =>
      eqA onSevenQR.size onSevenQCert.pts[k]! (powArr onSevenQR.size onSevenLineTabs[j]! e)) =
    true
  dist : allLt 57 (fun j => allLt 57 fun j' => j == j' || allLt 7 fun e =>
    !(eqA onSevenQR.size onSevenLineTabs[j]! (powArr onSevenQR.size onSevenLineTabs[j']! e))) =
    true
  lines : allLt 57 (fun j => validA onSevenQR.size onSevenLineTabs[j]! &&
    eqA onSevenQR.size (powArr onSevenQR.size onSevenLineTabs[j]! 7) (idA onSevenQR.size) &&
    !(eqA onSevenQR.size onSevenLineTabs[j]! (idA onSevenQR.size)) &&
    onSevenQCert.pts.toList.any (eqA onSevenQR.size onSevenLineTabs[j]!)) = true

theorem onSeven_Q_facts : ONSevenQFacts := by
  have h := onSeven_Q_check
  simp only [onSevenQCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hR, hE⟩, hS⟩, hL⟩, hP⟩, hC⟩, hD⟩, hX⟩ := h
  exact ⟨hR, hE, hS, hL, hP, hC, hD, hX⟩

theorem onSevenQ_res : ONSevenRes onSevenQR onSevenSylowWords :=
  (onSevenRes_of_append onSeven_Q_facts.res onSeven_letters.1).1

theorem onSevenQ_cert :
    enumOK onSevenQR.size (onSevenTabsOf onSevenQR onSevenSylowWords) onSevenKeys onSevenQCert =
      true :=
  onSeven_Q_facts.enum

theorem card_onSevenQ : Nat.card onSevenQ = 343 :=
  (onSevenQ_res.card_eq onSevenQ_cert).trans onSeven_Q_facts.size

theorem onSevenLineTabs_get {j : ℕ} (hj : j < 57) :
    onSevenLineTabs[j]! = onSevenTab onSevenQR onSevenLineArrs[j]! :=
  getElem!_map_onSeven _ _ (by simp [onSevenLineArrs, onSevenLineWords_size, hj])

theorem onSevenLine_restrict (j : Fin 57) :
    restrictOK onSevenLineArrs[j.val]! onSevenQR onSevenLineTabs[j.val]! = true := by
  have h := (onSevenRes_of_append onSeven_Q_facts.res onSeven_letters.1).2 j.val
    (by simp [onSevenLineArrs, onSevenLineWords_size])
  rwa [← onSevenLineTabs_get j.isLt] at h

theorem onSevenLine_facts (j : Fin 57) :
    validA onSevenQR.size onSevenLineTabs[j.val]! = true ∧
    eqA onSevenQR.size (powArr onSevenQR.size onSevenLineTabs[j.val]! 7) (idA onSevenQR.size) =
      true ∧
    eqA onSevenQR.size onSevenLineTabs[j.val]! (idA onSevenQR.size) = false ∧
    onSevenQCert.pts.toList.any (eqA onSevenQR.size onSevenLineTabs[j.val]!) = true := by
  have h := allLt_spec onSeven_Q_facts.lines j.isLt
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem onSevenLine_mem_Q (j : Fin 57) : onSevenLine j ∈ onSevenQ :=
  onSevenQ_res.mem_of_any onSevenQ_cert (evalS_mem _) (prep_onSevenLine j)
    (onSevenLine_restrict j) (onSevenLine_facts j).2.2.2

@[expose] def onSevenLineQ (j : Fin 57) : onSevenGen onSevenSylowWords :=
  ⟨onSevenLine j, onSevenLine_mem_Q j⟩

theorem rep_onSevenLineQ (j : Fin 57) :
    CFSG.Monster.B.Co2.Rep onSevenQR.size onSevenLineTabs[j.val]!
      (onSevenQ_res.rho (onSevenLineQ j)) :=
  onSevenQ_res.prep_rho (G := onSevenLineQ j) (prep_onSevenLine j) (onSevenLine_restrict j)

theorem onSevenQ_rho_eq_one {g : onSevenGen onSevenSylowWords} (h : onSevenQ_res.rho g = 1) :
    (g : Equiv.Perm (Fin N)) = 1 := by
  have := onSevenQ_res.rho_injective (h.trans (map_one _).symm)
  rw [this]
  rfl

theorem onSevenLine_pow_seven (j : Fin 57) : onSevenLine j ^ 7 = 1 := by
  have h := (eqA_iff (rep_powArr (rep_onSevenLineQ j) 7) rep_idA).1 (onSevenLine_facts j).2.1
  rw [← map_pow] at h
  have := onSevenQ_rho_eq_one h
  simpa [onSevenLineQ] using this

theorem onSevenLine_ne_one (j : Fin 57) : onSevenLine j ≠ 1 := by
  intro h1
  have hg : onSevenLineQ j = 1 := Subtype.ext h1
  have h := (eqA_iff (rep_onSevenLineQ j) rep_idA).2 (by rw [hg, map_one])
  rw [(onSevenLine_facts j).2.2.1] at h
  exact Bool.false_ne_true h

theorem orderOf_onSevenLine (j : Fin 57) : orderOf (onSevenLine j) = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact orderOf_eq_prime (onSevenLine_pow_seven j) (onSevenLine_ne_one j)

theorem onSevenQ_elem (g : onSevenGen onSevenSylowWords) :
    ∃ k < 343, CFSG.Monster.B.Co2.Rep onSevenQR.size onSevenQCert.pts[k]! (onSevenQ_res.rho g) := by
  obtain ⟨k, hk, hr⟩ := onSevenQ_res.exists_rep onSevenQ_cert g
  exact ⟨k, onSeven_Q_facts.size ▸ hk, hr⟩

theorem onSevenQ_pow_seven {g : Equiv.Perm (Fin N)} (hg : g ∈ onSevenQ) : g ^ 7 = 1 := by
  obtain ⟨k, hk, hkg⟩ := onSevenQ_elem ⟨g, hg⟩
  have h := (eqA_iff (rep_powArr hkg 7) rep_idA).1 (allLt_spec onSeven_Q_facts.pow hk)
  rw [← map_pow] at h
  have := onSevenQ_rho_eq_one h
  simpa using this

theorem exponent_onSevenQ : Monoid.exponent onSevenQ = 7 := by
  have hdvd : Monoid.exponent onSevenQ ∣ 7 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (onSevenQ_pow_seven g.2)
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).1 hdvd with h | h
  · exfalso
    have hs := Monoid.exp_eq_one_iff.1 h
    have := congrArg Subtype.val
      (hs.elim (⟨onSevenLine 0, onSevenLine_mem_Q 0⟩ : onSevenQ) 1)
    exact onSevenLine_ne_one 0 this
  · exact h

theorem factorization_card_Pv_seven : (Nat.card Pv).factorization 7 = 3 := by
  rw [card_Pv, show (460815505920 : ℕ) = 7 ^ 3 * 1343485440 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow (by norm_num : Nat.Prime 7), Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem onSevenQ_sylow : ∃ S : Sylow 7 Pv, (S : Subgroup Pv) = onSevenQ.subgroupOf Pv := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hle : onSevenQ ≤ Pv := onSeven_mem_P.1
  have hcard : Nat.card (onSevenQ.subgroupOf Pv) = 7 ^ (Nat.card Pv).factorization 7 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, card_onSevenQ,
      factorization_card_Pv_seven]
    norm_num
  exact ⟨Sylow.ofCard _ hcard, rfl⟩

theorem onSevenQ_lines :
    {H : Subgroup (Equiv.Perm (Fin N)) | H ≤ onSevenQ ∧ Nat.card H = 7} =
        Set.range (fun j : Fin 57 => Subgroup.zpowers (onSevenLine j)) ∧
      Function.Injective (fun j : Fin 57 => Subgroup.zpowers (onSevenLine j)) := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  apply prime_subgroups_eq_range onSevenLine onSevenLine_mem_Q onSevenLine_ne_one
    onSevenLine_pow_seven
  · intro g hg hg1
    obtain ⟨k, hk, hkg⟩ := onSevenQ_elem ⟨g, hg⟩
    have h := allLt_spec onSeven_Q_facts.cover hk
    simp only [Bool.or_eq_true, List.any_eq_true, List.mem_range] at h
    rcases h with h | ⟨j, hj, e, he, hje⟩
    · have h1 := (eqA_iff hkg rep_idA).1 h
      exact absurd (onSevenQ_rho_eq_one h1) hg1
    · refine ⟨⟨j, hj⟩, e, ?_⟩
      have h2 := (eqA_iff hkg (rep_powArr (rep_onSevenLineQ ⟨j, hj⟩) e)).1 hje
      rw [← map_pow] at h2
      have := congrArg Subtype.val (onSevenQ_res.rho_injective h2)
      simpa [onSevenLineQ] using this
  · intro j j' k hk hjj'
    have h := allLt_spec (allLt_spec onSeven_Q_facts.dist j.isLt) j'.isLt
    simp only [Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h | h
    · exact Fin.ext h
    · have h' := allLt_spec h hk
      rw [Bool.not_eq_true'] at h'
      have hg : onSevenLineQ j = onSevenLineQ j' ^ k := Subtype.ext (by simpa [onSevenLineQ])
      have := (eqA_iff (rep_onSevenLineQ j) (rep_powArr (rep_onSevenLineQ j') k)).2
        (by rw [hg, map_pow])
      rw [h'] at this
      exact absurd this Bool.false_ne_true

theorem onSevenCCheck_spec {R x : Array ℕ} {cs ts : Array (Array ℕ)} {c : ArrCert} {sz : ℕ}
    (h : onSevenCCheck R x cs ts c sz = true) :
    onSevenResOK R (cs.push x) = true ∧
      allBelowN cs.size (fun k => peq nPts (pcomp nPts cs[k]! x) (pcomp nPts x cs[k]!)) = true ∧
      enumOK R.size ts onSevenKeys c = true ∧ c.pts.size = sz := by
  simp only [onSevenCCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

theorem onSeven_bound_spec {r : ℕ} (hr : r < 5) {c good : ℕ} {useScan : Bool}
    (hB : onSevenBoundCheck r (onSevenConjArr r) c good useScan = true) :
    Nat.card (Subgroup.centralizer {onSevenLine (onSevenRep ⟨r, hr⟩)} ⊓ Pv :
      Subgroup (Equiv.Perm (Fin N))) ≤ good * c := by
  simp only [onSevenBoundCheck, Bool.and_eq_true, beq_iff_eq] at hB
  obtain ⟨⟨⟨⟨hT, h0⟩, hc⟩, hg⟩, hbad⟩ := hB
  set X := onSevenLine (onSevenRep ⟨r, hr⟩)
  have hX : PRep N (onSevenRepArr r) X := prep_onSevenRepArr hr
  set T := evalS onSevenConjWords[r]!
  have hTp : PRep N (onSevenArr onSevenConjWords[r]!) T :=
    prep_onSevenArr (onSeven_letters.2.2.2.2.2.1 r hr)
  have hXp : PRep N (onSevenConjArr r) (T * X * T⁻¹) := prep_onSevenConj hTp hX hT
  have hXP : T * X * T⁻¹ ∈ Pv :=
    mul_mem (mul_mem (evalS_mem _) (evalS_mem _)) (inv_mem (evalS_mem _))
  have hx0 : (T * X * T⁻¹) x0 = x0 := Fin.ext (by rw [← hXp x0]; exact h0)
  have hbound := card_centralizer_le_of_good hXp hXP hx0
    (bad := onSevenBadData[r]!.toList.map Prod.fst) ?_
  · rw [hg, hc] at hbound
    rw [card_centralizer_inf_conj Pv (evalS_mem _) rfl]
    exact hbound
  · intro q hq g hgP hcomm
    obtain ⟨⟨q', uw⟩, hmem, rfl⟩ := List.mem_map.1 hq
    obtain ⟨i, hi, hei⟩ := List.getElem_of_mem hmem
    have hi' : i < onSevenBadData[r]!.size := by simpa using hi
    have hei' : (onSevenBadData[r]!)[i]! = (q', uw) := by
      rw [getElem!_pos _ i hi', ← Array.getElem_toList]
      exact hei
    have hbi := allBelowN_spec hbad hi'
    rw [hei'] at hbi
    simp only [Bool.and_eq_true, beq_iff_eq] at hbi
    obtain ⟨⟨hu0, huinv⟩, hcert⟩ := hbi
    have hul : plettersOK 7 uw = true := by
      have := onSeven_letters.2.2.2.2.2.2 r hr i hi'
      rwa [hei'] at this
    have hu : PRep N (onSevenArr uw) (evalS uw) := prep_onSevenArr hul
    have hq' : ((evalS uw x0 : Fin N) : ℕ) = q' := by rw [← hu x0]; exact hu0
    have hne : g x0 ≠ evalS uw x0 := by
      by_cases hs : useScan = true
      · rw [ite_eq_left hs] at hcert
        exact ne_of_cosetFree hXp hXP hu (evalS_mem _) hcert g hgP hcomm
      · rw [ite_eq_right hs, bne_iff_ne] at hcert
        exact ne_of_count_ne hXp hXP (evalS_mem _) (prep_onSevenConjInv hu hXp huinv)
          (by rw [hc]; exact hcert) g hgP hcomm
    intro hgq
    apply hne
    apply Fin.ext
    simp only at hgq
    rw [hgq, hq']

theorem onSevenC_spec {r : ℕ} (hr : r < 5) {sz good : ℕ} {useScan : Bool}
    (hC : onSevenCCheck (onSevenCR r) (onSevenRepArr r) (onSevenCArrs r) (onSevenCTabs r)
      (onSevenCCert r) sz = true)
    (hB : onSevenBoundCheck r (onSevenConjArr r) 49 good useScan = true) (hle : good * 49 ≤ sz) :
    onSevenC ⟨r, hr⟩ = Subgroup.centralizer {onSevenLine (onSevenRep ⟨r, hr⟩)} ⊓ Pv ∧
      Nat.card (onSevenC ⟨r, hr⟩) = sz := by
  obtain ⟨hres, hcomm, henum, hsize⟩ := onSevenCCheck_spec hC
  obtain ⟨hD, -⟩ := onSevenRes_of_push hres (onSeven_letters.2.2.1 r hr)
  have hcard : Nat.card (onSevenC ⟨r, hr⟩) = sz := (hD.card_eq henum).trans hsize
  have hle1 : onSevenC ⟨r, hr⟩ ≤ Subgroup.centralizer {onSevenLine (onSevenRep ⟨r, hr⟩)} := by
    rw [onSevenC, Subgroup.closure_le]
    intro g hg
    obtain ⟨k, hk, rfl⟩ := mem_evalList_iff.1 hg
    have hck := allBelowN_spec hcomm (by simpa [onSevenCArrs] using hk)
    rw [onSevenCArrs, getElem!_map_onSeven _ _ hk] at hck
    exact Subgroup.mem_centralizer_singleton_iff.2 (eq_of_peq
      (prep_pcomp (hD.prep_gen hk) (prep_onSevenRepArr hr))
      (prep_pcomp (prep_onSevenRepArr hr) (hD.prep_gen hk)) hck)
  have hle2 : onSevenC ⟨r, hr⟩ ≤
      Subgroup.centralizer {onSevenLine (onSevenRep ⟨r, hr⟩)} ⊓ Pv :=
    le_inf hle1 (closure_evalList_le _)
  refine ⟨Subgroup.eq_of_le_of_card_ge hle2 ?_, hcard⟩
  rw [hcard]
  exact (onSeven_bound_spec hr hB).trans hle

theorem onSevenFCheck_spec {R : Array ℕ} {ts : Array (Array ℕ)} {cC : ArrCert}
    {fs tf : Array (Array ℕ)} {tx : Array ℕ} {cF : ArrCert}
    (h : onSevenFCheck R ts cC fs tf tx cF = true) :
    onSevenResOK R fs = true ∧ enumOK R.size tf onSevenKeys cF = true ∧ cF.pts.size = 343 ∧
      allLt tf.size (fun l => cC.pts.toList.any (eqA R.size tf[l]!)) = true ∧
      allLt ts.size (fun k => allLt tf.size fun l =>
        cF.pts.toList.any (eqA R.size (conjA R.size ts[k]! tf[l]!))) = true ∧
      cF.pts.toList.any (eqA R.size tx) = true ∧
      allLt cC.pts.size (fun k => !(allLt tf.size fun l => commA R.size cC.pts[k]! tf[l]!) ||
        (List.range 7).any fun e => eqA R.size cC.pts[k]! (powArr R.size tx e)) = true := by
  simp only [onSevenFCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem onSevenF_spec {r : ℕ} (hr : r < 3) {sz : ℕ}
    (hC : onSevenCCheck (onSevenCR r) (onSevenRepArr r) (onSevenCArrs r) (onSevenCTabs r)
      (onSevenCCert r) sz = true)
    (hF : onSevenFCheck (onSevenCR r) (onSevenCTabs r) (onSevenCCert r) (onSevenFArrs r)
      (onSevenFTabs r) (onSevenRepTab r) (onSevenFCert r) = true)
    (hCeq : onSevenC ⟨r, by omega⟩ =
      Subgroup.centralizer {onSevenLine (onSevenRep ⟨r, by omega⟩)} ⊓ Pv) :
    onSevenF ⟨r, hr⟩ ≤ onSevenC ⟨r, by omega⟩ ∧
      ((onSevenF ⟨r, hr⟩).subgroupOf (onSevenC ⟨r, by omega⟩)).Normal ∧
      Nat.card (onSevenF ⟨r, hr⟩) = 343 ∧
      Subgroup.centralizer (onSevenF ⟨r, hr⟩ : Set (Equiv.Perm (Fin N))) ⊓
          onSevenC ⟨r, by omega⟩ = Subgroup.zpowers (onSevenLine (onSevenRep ⟨r, by omega⟩)) ∧
      onSevenLine (onSevenRep ⟨r, by omega⟩) ∈ onSevenF ⟨r, hr⟩ := by
  have hr5 : r < 5 := by omega
  obtain ⟨hresC, -, henumC, -⟩ := onSevenCCheck_spec hC
  obtain ⟨hDC, hxres⟩ := onSevenRes_of_push hresC (onSeven_letters.2.2.1 r hr5)
  obtain ⟨hresF, henumF, hsizeF, hFC, hnorm, hxF, hcent⟩ := onSevenFCheck_spec hF
  have hDF : ONSevenRes (onSevenCR r) onSevenNormalWords[r]! :=
    onSevenRes_of_map hresF (onSeven_letters.2.2.2.1 r hr)
  set X := onSevenLine (onSevenRep ⟨r, hr5⟩)
  have hX : PRep N (onSevenRepArr r) X := prep_onSevenRepArr hr5
  have hFsize : (onSevenFTabs r).size = onSevenNormalWords[r]!.size := by
    simp [onSevenFTabs, onSevenFArrs]
  have hCsize : (onSevenCTabs r).size = onSevenCentWords[r]!.size := by
    simp [onSevenCTabs, onSevenCArrs]
  have hfgen : ∀ l < onSevenNormalWords[r]!.size,
      evalS (onSevenNormalWords[r]!)[l]! ∈ onSevenC ⟨r, hr5⟩ := by
    intro l hl
    have hany := allLt_spec hFC (by rw [hFsize]; exact hl)
    rw [onSevenFTabs, getElem!_map_onSeven _ _ (by simpa [onSevenFArrs] using hl), onSevenFArrs,
      getElem!_map_onSeven _ _ hl] at hany
    exact hDC.mem_of_any henumC (evalS_mem _) (hDF.prep_gen hl) (hDF.res l hl) hany
  have hFC' : onSevenF ⟨r, hr⟩ ≤ onSevenC ⟨r, hr5⟩ := by
    rw [onSevenF, Subgroup.closure_le]
    intro g hg
    obtain ⟨l, hl, rfl⟩ := mem_evalList_iff.1 hg
    exact hfgen l hl
  have hxmem : X ∈ onSevenF ⟨r, hr⟩ :=
    hDF.mem_of_any henumF (evalS_mem _) hX hxres hxF
  refine ⟨hFC', ?_, (hDF.card_eq henumF).trans hsizeF, ?_, hxmem⟩
  ·
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hFC', onSevenC, onSevenF]
    apply closure_le_normalizer_closure
    intro s hs t ht
    obtain ⟨k, hk, rfl⟩ := mem_evalList_iff.1 hs
    obtain ⟨l, hl, rfl⟩ := mem_evalList_iff.1 ht
    set sC : onSevenGen onSevenCentWords[r]! := ⟨evalS (onSevenCentWords[r]!)[k]!,
      evalS_mem_onSevenGen hk⟩
    set tC : onSevenGen onSevenCentWords[r]! := ⟨evalS (onSevenNormalWords[r]!)[l]!, hfgen l hl⟩
    have hval : CFSG.RankThree.Native.validA (onSevenCR r).size (onSevenCTabs r)[k]! = true :=
      enumOK_gens_valid henumC (by rw [hCsize]; exact hk)
    have hsrep : CFSG.Monster.B.Co2.Rep (onSevenCR r).size (onSevenCTabs r)[k]! (hDC.rho sC) := by
      have h := hDC.rep_tab hk
      rwa [show ONSevenRes.gen onSevenCentWords[r]! k = sC from
        Subtype.ext (ONSevenRes.gen_val hk)] at h
    have htrep : CFSG.Monster.B.Co2.Rep (onSevenCR r).size (onSevenFTabs r)[l]! (hDC.rho tC) := by
      rw [onSevenFTabs, getElem!_map_onSeven _ _ (by simpa [onSevenFArrs] using hl), onSevenFArrs,
        getElem!_map_onSeven _ _ hl]
      exact hDC.prep_rho (G := tC) (hDF.prep_gen hl) (hDF.res l hl)
    have hconj : CFSG.Monster.B.Co2.Rep (onSevenCR r).size
        (conjA (onSevenCR r).size (onSevenCTabs r)[k]! (onSevenFTabs r)[l]!)
        (hDC.rho (sC * tC * sC⁻¹)) := by
      have := rep_conjA hval htrep
      rwa [permOfArr_eq_of_rep hsrep, ← map_mul, ← map_inv, ← map_mul] at this
    have hany := allLt_spec (allLt_spec hnorm (by rw [hCsize]; exact hk)) (by rw [hFsize]; exact hl)
    exact hDC.mem_of_rho_any hDF henumF hconj hany
  ·
    apply le_antisymm
    · intro g hg
      obtain ⟨hgF, hgC⟩ := Subgroup.mem_inf.1 hg
      set gC : onSevenGen onSevenCentWords[r]! := ⟨g, hgC⟩
      set xC : onSevenGen onSevenCentWords[r]! := ⟨X, hFC' hxmem⟩
      obtain ⟨i, hi, hgi⟩ := hDC.exists_rep henumC gC
      have hxrep : CFSG.Monster.B.Co2.Rep (onSevenCR r).size (onSevenRepTab r) (hDC.rho xC) :=
        hDC.prep_rho (G := xC) hX hxres
      have hcomm : allLt (onSevenFTabs r).size (fun l =>
          commA (onSevenCR r).size (onSevenCCert r).pts[i]! (onSevenFTabs r)[l]!) = true := by
        rw [CFSG.Monster.B.Co2.allLt_iff]
        intro l hl
        have hl' : l < onSevenNormalWords[r]!.size := by rw [← hFsize]; exact hl
        set tC : onSevenGen onSevenCentWords[r]! :=
          ⟨evalS (onSevenNormalWords[r]!)[l]!, hfgen l hl'⟩
        have htrep : CFSG.Monster.B.Co2.Rep (onSevenCR r).size (onSevenFTabs r)[l]!
            (hDC.rho tC) := by
          rw [onSevenFTabs, getElem!_map_onSeven _ _ (by simpa [onSevenFArrs] using hl'),
            onSevenFArrs, getElem!_map_onSeven _ _ hl']
          exact hDC.prep_rho (G := tC) (hDF.prep_gen hl') (hDF.res l hl')
        rw [commA_iff hgi htrep, ← map_mul, ← map_mul]
        congr 1
        apply Subtype.ext
        exact (Subgroup.mem_centralizer_iff.1 hgF _ (evalS_mem_onSevenGen hl')).symm
      have hc := allLt_spec hcent hi
      rw [hcomm, Bool.not_true, Bool.false_or, List.any_eq_true] at hc
      obtain ⟨e, -, he⟩ := hc
      have h1 := (eqA_iff hgi (rep_powArr hxrep e)).1 he
      rw [← map_pow] at h1
      have h2 := congrArg Subtype.val (hDC.rho_injective h1)
      simp only [gC, xC, Subgroup.coe_pow] at h2
      rw [h2]
      exact Subgroup.npow_mem_zpowers _ e
    · rw [Subgroup.zpowers_le]
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 fun f hf => ?_, hFC' hxmem⟩
      have hfC := hFC' hf
      rw [hCeq] at hfC
      exact Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hfC).1

theorem onSevenTrans_spec {r : ℕ} (hr : r < 5) (h : onSevenTransCheck r = true) :
    ∀ t ∈ onSevenTransporters ⟨r, hr⟩, onSevenTransporterPerm t ∈ Pv ∧ 1 ≤ t.power ∧
      t.power ≤ 6 ∧ ∃ hj : t.line < 57, (onSevenTransporterPerm t *
        onSevenLine (onSevenRep ⟨r, hr⟩) * (onSevenTransporterPerm t)⁻¹) ^ t.power =
          onSevenLine ⟨t.line, hj⟩ := by
  intro t ht
  have hmem : t ∈ onSevenTransporterData[r]!.toList := ht
  obtain ⟨i, hi, hti⟩ := List.getElem_of_mem hmem
  have hi' : i < onSevenTransporterData[r]!.size := by simpa using hi
  rw [onSevenTransCheck, Array.all_eq_true] at h
  have hc := h i hi'
  rw [← Array.getElem_toList, hti] at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨h1, h6⟩, hj⟩, hpeq⟩ := hc
  have hl := onSeven_letters.2.2.2.2.1 r hr t hmem
  have hH : PRep N (onSevenArr t.word) (onSevenTransporterPerm t) := prep_onSevenArr hl
  refine ⟨evalS_mem _, h1, h6, hj, ?_⟩
  have he := eq_of_peq (prep_pcomp hH (prep_onSevenPow (prep_onSevenRepArr hr) t.power))
    (prep_pcomp (prep_onSevenLine ⟨t.line, hj⟩) hH) hpeq
  rw [conj_pow, he, mul_inv_cancel_right]

theorem onSeven_coverage :
    ∀ j : Fin 57, ∃ r : Fin 5, ∃ t ∈ onSevenTransporters r, t.line = j.val := by
  decide

theorem onSevenC_eq (r : Fin 5) :
    onSevenC r = Subgroup.centralizer {onSevenLine (onSevenRep r)} ⊓ Pv := by
  fin_cases r
  · exact (onSevenC_spec (r := 0) (by norm_num) onSeven_C_check_0 onSeven_bound_check_0
      (by norm_num)).1
  · exact (onSevenC_spec (r := 1) (by norm_num) onSeven_C_check_1 onSeven_bound_check_1
      (by norm_num)).1
  · exact (onSevenC_spec (r := 2) (by norm_num) onSeven_C_check_2 onSeven_bound_check_2
      (by norm_num)).1
  · exact (onSevenC_spec (r := 3) (by norm_num) onSeven_C_check_3 onSeven_bound_check_3
      (by norm_num)).1
  · exact (onSevenC_spec (r := 4) (by norm_num) onSeven_C_check_4 onSeven_bound_check_4
      (by norm_num)).1

theorem card_onSevenC_low (r : Fin 3) :
    Nat.card (onSevenC (Fin.castLE (by norm_num) r)) = 1372 := by
  fin_cases r
  · exact (onSevenC_spec (r := 0) (by norm_num) onSeven_C_check_0 onSeven_bound_check_0
      (by norm_num)).2
  · exact (onSevenC_spec (r := 1) (by norm_num) onSeven_C_check_1 onSeven_bound_check_1
      (by norm_num)).2
  · exact (onSevenC_spec (r := 2) (by norm_num) onSeven_C_check_2 onSeven_bound_check_2
      (by norm_num)).2

theorem card_onSevenC_high (r : Fin 5) (hr : 3 ≤ r.val) : Nat.card (onSevenC r) = 49 := by
  fin_cases r
  · exact absurd hr (by norm_num)
  · exact absurd hr (by norm_num)
  · exact absurd hr (by norm_num)
  · exact (onSevenC_spec (r := 3) (by norm_num) onSeven_C_check_3 onSeven_bound_check_3
      (by norm_num)).2
  · exact (onSevenC_spec (r := 4) (by norm_num) onSeven_C_check_4 onSeven_bound_check_4
      (by norm_num)).2

theorem onSevenF_facts (r : Fin 3) :
    onSevenF r ≤ onSevenC (Fin.castLE (by norm_num) r) ∧
      ((onSevenF r).subgroupOf (onSevenC (Fin.castLE (by norm_num) r))).Normal ∧
      Nat.card (onSevenF r) = 343 ∧
      Subgroup.centralizer (onSevenF r : Set (Equiv.Perm (Fin N))) ⊓
          onSevenC (Fin.castLE (by norm_num) r) =
        Subgroup.zpowers (onSevenLine (onSevenRep (Fin.castLE (by norm_num) r))) ∧
      onSevenLine (onSevenRep (Fin.castLE (by norm_num) r)) ∈ onSevenF r := by
  fin_cases r
  · exact onSevenF_spec (r := 0) (by norm_num) onSeven_C_check_0 onSeven_F_check_0
      (onSevenC_eq 0)
  · exact onSevenF_spec (r := 1) (by norm_num) onSeven_C_check_1 onSeven_F_check_1
      (onSevenC_eq 1)
  · exact onSevenF_spec (r := 2) (by norm_num) onSeven_C_check_2 onSeven_F_check_2
      (onSevenC_eq 2)

theorem onSevenTransporters_spec (r : Fin 5) :
    ∀ t ∈ onSevenTransporters r, onSevenTransporterPerm t ∈ Pv ∧ 1 ≤ t.power ∧
      t.power ≤ 6 ∧ ∃ hj : t.line < 57, (onSevenTransporterPerm t * onSevenLine (onSevenRep r) *
        (onSevenTransporterPerm t)⁻¹) ^ t.power = onSevenLine ⟨t.line, hj⟩ := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := onSeven_trans_check
  fin_cases r
  · exact onSevenTrans_spec (r := 0) (by norm_num) h0
  · exact onSevenTrans_spec (r := 1) (by norm_num) h1
  · exact onSevenTrans_spec (r := 2) (by norm_num) h2
  · exact onSevenTrans_spec (r := 3) (by norm_num) h3
  · exact onSevenTrans_spec (r := 4) (by norm_num) h4

theorem R3E_ON_full_seven_centralizer_structures :
    (onSevenQ ≤ Pv ∧ (∃ S : Sylow 7 Pv, (S : Subgroup Pv) = onSevenQ.subgroupOf Pv) ∧
      Nat.card onSevenQ = 343 ∧ Monoid.exponent onSevenQ = 7) ∧
    ({H : Subgroup (Equiv.Perm (Fin N)) | H ≤ onSevenQ ∧ Nat.card H = 7} =
        Set.range (fun j : Fin 57 => Subgroup.zpowers (onSevenLine j)) ∧
      Function.Injective (fun j : Fin 57 => Subgroup.zpowers (onSevenLine j))) ∧
    (∀ r : Fin 5, onSevenC r = Subgroup.centralizer {onSevenLine (onSevenRep r)} ⊓ Pv) ∧
    (∀ r : Fin 3, Nat.card (onSevenC (Fin.castLE (by norm_num) r)) = 1372 ∧
      onSevenF r ≤ onSevenC (Fin.castLE (by norm_num) r) ∧
      ((onSevenF r).subgroupOf (onSevenC (Fin.castLE (by norm_num) r))).Normal ∧
      Nat.card (onSevenF r) = 343 ∧
      Subgroup.centralizer (onSevenF r : Set (Equiv.Perm (Fin N))) ⊓
        onSevenC (Fin.castLE (by norm_num) r) ≤ onSevenF r ∧
      Nat.card (Subgroup.centralizer (onSevenF r : Set (Equiv.Perm (Fin N))) ⊓
        onSevenC (Fin.castLE (by norm_num) r) : Subgroup (Equiv.Perm (Fin N))) = 7) ∧
    (∀ r : Fin 5, 3 ≤ r.val → Nat.card (onSevenC r) = 49) ∧
    (∀ r : Fin 5, ∀ t ∈ onSevenTransporters r, onSevenTransporterPerm t ∈ Pv ∧ 1 ≤ t.power ∧
      t.power ≤ 6 ∧ ∃ hj : t.line < 57, (onSevenTransporterPerm t * onSevenLine (onSevenRep r) *
        (onSevenTransporterPerm t)⁻¹) ^ t.power = onSevenLine ⟨t.line, hj⟩) ∧
    (∀ j : Fin 57, ∃ r : Fin 5, ∃ t ∈ onSevenTransporters r, t.line = j.val) := by
  refine ⟨⟨onSeven_mem_P.1, onSevenQ_sylow, card_onSevenQ, exponent_onSevenQ⟩, onSevenQ_lines,
    onSevenC_eq, fun r => ?_, card_onSevenC_high, onSevenTransporters_spec, onSeven_coverage⟩
  obtain ⟨hle, hnorm, hcard, hcent, hx⟩ := onSevenF_facts r
  refine ⟨card_onSevenC_low r, hle, hnorm, hcard, ?_, ?_⟩
  · rw [hcent, Subgroup.zpowers_le]
    exact hx
  · rw [hcent, Nat.card_zpowers, orderOf_onSevenLine]

end CFSG.RankThree.Native
