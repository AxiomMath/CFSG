module

public import Certificates.Data.J4Seven.Native
import Certificates.Kernel.J4Q.C4219
import Certificates.Kernel.J4Q.Orb
import CFSG.Certificates.Kernel.J4Q.VOrbPts
import CFSG.Certificates.Kernel.J4Q.VOrbBFS

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KC.LQT.Syl CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT
  CFSG.Sporadic.J4.QT2 CFSG.Quasithin.J4Seven CertificateChecks.KernelJ4Q
  CertificateChecks.KernelJ4Q.C4219

namespace CertificateChecks.KernelJ4Q.C4219

theorem andB_true {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, h⟩

theorem orB_true {a b : Bool} (h : orB a b = true) : a = true ∨ b = true := by
  cases a
  · exact Or.inr h
  · exact Or.inl rfl

theorem notB_true {b : Bool} (h : notB b = true) : b = false := by
  cases b
  · rfl
  · exact absurd h Bool.false_ne_true

theorem memK_mem {x : Nat} : ∀ {l : List Nat}, memK x l = true → x ∈ l
  | [], h => absurd h Bool.false_ne_true
  | y :: l, h => by
    rcases orB_true (a := Nat.beq x y) (b := memK x l) h with h1 | h1
    · rw [Nat.eq_of_beq_eq_true h1]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (memK_mem h1)

theorem allK_spec {f : Nat → Bool} : ∀ {l : List Nat}, allK f l = true → ∀ x ∈ l, f x = true
  | [], _, x, hx => absurd hx List.not_mem_nil
  | y :: l, h, x, hx => by
    obtain ⟨h1, h2⟩ := andB_true (a := f y) (b := allK f l) h
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h1
    · exact allK_spec h2 x hx

theorem strictN_eq' (y : Nat) (k : Nat → Nat) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

theorem x2_enc : WfA x2R ∧ encR x2R = L2 := by
  have hs : 2 < (locMats ()).size := by simp [locMats, localWords]
  have h := loc_gens 2
  have e : x2R = (locMats ())[2]?.getD (idRows ()) := by
    rw [x2R, locM, getElem!_pos _ 2 hs, Array.getElem?_eq_getElem hs, Option.getD_some]
  rw [e]
  exact h

theorem s7_enc : WfA sevenR ∧ encR sevenR = S7 := by
  refine ⟨wf_powRows x2_enc.1 3, ?_⟩
  rw [sevenR, enc_powRows hK x2_enc.1, x2_enc.2]
  rfl

theorem ordF : eqRows (powRows sevenR 7) idRows = true ∧ eqRows sevenR idRows = false := by
  obtain ⟨h1, h2⟩ := andB_true ch4219o
  refine ⟨?_, ?_⟩
  · rw [eqRows_eq (wf_powRows s7_enc.1 7) wf_idRows, enc_powRows hK s7_enc.1, s7_enc.2,
      enc_idRows hK]
    exact h1
  · rw [eqRows_eq s7_enc.1 wf_idRows, s7_enc.2, enc_idRows hK]
    exact notB_true h2

theorem pts_of {ℓ cap bits : Nat} {CH SPC : List (List Nat)} {P0 : List Nat} (hcap : cap < 2 ^ bits)
    (h32 : 4 * 2 ^ bits < 2 ^ 32) (hsize : sizeK cap CH SPC = true)
    (htree : ∀ i < CH.length, vtB rm (rep 1 128 1024) [L0, L1, L2] (vptsK rm (repK ℓ) CH.flatten)
      (CH.getD i []) (P0.getD i 0) (1 + 1024 * i) = true)
    (hsinc : sincK SPC.flatten 0 = true)
    (hin : ∀ i < (pchK rm (repK ℓ) CH).length,
      inSK ((pchK rm (repK ℓ) CH).getD i []) SPC.flatten = true)
    (hsp : ∀ i < SPC.length, spInK (SPC.getD i []) (pchK rm (repK ℓ) CH) = true)
    (hcl : ∀ i < (pchK rm (repK ℓ) CH).length,
      clB rm (rep 1 128 1024) [L0, L1, L2] ((pchK rm (repK ℓ) CH).getD i []) SPC.flatten = true) :
    ∀ v, v ∈ (vorbit locTabs (pathVec (repPaths.getD ℓ [])) cap bits).pts ↔
      v.wf = true ∧ v2N v ∈ vptsK rm (repK ℓ) CH.flatten := by
  obtain ⟨hw, hv⟩ := pathVec_enc (repPaths.getD ℓ [])
  have hr : v2N (pathVec (repPaths.getD ℓ [])) = repK ℓ := hv
  simp only [sizeK, andB_eq, Bool.and_eq_true] at hsize
  obtain ⟨h1, h2, h3, h4, h5⟩ := hsize
  rw [← hr] at htree hin hsp hcl ⊢
  exact vorbit_pts_iff hK (mats := locMats ()) (Ms := [L0, L1, L2]) (by simp [locMats, localWords])
    loc_gens hw hcap h32 LRs_eq (B := 1024) (by decide) (by decide) (Nat.eq_of_beq_eq_true h1)
    (fun i hi => Nat.eq_of_beq_eq_true (allR_spec h3 i (by omega)))
    (fun ch hch => Nat.le_of_ble_eq_true (List.all_eq_true.1 h4 ch hch)) htree hsinc
    (Nat.eq_of_beq_eq_true h2)
    (fun sc hsc => Nat.le_trans (Nat.le_of_ble_eq_true (List.all_eq_true.1 h5 sc hsc)) (by decide))
    (forall_mem_of_getD (f := fun pc => inSK pc SPC.flatten) hin)
    (forall_mem_of_getD (f := fun sc => spInK sc (pchK rm (v2N (pathVec (repPaths.getD ℓ []))) CH)) hsp)
    (forall_mem_of_getD (f := fun pc => clB rm (rep 1 128 1024) [L0, L1, L2] pc SPC.flatten) hcl)

theorem pts5 : ∀ v, v ∈ orbS5.pts ↔ v.wf = true ∧ v2N v ∈ vptsK rm (repK 5) CH5.flatten :=
  pts_of (ℓ := 5) (P0 := P05) (by decide) (by decide) size5 T5.all sinc5 (inSK_chunks (SQ := SQ5) I5.all)
    (spInK_chunks (SQ := SQ5) rfl I5.all S5.all) C5.all

theorem fixed_iff {v : V2} (hv : v.wf = true) :
    (frApply (frTable sevenR) v).beq v = true ↔ fixK S7R (v2N v) = true := by
  rw [V2.beq_iff]
  constructor
  · intro h
    have e := congrArg v2N h
    rw [v2N_frApply hK s7_enc.1 hv, s7_enc.2, ← vecLJ_rowsOfJ] at e
    unfold fixK S7R
    rw [e]
    exact Nat.beq_refl _
  · intro h
    apply VOrbBFS.v2N_inj
    rw [v2N_frApply hK s7_enc.1 hv, s7_enc.2, ← vecLJ_rowsOfJ]
    exact Nat.eq_of_beq_eq_true h

theorem getD_mem4 {i : Nat} (hi : i < 4) : sevenFix.getD i rootV ∈ sevenFix := by
  have hl : sevenFix.length = 4 := rfl
  rw [List.getD_eq_getElem _ _ (by rw [hl]; exact hi)]
  exact List.getElem_mem _

theorem mem_SFK {v : V2} : v2N v ∈ SFK ↔ v ∈ sevenFix := by
  simp only [SFK, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro (h | h | h | h) <;> rw [VOrbBFS.v2N_inj h] <;> exact getD_mem4 (by norm_num)
  · intro hv
    obtain ⟨j, hj, hjv⟩ := List.getElem_of_mem hv
    have hl : sevenFix.length = 4 := rfl
    have hj4 : j < 4 := by rw [← hl]; exact hj
    have e : v = sevenFix.getD j rootV := by
      rw [List.getD_eq_getElem _ _ hj]
      exact hjv.symm
    rw [e]
    interval_cases j
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))

theorem wfF : ∀ v ∈ sevenFix, v.wf = true := by decide

theorem fix5 : ∀ v, v ∈ fixedS sevenR orbS5 ↔ v ∈ sevenFix := by
  intro v
  have hmem : v ∈ fixedS sevenR orbS5 ↔
      v ∈ orbS5.pts ∧ (frApply (frTable sevenR) v).beq v = true := by
    simp [fixedS]
  rw [hmem]
  constructor
  · rintro ⟨hp, hfx⟩
    obtain ⟨hw, hA⟩ := (pts5 v).1 hp
    have hf := (fixed_iff hw).1 hfx
    refine mem_SFK.1 (memK_mem ?_)
    rcases List.mem_cons.1 hA with h0 | h1
    · rw [h0] at hf ⊢
      rcases orB_true ch4219r with h | h
      · rw [hf] at h
        exact absurd h Bool.false_ne_true
      · exact h
    · obtain ⟨e, he, hev⟩ := List.mem_map.1 h1
      obtain ⟨ch, hch, hech⟩ := List.mem_flatten.1 he
      obtain ⟨i, hi, hci⟩ := List.mem_iff_getElem.1 hch
      have hi15 : i < 15 := by rw [← Nat.eq_of_beq_eq_true ch4219len]; exact hi
      have hc := allK_spec (f := fun e => orB (notB (fixK S7R (Nat.land e rm)))
        (memK (Nat.land e rm) SFK)) (l := CH5.getD i []) (ch4219f.all i hi15) e
        (by rw [List.getD_eq_getElem _ _ hi, hci]; exact hech)
      rw [← hev] at hf ⊢
      rcases orB_true hc with h | h
      · rw [hf] at h
        exact absurd h Bool.false_ne_true
      · exact h
  · intro hv
    have hw := wfF v hv
    obtain ⟨h1, h2⟩ := andB_true (allK_spec ch4219s (v2N v) (mem_SFK.2 hv))
    exact ⟨(pts5 v).2 ⟨hw, memK_mem h2⟩, (fixed_iff hw).2 h1⟩

theorem actF : ∀ c < 2048, actMask c = actX c ∧ actMask c < 2048 := fun c hc => by
  have e : actMask c = actX c := by
    simp [actMask, actTab, Array.getD, hc]
  have h := andB_true (CFSG.KS.allN_spec ch4219a c hc)
  refine ⟨e, ?_⟩
  rw [e, ← Nat.eq_of_beq_eq_true h.2]
  exact Nat.le_of_ble_eq_true h.1

theorem itK_eq : ∀ j, ∀ c < 2048, actIter j c = itK j c ∧ itK j c < 2048
  | 0, c, hc => ⟨rfl, hc⟩
  | j + 1, c, hc => by
    obtain ⟨e, hl⟩ := itK_eq j c hc
    have h := andB_true (CFSG.KS.allN_spec ch4219a _ hl)
    have e2 : actIter (j + 1) c = actMask (actIter j c) := rfl
    have e3 : itK (j + 1) c = CFSG.KC.Enum.pg 11 (CFSG.KS.mask 11) AT (itK j c) := rfl
    refine ⟨?_, ?_⟩
    · rw [e2, e, (actF _ hl).1, e3, ← Nat.eq_of_beq_eq_true h.2]
    · rw [e3]
      exact Nat.le_of_ble_eq_true h.1

theorem cntN_eq (p : Nat → Bool) : ∀ n, ((List.range n).filter p).length = cntN n p
  | 0 => by simp [cntN]
  | n + 1 => by
    have e : cntN (n + 1) p = Bool.rec (motive := fun _ => Nat) (cntN n p) (Nat.succ (cntN n p))
        (p n) :=
      strictN_eq' (cntN n p) (fun a => Bool.rec (motive := fun _ => Nat) a (Nat.succ a) (p n))
    rw [List.range_succ, List.filter_append, List.length_append, cntN_eq p n, e]
    cases h : p n <;> simp [h]

theorem beq0 (a : Nat) : (a == 0) = Nat.beq a 0 := by cases a <;> rfl

theorem cntF_eq (k : Nat) : cntF k = cntK k := by
  unfold cntF cntK
  rw [List.filter_congr (q := fun c => Nat.beq (Nat.xor (Nat.xor (itK (k * 3) c) (itK k c)) c) 0)
    (fun c hc => by
      have hc' := List.mem_range.1 hc
      rw [(itK_eq _ c hc').1, (itK_eq _ c hc').1, beq0]
      rfl), cntN_eq]

theorem cntFs_eq (k : Nat) : cntFs k = cntsK k := by
  unfold cntFs cntsK
  rw [List.filter_congr (q := fun c => Nat.beq (Nat.xor (Nat.xor (itK (k * 3) c) (itK (k * 2) c)) c) 0)
    (fun c hc => by
      have hc' := List.mem_range.1 hc
      rw [(itK_eq _ c hc').1, (itK_eq _ c hc').1, beq0]
      rfl), cntN_eq]

theorem cntF_ne : ∀ k ∈ List.range' 1 6, cntF k ≠ cntFs k := fun k hk => by
  rw [List.mem_range'_1] at hk
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have h := notB_true (CFSG.KS.allN_spec ch4219c m (by omega))
  rw [cntF_eq, cntFs_eq]
  intro e
  rw [e, Nat.beq_refl] at h
  exact Bool.noConfusion h

end CertificateChecks.KernelJ4Q.C4219

public section

namespace Certificates

open CertificateChecks

open CFSG.Quasithin.J4Seven CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2 in
theorem certificate4219 : eqRows (CFSG.Sporadic.J4.Native.powRows sevenR 7) idRows = true ∧ eqRows sevenR idRows = false ∧
    (sevenR.size = 112 ∧ ∀ v ∈ sevenR, v.wf = true) ∧
    vorbOK locTabsS rep5S orbS5 15180 = true ∧
    (∀ v, v ∈ fixedS sevenR orbS5 ↔ v ∈ sevenFix) ∧ (∀ v ∈ sevenFix, v.wf = true) ∧
    rootV.wf = true ∧ (∀ v ∈ sevenFix, v.beq rootV = false) ∧
    (∀ i < 4, ∀ j < 4, i ≠ j → (sevenFix.getD i rootV).beq (sevenFix.getD j rootV) = false) ∧
    (∀ c < 2048, actMask c = actX c ∧ actMask c < 2048) ∧
    (∀ k ∈ List.range' 1 6, cntF k ≠ cntFs k) :=
  ⟨KernelJ4Q.C4219.ordF.1, KernelJ4Q.C4219.ordF.2,
    ⟨KernelJ4Q.C4219.s7_enc.1.1, fun v hv =>
      (Array.all_eq_true_iff_forall_mem.1 KernelJ4Q.C4219.s7_enc.1.2) v hv⟩,
    orb5_vorbOK, KernelJ4Q.C4219.fix5, KernelJ4Q.C4219.wfF, by decide, by decide, by decide,
    KernelJ4Q.C4219.actF, KernelJ4Q.C4219.cntF_ne⟩

end Certificates

end
