module

public import Certificates.Kernel.J4M4F.Checks
public import Certificates.Kernel.J4NPVerdict.Tabs
public import Certificates.Kernel.J4Q.Mat
public import CFSG.Certificates.Kernel.J4NPVerdict.Sound
public import CFSG.Certificates.Kernel.J4M4F.Sound
public import CFSG.Certificates.Kernel.J4Q.VOrbBFS

public section

namespace CertificateChecks.KernelJ4M4F

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KD.J4NPV CFSG.KD.J4M4F CFSG.KS.J4M4F CFSG.KC.J4NPV
  CertificateChecks.KernelJ4Q CertificateChecks.KernelJ4NPV CFSG.Quasithin.KGC31.J4M4
  CFSG.Sporadic.J4.Native

theorem andB_iff' {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

theorem orB_iff' {a b : Bool} : orB a b = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> decide

theorem getN_eq' (d : Nat) : ∀ (l : List Nat) (i : Nat), getN d l i = l.getD i d
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => getN_eq' d l i

theorem getD_map_v2N : ∀ (l : List V2) (k : Nat), (l.map v2N).getD k 0 = v2N (l.getD k V2.zero)
  | [], _ => by simp [v2N_zero]
  | _ :: _, 0 => rfl
  | _ :: l, k + 1 => getD_map_v2N l k

theorem beq_of_v2N {a b : V2} (h : v2N a = v2N b) : (a == b) = true := by
  rw [CFSG.KC.J4Q.VOrbBFS.v2N_inj h]
  exact beq_self_eq_true _

theorem rootV_wf7253 : rootV.wf = true := by decide

theorem w_eq : W1 = wordJ c rm one [A, B] [Ai, Bi] w1Word ∧
    W2 = wordJ c rm one [A, B] [Ai, Bi] w2Word := by
  obtain ⟨hw, -⟩ := andB_iff'.1 vj79_w
  obtain ⟨-, hw⟩ := wordsK_spec hw
  exact ⟨hw 0 (by decide), hw 1 (by decide)⟩

theorem wi_eq : wordJ c rm one [A, B] [Ai, Bi] (invW w1Word) = W1i ∧
    wordJ c rm one [A, B] [Ai, Bi] (invW w2Word) = W2i := by
  obtain ⟨h1, h2⟩ := andB_iff'.1 m4i_ok
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2⟩

theorem m4_enc (k : Nat) : WfA ((m4Mats ())[k]?.getD (idRows ())) ∧
    encR ((m4Mats ())[k]?.getD (idRows ())) = getN one [W1, W2] k := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ 2 ≤ k) with rfl | rfl | hk
  · have e : (m4Mats ())[0]?.getD (idRows ()) = wordRows baseMats baseInvs w1Word := rfl
    have h := enc_wordRows hK base_gens base_invs w1Word
    rw [e]
    exact ⟨h.1, h.2.trans w_eq.1.symm⟩
  · have e : (m4Mats ())[1]?.getD (idRows ()) = wordRows baseMats baseInvs w2Word := rfl
    have h := enc_wordRows hK base_gens base_invs w2Word
    rw [e]
    exact ⟨h.1, h.2.trans w_eq.2.symm⟩
  · have e : (m4Mats ())[k]?.getD (idRows ()) = idRows () := by
      unfold m4Mats
      rw [Array.getElem?_eq_none (by simp; omega)]
      rfl
    rw [e, getN_eq', List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨wf_idRows, enc_idRows hK⟩

theorem m4i_enc (k : Nat) : WfA ((m4Invs ())[k]?.getD (idRows ())) ∧
    encR ((m4Invs ())[k]?.getD (idRows ())) = getN one [W1i, W2i] k := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ 2 ≤ k) with rfl | rfl | hk
  · have e : (m4Invs ())[0]?.getD (idRows ()) = wordRows baseMats baseInvs (invW w1Word) := rfl
    have h := enc_wordRows hK base_gens base_invs (invW w1Word)
    rw [e]
    exact ⟨h.1, h.2.trans wi_eq.1⟩
  · have e : (m4Invs ())[1]?.getD (idRows ()) = wordRows baseMats baseInvs (invW w2Word) := rfl
    have h := enc_wordRows hK base_gens base_invs (invW w2Word)
    rw [e]
    exact ⟨h.1, h.2.trans wi_eq.2⟩
  · have e : (m4Invs ())[k]?.getD (idRows ()) = idRows () := by
      unfold m4Invs
      rw [Array.getElem?_eq_none (by simp; omega)]
      rfl
    rw [e, getN_eq', List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨wf_idRows, enc_idRows hK⟩

theorem fWords_length : fWords.length = 10 := rfl

theorem fTab_size : (fTab ()).size = 10 := by
  unfold fTab
  rw [List.size_toArray, List.length_map, fWords_length]

theorem fTab_enc : ∀ j < 10, WfA ((fTab ())[j]?.getD (idRows ())) ∧
    encR ((fTab ())[j]?.getD (idRows ())) = getN one FMs j := by
  intro j hj
  have e : (fTab ())[j]?.getD (idRows ()) = wordRows (m4Mats ()) (m4Invs ()) (fWords.getD j []) := by
    unfold fTab
    rw [List.getElem?_toArray, List.getElem?_map, List.getElem?_eq_getElem (by rw [fWords_length]; omega),
      List.getD_eq_getElem _ _ (by rw [fWords_length]; omega)]
    rfl
  have h := enc_wordRows hK m4_enc m4i_enc (fWords.getD j [])
  obtain ⟨-, hf⟩ := wordsK_spec vj79_f
  have hfm : vjT.fm = FMs := rfl
  rw [hfm] at hf
  have hlen : j < FMs.length := Nat.lt_of_lt_of_le hj (by decide)
  have hfj := hf j hlen
  rw [List.getD_eq_getElem _ _ hlen] at hfj
  rw [e, getN_eq', List.getD_eq_getElem _ _ hlen, hfj]
  exact h

theorem fb_all : ∀ x < 1024, orB (Nat.beq x 0) (neN (fVK rm one FMs (v2N rootV) x) (v2N rootV)) = true := by
  have key : ∀ lo, chkB rm one FMs (v2N rootV) lo 128 = true → ∀ x, lo ≤ x → x < lo + 128 →
      orB (Nat.beq x 0) (neN (fVK rm one FMs (v2N rootV) x) (v2N rootV)) = true := by
    intro lo h x h1 h2
    have := allR_spec h (x - lo) (by omega)
    have e : Nat.add lo (x - lo) = x := by
      simp only [Nat.add_eq]
      omega
    simp only [e] at this
    exact this
  intro x hx
  rcases (by omega : x < 128 ∨ (128 ≤ x ∧ x < 256) ∨ (256 ≤ x ∧ x < 384) ∨ (384 ≤ x ∧ x < 512) ∨
      (512 ≤ x ∧ x < 640) ∨ (640 ≤ x ∧ x < 768) ∨ (768 ≤ x ∧ x < 896) ∨ (896 ≤ x ∧ x < 1024)) with
    h | h | h | h | h | h | h | h
  · exact key 0 fb_ok0 x (by omega) (by omega)
  · exact key 128 fb_ok1 x h.1 (by omega)
  · exact key 256 fb_ok2 x h.1 (by omega)
  · exact key 384 fb_ok3 x h.1 (by omega)
  · exact key 512 fb_ok4 x h.1 (by omega)
  · exact key 640 fb_ok5 x h.1 (by omega)
  · exact key 768 fb_ok6 x h.1 (by omega)
  · exact key 896 fb_ok7 x h.1 (by omega)

theorem chkF_ok : chkF () = true := by
  unfold chkF
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    and_assoc]
  refine ⟨fun i hi => ⟨?_, fun j hj => ?_⟩, fun x hx => ?_, fun w hw j hj => ?_⟩
  · obtain ⟨a1, a2⟩ := fTab_enc i hi
    rw [eqRows_eq (wf_mulRows a1 a1) wf_idRows, enc_mulRows hK a1 a1, a2, enc_idRows hK]
    exact (andB_iff'.1 (allR_spec fa_ok i hi)).1
  · obtain ⟨a1, a2⟩ := fTab_enc i hi
    obtain ⟨b1, b2⟩ := fTab_enc j hj
    rw [eqRows_eq (wf_mulRows a1 b1) (wf_mulRows b1 a1), enc_mulRows hK a1 b1, enc_mulRows hK b1 a1,
      a2, b2]
    exact allR_spec (andB_iff'.1 (allR_spec fa_ok i hi)).2 j hj
  · obtain ⟨v1, v2⟩ := fVec_enc hK fTab_size fTab_enc rootV_wf7253 x
    rcases orB_iff'.1 (fb_all x hx) with h | h
    · exact Or.inl (Nat.eq_of_beq_eq_true h)
    · refine Or.inr ?_
      rw [differs_eq v1 rootV_wf7253, v2]
      exact h
  · obtain ⟨m1, m2⟩ := m4_enc w
    obtain ⟨i1, i2⟩ := m4i_enc w
    obtain ⟨t1, t2⟩ := fTab_enc j hj
    obtain ⟨f1, f2⟩ := fRows_enc hK fTab_enc ((cTab.getD w []).getD j 0)
    rw [eqRows_eq (wf_mulRows (wf_mulRows m1 t1) i1) f1, enc_mulRows hK (wf_mulRows m1 t1) i1,
      enc_mulRows hK m1 t1, m2, t2, i2, f2]
    exact allR_spec (allR_spec fc_ok w hw) j hj

theorem letRows_enc : ∀ l < 4, WfA ((letRows ())[l]?.getD (idRows ())) ∧
    encR ((letRows ())[l]?.getD (idRows ())) = getN one [W1i, W2i, W1, W2] l := by
  intro l hl
  rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl
  · unfold letRows
    rw [Array.getElem?_eq_getElem (by simp), Option.getD_some]
    exact m4i_enc 0
  · unfold letRows
    rw [Array.getElem?_eq_getElem (by simp), Option.getD_some]
    exact m4i_enc 1
  · have e : (letRows ())[2]?.getD (idRows ()) = (m4Mats ())[0]?.getD (idRows ()) := by
      unfold letRows
      simp only [List.getElem?_toArray, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.getD_some]
    rw [e]
    refine ⟨(m4_enc 0).1, (m4_enc 0).2.trans ?_⟩
    simp only [getN_eq', List.getD_cons_zero, List.getD_cons_succ]
  · have e : (letRows ())[3]?.getD (idRows ()) = (m4Mats ())[1]?.getD (idRows ()) := by
      unfold letRows
      simp only [List.getElem?_toArray, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.getD_some]
    rw [e]
    refine ⟨(m4_enc 1).1, (m4_enc 1).2.trans ?_⟩
    simp only [getN_eq', List.getD_cons_zero, List.getD_cons_succ]

theorem chkKW_ok : chkKW () = true := by
  obtain ⟨k1, k2⟩ := andB_iff'.1 kw_ok
  obtain ⟨k2, k3⟩ := andB_iff'.1 k2
  have hwf : ∀ k < 31, (kwVecs.getD k V2.zero).wf = true := by
    intro k hk
    have h := allR_spec k2 k hk
    have hlt := Nat.blt_eq.mp h
    change _ < 2 ^ 112 at hlt
    rw [getD_map_v2N] at hlt
    exact wf_of_bits fun b hb =>
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) hb))
  unfold chkKW
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range]
  refine ⟨?_, fun l hl k hk => ?_⟩
  · have hg := enc_wordRows hK base_gens base_invs gWord
    apply beq_of_v2N
    rw [v2N_frApply hK hg.1 rootV_wf7253, hg.2, ← getD_map_v2N]
    exact Nat.eq_of_beq_eq_true k1
  · obtain ⟨l1, l2⟩ := letRows_enc l hl
    apply beq_of_v2N
    rw [v2N_frApply hK l1 (hwf k hk), l2, ← getD_map_v2N, ← getD_map_v2N]
    exact Nat.eq_of_beq_eq_true (allR_spec (allR_spec k3 l hl) k hk)

end CertificateChecks.KernelJ4M4F

namespace Certificates

open CertificateChecks

theorem certificate7253 : CFSG.Quasithin.KGC31.J4M4.chkF () = true ∧ CFSG.Quasithin.KGC31.J4M4.chkKW () = true :=
  ⟨KernelJ4M4F.chkF_ok, KernelJ4M4F.chkKW_ok⟩

end Certificates
