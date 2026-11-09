module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.QuadDataDefs
public import Certificates.Certificate11003
import CFSG.Certificates.Kernel.Sym6SqSound
import Certificates.Kernel.LocalQT.Syl.C4137
import CFSG.Certificates.Kernel.Common.Harness

namespace CertificateChecks.Batch24846

open Equiv CFSG.KC.LQT.P CFSG.KC.LQT.W CFSG.KC.LQT.Syl CFSG.KC.Sym6Sq CFSG.KD.LQT.C4137
  CFSG.QuasithinUnique.Setup.X1 CFSG.Sporadic.Schreier CFSG.Blueprint
  CFSG.EvenSporadicStandard.M24Std

def qfxRec : List (ℕ × ℕ × ℕ × ℕ) :=
  [(1, 0, 1, 0), (1, 0, 1, 0), (1, 4, 19, 1), (1, 4, 32, 0), (1, 5, 17, 0), (1, 5, 13, 1),
    (1, 1, 1, 0), (1, 4, 30, 1), (1, 2, 34, 0), (1, 3, 18, 0), (1, 2, 6, 1), (1, 5, 2, 0),
    (1, 5, 42, 1), (1, 4, 24, 1), (1, 3, 57, 1), (1, 4, 19, 0), (1, 5, 40, 0), (1, 4, 24, 0),
    (1, 2, 34, 1), (1, 3, 8, 0), (1, 3, 57, 0), (1, 4, 9, 0), (22, 0, 22, 0), (22, 2, 25, 0),
    (1, 3, 10, 0), (22, 1, 22, 1), (22, 4, 55, 1), (1, 5, 42, 0), (1, 6, 27, 0), (22, 5, 41, 1),
    (1, 3, 8, 1), (22, 2, 59, 0), (1, 3, 18, 1), (1, 4, 32, 1), (1, 1, 1, 1), (1, 6, 51, 1),
    (1, 4, 45, 0), (22, 3, 31, 1), (22, 3, 61, 0), (1, 5, 13, 0), (1, 4, 30, 0), (22, 4, 46, 0),
    (1, 4, 20, 1), (22, 4, 38, 1), (1, 5, 15, 0), (1, 3, 10, 1), (22, 3, 31, 0), (22, 2, 25, 1),
    (1, 4, 20, 0), (1, 5, 17, 1), (1, 5, 48, 1), (1, 5, 2, 1), (1, 6, 5, 0), (22, 4, 46, 1),
    (1, 5, 15, 1), (22, 3, 61, 1), (1, 6, 54, 0), (1, 2, 6, 0), (22, 4, 37, 1), (22, 1, 22, 0),
    (1, 4, 9, 1), (22, 2, 59, 1), (22, 4, 55, 0), (1, 5, 40, 1)]

noncomputable def qfCj (c x : ℕ) : ℕ := mul 24 (mul 24 c x) (inv 24 c)

noncomputable def qfRow (E : List ℕ) (c1 c2 : ℕ) (R : List (ℕ × ℕ × ℕ × ℕ)) (k : ℕ) : Bool :=
  let r := R.getD k (0, 0, 0, 0)
  let q := R.getD r.2.2.1 (0, 0, 0, 0)
  (r.1 == 1 || r.1 == 22) && r.2.1 ≤ 12 &&
    (if r.2.1 = 0 then k == r.1 else
      q.1 == r.1 && q.2.1 + 1 == r.2.1 && 1 ≤ r.2.2.1 && r.2.2.1 < 64 &&
        qfCj (if r.2.2.2 = 0 then c1 else c2) (E.getD r.2.2.1 (one 24)) == E.getD k (one 24))

noncomputable def qfReachChk (E : List ℕ) (c1 c2 : ℕ) (R : List (ℕ × ℕ × ℕ × ℕ)) : Bool :=
  E.getD 0 (one 24) == one 24 && (List.range' 1 63).all (qfRow E c1 c2 R)

noncomputable def qfBaseChk (E : List ℕ) (a : ℕ) (cs : List ℕ) : Bool :=
  cs.all (fun c => qfCj c a == a) &&
    E.all fun x => !(cs.all fun c => qfCj c x == x) || x == one 24 || x == a

noncomputable def qfReachK : Bool :=
  forceA (lstK 24 6 (rlGK 24 GC m24RGens m24E1Bw)) fun E =>
    strictA (evalZK 24 GC wordQdG1) fun c1 => strictA (evalZK 24 GC wordQdG2) fun c2 =>
      qfReachChk E c1 c2 qfxRec

noncomputable def qfBaseK (j : ℕ) (ws : List (List ℤ)) : Bool :=
  forceA (lstK 24 6 (rlGK 24 GC m24RGens m24E1Bw)) fun E =>
    forceA (ws.map (evalZK 24 GC)) fun cs => qfBaseChk E (E.getD j (one 24)) cs

theorem qfReach_ok : qfReachK = true := by quickRfl

theorem qfBase1_ok : qfBaseK 1 [wordQdS11, wordQdS12, wordQdS13] = true := by quickRfl

theorem qfBase2_ok : qfBaseK 22 [wordQdS21, wordQdS22, wordQdS23] = true := by quickRfl

theorem qfNorm_ok : [wordQdG1, wordQdG2, wordQdS11, wordQdS12, wordQdS13, wordQdS21, wordQdS22,
    wordQdS23].all (fun w => normChk GC m24RGens m24E1Bw w) = true := by quickRfl

local notation "cd" => fun x : S24 => codeP (x : Perm (Fin 24))

theorem qfCj_code (g x : S24) : qfCj (codeP (g : Perm (Fin 24))) (codeP (x : Perm (Fin 24))) =
    codeP ((g * x * g⁻¹ : S24) : Perm (Fin 24)) := by
  rw [qfCj, ciS, cmS, cmS]

theorem qfE_getD (j : ℕ) : (m24E1l.map cd).getD j (one 24) = codeP ((m24E1l.getD j 1 : S24) :
    Perm (Fin 24)) := by
  rw [c1S, List.getD_map]

theorem qfNorm_w (w : List ℤ) (h : normChk GC m24RGens m24E1Bw w = true) :
    QdNormChk (m24Cj w) := by
  unfold normChk at h
  rw [forceA_eq, ← codesE hG, ← codeW hG] at h
  unfold CFSG.KC.Sym6Sq.normK at h
  rw [strictA_eq, ciS, CFSG.KC.LQT.P.allL_iff] at h
  intro x hx
  have := h _ (List.mem_map_of_mem hx)
  rw [CFSG.KC.LQT.P.andB_iff, CFSG.KC.LQT.P.blt_iff, CFSG.KC.LQT.P.blt_iff, cmS, cmS, cmS, cmS,
    mem_iff, mem_iff] at this
  exact this

theorem qfNorm_all : ∀ w ∈ [wordQdG1, wordQdG2, wordQdS11, wordQdS12, wordQdS13, wordQdS21,
    wordQdS22, wordQdS23], QdNormChk (m24Cj w) := by
  have h := qfNorm_ok
  rw [List.all_eq_true] at h
  exact fun w hw => qfNorm_w w (h w hw)

theorem qdReach_succ_of {gs : List S24} {a x : S24} {n : ℕ} (hx : x ∈ qdReach gs a n) :
    x ∈ qdReach gs a (n + 1) := by
  rw [qdReach, qdStep, List.mem_dedup]
  exact List.mem_append_left _ hx

theorem qdReach_conj {gs : List S24} {a x g : S24} {n : ℕ} (hx : x ∈ qdReach gs a n)
    (hg : g ∈ gs) : g * x * g⁻¹ ∈ qdReach gs a (n + 1) := by
  rw [qdReach, qdStep, List.mem_dedup]
  refine List.mem_append_right _ (List.mem_flatMap.2 ⟨g, hg, List.mem_map.2 ⟨x, hx, ?_⟩⟩)
  rw [normH_eq]

theorem qdReach_mono {gs : List S24} {a x : S24} {n : ℕ} (hx : x ∈ qdReach gs a n) :
    ∀ m, n ≤ m → x ∈ qdReach gs a m := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => exact hx
  | succ m _ ih => exact qdReach_succ_of ih

theorem qfReach_sound {R : List (ℕ × ℕ × ℕ × ℕ)}
    (h : qfReachChk (m24E1l.map cd) (codeP ((m24Cj wordQdG1 : S24) : Perm (Fin 24)))
      (codeP ((m24Cj wordQdG2 : S24) : Perm (Fin 24))) R = true) :
    m24E1l.getD 0 1 = 1 ∧ ∀ k, 1 ≤ k → k < 64 →
      ((R.getD k (0, 0, 0, 0)).1 = 1 ∨ (R.getD k (0, 0, 0, 0)).1 = 22) ∧
      m24E1l.getD k 1 ∈ qdReach qdGens (m24E1l.getD (R.getD k (0, 0, 0, 0)).1 1) qdDepth := by
  rw [qfReachChk, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, qfE_getD, c1S] at h
  obtain ⟨h0, hr⟩ := h
  have hrow : ∀ k, 1 ≤ k → k < 64 → qfRow (m24E1l.map cd) (codeP ((m24Cj wordQdG1 : S24) :
      Perm (Fin 24))) (codeP ((m24Cj wordQdG2 : S24) : Perm (Fin 24))) R k = true :=
    fun k h1 h2 => hr k (List.mem_range'_1.2 ⟨h1, by omega⟩)
  refine ⟨cinjS h0, ?_⟩
  have key : ∀ n k, 1 ≤ k → k < 64 → (R.getD k (0, 0, 0, 0)).2.1 = n →
      m24E1l.getD k 1 ∈ qdReach qdGens (m24E1l.getD (R.getD k (0, 0, 0, 0)).1 1) n := by
    intro n
    induction n with
    | zero =>
      intro k h1 h2 hd
      have := hrow k h1 h2
      simp only [qfRow, hd, ite_true, Bool.and_eq_true, beq_iff_eq] at this
      rw [← this.2]
      exact List.mem_singleton_self _
    | succ n ih =>
      intro k h1 h2 hd
      have := hrow k h1 h2
      simp only [qfRow, hd, Nat.succ_ne_zero, ite_false, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq] at this
      obtain ⟨-, ⟨⟨⟨⟨hq1, hq2⟩, hp1⟩, hp2⟩, hc⟩⟩ := this
      have hp := ih _ hp1 hp2 (by omega)
      rw [hq1] at hp
      rw [qfE_getD, qfE_getD] at hc
      have hg : ∀ i : ℕ, (if i = 0 then m24Cj wordQdG1 else m24Cj wordQdG2) ∈ qdGens := by
        intro i
        split
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ List.mem_cons_self
      have hc' : qfCj (codeP (((if (R.getD k (0, 0, 0, 0)).2.2.2 = 0 then m24Cj wordQdG1 else
          m24Cj wordQdG2 : S24)) : Perm (Fin 24))) (codeP ((m24E1l.getD
          (R.getD k (0, 0, 0, 0)).2.2.1 1 : S24) : Perm (Fin 24))) =
          codeP ((m24E1l.getD k 1 : S24) : Perm (Fin 24)) := by
        rw [← hc]
        split <;> rfl
      rw [qfCj_code] at hc'
      rw [← cinjS hc']
      exact qdReach_conj hp (hg _)
  intro k h1 h2
  have := hrow k h1 h2
  simp only [qfRow, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  exact ⟨this.1.1, qdReach_mono (key _ k h1 h2 rfl) _ this.1.2⟩

theorem qfBase_sound {a : S24} {st : List S24} (ha : a ∈ m24E1l)
    (hst : ∀ g ∈ st, QdNormChk g)
    (h : qfBaseChk (m24E1l.map cd) (codeP (a : Perm (Fin 24))) (st.map cd) = true) :
    QdBase a st := by
  rw [qfBaseChk, Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h
  obtain ⟨hf, hE⟩ := h
  refine ⟨ha, fun g hg => ⟨hst g hg, ?_⟩, fun t ht hfix => ?_⟩
  · have := hf _ (List.mem_map_of_mem hg)
    rw [beq_iff_eq, qfCj_code] at this
    exact cinjS this
  · have := hE _ (List.mem_map_of_mem ht)
    have hall : (st.map cd).all (fun c => qfCj c (codeP (t : Perm (Fin 24))) ==
        codeP (t : Perm (Fin 24))) = true := by
      rw [List.all_eq_true]
      intro c hc
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hc
      rw [beq_iff_eq, qfCj_code, hfix g hg]
    rw [hall, Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq, beq_iff_eq, c1S] at this
    exact this.imp cinjS cinjS

theorem qfE_mem (j : ℕ) (hj : j < 64) : m24E1l.getD j 1 ∈ m24E1l := by
  have hl : m24E1l.length = 64 := by simp [m24E1l, m24Lst]
  rw [List.getD_eq_getElem _ _ (by rw [hl]; exact hj)]
  exact List.getElem_mem _

theorem qfCodes_map : ∀ ws : List (List ℤ), ws.map (evalZK 24 GC) = (ws.map m24Cj).map cd
  | [] => rfl
  | w :: ws => by
    rw [List.map_cons, List.map_cons, List.map_cons, qfCodes_map ws, ← codeW hG w]

theorem qfBase_of (j : ℕ) (hj : j < 64) (ws : List (List ℤ))
    (hn : ∀ w ∈ ws, QdNormChk (m24Cj w)) (h : qfBaseK j ws = true) :
    QdBase (m24E1l.getD j 1) (ws.map m24Cj) := by
  unfold qfBaseK at h
  rw [forceA_eq, forceA_eq, ← codesE hG, qfCodes_map, qfE_getD] at h
  refine qfBase_sound (qfE_mem j hj) (fun g hg => ?_) h
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hg
  exact hn w hw

theorem qdFixData_0 : QdFixData := by
  have hN := qfNorm_all
  refine ⟨fun g hg => ?_, fun s hs hs1 => ?_, ?_, ?_⟩
  · have hg' : g ∈ [wordQdG1, wordQdG2].map m24Cj := hg
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hg'
    exact hN w (List.mem_append_left [wordQdS11, wordQdS12, wordQdS13, wordQdS21, wordQdS22,
      wordQdS23] hw)
  · have h := qfReach_ok
    unfold qfReachK at h
    rw [forceA_eq, strictA_eq, strictA_eq, ← codesE hG, ← codeW hG, ← codeW hG] at h
    obtain ⟨h0, hr⟩ := qfReach_sound h
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hs
    have hl : m24E1l.length = 64 := by simp [m24E1l, m24Lst]
    have hk' : m24E1l[k] = m24E1l.getD k 1 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
    rw [hk'] at hs1 ⊢
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | h
      · exact absurd h0 hs1
      · exact h
    obtain ⟨hroot, hm⟩ := hr k hk1 (hl ▸ hk)
    rcases hroot with h1 | h1
    · left
      rw [h1] at hm
      exact hm
    · right
      rw [h1] at hm
      exact hm
  · have := qfBase_of 1 (by norm_num) [wordQdS11, wordQdS12, wordQdS13]
      (fun w hw => hN w (List.mem_append_right [wordQdG1, wordQdG2]
        (List.mem_append_left [wordQdS21, wordQdS22, wordQdS23] hw))) qfBase1_ok
    exact this
  · have := qfBase_of 22 (by norm_num) [wordQdS21, wordQdS22, wordQdS23]
      (fun w hw => hN w (List.mem_append_right [wordQdG1, wordQdG2]
        (List.mem_append_right [wordQdS11, wordQdS12, wordQdS13] hw))) qfBase2_ok
    exact this

end CertificateChecks.Batch24846

namespace Certificates

open CertificateChecks

public theorem certificate24846 : CFSG.EvenSporadicStandard.M24Std.QdFixData := by
  exact CertificateChecks.Batch24846.qdFixData_0

end Certificates
