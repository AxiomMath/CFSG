module

public import Certificates.Kernel.AutJ2Vtx.TblChk
public import Certificates.Kernel.AutJ2Vtx.Tabs
public import Certificates.Kernel.Sporadic.OddCore.MulHGlue
public import CFSG.Certificates.Kernel.BfsPinSetSound
public import CFSG.Certificates.Kernel.BfsPinAlg

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelAJV

open CFSG.Quasithin.F112R.St84.AutJ2Model CFSG.ComponentClassification.J2Cover
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.BfsPin

noncomputable abbrev tt (k : Nat) : Table := tabT (unpack 315 9 (AJT k))

abbrev Cn (p : Nat) : Prop := canonK 315 9 (mask 9) (315 * 9) p = true

theorem hn : szOK 315 9 = true := by decide

theorem hidc : Cn (pidn 315 9) := (CFSG.KC.BfsPin.PP.id hn).1

theorem hid : idT 315 = tabT (unpack 315 9 (pidn 315 9)) := by
  rw [idT_tabT, CFSG.KC.BfsPin.idA_eq hn]

theorem inv_spec {k : Nat} (hk : k < 22) :
    Cn (AJT k) ∧ Cn (AJI k) ∧ invEqK 315 9 (mask 9) (315 * 9) (AJT k) (AJI k) = true := by
  have h := allN_spec inv_ok k hk
  simp only [bAnd_iff] at h
  exact h

theorem binds : sylowStrong.getD 0 #[] = unpack 315 9 (AJT 0) ∧
    sylowStrong.getD 1 #[] = unpack 315 9 (AJT 1) ∧ sylowStrong.getD 2 #[] = unpack 315 9 (AJT 2) ∧
    autStrong.getD 0 #[] = unpack 315 9 (AJT 3) ∧ autStrong.getD 1 #[] = unpack 315 9 (AJT 4) ∧
    outerArr = unpack 315 9 (AJT 5) := by
  have h := binds_ok
  simp only [bAnd_iff] at h
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h
  exact ⟨eq_unpack_of_bindListK h0, eq_unpack_of_bindListK h1, eq_unpack_of_bindListK h2,
    eq_unpack_of_bindListK h3, eq_unpack_of_bindListK h4, eq_unpack_of_bindListK h5⟩

theorem words : AJT 6 = wK abuL [2, 3, 1, 2, 2, 1, 3, 3, 3, 3, 3, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3,
      3, 1] ∧ AJT 7 = wK abuL [2, 3, 2] ∧ AJT 8 = wK sylL [2, 3, 1, 3, 3, 3] ∧
    AJT 9 = wK sylL [1, 1, 3, 3, 3, 3] ∧ AJT 10 = wK sylL [2, 1, 2, 1] ∧
    AJT 11 = wK sylL [2, 3, 3, 1] ∧ AJT 12 = wK sylL [2] ∧ AJT 13 = wK q2L [1, 1, 2] ∧
    AJT 14 = wK sylL [3, 1, 3, 1, 3, 3] ∧ AJT 15 = wK sylL [1, 1, 1, 3, 2, 1] ∧
    AJT 16 = wK sylL [2, 1, 3, 2, 1, 3] ∧ AJT 17 = wK sylL [1, 1, 1, 2, 3, 1] ∧
    AJT 18 = wK sylL [1, 1, 3, 1, 2, 3] ∧ AJT 19 = wK sylL [1, 1, 1, 2, 1] ∧
    AJT 20 = wK s1L [2, 4, 3, 4, 2, 3] ∧ AJT 21 = wK s1L [3, 4, 3, 4, 1, 4] := by
  have h := words_ok
  simp only [bAnd_iff, Nat.beq_eq] at h
  exact h

theorem sylT_eq : sylT = [tt 0, tt 1, tt 2] := by
  have e : (sylowStrong.extract 0 3).toList =
      [sylowStrong.getD 0 #[], sylowStrong.getD 1 #[], sylowStrong.getD 2 #[]] := by rfl
  unfold sylT
  rw [e, List.map_cons, List.map_cons, List.map_cons, List.map_nil, binds.1, binds.2.1,
    binds.2.2.1]
  rfl

theorem abuT_eq : abuT = [tt 3, tt 4, tt 5] := by
  have e0 : autStrong[0]! = autStrong.getD 0 #[] := rfl
  have e1 : autStrong[1]! = autStrong.getD 1 #[] := rfl
  unfold abuT
  rw [e0, e1, binds.2.2.2.1, binds.2.2.2.2.1, binds.2.2.2.2.2]
  rfl

theorem word_of {gs : List Table} {L : Nat → Nat} {wd : List Nat}
    (hw : ∀ l ∈ wd, 1 ≤ l ∧ l ≤ gs.length)
    (hL : ∀ l, 1 ≤ l → l ≤ gs.length → gs.getD (l - 1) (idT 315) = tabT (unpack 315 9 (L l)) ∧
      Cn (L l)) :
    wordTbl 315 gs wd = tabT (unpack 315 9 (wK L wd)) :=
  (wordTbl_unpack hid hidc fun l hl => hL l (hw l hl).1 (hw l hl).2).1

theorem abuL_ok : ∀ l, 1 ≤ l → l ≤ [tt 3, tt 4, tt 5].length →
    [tt 3, tt 4, tt 5].getD (l - 1) (idT 315) = tabT (unpack 315 9 (abuL l)) ∧ Cn (abuL l) := by
  intro l h1 h2
  simp only [List.length_cons, List.length_nil] at h2
  interval_cases l
  · exact ⟨rfl, (inv_spec (k := 3) (by norm_num)).1⟩
  · exact ⟨rfl, (inv_spec (k := 4) (by norm_num)).1⟩
  · exact ⟨rfl, (inv_spec (k := 5) (by norm_num)).1⟩

theorem sylL_ok : ∀ l, 1 ≤ l → l ≤ [tt 0, tt 1, tt 2].length →
    [tt 0, tt 1, tt 2].getD (l - 1) (idT 315) = tabT (unpack 315 9 (sylL l)) ∧ Cn (sylL l) := by
  intro l h1 h2
  simp only [List.length_cons, List.length_nil] at h2
  interval_cases l
  · exact ⟨rfl, (inv_spec (k := 0) (by norm_num)).1⟩
  · exact ⟨rfl, (inv_spec (k := 1) (by norm_num)).1⟩
  · exact ⟨rfl, (inv_spec (k := 2) (by norm_num)).1⟩

theorem q2L_ok : ∀ l, 1 ≤ l → l ≤ [tt 8, tt 9, tt 10, tt 11].length →
    [tt 8, tt 9, tt 10, tt 11].getD (l - 1) (idT 315) = tabT (unpack 315 9 (q2L l)) ∧
      Cn (q2L l) := by
  intro l h1 h2
  simp only [List.length_cons, List.length_nil] at h2
  interval_cases l
  · exact ⟨rfl, (inv_spec (k := 8) (by norm_num)).1⟩
  · exact ⟨rfl, (inv_spec (k := 9) (by norm_num)).1⟩
  · exact ⟨rfl, (inv_spec (k := 10) (by norm_num)).1⟩
  · exact ⟨rfl, (inv_spec (k := 11) (by norm_num)).1⟩

theorem s1L_ok : ∀ l, 1 ≤ l → l ≤ [tt 0, tt 1, tt 2, tt 7].length →
    [tt 0, tt 1, tt 2, tt 7].getD (l - 1) (idT 315) = tabT (unpack 315 9 (s1L l)) ∧
      Cn (s1L l) := by
  intro l h1 h2
  simp only [List.length_cons, List.length_nil] at h2
  interval_cases l
  · exact ⟨rfl, (inv_spec (k := 0) (by norm_num)).1⟩
  · exact ⟨rfl, (inv_spec (k := 1) (by norm_num)).1⟩
  · exact ⟨rfl, (inv_spec (k := 2) (by norm_num)).1⟩
  · exact ⟨rfl, (inv_spec (k := 7) (by norm_num)).1⟩

theorem abuW {wd : List Nat} (hw : ∀ l ∈ wd, 1 ≤ l ∧ l ≤ 3) :
    wordTbl 315 abuT wd = tabT (unpack 315 9 (wK abuL wd)) := by
  rw [abuT_eq]
  exact word_of hw abuL_ok

theorem sylW {wd : List Nat} (hw : ∀ l ∈ wd, 1 ≤ l ∧ l ≤ 3) :
    wordTbl 315 sylT wd = tabT (unpack 315 9 (wK sylL wd)) := by
  rw [sylT_eq]
  exact word_of hw sylL_ok

theorem gWT_eq : gWT = tt 6 := by
  unfold gWT
  rw [abuW (wd := [2, 3, 1, 2, 2, 1, 3, 3, 3, 3, 3, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 3, 1])
    (by decide), ← words.1]

theorem g1T_eq : g1T = tt 7 := by
  unfold g1T
  rw [abuW (wd := [2, 3, 2]) (by decide), ← words.2.1]

theorem s1W {wd : List Nat} (hw : ∀ l ∈ wd, 1 ≤ l ∧ l ≤ 4) :
    wordTbl 315 (sylT ++ [g1T]) wd = tabT (unpack 315 9 (wK s1L wd)) := by
  rw [sylT_eq, g1T_eq]
  exact word_of hw s1L_ok

theorem q2T_eq : q2T = [tt 8, tt 9, tt 10, tt 11] := by
  obtain ⟨-, -, w8, w9, w10, w11, -⟩ := words
  unfold q2T
  rw [List.map_cons, List.map_cons, List.map_cons, List.map_cons, List.map_nil,
    sylW (wd := [2, 3, 1, 3, 3, 3]) (by decide), sylW (wd := [1, 1, 3, 3, 3, 3]) (by decide),
    sylW (wd := [2, 1, 2, 1]) (by decide), sylW (wd := [2, 3, 3, 1]) (by decide),
    ← w8, ← w9, ← w10, ← w11]

theorem q2W {wd : List Nat} (hw : ∀ l ∈ wd, 1 ≤ l ∧ l ≤ 4) :
    wordTbl 315 q2T wd = tabT (unpack 315 9 (wK q2L wd)) := by
  rw [q2T_eq]
  exact word_of hw q2L_ok

theorem umT_eq : umT = tt 12 := by
  unfold umT
  rw [sylW (wd := [2]) (by decide), ← words.2.2.2.2.2.2.1]

theorem vmT_eq : vmT = tt 13 := by
  unfold vmT
  rw [q2W (wd := [1, 1, 2]) (by decide), ← words.2.2.2.2.2.2.2.1]

theorem e1RT_eq : e1RT = tt 14 := by
  unfold e1RT
  rw [sylW (wd := [3, 1, 3, 1, 3, 3]) (by decide), ← words.2.2.2.2.2.2.2.2.1]

theorem e2RT_eq : e2RT = tt 15 := by
  unfold e2RT
  rw [sylW (wd := [1, 1, 1, 3, 2, 1]) (by decide), ← words.2.2.2.2.2.2.2.2.2.1]

theorem f1RT_eq : f1RT = tt 16 := by
  unfold f1RT
  rw [sylW (wd := [2, 1, 3, 2, 1, 3]) (by decide), ← words.2.2.2.2.2.2.2.2.2.2.1]

theorem f2RT_eq : f2RT = tt 17 := by
  unfold f2RT
  rw [sylW (wd := [1, 1, 1, 2, 3, 1]) (by decide), ← words.2.2.2.2.2.2.2.2.2.2.2.1]

theorem tmRT_eq : tmRT = tt 18 := by
  unfold tmRT
  rw [sylW (wd := [1, 1, 3, 1, 2, 3]) (by decide), ← words.2.2.2.2.2.2.2.2.2.2.2.2.1]

theorem gmRT_eq : gmRT = tt 19 := by
  unfold gmRT
  rw [sylW (wd := [1, 1, 1, 2, 1]) (by decide), ← words.2.2.2.2.2.2.2.2.2.2.2.2.2.1]

theorem bmRT_eq : bmRT = tt 20 := by
  unfold bmRT
  rw [s1W (wd := [2, 4, 3, 4, 2, 3]) (by decide), ← words.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]

theorem rmRT_eq : rmRT = tt 21 := by
  unfold rmRT
  rw [s1W (wd := [3, 4, 3, 4, 1, 4]) (by decide), ← words.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2]

theorem tbls_eq : autJ2Tbls = (List.range 22).map tt := by
  unfold autJ2Tbls
  rw [sylT_eq, abuT_eq, gWT_eq, g1T_eq, q2T_eq, umT_eq, vmT_eq, e1RT_eq, e2RT_eq, f1RT_eq,
    f2RT_eq, tmRT_eq, gmRT_eq, bmRT_eq, rmRT_eq]
  rfl

theorem c0 : autJ2VtxC0 () = true := by
  unfold autJ2VtxC0
  rw [tbls_eq, Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  constructor
  · intro t ht
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 ht
    obtain ⟨c1, -, c3⟩ := inv_spec (List.mem_range.1 hk)
    exact permOK_unpack c1 c3
  · intro t ht
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 ht
    obtain ⟨c1, c2, c3⟩ := inv_spec (List.mem_range.1 hk)
    rw [invT_unpack (lt_of_canonK c2) c3]
    exact invOK_unpack c1 c2 c3

end CertificateChecks.KernelAJV

end
