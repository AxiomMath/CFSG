module

public import Certificates.Kernel.AutJ2Vtx.Glue
public import Certificates.Kernel.AutJ2Vtx.KChk
public import Certificates.Kernel.AutJ2Vtx.C3Chk
public import CFSG.Certificates.Kernel.Spor.SiftEq

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelAJV

open CFSG.Quasithin.F112R.St84.AutJ2Model CFSG.Quasithin.F112R.St84.Heis
open CFSG.ComponentClassification.J2Cover CFSG.Fischer
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.BfsPin

theorem cn {k : Nat} (hk : k < 22) : Cn (AJT k) := (inv_spec hk).1

theorem cni {k : Nat} (hk : k < 22) : Cn (AJI k) := (inv_spec hk).2.1

theorem invT_tt {k : Nat} (hk : k < 22) : invT 315 (tt k) = tabT (unpack 315 9 (AJI k)) :=
  invT_unpack (by norm_num) (inv_spec hk).2.2

theorem powT_unpack {p : Nat} (hp : Cn p) :
    ∀ e, powT 315 e (tabT (unpack 315 9 p)) = tabT (unpack 315 9 (ppK p e)) ∧ Cn (ppK p e)
  | 0 => ⟨hid, hidc⟩
  | e + 1 => by
    obtain ⟨h1, h2⟩ := powT_unpack hp e
    rw [powT, h1, compT_unpack hp h2]
    exact ⟨rfl, canonK_pcomp hp h2⟩

theorem pE_eq {T1 T2 : Table} {P1 P2 : Nat} (h1 : T1 = tabT (unpack 315 9 P1)) (c1 : Cn P1)
    (h2 : T2 = tabT (unpack 315 9 P2)) (c2 : Cn P2) (a : Nat) :
    compT 315 (powT 315 (a % 2) T1) (powT 315 (a / 2) T2) = tabT (unpack 315 9 (pE P1 P2 a)) ∧
      Cn (pE P1 P2 a) := by
  obtain ⟨e1, d1⟩ := powT_unpack c1 (a % 2)
  obtain ⟨e2, d2⟩ := powT_unpack c2 (a / 2)
  rw [h1, h2, e1, e2, compT_unpack d1 d2]
  exact ⟨rfl, canonK_pcomp d1 d2⟩

theorem pEI_eq {T1 T2 : Table} {P1 P2 : Nat} (h1 : T1 = tabT (unpack 315 9 P1)) (c1 : Cn P1)
    (h2 : T2 = tabT (unpack 315 9 P2)) (c2 : Cn P2) (b : Nat) :
    compT 315 (powT 315 (b / 2) T2) (powT 315 (b % 2) T1) = tabT (unpack 315 9 (pEI P1 P2 b)) ∧
      Cn (pEI P1 P2 b) := by
  obtain ⟨e1, d1⟩ := powT_unpack c1 (b % 2)
  obtain ⟨e2, d2⟩ := powT_unpack c2 (b / 2)
  rw [h1, h2, e1, e2, compT_unpack d2 d1]
  exact ⟨rfl, canonK_pcomp d2 d1⟩

theorem EmT_eq (a : F4) : EmT a = tabT (unpack 315 9 (pE (AJT 14) (AJT 15) a.code.val)) ∧
    Cn (pE (AJT 14) (AJT 15) a.code.val) :=
  pE_eq e1RT_eq (cn (by norm_num)) e2RT_eq (cn (by norm_num)) a.code.val

theorem FmT_eq (b : F4) : FmT b = tabT (unpack 315 9 (pE (AJT 16) (AJT 17) b.code.val)) ∧
    Cn (pE (AJT 16) (AJT 17) b.code.val) :=
  pE_eq f1RT_eq (cn (by norm_num)) f2RT_eq (cn (by norm_num)) b.code.val

theorem FmInvT_eq (b : F4) : FmInvT b = tabT (unpack 315 9 (pEI (AJI 16) (AJI 17) b.code.val)) ∧
    Cn (pEI (AJI 16) (AJI 17) b.code.val) := by
  have h1 : invT 315 f1RT = tabT (unpack 315 9 (AJI 16)) := by
    rw [f1RT_eq]
    exact invT_tt (by norm_num)
  have h2 : invT 315 f2RT = tabT (unpack 315 9 (AJI 17)) := by
    rw [f2RT_eq]
    exact invT_tt (by norm_num)
  exact pEI_eq h1 (cni (by norm_num)) h2 (cni (by norm_num)) b.code.val

theorem κRT_eq (q : Q1M) : κRT q = tabT (unpack 315 9 (κQ q)) ∧ Cn (κQ q) := by
  obtain ⟨hA, cA⟩ := EmT_eq q.a
  obtain ⟨hB, cB⟩ := FmT_eq q.b
  obtain ⟨hW, cW⟩ := FmT_eq (q.c + q.a * q.b)
  obtain ⟨hI, cI⟩ := FmInvT_eq (q.c + q.a * q.b)
  have c14 : Cn (AJT 14) := cn (by norm_num)
  have i14 : Cn (AJI 14) := cni (by norm_num)
  have e : κRT q = compT 315 (compT 315 (EmT q.a) (FmT q.b))
      (compT 315 (compT 315 (compT 315 e1RT (FmT (q.c + q.a * q.b))) (invT 315 e1RT))
        (FmInvT (q.c + q.a * q.b))) := rfl
  rw [e, hA, hB, hW, hI, e1RT_eq, invT_tt (k := 14) (by norm_num), compT_unpack cA cB, compT_unpack c14 cW,
    compT_unpack (canonK_pcomp c14 cW) i14,
    compT_unpack (canonK_pcomp (canonK_pcomp c14 cW) i14) cI,
    compT_unpack (canonK_pcomp cA cB) (canonK_pcomp (canonK_pcomp (canonK_pcomp c14 cW) i14) cI)]
  exact ⟨rfl, canonK_pcomp (canonK_pcomp cA cB)
    (canonK_pcomp (canonK_pcomp (canonK_pcomp c14 cW) i14) cI)⟩

theorem κRT_K (q : Q1M) :
    κRT q = tabT (unpack 315 9 (AJK (q1mIdx q).val)) ∧ Cn (AJK (q1mIdx q).val) := by
  have h : Nat.beq (AJK (q1mIdx q).val) (κQ (q1mOfCode (q1mIdx q).val)) = true :=
    allN_spec kK _ (q1mIdx q).isLt
  rw [q1mOfCode_idx] at h
  rw [Nat.eq_of_beq_eq_true h]
  exact κRT_eq q

theorem homRow_all {i : Nat} (hi : i < 64) : homRow i = true := by
  by_cases h1 : i < 16
  · exact allN_spec kHom0 i h1
  by_cases h2 : i < 32
  · have h := allN_spec kHom1 (i - 16) (by omega)
    have e : Nat.add (i - 16) 16 = i := by
      rw [Nat.add_eq]
      omega
    rwa [e] at h
  by_cases h3 : i < 48
  · have h := allN_spec kHom2 (i - 32) (by omega)
    have e : Nat.add (i - 32) 32 = i := by
      rw [Nat.add_eq]
      omega
    rwa [e] at h
  · have h := allN_spec kHom3 (i - 48) (by omega)
    have e : Nat.add (i - 48) 48 = i := by
      rw [Nat.add_eq]
      omega
    rwa [e] at h

theorem c4hom : autJ2VtxC4Hom () = true := by
  unfold autJ2VtxC4Hom
  simp only [List.all_eq_true]
  intro x _ y _
  obtain ⟨ex, cx⟩ := κRT_K x
  obtain ⟨ey, cy⟩ := κRT_K y
  obtain ⟨exy, cxy⟩ := κRT_K (x * y)
  rw [κArr_get, κArr_get, κArr_get, ex, ey, exy, compT_unpack cx cy,
    tblEq_unpack cxy (canonK_pcomp cx cy)]
  have h := allN_spec (homRow_all (q1mIdx x).isLt) _ (q1mIdx y).isLt
  rwa [q1mOfCode_idx, q1mOfCode_idx] at h

theorem c4inj : autJ2VtxC4Inj () = true := by
  unfold autJ2VtxC4Inj
  simp only [List.all_eq_true]
  intro x _
  obtain ⟨ex, cx⟩ := κRT_K x
  rw [κArr_get, ex, hid, tblEq_unpack cx hidc]
  by_cases hx : x = 1
  · rw [decide_eq_true hx, Bool.true_or]
  · have h := allN_spec kInj (q1mIdx x).val (q1mIdx x).isLt
    have h0 : Nat.beq (q1mIdx x).val 0 = false := by
      refine Bool.eq_false_iff.2 fun e => hx ?_
      rw [← q1mOfCode_idx x, Nat.eq_of_beq_eq_true e]
      decide
    rw [h0, Bool.false_or] at h
    rw [decide_eq_false hx, Bool.false_or]
    exact h

theorem c4 : autJ2VtxC4 () = true := by
  unfold autJ2VtxC4
  simp only [c4hom, c4inj, Bool.and_self]

theorem conjGen_of {k : Nat} (hk : k < 22) {α : MulAut Q1M} (h : cgK k α = true) :
    conjGenOK (tt k) α = true := by
  unfold conjGenOK
  unfold cgK at h
  rw [List.all_eq_true] at h ⊢
  intro g hg
  obtain ⟨c1, c2, c3⟩ := inv_spec hk
  obtain ⟨e1', d1⟩ := κRT_K g
  obtain ⟨e2', d2⟩ := κRT_K (α g)
  rw [invT_unpack (by norm_num) c3, e1', e2', conjT_unpack c1 c2 d1,
    tblEq_unpack (canonK_pcomp (canonK_pcomp c1 d1) c2) d2]
  exact h g hg

theorem c5 : autJ2VtxC5 () = true := by
  have h := kC5
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h21, h20⟩, h18⟩, h19⟩ := h
  unfold autJ2VtxC5
  simp only [rmRT_eq, bmRT_eq, tmRT_eq, gmRT_eq, conjGen_of (by norm_num) h21,
    conjGen_of (by norm_num) h20, conjGen_of (by norm_num) h18, conjGen_of (by norm_num) h19,
    Bool.and_self]

theorem hi_of {G : Nat} (h : Cn G) : Nat.shiftRight G (315 * 9) = 0 := by
  have h' : bAnd(szOK 315 9, bAnd(Nat.beq (Nat.shiftRight G (315 * 9)) (nat_lit 0),
      allN 315 (fun i => Nat.blt (pg 9 (mask 9) G i) 315))) = true := h
  obtain ⟨-, h2⟩ := (bAnd_iff (szOK 315 9) (bAnd(Nat.beq (Nat.shiftRight G (315 * 9)) (nat_lit 0),
    allN 315 (fun i => Nat.blt (pg 9 (mask 9) G i) 315)))).1 h'
  exact Nat.eq_of_beq_eq_true ((bAnd_iff (Nat.beq (Nat.shiftRight G (315 * 9)) (nat_lit 0))
    (allN 315 (fun i => Nat.blt (pg 9 (mask 9) G i) 315))).1 h2).1

theorem c3 : autJ2VtxC3 () = true := by
  have h := kC3
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  have c8 : Cn (AJT 8) := cn (by norm_num)
  have c12 : Cn (AJT 12) := cn (by norm_num)
  have c13 : Cn (AJT 13) := cn (by norm_num)
  have i12 : CFSG.Sporadic.Th.Native.invoOK 315 (tt 12) = true := invOK_unpack c12 c12 h1
  have i13 : CFSG.Sporadic.Th.Native.invoOK 315 (tt 13) = true := invOK_unpack c13 c13 h3
  have hq0 : q2T[0]! = tt 8 := by rw [q2T_eq, List.getElem!_cons_zero]
  have p12 : inP (natArr (tt 12)) = false := by
    unfold inP autLevels
    rw [natArr_tabT c12, CFSG.KS.Raw.siftK_eq CertificateChecks.KernelJ2Cover.binds
      CertificateChecks.KernelJ2Cover.perm CertificateChecks.KernelJ2Cover.PA.hl rfl (hi_of c12)
      (range_of_canonK c12)]
    rw [Bool.not_eq_true'] at h2
    exact h2
  have h4' : Nat.beq (pcomp 315 9 (mask 9) (AJT 13) (AJT 8))
      (pcomp 315 9 (mask 9) (AJT 8) (AJT 13)) = false := by
    rw [Bool.not_eq_true'] at h4
    exact h4
  unfold autJ2VtxC3
  simp only [umT_eq, vmT_eq, hq0, i12, i13, p12, commTT_unpack c13 c8, commTT_unpack c12 c13, h4',
    h5, Bool.not_false, Bool.and_self]

end CertificateChecks.KernelAJV

end
