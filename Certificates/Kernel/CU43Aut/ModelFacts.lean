
module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43ModelBase
public import Certificates.Kernel.CU43Aut.Small
public import Certificates.Kernel.Multipliers.U43BFacts
public import CFSG.Certificates.Kernel.Spor.RawSiftKConv
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Certificates.Kernel.Misc.RuInvPack

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCU43Aut

open CFSG.EvenSporadicStandard.M24Std.CU43
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.Raw.Orb
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CertificateChecks.KernelU43B
open CFSG.LieType.Multipliers.U43

theorem arr_of_bind {t : Array ℕ} {P : ℕ} (h : bindListK 820 10 P t.toList = true) :
    t = unpack 820 10 P := by
  have := toArray_eq_of_bindListK h
  rwa [Array.toArray_toList] at this

theorem kIn_spec {i : ℕ} (hi : i < 11) :
    invEqK 820 10 (mask 10) (820 * 10) (CU43T i) (CU43TI i) = true := by
  have h := allN_spec kIn i hi
  exact ((bAnd_iff _ _).1 ((bAnd_iff _ _).1 h).2).2

theorem isInv_T {i : ℕ} (hi : i < 11) :
    isInvA 820 (unpack 820 10 (CU43T i)) (invCand 820 (unpack 820 10 (CU43T i))) = true := by
  obtain ⟨e1, e2⟩ := invEqK_sound (kIn_spec hi)
  rw [e1]
  exact e2

theorem rep_T {i : ℕ} (hi : i < 11) :
    Rep 820 (unpack 820 10 (CU43T i)) (permOfArr 820 (unpack 820 10 (CU43T i))) :=
  (rep_permOfArr (isInv_T hi)).1

theorem arr_d : deltaArr = unpack 820 10 (CU43T 0) := arr_of_bind kBind.1
theorem arr_f : phiArr = unpack 820 10 (CU43T 1) := arr_of_bind kBind.2.1

theorem reps_T : ∀ j < 9, reps[j]! = unpack 820 10 (CU43T (j + 2)) := by
  obtain ⟨-, -, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := kBind
  intro j hj
  interval_cases j
  exacts [arr_of_bind h2, arr_of_bind h3, arr_of_bind h4, arr_of_bind h5, arr_of_bind h6,
    arr_of_bind h7, arr_of_bind h8, arr_of_bind h9, arr_of_bind h10]

theorem tabs_T : ∀ t ∈ deltaArr :: phiArr :: reps, ∃ i < 11, t = unpack 820 10 (CU43T i) := by
  intro t ht
  rw [List.mem_cons, List.mem_cons] at ht
  rcases ht with rfl | rfl | ht
  · exact ⟨0, by norm_num, arr_d⟩
  · exact ⟨1, by norm_num, arr_f⟩
  · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ht
    have hj' : j < 9 := hj
    refine ⟨j + 2, by omega, ?_⟩
    rw [← reps_T j hj', List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    rfl

theorem rep_dA : Rep 820 deltaArr dP := by
  have h := isInv_T (i := 0) (by norm_num)
  rw [← arr_d] at h
  exact (rep_permOfArr h).1

theorem rep_fA : Rep 820 phiArr fP := by
  have h := isInv_T (i := 1) (by norm_num)
  rw [← arr_f] at h
  exact (rep_permOfArr h).1

theorem rep_d : Rep 820 (unpack 820 10 (CU43T 0)) dP := by rw [← arr_d]; exact rep_dA
theorem rep_f : Rep 820 (unpack 820 10 (CU43T 1)) fP := by rw [← arr_f]; exact rep_fA

theorem rep_tA (k : ℕ) : Rep 820 (tArr k) (tP k) :=
  rep_compA (CFSG.EvenSporadicStandard.M24Std.CU43.rep_powA rep_fA _)
    (CFSG.EvenSporadicStandard.M24Std.CU43.rep_powA rep_dA _)

theorem rep_pc {p q : ℕ} {g h : Equiv.Perm (Fin 820)} (hp : Rep 820 (unpack 820 10 p) g)
    (hq : Rep 820 (unpack 820 10 q) h) : Rep 820 (unpack 820 10 (pc p q)) (g * h) :=
  rep_unpack (prep_pcomp (by norm_num) (prep_of_rep hp) (prep_of_rep hq))

theorem rep_pid : Rep 820 (unpack 820 10 (pidn 820 10)) 1 :=
  rep_unpack (prep_pidn (by norm_num) (by norm_num))

theorem rep_ppow {p : ℕ} {g : Equiv.Perm (Fin 820)} (hp : Rep 820 (unpack 820 10 p) g) :
    ∀ e, Rep 820 (unpack 820 10 (ppow p e)) (g ^ e)
  | 0 => by
    rw [pow_zero]
    exact rep_pid
  | e + 1 => by
    rw [pow_succ']
    exact rep_pc hp (rep_ppow hp e)

theorem rep_TK (k : ℕ) : Rep 820 (unpack 820 10 (TK k)) (tP k) :=
  rep_pc (rep_ppow rep_f _) (rep_ppow rep_d _)

theorem kTK_spec {k : ℕ} (hk : k < 8) :
    cK (TK k) = true ∧ permOK 820 10 (mask 10) (820 * 10) (TK k) (TKI k) = true :=
  (bAnd_iff _ _).1 (allN_spec kTK k hk)

theorem rep_TKI {k : ℕ} (hk : k < 8) : Rep 820 (unpack 820 10 (TKI k)) (tP k)⁻¹ :=
  rep_inv_of_isInvA (rep_TK k) (isInvA_unpack (kTK_spec hk).2)

theorem eq_of_pk {p q : ℕ} {g h : Equiv.Perm (Fin 820)} (hp : Rep 820 (unpack 820 10 p) g)
    (hq : Rep 820 (unpack 820 10 q) h) (e : Nat.beq p q = true) : g = h := by
  rw [Nat.eq_of_beq_eq_true e] at hp
  exact hp.unique hq

theorem range_of_rep {X : ℕ} {G : Equiv.Perm (Fin 820)} (hX : Rep 820 (unpack 820 10 X) G) :
    allN 820 (fun i => Nat.blt (pg 10 (mask 10) X i) 820) = true :=
  allN_of_forall fun i hi => by
    rw [← unpack_get hi]
    exact Nat.blt_eq.mpr (hX.lt hi)

theorem mem_of_inPK {X : ℕ} {G : Equiv.Perm (Fin 820)} (hX : Rep 820 (unpack 820 10 X) G)
    (h : inPK X = true) : G ∈ P := by
  have hs := siftK_sound binds perm C.hl rfl (range_of_rep hX) h
  rw [← base_eq] at hs
  exact (inP_iff hX).1 hs

theorem not_mem_of_inPK {X : ℕ} {G : Equiv.Perm (Fin 820)} (hX : Rep 820 (unpack 820 10 X) G)
    (hc : cK X = true) (h : inPK X = false) : G ∉ P := by
  have hsz : szOK 820 10 = true := by
    have h := kSz
    simp only [Bool.and_eq_true] at h
    exact h.1.1
  have hhi : X >>> (820 * 10) = 0 := (CFSG.KS.PF.canon_facts hc).2.2.1
  have hs := siftA_false_of_K binds perm C.hl hsz hhi (range_of_rep hX) h
  rw [← base_eq] at hs
  have hs' : inP (unpack 820 10 X) = false := hs
  intro hG
  have h1 := (inP_iff hX).2 hG
  rw [hs'] at h1
  exact Bool.false_ne_true h1

theorem d_pow4 : dP ^ 4 = 1 := by
  have h := kRel
  simp only [Bool.and_eq_true] at h
  exact eq_of_pk (rep_ppow rep_d 4) rep_pid h.1.1

theorem f_pow2 : fP ^ 2 = 1 := by
  have h := kRel
  simp only [Bool.and_eq_true] at h
  exact eq_of_pk (rep_ppow rep_f 2) rep_pid h.1.2

theorem fdf : fP * (dP * fP) = dP ^ 3 := by
  have h := kRel
  simp only [Bool.and_eq_true] at h
  exact eq_of_pk (rep_pc rep_f (rep_pc rep_d rep_f)) (rep_ppow rep_d 3) h.2

theorem df : dP * fP = fP * dP ^ 3 := by
  have hff : fP * fP = 1 := by rw [← sq]; exact f_pow2
  calc dP * fP = fP * fP * (dP * fP) := by rw [hff, one_mul]
    _ = fP * dP ^ 3 := by rw [mul_assoc, fdf]

theorem dpow_f : ∀ a : ℕ, dP ^ a * fP = fP * dP ^ (3 * a)
  | 0 => by simp
  | a + 1 => by
    rw [pow_succ, mul_assoc, df, ← mul_assoc, dpow_f a, mul_assoc, ← pow_add]
    congr 2

@[expose] def mulD (k k' : ℕ) : ℕ :=
  if k' / 4 = 0 then 4 * (k / 4) + (k % 4 + k' % 4) % 4
  else 4 * ((k / 4 + 1) % 2) + (3 * (k % 4) + k' % 4) % 4

theorem mulD_lt {k k' : ℕ} (hk : k < 8) : mulD k k' < 8 := by
  unfold mulD
  split_ifs <;> omega

theorem tP_mul_eq {k k' : ℕ} (hk : k < 8) (hk' : k' < 8) : tP k * tP k' = tP (mulD k k') := by
  have hd (n : ℕ) : dP ^ n = dP ^ (n % 4) := pow_eq_pow_mod n d_pow4
  have hf (n : ℕ) : fP ^ n = fP ^ (n % 2) := pow_eq_pow_mod n f_pow2
  unfold tP mulD
  rcases (show k' / 4 = 0 ∨ k' / 4 = 1 by omega) with h | h
  · rw [if_pos h, h, pow_zero, one_mul, mul_assoc, ← pow_add, hd (k % 4 + k' % 4)]
    have e1 : (4 * (k / 4) + (k % 4 + k' % 4) % 4) / 4 = k / 4 := by omega
    have e2 : (4 * (k / 4) + (k % 4 + k' % 4) % 4) % 4 = (k % 4 + k' % 4) % 4 := by omega
    rw [e1, e2]
  · rw [if_neg (by omega), h, pow_one]
    have e1 : (4 * ((k / 4 + 1) % 2) + (3 * (k % 4) + k' % 4) % 4) / 4 = (k / 4 + 1) % 2 := by
      omega
    have e2 : (4 * ((k / 4 + 1) % 2) + (3 * (k % 4) + k' % 4) % 4) % 4 =
        (3 * (k % 4) + k' % 4) % 4 := by omega
    have : fP ^ (k / 4) * dP ^ (k % 4) * (fP * dP ^ (k' % 4)) =
        fP ^ (k / 4 + 1) * dP ^ (3 * (k % 4) + k' % 4) := by
      calc fP ^ (k / 4) * dP ^ (k % 4) * (fP * dP ^ (k' % 4)) =
            fP ^ (k / 4) * (dP ^ (k % 4) * fP) * dP ^ (k' % 4) := by simp only [mul_assoc]
        _ = fP ^ (k / 4) * (fP * dP ^ (3 * (k % 4))) * dP ^ (k' % 4) := by rw [dpow_f]
        _ = _ := by rw [pow_succ, pow_add]; simp only [mul_assoc]
    rw [this, hf (k / 4 + 1), hd (3 * (k % 4) + k' % 4), e1, e2]

theorem mulD_solve : ∀ k < 8, ∀ k' < 8, ∃ m < 8, mulD m k' = k ∧ (m = 0 → k = k') := by
  decide

theorem permC : permCheck = true := by
  unfold permCheck
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  refine ⟨fun t ht => ?_, fun k _ => CFSG.KC.Misc.RuInv.P.isInvA_invCand (rep_tA k)⟩
  obtain ⟨i, hi, rfl⟩ := tabs_T t ht
  exact isInv_T hi

theorem norm_spec {u g : ℕ} (hu : u < 2) (hg : g < 2) :
    inP (compA 820 (unpack 820 10 (CU43T u)) (compA 820 (unpack 820 10 (C.S g))
      (invCand 820 (unpack 820 10 (CU43T u))))) = true := by
  have hS := (rep_permOfArr (isInvA_unpack (allN_spec perm g (by omega)))).1
  have hU := rep_T (i := u) (by omega)
  have hUi : Rep 820 (unpack 820 10 (CU43TI u)) (permOfArr 820 (unpack 820 10 (CU43T u)))⁻¹ := by
    rw [← (invEqK_sound (kIn_spec (i := u) (by omega))).1]
    exact CFSG.KC.Misc.RuInv.P.rep_invCand hU
  have hm := mem_of_inPK (rep_pc (rep_pc hU hS) hUi) (allN_spec (allN_spec kNorm u hu) g hg)
  refine (inP_iff (rep_compA hU (rep_compA hS (CFSG.KC.Misc.RuInv.P.rep_invCand hU)))).2 ?_
  rwa [← mul_assoc]

theorem normC : normCheck = true := by
  unfold normCheck
  have ha : tabA = unpack 820 10 (C.S 0) := binds.2.2.2.2.1 0 (by omega)
  have hb : tabB = unpack 820 10 (C.S 1) := binds.2.2.2.2.1 1 (by omega)
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  rw [arr_d, arr_f, ha, hb]
  exact ⟨⟨norm_spec (by omega) (by omega), norm_spec (by omega) (by omega)⟩,
    ⟨norm_spec (by omega) (by omega), norm_spec (by omega) (by omega)⟩⟩

theorem relC : relCheck = true := by
  unfold relCheck
  simp only [Bool.and_eq_true]
  have e := CFSG.EvenSporadicStandard.M24Std.CU43.rep_powA rep_dA
  refine ⟨⟨(eqA_iff (e 4) rep_idA).2 d_pow4,
    (eqA_iff (CFSG.EvenSporadicStandard.M24Std.CU43.rep_powA rep_fA 2) rep_idA).2 f_pow2⟩,
    (eqA_iff (rep_compA rep_fA (rep_compA rep_dA rep_fA)) (e 3)).2 fdf⟩

theorem multC : multCheck = true := by
  unfold multCheck
  simp only [List.all_eq_true, List.any_eq_true, List.mem_range]
  intro k hk k' hk'
  exact ⟨mulD k k', mulD_lt hk,
    (eqA_iff (rep_compA (rep_tA k) (rep_tA k')) (rep_tA _)).2 (tP_mul_eq hk hk')⟩

theorem tP_not_mem {m : ℕ} (hm : m < 8) (h0 : m ≠ 0) : tP m ∉ P := by
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero h0
  have h := allN_spec kCos m' (by omega)
  exact not_mem_of_inPK (rep_TK _) (kTK_spec hm).1 (by simpa using h)

theorem cosetC : cosetCheck = true := by
  unfold cosetCheck
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq]
  intro k hk k' hk'
  by_cases e : k = k'
  · exact Or.inl e
  · right
    obtain ⟨m, hm, hmk, hm0⟩ := mulD_solve k hk k' hk'
    have hne : m ≠ 0 := fun h => e (hm0 h)
    have heq : tP k * (tP k')⁻¹ = tP m := by
      rw [← hmk, ← tP_mul_eq hm hk', mul_inv_cancel_right]
    have hr := rep_compA (rep_tA k) (CFSG.KC.Misc.RuInv.P.rep_invCand (rep_tA k'))
    cases hs : inP (compA 820 (tArr k) (invCand 820 (tArr k')))
    · rfl
    · exact absurd (heq ▸ (inP_iff hr).1 hs) (tP_not_mem hm hne)

theorem repCoset_spec : ∀ j < 9, repCoset[j]! = repCoset.getD j 0 ∧ repCoset.getD j 0 < 8 := by
  decide

theorem repC : repCheck = true := by
  unfold repCheck
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true]
  intro j hj
  have h := allN_spec kRep j hj
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  obtain ⟨ec, hc⟩ := repCoset_spec j hj
  have hR := rep_T (i := j + 2) (by omega)
  rw [reps_T j hj, ec]
  refine ⟨(eqA_iff (rep_compA hR hR) rep_idA).2 (eq_of_pk (rep_pc hR hR) rep_pid h1), ?_⟩
  have hm := mem_of_inPK (rep_pc hR (rep_TKI hc)) h2
  exact (inP_iff (rep_compA hR (CFSG.KC.Misc.RuInv.P.rep_invCand (rep_tA _)))).2 hm

theorem facts26010 : (permCheck = true) ∧ (normCheck = true) ∧ (relCheck = true) ∧
    (cosetCheck = true) ∧ (multCheck = true) ∧ (repCheck = true) :=
  ⟨permC, normC, relC, cosetC, multC, repC⟩

end CertificateChecks.KernelCU43Aut

end
