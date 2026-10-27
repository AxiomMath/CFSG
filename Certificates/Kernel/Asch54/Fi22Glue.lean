module

public import Certificates.Kernel.Asch54.Fi22Checks
public import Certificates.Kernel.Sporadic.Fi22.C2066
public import Certificates.Kernel.Sporadic.Fi22.E2065Eq
public import CFSG.Certificates.Kernel.Spor.RawTreeSound
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import CFSG.Certificates.Kernel.Spor.RawAgree
public import CFSG.Certificates.Kernel.Spor.RawSiftK
public import CFSG.Certificates.Kernel.Spor.SiftEq
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Quasithin.Recognition.CertChain
public import CFSG.Sporadic.FischerOddCore.Fi22FiveExact
public import CFSG.Sporadic.FischerOddCore.Fi22ExtSylow
public import CFSG.Monster.B.Fischer.Fi22Model
public import CFSG.Monster.B.Fischer.Fi22Local
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporIndexTwo
public import Certificates.Data.Asch54SporFi22Pair
public import CFSG.Monster.B.Fischer.Fi22Graph
public import CFSG.Sporadic.FischerOddCore.Fi22Cent
public import Certificates.Data.Asch54SporFi22Pair
public import CFSG.Monster.B.Fischer.PinnedChain
public import CFSG.Sporadic.FischerOddCore.Fi22Cent
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.A54F22G

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.Prim CFSG.KS.Mathieu
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
open CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.WeakClosure81.Asch54Fi22 CertificateChecks.KernelSpor
open CertificateChecks.KernelSpor.A54F22

theorem prep_eq {p q : ℕ} {g h : Equiv.Perm (Fin 3510)} (hp : PRep 3510 12 p g)
    (hq : PRep 3510 12 q h) (e : Nat.beq p q = true) : g = h := by
  rw [Nat.eq_of_beq_eq_true e] at hp
  exact prep_unique hp hq

theorem prep_c {p q : ℕ} {g h : Equiv.Perm (Fin 3510)} (hp : PRep 3510 12 p g)
    (hq : PRep 3510 12 q h) : PRep 3510 12 (Fi22X.c p q) (g * h) :=
  prep_pcomp (by norm_num) hp hq

theorem mem_P_of {p : ℕ}
    {g : Equiv.Perm (Fin 3510)} (hg : PRep 3510 12 p g) (hc : Fi22X.cn p = true)
    (hs : Fi22X.siftP p = true) : g ∈ fi22P :=
  (fi22InP_iff (rep_unpack hg)).1
    (Fi22C2066.fi22InP_of (PS := fun _ => p) (j := 0) rfl hc hs)

theorem mem_T_of {p : ℕ} {g : Equiv.Perm (Fin 3510)}
    (hg : PRep 3510 12 p g) (hc : Fi22X.cn p = true) (hs : Fi22X.siftT p = true) :
    g ∈ fi22OuterT := by
  refine (fi22InT_iff (rep_unpack hg)).1 ?_
  rw [fi22InT, fi22TLevels, siftK_eq Fi22X.bindsT Fi22X.permT Fi22TC.hl rfl (Fi22X.hi_of hc)
    (range_of_canonK hc)]
  exact hs

theorem prep_perm {p q : ℕ} (h : permOK 3510 12 (mask 12) (3510 * 12) p q = true) :
    PRep 3510 12 p (permOfArr 3510 (unpack 3510 12 p)) ∧
      PRep 3510 12 q (permOfArr 3510 (unpack 3510 12 p))⁻¹ := by
  have hr := rep_permOfArr (isInvA_unpack h)
  exact ⟨prep_of_rep hr.1, prep_of_rep hr.2⟩

theorem a0Gen_get {k : ℕ} (hk : k < 2) : a0Gen[k]! = unpack 3510 12 (A54F22X.F k) := by
  rw [a0Gen, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn, A54F22X.eq]
  exact CFSG.KC.Misc.HexFlat.hexTable_sound A54F22X.all k hk

theorem mArr_eq : mArr = unpack 3510 12 M := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound A54F22M.all 0 (by norm_num)
  rw [Nat.mul_zero, ← A54F22M.eq] at h
  exact h

theorem prep_M : PRep 3510 12 M mP ∧ PRep 3510 12 M mP⁻¹ := by
  have h := prep_perm (bAnd_iff (Fi22X.cn M) (permOK 3510 12 (mask 12) (3510 * 12) M M) |>.1 mInv).2
  rw [← mArr_eq] at h
  exact h

theorem cnM : Fi22X.cn M = true :=
  (bAnd_iff (Fi22X.cn M) (permOK 3510 12 (mask 12) (3510 * 12) M M) |>.1 mInv).1

theorem mP_mul_self : mP * mP = 1 := by
  have e : mP = mP⁻¹ := prep_unique prep_M.1 prep_M.2
  calc mP * mP = mP * mP⁻¹ := by rw [← e]
    _ = 1 := mul_inv_cancel mP

theorem mP_inv : mP⁻¹ = mP := inv_eq_of_mul_eq_one_right mP_mul_self

theorem prep_TS {k : ℕ} (hk : k < 9) :
    PRep 3510 12 (Fi22X.TS k) (fi22TSeed k) := by
  have h := rep_fi22TSeed hk
  rw [Fi22X.outT_eq (by omega)] at h
  exact prep_of_rep h

theorem cnTS {k : ℕ} (hk : k < 9) : Fi22X.cn (Fi22X.TS k) = true := allN_spec Fi22X.cnT k (by omega)

theorem prep_T1 : PRep 3510 12 T1 (fi22ExtRep 1) := by
  have h := rep_fi22ExtRep (k := 1) (by norm_num)
  rw [Fi22E2067.ext_eq (L := 21 + 1) (by norm_num)] at h
  exact prep_of_rep h

@[expose] noncomputable def SA : Array (Array ℕ) :=
  Array.ofFn (n := 20) fun j => unpack 3510 12 (A54F22C.S j.val)

@[expose] def BF : List (Fin 3510) := [0, 1, 2, 3, 6, 4]

theorem BF_val : (BF.map Fin.val).toArray = BL := rfl

theorem BF_nodup : BF.Nodup := by decide

theorem SA_get {j : ℕ} (hj : j < 20) : SA[j]! = unpack 3510 12 (A54F22C.S j) := by
  rw [getElem!_pos SA j (by simp [SA]; exact hj)]
  simp [SA]

theorem bindsA : Binds 3510 12 A54F22C.S 20 6 A54F22C.BP SA BL :=
  ⟨by norm_num, by norm_num, by norm_num, by simp [SA], fun j hj => SA_get hj, rfl,
    fun t ht => Nat.eq_of_beq_eq_true (allN_spec baseC t ht)⟩

theorem permA : allN 20 (fun j => permOK 3510 12 (mask 12) (3510 * 12) (A54F22C.S j)
    (A54F22C.SI j)) = true := (head_facts A54F22C.head).1

@[expose] noncomputable def gA (j : ℕ) : Equiv.Perm (Fin 3510) := permOfArr 3510 SA[j]!

theorem prep_gA {j : ℕ} (hj : j < 20) :
    PRep 3510 12 (A54F22C.S j) (gA j) ∧ PRep 3510 12 (A54F22C.SI j) (gA j)⁻¹ :=
  prep_PS bindsA permA hj

theorem gA_t {i : ℕ} (hi : i < 9) : gA i = tGenP i := by
  rw [gA, tGenP, SA_get (by omega), Nat.eq_of_beq_eq_true (allN_spec bindT i hi), tGen,
    Fi22X.outT_eq (by omega)]

theorem gA_x {k : ℕ} (hk : k < 2) : gA (9 + k) = a0GenP k := by
  have e : A54F22C.S (9 + k) = A54F22X.F k := Nat.eq_of_beq_eq_true (allN_spec bindX k hk)
  rw [gA, a0GenP, SA_get (by omega), e, a0Gen_get hk]

theorem tGenP_eq (i : ℕ) : tGenP i = fi22TSeed i := rfl

theorem gA_mem_P {j : ℕ}
    (hj : j < 20) : gA j ∈ fi22P := by
  obtain ⟨hc, hs⟩ := (bAnd_iff _ _).1 (allN_spec inP j hj)
  exact mem_P_of (prep_gA hj).1 hc hs

theorem sepA : Sep 3510 SA BL := by
  intro G hG hfix
  refine Fi22C2066.fi22P_sep ((Subgroup.closure_le _).2 ?_ hG) hfix
  rintro _ ⟨j, hj, rfl⟩
  exact gA_mem_P (by simpa [SA] using hj)

theorem chainA :
    rawChainOK 3510 (SA.extract 0 11) SA BL
      (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 11 20 D) 1 = true :=
  rawChainTK_sound bindsA A54F22C.head A54F22C.tl A54F22C.hst sepA A54F22C.hs (by norm_num)

theorem A0_eq : A0 = Subgroup.closure {g | ∃ k < 11, gA k = g} := by
  rw [A0]
  congr 1
  ext g
  constructor
  · rintro (⟨i, hi, rfl⟩ | ⟨k, hk, rfl⟩)
    · exact ⟨i, by omega, gA_t hi⟩
    · exact ⟨9 + k, by omega, gA_x hk⟩
  · rintro ⟨k, hk, rfl⟩
    by_cases h9 : k < 9
    · exact Or.inl ⟨k, h9, (gA_t h9).symm⟩
    · refine Or.inr ⟨k - 9, by omega, ?_⟩
      rw [← gA_x (by omega)]
      congr 1
      omega

theorem card_A0 :
    Nat.card A0 = 17694720 := by
  have hOS : (SA.extract 0 11).size ≤ SA.size := by simp
  have hext : (SA.extract 0 11).size = 11 := by simp [SA]
  have h := CFSG.Quasithin.card_closure_permOfArr_of_rawChainOK (n := 3510) (by norm_num) BF_nodup
    (O := SA.extract 0 11) (S := SA) (chunks := 1) (by norm_num) hOS
    (fun i hi => by
      rw [getElem!_pos SA i (by simp [SA] at hi ⊢; omega), getElem!_pos _ i hi]
      simp)
    (by rw [hext, BF_val]; exact chainA)
  rw [BF_val, rawOrbitSizesTK_sound bindsA A54F22C.head A54F22C.tl, orb] at h
  have hcl : Subgroup.closure {g | ∃ k < (SA.extract 0 11).size,
      permOfArr 3510 (SA.extract 0 11)[k]! = g} = A0 := by
    rw [A0_eq]
    refine congrArg Subgroup.closure (Set.ext fun g => ?_)
    refine exists_congr fun k => ?_
    rw [hext]
    refine and_congr_right fun hk => ?_
    rw [getElem!_pos _ k (by rw [hext]; exact hk), Array.getElem_extract]
    simp only [Nat.zero_add]
    rw [← getElem!_pos SA k (by simp [SA]; omega)]
    exact Iff.rfl
  rw [hcl] at h
  rw [h]
  norm_num

theorem A0_le_P : A0 ≤ fi22P := by
  rw [A0_eq, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  exact gA_mem_P (by omega)

theorem T_le_A0 : fi22OuterT ≤ A0 := by
  rw [fi22OuterT_eq_closure, Subgroup.closure_le, A0]
  rintro _ ⟨k, hk, rfl⟩
  exact Subgroup.subset_closure (Or.inl ⟨k, hk, tGenP_eq k⟩)

theorem gA_mem :
    ∀ j < 20, gA j ∈ A0 := by
  have hF := chainCheckFacts chainA
  have hsz : SA.size = 20 := by simp [SA]
  have hrep : ∀ h < SA.size, Rep 3510 SA[h]! (gA h) := fun h hh =>
    (rep_permOfArr (hF.strong_inv h hh)).1
  have hrepi : ∀ h < SA.size, Rep 3510 (rawInvs 3510 SA)[h]! (gA h)⁻¹ := fun h hh =>
    (rep_permOfArr (hF.strong_inv h hh)).2
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    by_cases h11 : j < 11
    · rw [A0_eq]
      exact Subgroup.subset_closure ⟨j, h11, rfl⟩
    · have hO : (SA.extract 0 11).size = 11 := by simp [SA]
      obtain ⟨hl, he⟩ := hF.words j (by omega) (by omega)
      rw [eq_of_eqA (hrep j (by omega))
        (rep_wordA (gs := gA) (fun h hh => hrep h (by omega)) (fun h hh => hrepi h (by omega)) _ hl)
        he]
      apply (Subgroup.closure_le _).2 ?_ (Quiver.SchreierGraph.evalWord_mem_closure _ _)
      rintro _ ⟨a, rfl⟩
      exact ih a a.2 (by omega)

theorem u_mul_mP_mem :
    fi22U * mP ∈ fi22P := by
  have hu : PRep 3510 12 Fi22X.GO fi22U := by
    have h := rep_fi22U
    rw [Fi22X.go_eq] at h
    exact prep_of_rep h
  exact mem_P_of (prep_c hu prep_M.1) (Fi22X.cn_c Fi22X.cnG cnM) mU

theorem mP_conj_T : ∀ x ∈ fi22OuterT, mP * x * mP⁻¹ ∈ fi22OuterT := by
  rw [fi22OuterT_eq_closure]
  refine conj_mem_of_forall_mem_closure ?_
  rintro _ ⟨k, hk, rfl⟩
  rw [← fi22OuterT_eq_closure, mP_inv, mul_assoc]
  exact mem_T_of (prep_c prep_M.1 (prep_c (prep_TS hk) prep_M.1))
    (Fi22X.cn_c cnM (Fi22X.cn_c (cnTS hk) cnM)) (allN_spec mT k hk)

theorem mP_conj_A0 :
    ∀ x ∈ A0, mP * x * mP⁻¹ ∈ A0 := by
  rw [A0_eq]
  refine conj_mem_of_forall_mem_closure ?_
  rintro _ ⟨k, hk, rfl⟩
  rw [← A0_eq]
  by_cases h9 : k < 9
  · have hT : fi22TSeed k ∈ fi22OuterT := by
      rw [fi22OuterT_eq_closure]
      exact Subgroup.subset_closure ⟨k, h9, rfl⟩
    rw [gA_t h9, tGenP_eq]
    exact T_le_A0 (mP_conj_T _ hT)
  · obtain ⟨l, rfl⟩ : ∃ l, k = 9 + l := ⟨k - 9, by omega⟩
    have hl : l < 2 := by omega
    obtain ⟨hlt, he⟩ := (bAnd_iff _ _).1 (allN_spec mA l hl)
    have hx : PRep 3510 12 (A54F22X.F l) (gA (9 + l)) := by
      have h := (prep_gA (j := 9 + l) (by omega)).1
      have e : A54F22C.S (9 + l) = A54F22X.F l := Nat.eq_of_beq_eq_true (allN_spec bindX l hl)
      rwa [e] at h
    have hw := (prep_wordK (n := 3510) (w := 12) (by norm_num) (by norm_num)
      (PS := A54F22C.S) (PSI := A54F22C.SI) (gs := gA) (j := 20)
      (fun h hh => (prep_gA hh).1) (fun h hh => (prep_gA hh).2) (W l) hlt).1
    have heq := prep_eq (prep_c prep_M.1 (prep_c hx prep_M.1)) hw he
    rw [mP_inv, mul_assoc, heq]
    apply (Subgroup.closure_le _).2 ?_ (Quiver.SchreierGraph.evalWord_mem_closure _ _)
    rintro _ ⟨a, rfl⟩
    exact gA_mem a a.2

theorem H_eq :
    fi22P ⊓ Subgroup.centralizer {fi22ExtRep 1} = fi22H 1 :=
  CTUC_Fi22_five_exact_involution_fixed_subgroups.2.1

theorem T_le_H :
    fi22OuterT ≤ fi22H 1 := by
  rw [← H_eq, fi22OuterT_eq_closure, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  have hT : fi22TSeed k ∈ fi22OuterT := by
    rw [fi22OuterT_eq_closure]
    exact Subgroup.subset_closure ⟨k, hk, rfl⟩
  have hc := (bAnd_iff (Fi22X.cn T1) (allN 9 (fun i =>
    Nat.beq (Fi22X.c (Fi22X.TS i) T1) (Fi22X.c T1 (Fi22X.TS i)))) |>.1 tComm).2
  refine ⟨fi22OuterT_le hT, Subgroup.mem_centralizer_iff.2 ?_⟩
  rintro _ rfl
  exact (prep_eq (prep_c (prep_TS hk) prep_T1) (prep_c prep_T1 (prep_TS hk))
    (allN_spec hc k hk)).symm

theorem mP_conj_H :
    ∀ x ∈ fi22H 1, mP * x * mP⁻¹ ∈ fi22H 1 := by
  rw [← H_eq]
  rintro x ⟨hxP, hxC⟩
  have hR : mP ∈ fi22R := (mem_fi22R_iff mP).2 (Or.inr u_mul_mP_mem)
  refine ⟨(Subgroup.mem_normalizer_iff.1 (fi22R_le_normalizer hR) x).1 hxP, ?_⟩
  refine Subgroup.mem_centralizer_iff.2 ?_
  rintro _ rfl
  have hc : Commute (fi22ExtRep 1) x := Subgroup.mem_centralizer_iff.1 hxC _ rfl
  have hm : Commute (fi22ExtRep 1) mP :=
    (prep_eq (prep_c prep_T1 prep_M.1) (prep_c prep_M.1 prep_T1) mt1)
  exact ((hm.mul_right hc).mul_right hm.inv_right).eq

open CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore CFSG.LocalAnalysis.WeakClosure81.Asch54Fi22 in
theorem facts75338 :
 A0 ≤ fi22P ∧ Nat.card A0 = 17694720 ∧ fi22OuterT ≤ A0 ∧ fi22OuterT ≤ fi22H 1 ∧
    mP * mP = 1 ∧ fi22U * mP ∈ fi22P ∧ (∀ x ∈ fi22OuterT, mP * x * mP⁻¹ ∈ fi22OuterT) ∧
    (∀ x ∈ A0, mP * x * mP⁻¹ ∈ A0) ∧ (∀ x ∈ fi22H 1, mP * x * mP⁻¹ ∈ fi22H 1) :=
  ⟨A0_le_P, card_A0, T_le_A0, T_le_H, mP_mul_self, u_mul_mP_mem, mP_conj_T, mP_conj_A0,
    mP_conj_H⟩

@[expose] noncomputable def gR (j : ℕ) : Equiv.Perm (Fin 3510) := permOfArr 3510 (unpack 3510 12 (R j))

theorem prep_gR {j : ℕ} (hj : j < 26) : PRep 3510 12 (R j) (gR j) ∧ PRep 3510 12 (RI j) (gR j)⁻¹ :=
  prep_perm ((bAnd_iff _ _).1 (allN_spec slpPerm j hj)).2

theorem line_eq {L : ℕ} (hL : L < 306) : fi22CentArr L = unpack 3510 12 (Fi22CentT.L L) := by
  rw [fi22CentArr, fi22CentBytes, Fi22CentB.text_eq]
  exact Fi22E2065.cent_eq hL

theorem gR_mem : ∀ j < 26, gR j ∈ A0 ⊔ fi22H 1 := by
  obtain ⟨hb0, hb1⟩ := bAnd_iff (allN 2 (fun k => Nat.beq (R k) (A54F22X.F k)))
    (allN 9 (fun k => Nat.beq (R (Nat.add 2 k)) (Fi22CentT.L (Nat.add 19 k)))) |>.1 slpBind
  obtain ⟨-, hd⟩ := bAnd_iff (Nat.beq (Nat.add (lenW GD) 11) 26) (allN 26 (fun j =>
    bIf(Nat.blt j 11, true, bAnd(lettersK j (dword GD 11 j), Nat.beq (R j) (wR (dword GD 11 j))))))
    |>.1 slpDeriv
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    by_cases h2 : j < 2
    · have e : gR j = a0GenP j := by
        rw [gR, a0GenP, a0Gen_get h2, Nat.eq_of_beq_eq_true (allN_spec hb0 j h2)]
      rw [e, A0]
      exact Subgroup.mem_sup_left (Subgroup.subset_closure (Or.inr ⟨j, h2, rfl⟩))
    by_cases h11 : j < 11
    · have h := allN_spec hb1 (j - 2) (by omega)
      have e2 : 2 + (j - 2) = j := by omega
      simp only [Nat.add_eq, e2] at h
      have hL : 19 + (j - 2) < 306 := by omega
      have hc : PRep 3510 12 (Fi22CentT.L (19 + (j - 2))) (fi22CentPerm (19 + (j - 2))) := by
        have hr := rep_fi22CentPerm hL
        rw [line_eq hL] at hr
        exact prep_of_rep hr
      rw [prep_eq (prep_gR hj).1 hc h]
      refine Subgroup.mem_sup_right ?_
      rw [fi22H_eq_closure (c := 1) (by norm_num)]
      have e9 : fi22CentGenCount.getD 1 0 = 9 := rfl
      exact Subgroup.subset_closure ⟨j - 2, by omega, rfl⟩
    · have h := allN_spec hd j hj
      have hb : Nat.blt j 11 = false := Bool.eq_false_iff.2 fun h' => h11 (Nat.blt_eq ▸ h')
      rw [hb] at h
      obtain ⟨hl, he⟩ := (bAnd_iff _ _).1 h
      have hw := (prep_wordK (n := 3510) (w := 12) (by norm_num) (by norm_num)
        (PS := R) (PSI := RI) (gs := gR) (j := j)
        (fun h hh => (prep_gR (by omega)).1) (fun h hh => (prep_gR (by omega)).2) _ hl).1
      rw [prep_eq (prep_gR hj).1 hw he]
      apply (Subgroup.closure_le _).2 ?_ (Quiver.SchreierGraph.evalWord_mem_closure _ _)
      rintro _ ⟨a, rfl⟩
      exact ih a a.2 (by omega)

theorem P_le_sup :
    fi22P ≤ A0 ⊔ fi22H 1 := by
  obtain ⟨hl, he⟩ := bAnd_iff (bAnd(lettersK 26 (genA0Word ()), lettersK 26 (genA1Word ())))
    (bAnd(Nat.beq (Fi22CGT.F 0) (wR (genA0Word ())), Nat.beq (Fi22CGT.F 1) (wR (genA1Word ()))))
    |>.1 slpGen
  obtain ⟨hl0, hl1⟩ := bAnd_iff (lettersK 26 (genA0Word ())) (lettersK 26 (genA1Word ())) |>.1 hl
  obtain ⟨he0, he1⟩ := bAnd_iff (Nat.beq (Fi22CGT.F 0) (wR (genA0Word ())))
    (Nat.beq (Fi22CGT.F 1) (wR (genA1Word ()))) |>.1 he
  have hw := fun wd (hl : lettersK 26 wd = true) => (prep_wordK (n := 3510) (w := 12)
    (by norm_num) (by norm_num) (PS := R) (PSI := RI) (gs := gR) (j := 26)
    (fun h hh => (prep_gR hh).1) (fun h hh => (prep_gR hh).2) wd hl).1
  have hmem : ∀ wd : List ℤ, Quiver.SchreierGraph.evalWord (fun h : Fin 26 => gR h)
      (toLetters 26 wd) ∈ A0 ⊔ fi22H 1 := fun wd => by
    apply (Subgroup.closure_le _).2 ?_ (Quiver.SchreierGraph.evalWord_mem_closure _ _)
    rintro _ ⟨a, rfl⟩
    exact gR_mem a a.2
  have hg : ∀ {k : ℕ} (hk : k < 2), PRep 3510 12 (Fi22CGT.F k) (fi22GenPerm k) := fun hk => by
    have h := rep_fi22Gen hk
    rw [Fi22G.gen_eq hk] at h
    exact prep_of_rep h
  rw [fi22P, RawSchreierDatum.originalSubgroup, Subgroup.closure_le]
  intro g hg'
  obtain ⟨k, rfl⟩ := (schreier_vector_mem_toList_iff_get _ _).1 hg'
  rw [fi22Chain_original_get]
  obtain ⟨k, hk⟩ := k
  change fi22GenPerm k ∈ _
  have hk2 : k < 2 := hk
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · rw [prep_eq (hg hk2) (hw _ hl0) he0]
    exact hmem _
  · rw [prep_eq (hg hk2) (hw _ hl1) he1]
    exact hmem _

open Certificates in
open CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore CFSG.LocalAnalysis.WeakClosure81.Asch54Fi22 in
theorem facts75339 : fi22P ≤ A0 ⊔ fi22H 1 :=
  P_le_sup

end CertificateChecks.KernelSpor.A54F22G

end
