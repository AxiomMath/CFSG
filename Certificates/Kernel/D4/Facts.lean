module

public import Certificates.Kernel.D4.ChainA
public import Certificates.Kernel.D4.ChainB
public import Certificates.Kernel.D4.ChecksA
public import Certificates.Kernel.D4.ChecksB
public import Certificates.Kernel.D4.OrbA
public import CFSG.Certificates.Kernel.D4Sound
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Quasithin.Recognition.CertChain
public import CFSG.Certificates.Kernel.B3S3KSound
public import CFSG.Certificates.Kernel.Misc.ChainTailOrbSound
public import CFSG.Certificates.NativeSchreierArrays

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelD4

open CFSG.RankThree.PartTwo.Sec4.Item434D42 CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.B3S3K
open CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail CFSG.KC.D4K CFSG.KC.BfsPin
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.RankThree.Native
open CFSG.RankThree.PartOne CFSG.Monster.B.Fischer CFSG.RankThree.PartTwo.KFacts.K426
open CFSG.Monster.B.Co2 (allLt_iff permOfArr)

theorem arr_eq : ∀ k < 91, d4Arr k = unpack 2457 12 (HX.F k) := by
  intro k hk
  rw [d4Arr, HX.eq]
  exact CFSG.KC.Misc.HexFlat.hexTable_sound HX.all k hk

theorem fget {m o : ℕ} (hm : o + m ≤ 91) {j : ℕ} (hj : j < m) :
    (Array.ofFn fun i : Fin m => d4Arr (o + i.val))[j]! = unpack 2457 12 (HX.F (o + j)) := by
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  exact arr_eq _ (by omega)

theorem eqA_self' (n : ℕ) (t : Array ℕ) : eqA n t t = true := by
  unfold eqA
  rw [allLt_iff]
  intro i _
  exact beq_self_eq_true _

theorem keys_eq : d4ChainABaseArr.toList = d4Keys := by
  simp [d4ChainABaseArr, d4Keys]

theorem bindL : BindA 2457 12 d4Lines 31 LX :=
  ⟨by simp [d4Lines], fun j hj => by unfold d4Lines; rw [fget (by norm_num) hj]; rfl⟩

theorem bindH : BindA 2457 12 d4Trans 31 HT :=
  ⟨by simp [d4Trans], fun j hj => by unfold d4Trans; rw [fget (by norm_num) hj]; rfl⟩

theorem pLX : ∀ j < 31, permB 2457 12 (LX j) = true := fun j hj => by
  have := Orb.allN_iff.1 pL j hj
  rw [Bool.and_eq_true] at this
  exact this.1

theorem bindsA : Binds 2457 12 CA.S 8 7 CA.BP d4ChainAArrs d4ChainABaseArr := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [d4ChainAArrs], fun j hj => ?_,
    by simp [d4ChainABaseArr, d4ChainABase], baseA⟩
  have e : CA.S j = HX.F (66 + j) := Nat.eq_of_beq_eq_true (Orb.allN_iff.1 sA j hj)
  unfold d4ChainAArrs
  rw [fget (by norm_num) hj, e]

theorem rawA : rawChainOK 2457 (d4ChainAArrs.extract 0 2) d4ChainAArrs d4ChainABaseArr
    d4ChainAWords 1 = true := by
  have h := rawChainK_sound (chunks := 1) (NS := 154) (CH := 16) bindsA CA.head CA.hl
    (by norm_num) CA.hs
  rwa [wA] at h

theorem chainA_ok :
    caseChainOK2P 2457 d4ChainAArrs d4ChainABaseArr d4ChainAWords d4GenA d4GenB = true := by
  unfold caseChainOK2P d4GenA d4GenB
  rw [rawA, eqA_self', eqA_self']
  rfl

theorem orbitsA : rawOrbitSizes 2457 d4ChainAArrs d4ChainABaseArr = [2457, 2048, 7, 1, 1, 3, 2] := by
  rw [rawOrbitSizesK_sound bindsA permA CA.hl]
  exact orbA

theorem siftA_ofOK {G : ℕ} (h : siftOK 2457 12 CA.LR CA.TRI CA.BP 7 G = true) :
    siftA 2457 d4LevelsA d4ChainABaseArr 0 (unpack 2457 12 G) = true :=
  siftA_of bindsA permA CA.hl (siftOK_parts h)

theorem bindQ : BindA 2457 12 d4QGens EQ.ng EQ.G := by
  have hng : EQ.ng = 4 := Nat.eq_of_beq_eq_true bQ.2.1
  refine ⟨by rw [hng]; simp [d4QGens], fun j hj => ?_⟩
  rw [hng] at hj
  have e : EQ.G j = HX.F j := Nat.eq_of_beq_eq_true (Orb.allN_iff.1 bQ.1 j hj)
  unfold d4QGens
  rw [fget (by norm_num) hj, e, Nat.zero_add]

theorem okQ : bfsK 2457 12 EQ.ng EQ.G EQ.N EQ.T EQ.E EQ.S = true :=
  bfsK_of_slices (L := 27) (K := 3) (C := EQ.C) (by decide) (by norm_num) szOK' EQ.g EQ.csAll EQ.t0
    EQ.dist (Nat.eq_of_beq_eq_true EQ.c0) (Nat.eq_of_beq_eq_true EQ.cK) EQ.rsAll

theorem pQG : ∀ k < EQ.ng, permB 2457 12 (EQ.G k) = true := fun k hk => by
  rw [Nat.eq_of_beq_eq_true bQ.2.1] at hk
  exact Orb.allN_iff.1 pQ k hk

theorem enumQ : enumOK 2457 d4QGens d4Keys d4QCert = true ∧ d4QCert.pts.size = EQ.N ∧
    ∀ i < EQ.N, d4QCert.pts[i]! = unpack 2457 12 (EQ.T i) := by
  have h := enum_of (fuel := 100) bindQ pQG okQ (mem_base_lt bindsA CA.hl) EQ.keys
    (by rw [Nat.eq_of_beq_eq_true bQ.2.2]; norm_num)
  rw [keys_eq] at h
  exact h

theorem lines_ok : linesOK3 3 81 31 2457 d4QGens d4Keys d4QCert d4Lines = true := by
  obtain ⟨h1, h2, h3⟩ := enumQ
  have hN : EQ.N = 81 := Nat.eq_of_beq_eq_true bQ.2.2
  rw [hN] at h2 h3
  have hTp : ∀ i < 81, permB 2457 12 (EQ.T i) = true := by
    rw [← hN]
    exact permB_pts okQ pQG
  have hl : linesK 2457 12 3 81 31 EQ.T LX = true :=
    linesK_of (forall_of_slices (L := 9) (K := 9) (by norm_num) LS.all) pL
  exact linesOK3_of szOK' h1 h2 h3 hTp bindL hl

theorem siftQ_ok :
    allLt d4QGens.size (fun l => siftA 2457 d4LevelsA d4ChainABaseArr 0 d4QGens[l]!) = true := by
  rw [allLt_iff]
  intro l hl
  have hl4 : l < 4 := by simpa [d4QGens] using hl
  have e : d4QGens[l]! = unpack 2457 12 (HX.F l) := by
    unfold d4QGens
    rw [fget (by norm_num) hl4, Nat.zero_add]
  rw [e]
  exact siftA_ofOK (Orb.allN_iff.1 siftQ l hl4)

theorem trans_ok :
    transOK2 31 2457 d4Trans d4Lines d4Lines d4Rec d4LevelsA d4ChainABaseArr = true :=
  transOK2_of szOK' bindH bindL pLX bindL pLX (by decide) (fun j hj => by
      rw [bindH.2 j hj]
      exact siftA_ofOK (Orb.allN_iff.1 siftH j hj)) trans

theorem rec_ok : allLt 31 (fun j => decide (d4Rec.getD j 0 < 2)) = true := by
  rw [allLt_iff]
  decide

theorem bindG : BindA 2457 12 d4CAGens EA.ng EA.G := by
  have hng : EA.ng = 3 := Nat.eq_of_beq_eq_true bG.2.1
  refine ⟨by rw [hng]; simp [d4CAGens], fun j hj => ?_⟩
  rw [hng] at hj
  have e : EA.G j = HX.F (74 + j) := Nat.eq_of_beq_eq_true (Orb.allN_iff.1 bG.1 j hj)
  unfold d4CAGens
  rw [fget (by norm_num) hj, e]

theorem pGA : ∀ k < EA.ng, permB 2457 12 (EA.G k) = true := fun k hk => by
  rw [Nat.eq_of_beq_eq_true bG.2.1] at hk
  have := Orb.allN_iff.1 commA k hk
  rw [Bool.and_eq_true] at this
  exact this.1

theorem okA : bfsK 2457 12 EA.ng EA.G EA.N EA.T EA.E EA.S = true :=
  bfsK_of_slices (L := 56) (K := 27) (C := EA.C) (by decide) (by norm_num) szOK' EA.g EA.csAll EA.t0
    EA.dist (Nat.eq_of_beq_eq_true EA.c0) (Nat.eq_of_beq_eq_true EA.cK) EA.rsAll

theorem enumA : enumOK 2457 d4CAGens d4Keys d4CACert = true ∧ d4CACert.pts.size = EA.N ∧
    ∀ i < EA.N, d4CACert.pts[i]! = unpack 2457 12 (EA.T i) := by
  have h := enum_of (fuel := 1600) bindG pGA okA (mem_base_lt bindsA CA.hl) EA.keys
    (by rw [Nat.eq_of_beq_eq_true bG.2.2]; norm_num)
  rw [keys_eq] at h
  exact h

theorem lineX0 : d4Lines[0]! = unpack 2457 12 (LX 0) := bindL.2 0 (by norm_num)

theorem caseA_ok : centOKP 3 2457 d4ChainAArrs d4ChainABaseArr d4Lines[0]! d4RelsA d4CAGens d4Keys
    d4CACert 1512 = true := by
  obtain ⟨h1, h2, h3⟩ := enumA
  have hTp : ∀ i < EA.N, permB 2457 12 (EA.T i) = true := permB_pts okA pGA
  have hps : ∀ q ∈ d4Keys, q < 2457 := by
    rw [← keys_eq]
    exact mem_base_lt bindsA CA.hl
  have h := centOKP_of_orbS (p := 3) szOK' bindsA permA CA.hl (k := 2) (by simp [d4ChainAArrs])
    ndA (by norm_num) rawA x0 relsA bindG commA
    (fun k hk => by
      rw [Nat.eq_of_beq_eq_true bG.2.1] at hk
      exact siftA_ofOK (Orb.allN_iff.1 siftG k hk)) hps h1 h2 h3 hTp (by norm_num) (NR := 1)
    (RB := RA) (RI := RIA) (EK := EKA) (fun j hj => by
      obtain rfl : j = 0 := by omega
      exact tbA0) (by rw [Nat.eq_of_beq_eq_true rc0A]; exact Orb.allN_iff.1 kOrbA)
  rw [Nat.eq_of_beq_eq_true bG.2.2] at h
  rw [lineX0]
  exact h

theorem bindsB : Binds 2457 12 CB.S 9 5 CB.BP d4ChainBArrs d4ChainBBaseArr := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [d4ChainBArrs], fun j hj => ?_,
    by simp [d4ChainBBaseArr, d4ChainBBase], baseB⟩
  have e : CB.S j = HX.F (77 + j) := Nat.eq_of_beq_eq_true (Orb.allN_iff.1 sB j hj)
  unfold d4ChainBArrs
  rw [fget (by norm_num) hj, e]

theorem b0 : d4ChainBArrs[0]! = d4GenA := by
  have e : HX.F 77 = HX.F 66 := Nat.eq_of_beq_eq_true abB.1
  unfold d4GenA d4ChainBArrs d4ChainAArrs
  rw [fget (o := 77) (by norm_num) (by norm_num : 0 < 9), fget (o := 66) (by norm_num)
    (by norm_num : 0 < 8)]
  change unpack 2457 12 (HX.F 77) = unpack 2457 12 (HX.F 66)
  rw [e]

theorem b1 : d4ChainBArrs[1]! = d4GenB := by
  have e : HX.F 78 = HX.F 67 := Nat.eq_of_beq_eq_true abB.2
  unfold d4GenB d4ChainBArrs d4ChainAArrs
  rw [fget (o := 77) (by norm_num) (by norm_num : 1 < 9), fget (o := 66) (by norm_num)
    (by norm_num : 1 < 8)]
  change unpack 2457 12 (HX.F 78) = unpack 2457 12 (HX.F 67)
  rw [e]

theorem orbitsB : rawOrbitSizes 2457 d4ChainBArrs d4ChainBBaseArr = [2457, 2048, 21, 2, 1] := by
  rw [rawOrbitSizesK_sound bindsB permB' CB.hl]
  exact orbB

theorem card_ab : Nat.card (Subgroup.closure {g | ∃ k < (#[d4GenA, d4GenB] : Array (Array ℕ)).size,
    permOfArr 2457 (#[d4GenA, d4GenB] : Array (Array ℕ))[k]! = g} :
      Subgroup (Equiv.Perm (Fin 2457))) = 211341312 := by
  have h := CFSG.Quasithin.card_closure_permOfArr_of_rawChainOK (n := 2457) (by norm_num)
    (O := #[d4GenA, d4GenB]) (S := d4ChainAArrs) (W := d4ChainAWords) (base := d4ChainABase)
    (by decide) (chunks := 1) (by norm_num) (by simp [d4ChainAArrs]) (fun i hi => by
      have hi2 : i < 2 := by simpa using hi
      interval_cases i <;> rfl) rawA
  rw [h]
  change (rawOrbitSizes 2457 d4ChainAArrs d4ChainABaseArr).prod = 211341312
  rw [orbitsA]
  decide

theorem rawB : rawChainOK 2457 (d4ChainBArrs.extract 0 2) d4ChainBArrs d4ChainBBaseArr
    d4ChainBWords 1 = true := by
  obtain ⟨hk, hH⟩ := Orb.rawHeadOK_of bindsB CB.head
  rw [wB] at hH
  refine Orb.rawChainOK_of_head_card 1 hk hH ?_
  rw [orbitsB]
  have e : (Set.range fun j : Fin 2 => permOfArr 2457 d4ChainBArrs[j.val]!) =
      {g | ∃ k < (#[d4GenA, d4GenB] : Array (Array ℕ)).size,
        permOfArr 2457 (#[d4GenA, d4GenB] : Array (Array ℕ))[k]! = g} := by
    ext g
    simp only [Set.mem_range, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨j, hj⟩, rfl⟩
      refine ⟨j, by simpa using hj, ?_⟩
      interval_cases j
      · simp [b0]
      · simp [b1]
    · rintro ⟨k, hk, rfl⟩
      have hk2 : k < 2 := by simpa using hk
      refine ⟨⟨k, hk2⟩, ?_⟩
      interval_cases k
      · simp [b0]
      · simp [b1]
  rw [e, card_ab]
  decide

theorem chainB_ok :
    caseChainOK2P 2457 d4ChainBArrs d4ChainBBaseArr d4ChainBWords d4GenA d4GenB = true := by
  unfold caseChainOK2P
  rw [rawB, b0, b1, eqA_self', eqA_self']
  rfl

theorem siftB_ofOK {G : ℕ} (h : siftOK 2457 12 CB.LR CB.TRI CB.BP 5 G = true) :
    siftA 2457 (rawLevels 2457 d4ChainBArrs d4ChainBBaseArr) d4ChainBBaseArr 0
      (unpack 2457 12 G) = true :=
  siftA_of bindsB permB' CB.hl (siftOK_parts h)

theorem bindGB : BindA 2457 12 d4CBGens EB.ng EB.G := by
  have hng : EB.ng = 5 := Nat.eq_of_beq_eq_true bGB.2.1
  refine ⟨by rw [hng]; simp [d4CBGens], fun j hj => ?_⟩
  rw [hng] at hj
  have e : EB.G j = HX.F (86 + j) := Nat.eq_of_beq_eq_true (Orb.allN_iff.1 bGB.1 j hj)
  unfold d4CBGens
  rw [fget (by norm_num) hj, e]

theorem pGB : ∀ k < EB.ng, permB 2457 12 (EB.G k) = true := fun k hk => by
  rw [Nat.eq_of_beq_eq_true bGB.2.1] at hk
  have := Orb.allN_iff.1 commB k hk
  rw [Bool.and_eq_true] at this
  exact this.1

theorem okB : bfsK 2457 12 EB.ng EB.G EB.N EB.T EB.E EB.S = true :=
  bfsK_of_slices (L := 54) (K := 12) (C := EB.C) (by decide) (by norm_num) szOK' EB.g EB.csAll EB.t0
    EB.dist (Nat.eq_of_beq_eq_true EB.c0) (Nat.eq_of_beq_eq_true EB.cK) EB.rsAll

theorem enumB : enumOK 2457 d4CBGens d4Keys d4CBCert = true ∧ d4CBCert.pts.size = EB.N ∧
    ∀ i < EB.N, d4CBCert.pts[i]! = unpack 2457 12 (EB.T i) := by
  have h := enum_of (fuel := 700) bindGB pGB okB (mem_base_lt bindsA CA.hl) EB.keys
    (by rw [Nat.eq_of_beq_eq_true bGB.2.2]; norm_num)
  rw [keys_eq] at h
  exact h

theorem lineX1 : d4Lines[1]! = unpack 2457 12 (LX 1) := bindL.2 1 (by norm_num)

theorem tailB_reps : ∀ j < 7, tailB (RB j) = true := by
  intro j hj
  interval_cases j
  exacts [tbR0, tbR1, tbR2, tbR3, tbR4, tbR5, tbR6]

theorem orbFactsB : ∀ k < rcnt (CB.LR 0), RB (RIB k) < rcnt (CB.LR 0) ∧ EKB k < EB.N ∧
    pg 12 (mask 12) (EB.T (EKB k)) (rpt 12 (mask 12) (CB.LR 0) (RB (RIB k))) =
      rpt 12 (mask 12) (CB.LR 0) k ∧
    ptailBranchK 2457 12 CB.LR CB.TR CB.BP (LX 1) (pw 2457 12 (LX 1)) d4RelsB EB.N EB.T 5
      (RB (RIB k)) = true := by
  rw [Nat.eq_of_beq_eq_true rc0B]
  intro k hk
  have h := Orb.allN_iff.1 kOrbB k hk
  unfold orbKB at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq,
    Nat.blt_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h2, h3, Nat.eq_of_beq_eq_true h4, tailB_reps _ h1⟩

theorem relsB0 : ∀ r ∈ d4RelsB, Nat.max r.1 r.2.1 ≠ 0 := by decide

theorem chainArraysB :
    CFSG.Certificates.ChainArrays (CFSG.Certificates.RawSchreierDatum.ofArrays 2457 (by norm_num)
      d4ChainBArrs 2 (by simp [d4ChainBArrs]) d4ChainBBase (by decide +kernel) d4ChainBWords)
      (d4ChainBArrs.extract 0 2) d4ChainBArrs d4ChainBBaseArr d4ChainBWords :=
  CFSG.Certificates.chainArrays_ofArrays (Orb.isInv_of bindsB permB')

theorem caseB_ok : centOKP 3 2457 d4ChainBArrs d4ChainBBaseArr d4Lines[1]! d4RelsB d4CBGens d4Keys
    d4CBCert 648 = true := by
  obtain ⟨h1, h2, h3⟩ := enumB
  have hTp : ∀ i < EB.N, permB 2457 12 (EB.T i) = true := permB_pts okB pGB
  have hps : ∀ q ∈ d4Keys, q < 2457 := by
    rw [← keys_eq]
    exact mem_base_lt bindsA CA.hl
  have h := centOKP_of_orb szOK' (p := 3) bindsB permB' CB.hl chainArraysB (by norm_num) rawB x1
    relsB relsB0 bindGB commB
    (fun k hk => by
      rw [Nat.eq_of_beq_eq_true bGB.2.1] at hk
      exact siftB_ofOK (Orb.allN_iff.1 siftGB k hk)) hps h1 h2 h3 hTp (by norm_num) orbFactsB
  rw [Nat.eq_of_beq_eq_true bGB.2.2] at h
  rw [lineX1]
  exact h

end CertificateChecks.KernelD4

end
