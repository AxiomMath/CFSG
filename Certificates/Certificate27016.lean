module

public import Certificates.Data.TitsAschbacherSecFour
public import Certificates.Kernel.EvenBN.CNtEq
public import Certificates.Kernel.EvenBN.Lists
public import Certificates.Kernel.EvenBN.K27016S0
public import Certificates.Kernel.EvenBN.K27016S1
public import Certificates.Kernel.EvenBN.K27016S2
public import Certificates.Kernel.EvenBN.K27016S3
public import Certificates.Kernel.EvenBN.K27016S4
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.EvenBN.BaseTwCSound
import CFSG.Certificates.Kernel.MonsterB.Co2MatSound
import CFSG.Certificates.Kernel.Spor.SiftRSound
public import Certificates.Certificate7050Base

public section

set_option maxRecDepth 400000

namespace CertificateChecks.Batch27016

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.BfsPin
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits
open CertificateChecks.KernelSpor CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.TitsHelp CertificateChecks.KernelSporSch.TitsInv
open CertificateChecks.KernelSporSch.TitsCentral (canId)
open CertificateChecks.KernelSpor.Tits2268 (bindsN permN)
open CFSG.Certificates.Native (rawLevels)
open CertificateChecks.KernelEvenBN Certificates.TitsAschbacherParrott Certificates.TitsAschbacherSecFour

theorem all_of_chunks {f : Nat → Bool} {L : List Nat} (n : Nat) : ∀ (k m : Nat),
    L.length ≤ m + n * k → (∀ i < k, ((L.drop (m + n * i)).take n).all f = true) →
    (L.drop m).all f = true
  | 0, m, hl, _ => by
    rw [List.drop_eq_nil_of_le (by omega)]
    rfl
  | k + 1, m, hl, h => by
    rw [← List.take_append_drop n (L.drop m), List.all_append, Bool.and_eq_true]
    refine ⟨by simpa using h 0 (by omega), ?_⟩
    rw [List.drop_drop]
    refine all_of_chunks n k (m + n) (by rw [Nat.mul_succ] at hl; omega) fun i hi => ?_
    have e : m + n + n * i = m + n * (i + 1) := by ring
    rw [e]
    exact h (i + 1) (by omega)

theorem all_chunks : CNtC.all cKc = true := by
  rw [← List.take_append_drop 128 CNtC, List.all_append, k0, Bool.true_and]
  refine all_of_chunks 16 88 128 (by rw [cnt_len]) fun i hi => ?_
  interval_cases i
  exacts [d128, d144, d160, d176, d192, d208, d224, d240, d256, d272, d288, d304, d320, d336,
    d352, d368, d384, d400, d416, d432, d448, d464, d480, d496, d512, d528, d544, d560, d576,
    d592, d608, d624, d640, d656, d672, d688, d704, d720, d736, d752, d768, d784, d800, d816,
    d832, d848, d864, d880, d896, d912, d928, d944, d960, d976, d992, d1008, d1024, d1040, d1056,
    d1072, d1088, d1104, d1120, d1136, d1152, d1168, d1184, d1200, d1216, d1232, d1248, d1264,
    d1280, d1296, d1312, d1328, d1344, d1360, d1376, d1392, d1408, d1424, d1440, d1456, d1472,
    d1488, d1504, d1520]

theorem compA_idA : compA 1755 (idA 1755) (idA 1755) = idA 1755 := by
  apply Array.ext
  · simp [compA, idA]
  · intro i h1 h2
    have hi : i < 1755 := by simpa [idA] using h2
    have e := CFSG.KC.Co2Mem.compA_get (t := idA 1755) (u := idA 1755) hi
    rw [CFSG.KC.Co2Mem.idA_get hi, CFSG.KC.Co2Mem.idA_get hi,
      getElem!_pos (compA 1755 (idA 1755) (idA 1755)) i h1] at e
    rw [e, ← getElem!_pos (idA 1755) i h2, CFSG.KC.Co2Mem.idA_get hi]

theorem sqIter_id : ∀ k, sqIter k (idA 1755) = idA 1755
  | 0 => rfl
  | k + 1 => by
    unfold sqIter
    rw [compA_idA]
    exact sqIter_id k

theorem sqE_eq : ∀ (k c : Nat), C c → sqE k c = eqA 1755 (sqIter k (unpack 1755 11 c)) (idA 1755)
  | 0, c, hc => by
    change Nat.beq c (pidn 1755 11) = _
    rw [sqIter, CertificateChecks.KernelSporSch.TitsCentral.id_eq, eqU hc canId]
  | k + 1, c, hc => by
    change bIf(Nat.beq c (pidn 1755 11), true, strictB (pc c c) (sqE k)) = _
    cases h : Nat.beq c (pidn 1755 11)
    · change strictB (pc c c) (sqE k) = _
      rw [strictB_app, sqE_eq k (pc c c) (cmpC hc hc)]
      have e : sqIter (k + 1) (unpack 1755 11 c) =
          sqIter k (compA 1755 (unpack 1755 11 c) (unpack 1755 11 c)) := rfl
      rw [e, cmpU hc hc]
      rfl
    · change true = _
      rw [Nat.eq_of_beq_eq_true h, ← CertificateChecks.KernelSporSch.TitsCentral.id_eq, sqIter_id]
      exact (CFSG.KC.Co2Mem.eqA_iff.2 fun _ _ => rfl).symm

theorem u1_eq : u1A = unpack 1755 11 U1 ∧ C U1 := nW (w := u1Word) (by decide)
theorem u2_eq : u2A = unpack 1755 11 U2 ∧ C U2 := nW (w := u2Word) (by decide)

theorem u3_eq : u3A = unpack 1755 11 U3 ∧ C U3 := by
  unfold u3A U3 pc
  rw [u1_eq.1, u2_eq.1, cmpU u1_eq.2 u2_eq.2]
  exact ⟨rfl, cmpC u1_eq.2 u2_eq.2⟩

theorem q_eq : qArrs = QL.map (unpack 1755 11) ∧ ∀ q ∈ QL, C q := by
  have hl : ∀ w ∈ qWords, nLetters w = true := by decide
  refine ⟨?_, fun q hq => ?_⟩
  · unfold qArrs QL
    rw [List.map_map]
    exact List.map_congr_left fun w hw => (nW (hl w hw)).1
  · unfold QL at hq
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hq
    exact (nW (hl w hw)).2

theorem tu_eq : u10List = TU.map (unpack 1755 11) ∧ ∀ x ∈ TU, C x := by
  obtain ⟨h1, c1⟩ := u1_eq
  obtain ⟨h2, c2⟩ := u2_eq
  obtain ⟨h3, c3⟩ := u3_eq
  refine ⟨?_, fun x hx => ?_⟩
  · unfold u10List TU pc
    rw [h1, h2, h3, t_eq, CertificateChecks.KernelSporSch.TitsCentral.id_eq, cmpU cT c1, cmpU cT c2,
      cmpU cT c3]
    rfl
  · unfold TU at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact canId
    · exact c1
    · exact c2
    · exact c3
    · exact cT
    · exact cmpC cT c1
    · exact cmpC cT c2
    · exact cmpC cT c3

theorem lit_eq : U1L = U1 ∧ U2L = U2 ∧ QL = [Q1L, Q2L, Q3L] := by
  have h := kLit
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, (beq_iff_eq.1 h3).symm⟩

theorem u3L_eq : U3L = U3 := by
  rw [Nat.eq_of_beq_eq_true kLit3, lit_eq.1, lit_eq.2.1]
  rfl

theorem uL_eq : u1A = unpack 1755 11 U1L ∧ u2A = unpack 1755 11 U2L ∧ u3A = unpack 1755 11 U3L := by
  rw [lit_eq.1, lit_eq.2.1, u3L_eq]
  exact ⟨u1_eq.1, u2_eq.1, u3_eq.1⟩

theorem qL_eq : qArrs = [unpack 1755 11 Q1L, unpack 1755 11 Q2L, unpack 1755 11 Q3L] := by
  rw [q_eq.1, lit_eq.2.2]
  simp only [List.map_cons, List.map_nil]

theorem tul_eq : u10List = TUL.map (unpack 1755 11) ∧ ∀ x ∈ TUL, C x := by
  have e : TUL = TU := by
    unfold TUL TU
    rw [lit_eq.1, lit_eq.2.1, u3L_eq]
  rw [e]
  exact tu_eq

theorem siftN {X : Nat} (cX : C X)
    (h : siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsN.LR TitsN.TRI TitsN.BP 5 0 X = true) :
    siftA 1755 (rawLevels 1755 titsNArrs (baseArr 1755 titsNBase)) (baseArr 1755 titsNBase) 0
      (unpack 1755 11 X) = true :=
  siftK_soundR bindsN permN TitsN.hl rfl (hi_of cX) (range_of_canonK cX) h

theorem rng {x : Nat} (cx : C x) : ∀ i < 1755, (unpack 1755 11 x)[i]! < 1755 := fun i hi => by
  rw [unpack_getT hi]
  exact (canonK_facts cx).2.2.2 i hi

theorem aInj : ∀ i < 1755, ∀ j < 1755,
    (unpack 1755 11 (TAux.F 0))[i]! = (unpack 1755 11 (TAux.F 0))[j]! → i = j := by
  intro i hi j hj e
  rw [unpack_getT hi, unpack_getT hj] at e
  have hi' := Nat.eq_of_beq_eq_true (allN_spec kInv i hi)
  have hj' := Nat.eq_of_beq_eq_true (allN_spec kInv j hj)
  rw [e] at hi'
  exact hi'.symm.trans hj'

theorem keyC {k Y Z : Nat} (hk : k < tot5 TitsN.LR) (cY : C Y)
    (sY : siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsN.LR TitsN.TRI TitsN.BP 5 0 Y = true)
    (cZ : C Z)
    (sZ : siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsN.LR TitsN.TRI TitsN.BP 5 0 Z = true) :
    eqA 1755 (compA 1755 (unpack 1755 11 (PN k)) (unpack 1755 11 Y))
      (compA 1755 (unpack 1755 11 Z) (unpack 1755 11 (PN k))) = bT (gptC TitsN.LR TitsN.TR k) Y Z :=
  (baseTwC_eq bindsN TitsN.head TitsN.hl (NS := 220) (CH := 8) (by norm_num) TitsN.hs ndN hk cY
    (siftN cY sY) cZ (siftN cZ sZ)).symm

theorem keyA {k V U Z : Nat} (hk : k < tot5 TitsN.LR) (cc : C (PN k)) (cU : C U)
    (hz : Nat.beq (pcomp 1755 11 (mask 11) U (TAux.F 0)) (pcomp 1755 11 (mask 11) (TAux.F 0) Z) = true)
    (cV : C V)
    (sV : siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsN.LR TitsN.TRI TitsN.BP 5 0 V = true)
    (cZ : C Z)
    (sZ : siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsN.LR TitsN.TRI TitsN.BP 5 0 Z = true) :
    eqA 1755 (compA 1755 (unpack 1755 11 (pc (TAux.F 0) (PN k))) (unpack 1755 11 V))
      (compA 1755 (unpack 1755 11 U) (unpack 1755 11 (pc (TAux.F 0) (PN k)))) =
      bT (gptC TitsN.LR TitsN.TR k) V Z := by
  have e : compA 1755 (unpack 1755 11 U) (unpack 1755 11 (TAux.F 0)) =
      compA 1755 (unpack 1755 11 (TAux.F 0)) (unpack 1755 11 Z) := by
    rw [cmpU cU cAux, cmpU cAux cZ, Nat.eq_of_beq_eq_true hz]
  have hUA : ∀ i < 1755, (unpack 1755 11 U)[(unpack 1755 11 (TAux.F 0))[i]!]! =
      (unpack 1755 11 (TAux.F 0))[(unpack 1755 11 Z)[i]!]! := fun i hi => by
    have := congrArg (·[i]!) e
    rwa [CFSG.KC.Co2Mem.compA_get hi, CFSG.KC.Co2Mem.compA_get hi] at this
  unfold pc
  rw [← cmpU cAux cc, eqA_conjL aInj (rng cc) (rng cV) (rng cZ) hUA]
  exact keyC hk cV sV cZ sZ

theorem cOK_gen {x : Nat} (cx : C x) {g : Nat → Nat} {Z1 Z2 Z3 R1 R2 R3 : Nat}
    (h11 : eqA 1755 (compA 1755 (unpack 1755 11 x) (unpack 1755 11 U1L))
      (compA 1755 (unpack 1755 11 U1L) (unpack 1755 11 x)) = bT g U1L Z1)
    (h12 : eqA 1755 (compA 1755 (unpack 1755 11 x) (unpack 1755 11 U1L))
      (compA 1755 (unpack 1755 11 U2L) (unpack 1755 11 x)) = bT g U1L Z2)
    (h13 : eqA 1755 (compA 1755 (unpack 1755 11 x) (unpack 1755 11 U1L))
      (compA 1755 (unpack 1755 11 U3L) (unpack 1755 11 x)) = bT g U1L Z3)
    (h21 : eqA 1755 (compA 1755 (unpack 1755 11 x) (unpack 1755 11 U2L))
      (compA 1755 (unpack 1755 11 U1L) (unpack 1755 11 x)) = bT g U2L Z1)
    (h22 : eqA 1755 (compA 1755 (unpack 1755 11 x) (unpack 1755 11 U2L))
      (compA 1755 (unpack 1755 11 U2L) (unpack 1755 11 x)) = bT g U2L Z2)
    (h23 : eqA 1755 (compA 1755 (unpack 1755 11 x) (unpack 1755 11 U2L))
      (compA 1755 (unpack 1755 11 U3L) (unpack 1755 11 x)) = bT g U2L Z3)
    (hq1 : eqA 1755 (compA 1755 (unpack 1755 11 x) (unpack 1755 11 Q1L))
      (compA 1755 (unpack 1755 11 Q1L) (unpack 1755 11 x)) = bT g Q1L R1)
    (hq2 : eqA 1755 (compA 1755 (unpack 1755 11 x) (unpack 1755 11 Q2L))
      (compA 1755 (unpack 1755 11 Q2L) (unpack 1755 11 x)) = bT g Q2L R2)
    (hq3 : eqA 1755 (compA 1755 (unpack 1755 11 x) (unpack 1755 11 Q3L))
      (compA 1755 (unpack 1755 11 Q3L) (unpack 1755 11 x)) = bT g Q3L R3) :
    cOK (unpack 1755 11 x) = cKG g Z1 Z2 Z3 R1 R2 R3 x := by
  have eT : u10List.any (eqA 1755 (unpack 1755 11 x)) = TUL.any (Nat.beq x) := by
    rw [tul_eq.1]
    exact any_mapU tul_eq.2 fun y cy => eqU cx cy
  obtain ⟨e1, e2, e3⟩ := uL_eq
  unfold cOK cKG uSharp
  rw [qL_eq, eT, ← sqE_eq 10 x cx, e1, e2, e3]
  unfold commA
  simp only [List.any_cons, List.any_nil, List.all_cons, List.all_nil, Bool.or_false,
    Bool.and_true]
  rw [h11, h12, h13, h21, h22, h23, hq1, hq2, hq3]

theorem cOK_c {k : Nat} (hk : k < tot5 TitsN.LR) (cc : C (PN k)) :
    cOK (unpack 1755 11 (PN k)) =
      cKG (gptC TitsN.LR TitsN.TR k) U1L U2L U3L Q1L Q2L Q3L (PN k) :=
  cOK_gen cc (keyC hk cU1 kS0 cU1 kS0) (keyC hk cU1 kS0 cU2 kS1)
    (keyC hk cU1 kS0 cU3 kS2) (keyC hk cU2 kS1 cU1 kS0) (keyC hk cU2 kS1 cU2 kS1)
    (keyC hk cU2 kS1 cU3 kS2) (keyC hk cQ1 kS3 cQ1 kS3) (keyC hk cQ2 kS4 cQ2 kS4)
    (keyC hk cQ3 kS5 cQ3 kS5)

theorem cOK_a {k : Nat} (hk : k < tot5 TitsN.LR) (cc : C (PN k)) :
    cOK (unpack 1755 11 (pcomp 1755 11 (mask 11) (TAux.F 0) (PN k))) =
      cKG (gptC TitsN.LR TitsN.TR k) AU1 AU2 AU3 AQ1 AQ2 AQ3 (pc (TAux.F 0) (PN k)) := by
  have h := kConj
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨z1, z2⟩, z3⟩, q1⟩, q2⟩, q3⟩ := h
  exact cOK_gen (cmpC cAux cc) (keyA hk cc cU1 z1 cU1 kS0 cAU1 kS6)
    (keyA hk cc cU2 z2 cU1 kS0 cAU2 kS7) (keyA hk cc cU3 z3 cU1 kS0 cAU3 kS8)
    (keyA hk cc cU1 z1 cU2 kS1 cAU1 kS6) (keyA hk cc cU2 z2 cU2 kS1 cAU2 kS7)
    (keyA hk cc cU3 z3 cU2 kS1 cAU3 kS8) (keyA hk cc cQ1 q1 cQ1 kS3 cAQ1 kS9)
    (keyA hk cc cQ2 q2 cQ2 kS4 cAQ2 kS10) (keyA hk cc cQ3 q3 cQ3 kS5 cAQ3 kS11)

theorem tits_sec_four_check_1 : enumCheck = true := by
  unfold enumCheck
  rw [cnt_eq, List.all_map, CertificateChecks.KernelEvenBN.aux_eq, ← all_chunks]
  refine all_congr_mem fun k hk => ?_
  have cc := cnt_canon k hk
  have hkt := ascK_lt aCNt k hk
  simp only [Function.comp_apply]
  unfold cKc
  rw [cmpU cAux cc, cOK_c hkt cc, cOK_a hkt cc]

end CertificateChecks.Batch27016

namespace Certificates

open CertificateChecks

theorem certificate27016 : Certificates.TitsAschbacherSecFour.enumCheck = true := by
  exact CertificateChecks.Batch27016.tits_sec_four_check_1

end Certificates
