module

public import Certificates.Data.TabCo1ThreeC
public meta import Certificates.Data.TabCo1ThreeC
public import Certificates.Kernel.Co1B.Chk17329
public import Certificates.Kernel.Co1B.Lvl17329A
public import Certificates.Kernel.Co1B.Lvl17329B
public import Certificates.Kernel.Co1B.C17330
public import Certificates.Kernel.Co1B.C17591
public import Certificates.Kernel.Co1B.C2041
public import CFSG.Certificates.Kernel.Co1BFixImpSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Monster.B.TwoA.Par3.Main

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Bound17329

open CFSG.KC.Co1BBoundP (selC storeSel lvlChunkP lvlChunkP_eq)
open CFSG.KC.Co1BBoundN CFSG.KC.Co1BBound CFSG.KC.Co1BSpin CFSG.KC.Co1B CFSG.KC.Co1F2 CFSG.KC.M1F2
  CFSG.KLie.CT CFSG.KC.Enum CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeC
  CFSG.HardMathSupport.Dickson.I271.TabCo1 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1.TwoBNative
open CertificateChecks.KernelCo1B.Bound17591 (XB mem_eq mem_of_memK certVecs_size)
open CertificateChecks.KernelCo1B.Bound17330 (boundOK_of_sel lvl_eqn span_okn lvlOK_of_selC
  not_of_notB mul_unpackW' wf_unpackR)
open CFSG.KS.SporSch.M24 (unpackR_eq_unpack dagWK_sound gtBFS_of_K bfsTree gensArr gtPinK)

section Bound

variable {nb m : Nat} {TL : List Nat} {base' cnts' : List Nat} {conds' : List (List Cond)}
  {CF : List (List (List Nat))} {CN : List (List Nat)}

theorem lvl_okn' (hl : TL.length = nb)
    (hCF : CF = (List.range m).map fun i =>
      storeKn nb XB TL (base'.take i) (base'.getD i 0) (conds'.getD i []))
    {i : Nat} (hi : i < m)
    (hch : ∀ c < 9, lvlChunkKn nb XB TL CF CertificateChecks.KernelCo1B.CV.F CN (9 * i + c) = true)
    (hm : memK XB (base'.getD i 0) = true)
    (hlen : (CN.getD i []).length = 9) (hs : (CN.getD i []).sum ≤ cnts'.getD i 0) :
    lvlOK (xsSet ()) (TL.map (unpackR 24)).toArray base' i (conds'.getD i []) (cnts'.getD i 0) =
      true := by
  rw [lvl_eqn hl hCF hi, hm, Bool.true_and, decide_eq_true_iff]
  have h117 : (117 : Nat) = 13 * 9 := rfl
  rw [h117, CertificateChecks.KernelCo1B.Bound17591.cntTab_blocks]
  have hb : ∀ c < 9, cntTabK (condsKn nb XB TL (CF.getD i [])) CertificateChecks.KernelCo1B.CV.F
      (13 * c) 13 = getL 0 (CN.getD i []) c := by
    intro c hc
    have := hch c hc
    unfold lvlChunkKn at this
    have e1 : Nat.div (9 * i + c) 9 = i := by
      change (9 * i + c) / 9 = i
      omega
    have e2 : Nat.mod (9 * i + c) 9 = c := by
      change (9 * i + c) % 9 = c
      omega
    rw [e1, e2] at this
    exact Nat.eq_of_beq_eq_true this
  rw [List.map_congr_left fun c hc => hb c (List.mem_range.1 hc), ← hlen,
    CertificateChecks.KernelCo1B.Bound17591.sum_getL]
  exact hs

theorem boundOKF_of_sel {nfix : Nat} {span' : List (Nat × Nat)} {comb' : List Nat}
    {Sel : List (List Nat)} {NP : List Nat} (hl : TL.length = nb)
    (hb : base'.length = m) (hc : conds'.length = m) (hn : cnts'.length = m)
    (hCF : CF = (List.range m).map fun i =>
      storeSel nb XB TL (base'.take i) (base'.getD i 0) (conds'.getD i []) (Sel.getD i []))
    (hfix : ∀ i < nfix, cnts'.getD i 0 = 1)
    (hN : ∀ i < m, memK XB (base'.getD i 0) = true ∧ (CN.getD i []).length = 9 ∧
      (CN.getD i []).sum ≤ cnts'.getD i 0)
    (hch : ∀ n < 9 * m, 9 * nfix ≤ n →
      lvlChunkP nb XB TL CF NP CertificateChecks.KernelCo1B.CV.F CN n = true)
    (hs : (Nat.beq span'.length 24 && Nat.beq comb'.length 24 &&
      span'.all (fun s => Nat.blt s.1 m && Nat.blt s.2 nb) &&
      CFSG.KLie.CT.allN 24 (fun l => Nat.beq (vmF 24 (packL (span'.map (slotKn nb TL base')))
        (comb'.getD l 0)) (Nat.shiftLeft 1 l))) = true) :
    boundOKF (TL.map (unpackR 24)).toArray nb base' nfix conds' cnts' span' comb' = true := by
  unfold boundOKF
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨⟨by simp [hl], by rw [hc, hb]⟩, by rw [hn, hb]⟩, fun i hi => ?_⟩, span_okn hl hb hs⟩
  obtain ⟨h1, h2, h3⟩ := hN i (by omega)
  unfold lvlOKF
  by_cases hfi : i < nfix
  · rw [if_pos hfi, mem_eq, h1, Bool.true_and, decide_eq_true_iff]
    exact hfix i hfi
  rw [if_neg hfi]
  have hgs : ∀ j < m, ((List.range m).map fun j => selC (conds'.getD j []) (Sel.getD j [])).getD j [] =
      selC (conds'.getD j []) (Sel.getD j []) := fun j hj => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
    rfl
  have hCF' : CF = (List.range m).map fun j => storeKn nb XB TL (base'.take j) (base'.getD j 0)
      (((List.range m).map fun j => selC (conds'.getD j []) (Sel.getD j [])).getD j []) := by
    rw [hCF]
    exact List.map_congr_left fun j hj => by rw [hgs j (List.mem_range.1 hj)]; rfl
  have h := lvl_okn' hl hCF' (by omega)
    (fun c hc => (lvlChunkP_eq _ _ _ _ NP _ _ _).symm.trans (hch (9 * i + c) (by omega) (by omega)))
    h1 h2 h3
  rw [hgs i (by omega)] at h
  exact lvlOK_of_selC h

end Bound

theorem DF_base : [aR, bR] = (List.range 2).map fun i => CFSG.KS.Raw.unpack 24 24 (DF.M i) := by
  have h := kDFB
  simp only [Bool.and_eq_true] at h
  have e0 : DF.M 0 = CertificateChecks.KernelCo1ThreeK.SM 0 := Nat.eq_of_beq_eq_true h.1
  have e1 : DF.M 1 = CertificateChecks.KernelCo1ThreeK.SM 1 := Nat.eq_of_beq_eq_true h.2
  rw [CertificateChecks.KernelCo1ThreeK.base_eq]
  refine List.map_congr_left fun i hi => ?_
  have hi2 : i < 2 := List.mem_range.1 hi
  interval_cases i
  · rw [e0]
  · rw [e1]

theorem kDagC_eq : kDag ext = ((List.range 91).map fun i => CFSG.KS.Raw.unpack 24 24 (DF.M i),
    (List.range 91).map fun i => CFSG.KS.Raw.unpack 24 24 (DF.MI i), true) := by
  rw [kDag, ← kDFW]
  exact dagWK_sound DF_base kDF

theorem hflag : (kDag ext).2.2 = true := by
  rw [kDagC_eq]

theorem nd_eq {i : Nat} (h1 : 0 < i) (h2 : i ≤ 91) :
    nd (kDag ext) i = unpackR 24 (DF.M (i - 1)) := by
  rw [nd, kDagC_eq,
    List.getD_eq_getElem _ _ (by simp only [List.length_map, List.length_range]; omega),
    List.getElem_map, List.getElem_range, unpackR_eq_unpack]

theorem ndI_eq {i : Nat} (h1 : 0 < i) (h2 : i ≤ 91) :
    ndI (kDag ext) i = unpackR 24 (DF.MI (i - 1)) := by
  rw [ndI, kDagC_eq,
    List.getD_eq_getElem _ _ (by simp only [List.length_map, List.length_range]; omega),
    List.getElem_map, List.getElem_range, unpackR_eq_unpack]

theorem q1_eq : nd (kDag ext) 88 = unpackR 24 Q1K := nd_eq (by decide) (by decide)
theorem q2_eq : nd (kDag ext) 89 = unpackR 24 Q2K := nd_eq (by decide) (by decide)
theorem q3_eq : nd (kDag ext) 90 = unpackR 24 Q3K := nd_eq (by decide) (by decide)
theorem q4_eq : nd (kDag ext) 91 = unpackR 24 Q4K := nd_eq (by decide) (by decide)
theorem q1I_eq : ndI (kDag ext) 88 = unpackR 24 Q1I := ndI_eq (by decide) (by decide)
theorem q2I_eq : ndI (kDag ext) 89 = unpackR 24 Q2I := ndI_eq (by decide) (by decide)

theorem rootC_eq : rootRows3C () = unpackR 24 XK := by
  unfold rootRows3C XK
  rw [CertificateChecks.KernelCo1ThreeK.rootRows_eq (by decide), ← unpackR_eq_unpack]

theorem kSmall' : eqK (powWK XK 3) oneK = true ∧ notB (eqK XK oneK) = true ∧
    eqK XK (mulWK (mulWK Q1K Q2K) (mulWK Q1I Q2I)) = true ∧
    eqK (mulWK XK Q1K) (mulWK Q1K XK) = true ∧ eqK (mulWK XK Q2K) (mulWK Q2K XK) = true ∧
    eqK (mulWK XK Q3K) (mulWK Q3K XK) = true ∧ eqK (mulWK XK Q4K) (mulWK Q4K XK) = true := by
  have h := kSmall
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem c_wf1 : wf (unpackR 24 XK) = true := wf_unpackR _

theorem c_wf2 : wf (one ()) = true := by
  rw [CFSG.KC.Co1B.one_eq]
  exact wf_unpackR _

theorem c_ne : (unpackR 24 XK != one ()) = true := by
  rw [CFSG.KC.Co1B.one_eq, bne, beq_unpack]
  exact not_of_notB kSmall'.2.1

theorem c_pow : (pow (unpackR 24 XK) 3 == one ()) = true := by
  rw [pow_unpack', CFSG.KC.Co1B.one_eq, beq_unpack]
  exact kSmall'.1

theorem c_comm : (unpackR 24 XK == mul (mul (unpackR 24 Q1K) (unpackR 24 Q2K))
    (mul (unpackR 24 Q1I) (unpackR 24 Q2I))) = true := by
  rw [mul_unpackW', mul_unpackW', mul_unpackW', beq_unpack]
  exact kSmall'.2.2.1

theorem comm_unpack {A B : Nat} (h : eqK (mulWK A B) (mulWK B A) = true) :
    (mul (unpackR 24 A) (unpackR 24 B) == mul (unpackR 24 B) (unpackR 24 A)) = true := by
  rw [mul_unpackW', mul_unpackW', beq_unpack]
  exact h

theorem kQ' : gtPinK QM 4 300 QT.N QT.P QT.PAR QT.LAB QT.W QT.S = true ∧ QT.N = 243 := by
  have h := kQ
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact h

theorem QG_eq : [unpackR 24 Q1K, unpackR 24 Q2K, unpackR 24 Q3K, unpackR 24 Q4K].toArray =
    gensArr 4 QM := by
  apply Array.ext (by simp [gensArr])
  intro i h1 h2
  have hi : i < 4 := by simpa using h1
  interval_cases i <;> simp [gensArr, QM, Q1K, Q2K, Q3K, Q4K, unpackR_eq_unpack]

theorem gt_eq : gtBFS [unpackR 24 Q1K, unpackR 24 Q2K, unpackR 24 Q3K, unpackR 24 Q4K].toArray 300 =
    bfsTree QT.N QT.P QT.PAR QT.LAB := by
  rw [QG_eq]
  exact (gtBFS_of_K kQ'.1).1

theorem c_gt : gtOK [unpackR 24 Q1K, unpackR 24 Q2K, unpackR 24 Q3K, unpackR 24 Q4K].toArray
    (gtBFS [unpackR 24 Q1K, unpackR 24 Q2K, unpackR 24 Q3K, unpackR 24 Q4K].toArray 300) =
    true := by
  rw [gt_eq, QG_eq]
  exact (gtBFS_of_K kQ'.1).2

theorem c_size : decide ((gtBFS [unpackR 24 Q1K, unpackR 24 Q2K, unpackR 24 Q3K,
    unpackR 24 Q4K].toArray 300).pts.size = 243) = true := by
  rw [gt_eq, decide_eq_true_iff]
  simp [bfsTree, kQ'.2]

theorem fix_imp {v : Nat} (hv : v ∈ certVecs.toList) (hx : act (unpackR 24 XK) v = v) :
    ∀ t ∈ QTs, vmF 24 t v = v := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
  have hi' : i < 98280 := by simpa [certVecs_size] using hi
  have hj : i / 840 < 117 := by omega
  have hk : i % 840 < 840 := Nat.mod_lt _ (by decide)
  have e := CertificateChecks.KernelCo1B.certVecs_get hj hk
  rw [Nat.div_add_mod] at e
  have hg : certVecs.toList[i] = certVecs[i]! := by
    rw [Array.getElem_toList, getElem!_pos certVecs i (by rw [certVecs_size]; exact hi')]
  rw [hg, e] at hx ⊢
  rw [CFSG.KC.F2W.act_unpackR (T := XT) rfl] at hx
  have hall : ∀ q < 9, ch17329fx q = true := by
    intro q hq
    interval_cases q
    exacts [ch17329fx0, ch17329fx1, ch17329fx2, ch17329fx3, ch17329fx4, ch17329fx5, ch17329fx6,
      ch17329fx7, ch17329fx8]
  have e2 : Nat.add (Nat.mul 13 ((i / 840) / 13)) ((i / 840) % 13) = i / 840 := Nat.div_add_mod _ _
  have hv' : vmF 24 XT (pg 24 (CFSG.KS.mask 24) (CertificateChecks.KernelCo1B.CV.F
      (Nat.add (Nat.mul 13 ((i / 840) / 13)) ((i / 840) % 13))) (i % 840)) =
      pg 24 (CFSG.KS.mask 24) (CertificateChecks.KernelCo1B.CV.F
      (Nat.add (Nat.mul 13 ((i / 840) / 13)) ((i / 840) % 13))) (i % 840) := by
    rw [e2]
    exact hx
  have hF : fixAllT QTs (pg 24 (CFSG.KS.mask 24) (CertificateChecks.KernelCo1B.CV.F
      (Nat.add (Nat.mul 13 ((i / 840) / 13)) ((i / 840) % 13))) (i % 840)) = true :=
    fixImpTab_sound (F := fun j => CertificateChecks.KernelCo1B.CV.F
      (Nat.add (Nat.mul 13 ((i / 840) / 13)) j)) (hall _ (by omega)) (Nat.mod_lt _ (by decide))
      hk hv'
  rw [e2] at hF
  exact fixAllT_sound hF

theorem c_fixes {Q : Nat} (hQ : trK 24 Q ∈ QTs) :
    fixesAll (unpackR 24 Q) (xFixList (unpackR 24 XK)) = true := by
  unfold fixesAll xFixList
  rw [List.all_eq_true]
  intro v hv
  obtain ⟨hvX, hfx⟩ := List.mem_filter.1 hv
  have hx : act (unpackR 24 XK) v = v := beq_iff_eq.1 hfx
  rw [CFSG.KC.F2W.act_unpackR rfl, fix_imp hvX hx _ hQ, beq_self_eq_true]

theorem c_base : ((List.range 6).all fun i => (xFixList (unpackR 24 XK)).contains (base.getD i 0)) =
    true := by
  rw [List.all_eq_true]
  intro i hi
  have h := allN_true' kBF i (List.mem_range.1 hi)
  rw [fixImp_andB] at h
  unfold xFixList
  rw [List.contains_iff_mem, List.mem_filter, CFSG.KC.F2W.act_unpackR (T := XT) rfl,
    Nat.eq_of_beq_eq_true h.2, beq_self_eq_true]
  exact ⟨mem_of_memK h.1, rfl⟩

theorem kT' : eqK (getL 0 KF.T 0) (trK 24 (powWK XK 0)) = true ∧
    eqK (getL 0 KF.T 1) (trK 24 (powWK XK 1)) = true ∧
    eqK (getL 0 KF.T 2) (trK 24 (powWK XK 2)) = true ∧ KF.T.length = 3 := by
  have h := kT
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  have h' := allN_true' h.2
  exact ⟨h' 0 (by decide), h' 1 (by decide), h' 2 (by decide), h.1⟩

theorem cs1 : colsOf (powList (unpackR 24 XK) 3) = (KF.T.map (unpackR 24)).toArray := by
  obtain ⟨h0, h1, h2, hl⟩ := kT'
  obtain ⟨a, b, c, hK⟩ : ∃ a b c, KF.T = [a, b, c] := List.length_eq_three.1 hl
  rw [hK] at h0 h1 h2
  have hp : ∀ e, transposeRows 24 (pow (unpackR 24 XK) e) = unpackR 24 (trK 24 (powWK XK e)) :=
    fun e => by rw [pow_unpack', CFSG.KC.F2W.transposeRows_unpackR]
  rw [hK, colsOf, powList, List.map_toArray, List.map_map]
  refine congrArg List.toArray ?_
  have hr : List.range 3 = [0, 1, 2] := rfl
  rw [hr]
  simp only [List.map_cons, List.map_nil, Function.comp_apply, hp]
  rw [← beq_of_eqK h0, ← beq_of_eqK h1, ← beq_of_eqK h2]
  rfl

theorem kNF {i : Nat} (hi : i < 15) : memK XB (base.getD i 0) = true ∧
    (KF.CNs.getD i []).length = 9 ∧ (KF.CNs.getD i []).sum ≤ cnts.getD i 0 := by
  have h := kNs
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  have h' := allN_true' h.2 i hi
  simp only [Bool.and_eq_true, Nat.beq_eq] at h'
  exact ⟨h'.1.1, h'.1.2, Nat.le_of_ble_eq_true h'.2⟩

theorem chunks1 : ∀ n < 9 * 15, 9 * 6 ≤ n →
    lvlChunkP 3 XB KF.T CFs1 KF.NP CertificateChecks.KernelCo1B.CV.F KF.CNs n = true := by
  intro n hn h0
  change n < 135 at hn
  change 54 ≤ n at h0
  rcases Nat.lt_or_ge n 81 with h | h
  · interval_cases n
    exacts [ch17329pA54, ch17329pA55, ch17329pA56, ch17329pA57, ch17329pA58, ch17329pA59,
      ch17329pA60, ch17329pA61, ch17329pA62, ch17329pA63, ch17329pA64, ch17329pA65, ch17329pA66,
      ch17329pA67, ch17329pA68, ch17329pA69, ch17329pA70, ch17329pA71, ch17329pA72, ch17329pA73,
      ch17329pA74, ch17329pA75, ch17329pA76, ch17329pA77, ch17329pA78, ch17329pA79, ch17329pA80]
  rcases Nat.lt_or_ge n 108 with h' | h'
  · interval_cases n
    exacts [ch17329pA81, ch17329pA82, ch17329pA83, ch17329pA84, ch17329pA85, ch17329pA86,
      ch17329pA87, ch17329pA88, ch17329pA89, ch17329pA90, ch17329pA91, ch17329pA92, ch17329pA93,
      ch17329pA94, ch17329pA95, ch17329pA96, ch17329pA97, ch17329pA98, ch17329pA99,
      ch17329pA100, ch17329pA101, ch17329pA102, ch17329pA103, ch17329pA104, ch17329pA105,
      ch17329pA106, ch17329pA107]
  · interval_cases n
    exacts [ch17329pA108, ch17329pA109, ch17329pA110, ch17329pA111, ch17329pA112, ch17329pA113,
      ch17329pA114, ch17329pA115, ch17329pA116, ch17329pA117, ch17329pA118, ch17329pA119,
      ch17329pA120, ch17329pA121, ch17329pA122, ch17329pA123, ch17329pA124, ch17329pA125,
      ch17329pA126, ch17329pA127, ch17329pA128, ch17329pA129, ch17329pA130, ch17329pA131,
      ch17329pA132, ch17329pA133, ch17329pA134]

theorem c_bound1 : boundOKF (colsOf (powList (unpackR 24 XK) 3)) 3 base 6 conds cnts span comb =
    true := by
  rw [cs1]
  exact boundOKF_of_sel (m := 15) kT'.2.2.2 rfl rfl rfl (of_decide_eq_true kCFs)
    (fun i hi => by interval_cases i <;> rfl) (fun i hi => kNF hi) chunks1 kSpan

theorem kT2' : KF.T2.length = 243 ∧ ∀ i < 243, eqK (getL 0 KF.T2 i) (trK 24 (QT.P i)) = true := by
  have h := kT2
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact ⟨h.1, allN_true' h.2⟩

theorem cs2 : colsOf (gtBFS [unpackR 24 Q1K, unpackR 24 Q2K, unpackR 24 Q3K,
    unpackR 24 Q4K].toArray 300).pts.toList = (KF.T2.map (unpackR 24)).toArray := by
  obtain ⟨hl, hall⟩ := kT2'
  have hs : (bfsTree QT.N QT.P QT.PAR QT.LAB).pts.size = 243 := by
    simp only [bfsTree, Array.size_ofFn]
    exact kQ'.2
  rw [gt_eq, colsOf, List.map_toArray]
  refine congrArg List.toArray ?_
  apply List.ext_getElem (by rw [List.length_map, Array.length_toList, hs, List.length_map, hl])
  intro i h1 h2
  have hi : i < 243 := by
    rw [List.length_map, Array.length_toList, hs] at h1
    exact h1
  have e := beq_of_eqK (hall i hi)
  rw [CFSG.KC.Co1B.getL_eq, List.getElem?_eq_getElem (by rw [hl]; exact hi), Option.getD_some] at e
  rw [List.getElem_map, List.getElem_map, Array.getElem_toList]
  simp only [bfsTree, Array.getElem_ofFn]
  rw [← unpackR_eq_unpack, CFSG.KC.F2W.transposeRows_unpackR, e]

theorem kN2F {i : Nat} (hi : i < 6) : memK XB (base2.getD i 0) = true ∧
    (KF.CNs2.getD i []).length = 9 ∧ (KF.CNs2.getD i []).sum ≤ cnts2.getD i 0 := by
  have h := kNs2
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  have h' := allN_true' h.2 i hi
  simp only [Bool.and_eq_true, Nat.beq_eq] at h'
  exact ⟨h'.1.1, h'.1.2, Nat.le_of_ble_eq_true h'.2⟩

theorem chunks2 : ∀ n < 54,
    lvlChunkP 243 XB KF.T2 KF.CFs2 KF.NP2 CertificateChecks.KernelCo1B.CV.F KF.CNs2 n = true := by
  intro n hn
  rcases Nat.lt_or_ge n 27 with h | h
  · interval_cases n
    exacts [ch17329pB0, ch17329pB1, ch17329pB2, ch17329pB3, ch17329pB4, ch17329pB5, ch17329pB6,
      ch17329pB7, ch17329pB8, ch17329pB9, ch17329pB10, ch17329pB11, ch17329pB12, ch17329pB13,
      ch17329pB14, ch17329pB15, ch17329pB16, ch17329pB17, ch17329pB18, ch17329pB19, ch17329pB20,
      ch17329pB21, ch17329pB22, ch17329pB23, ch17329pB24, ch17329pB25, ch17329pB26]
  · interval_cases n
    exacts [ch17329pB27, ch17329pB28, ch17329pB29, ch17329pB30, ch17329pB31, ch17329pB32,
      ch17329pB33, ch17329pB34, ch17329pB35, ch17329pB36, ch17329pB37, ch17329pB38, ch17329pB39,
      ch17329pB40, ch17329pB41, ch17329pB42, ch17329pB43, ch17329pB44, ch17329pB45, ch17329pB46,
      ch17329pB47, ch17329pB48, ch17329pB49, ch17329pB50, ch17329pB51, ch17329pB52, ch17329pB53]

theorem c_bound2 : boundOK (colsOf (gtBFS [unpackR 24 Q1K, unpackR 24 Q2K, unpackR 24 Q3K,
    unpackR 24 Q4K].toArray 300).pts.toList) 243 base2 conds2 cnts2 span2 comb2 = true := by
  rw [cs2]
  exact boundOK_of_sel (m := 6) kT2'.1 rfl rfl rfl (of_decide_eq_true kCFs2)
    (fun i hi => kN2F hi) chunks2 kSpan2

theorem c_prod1 : decide (cnts.prod ≤ 486) = true := by decide
theorem c_prod2 : decide (cnts2.prod ≤ 3) = true := by decide

open Certificates in
open CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeC in
theorem c17329 : threeCCheck () = true := by
  unfold threeCCheck
  simp only [hflag, rootC_eq, q1_eq, q2_eq, q3_eq, q4_eq, q1I_eq, q2I_eq, c_wf1, c_wf2, c_ne,
    c_pow, c_comm, comm_unpack kSmall'.2.2.2.1, comm_unpack kSmall'.2.2.2.2.1,
    comm_unpack kSmall'.2.2.2.2.2.1, comm_unpack kSmall'.2.2.2.2.2.2, c_gt, c_size,
    c_fixes (Q := Q1K) (by simp [QTs]), c_fixes (Q := Q2K) (by simp [QTs]),
    c_fixes (Q := Q3K) (by simp [QTs]), c_fixes (Q := Q4K) (by simp [QTs]), c_base, c_bound1,
    c_prod1, c_bound2, c_prod2, Bool.and_self]

end CertificateChecks.KernelCo1B.Bound17329

end
