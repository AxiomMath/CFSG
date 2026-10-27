module

public import Certificates.Data.TabCo1ThreeB
public meta import Certificates.Data.TabCo1ThreeB
public import Certificates.Kernel.Co1B.Chk17330
public import Certificates.Kernel.Co1B.Small17330
public import Certificates.Kernel.Co1B.Chk17330P
public import Certificates.Kernel.Co1B.Lvl17330P1
public import Certificates.Kernel.Co1B.Lvl17330P2
public import Certificates.Kernel.Co1B.C17591
public import Certificates.Kernel.Co1ThreeK.GluePlane
public import Certificates.Kernel.Co1ThreeK.LettersEq
public import CFSG.Certificates.Kernel.Co1BBoundNSound
public import CFSG.Certificates.Kernel.Co1BBoundPSound
public import CFSG.Certificates.Kernel.SporSch.Co1BfsSound
import Mathlib.Tactic.IntervalCases
public import CFSG.Monster.B.TwoA.Par3.Main
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
public import CFSG.Monster.B.TwoA.Unitary.Semilinear
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.AbelianSylow
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1ThreeKit
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Core
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.OuterTrivial
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicHolds
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.Monster.AxisCount.HSIdentBaby
public import CFSG.Monster.AxisCount.HSIdentRec0
public import CFSG.Monster.AxisCount.HSIdentRec1
public import CFSG.Monster.AxisCount.HSIdentRec2
public import CFSG.Monster.AxisCount.HSIdentRec3
public import CFSG.Monster.AxisCount.HSIdentRec4
public import CFSG.Monster.AxisCount.HSIdentRec5
public import CFSG.Monster.AxisCount.HSIdentRec6
public import CFSG.Monster.AxisCount.HSIdentRec7
public import CFSG.Monster.AxisCount.HSIdentSmall
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.Sporadic.Bridge.M11CheckInputs
public import CFSG.Sporadic.FischerOddCore.Basic
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.Sporadic.Schreier.LyFixedSet
public import CFSG.Sporadic.Schreier.RuLocal
public import CFSG.Sporadic.SchreierLemmas.FrattiniProfile
public import CFSG.Sporadic.SmallOddCore.CentSpec
public import CFSG.Sporadic.ThSchreier.ThSchreierCase
public import CFSG.YGroups.DCE.B433Check
public import Certificates.Certificate10027
public import Certificates.Certificate10107
public import Certificates.Certificate10108
public import Certificates.Certificate10110
public import Certificates.Certificate10111
public import Certificates.Certificate16018
public import Certificates.Certificate2323
public import Certificates.Certificate6006
public import Certificates.Certificate8026Base
public import Certificates.Certificate9124

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Bound17330

open CFSG.KC.Co1BBoundP (selC storeSel lvlChunkP lvlChunkP_eq filter_length_le_selC)
open CFSG.KC.Co1BBoundN CFSG.KC.Co1BBound CFSG.KC.Co1BSpin CFSG.KC.Co1B CFSG.KC.Co1F2 CFSG.KC.M1F2
  CFSG.KLie.CT CFSG.KC.Enum CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeB
  CFSG.HardMathSupport.Dickson.I271.TabCo1 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1.TwoBNative
open CertificateChecks.KernelCo1B.Bound17591 (XB mem_eq typN_eq filter_length cntTab_blocks
  foldl_filter sum_getL andB_eq')
open CFSG.KS.SporSch.M24 (gtBFS_of_K bfsMemK_sound contains_bfsTree bfsTree gensArr
  unpackR_eq_unpack)

section Bound

variable {nb m : Nat} {TL : List Nat}

theorem conds_all_eqn (hl : TL.length = nb) (b : List Nat) (u x : Nat) : ∀ conds : List Cond,
    conds.all (fun c => typN (xsSet ()) (combN (TL.map (unpackR 24)).toArray c.1
        (fN (TL.map (unpackR 24)).toArray b c.2) x) ==
      typN (xsSet ()) (combN (TL.map (unpackR 24)).toArray c.1
        (fN (TL.map (unpackR 24)).toArray b c.2) u)) =
      condsKn nb XB TL (storeKn nb XB TL b u conds) x
  | [] => rfl
  | c :: conds => by
    have hs : storeKn nb XB TL b u (c :: conds) =
        (typK XB (combKn nb TL c.1 (fKn nb TL b c.2) u) :: fKn nb TL b c.2 :: c.1) ::
          storeKn nb XB TL b u conds := rfl
    rw [List.all_cons, conds_all_eqn hl b u x conds, hs]
    change _ = andB (condKn nb XB TL x
      (typK XB (combKn nb TL c.1 (fKn nb TL b c.2) u) :: fKn nb TL b c.2 :: c.1))
      (condsKn nb XB TL (storeKn nb XB TL b u conds) x)
    rw [andB_eq', typN_eq, typN_eq, combN_eqn hl, combN_eqn hl, fN_eqn hl,
      CertificateChecks.KernelCo1B.beq_nat]
    rfl

variable {base' cnts' : List Nat} {conds' : List (List Cond)} {CF : List (List (List Nat))}
  {CN : List (List Nat)}

theorem lvl_eqn (hl : TL.length = nb)
    (hCF : CF = (List.range m).map fun i =>
      storeKn nb XB TL (base'.take i) (base'.getD i 0) (conds'.getD i []))
    {i : Nat} (hi : i < m) :
    lvlOK (xsSet ()) (TL.map (unpackR 24)).toArray base' i (conds'.getD i []) (cnts'.getD i 0) =
      (memK XB (base'.getD i 0) &&
        decide (cntTabK (condsKn nb XB TL (CF.getD i [])) CertificateChecks.KernelCo1B.CV.F 0 117 ≤
          cnts'.getD i 0)) := by
  have hcf : CF.getD i [] = storeKn nb XB TL (base'.take i) (base'.getD i 0) (conds'.getD i []) := by
    rw [hCF, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
    rfl
  unfold lvlOK candList
  rw [mem_eq, foldl_filter (fun (c : Cond) x =>
    typN (xsSet ()) (combN (TL.map (unpackR 24)).toArray c.1
      (fN (TL.map (unpackR 24)).toArray (base'.take i) c.2) x) ==
    typN (xsSet ()) (combN (TL.map (unpackR 24)).toArray c.1
      (fN (TL.map (unpackR 24)).toArray (base'.take i) c.2) (base'.getD i 0)))]
  simp only [conds_all_eqn hl]
  rw [filter_length, hcf]

theorem lvl_okn (hl : TL.length = nb)
    (hCF : CF = (List.range m).map fun i =>
      storeKn nb XB TL (base'.take i) (base'.getD i 0) (conds'.getD i []))
    (hch : ∀ n < 9 * m, lvlChunkKn nb XB TL CF CertificateChecks.KernelCo1B.CV.F CN n = true)
    {i : Nat} (hi : i < m) (hm : memK XB (base'.getD i 0) = true)
    (hlen : (CN.getD i []).length = 9) (hs : (CN.getD i []).sum ≤ cnts'.getD i 0) :
    lvlOK (xsSet ()) (TL.map (unpackR 24)).toArray base' i (conds'.getD i []) (cnts'.getD i 0) =
      true := by
  rw [lvl_eqn hl hCF hi, hm, Bool.true_and, decide_eq_true_iff]
  have h117 : (117 : Nat) = 13 * 9 := rfl
  rw [h117, cntTab_blocks]
  have hb : ∀ c < 9, cntTabK (condsKn nb XB TL (CF.getD i [])) CertificateChecks.KernelCo1B.CV.F
      (13 * c) 13 = getL 0 (CN.getD i []) c := by
    intro c hc
    have := hch (9 * i + c) (by omega)
    unfold lvlChunkKn at this
    have e1 : Nat.div (9 * i + c) 9 = i := by
      change (9 * i + c) / 9 = i
      omega
    have e2 : Nat.mod (9 * i + c) 9 = c := by
      change (9 * i + c) % 9 = c
      omega
    rw [e1, e2] at this
    exact Nat.eq_of_beq_eq_true this
  rw [List.map_congr_left fun c hc => hb c (List.mem_range.1 hc), ← hlen, sum_getL]
  exact hs

theorem span_okn {span' : List (Nat × Nat)} {comb' : List Nat} (hl : TL.length = nb)
    (hb : base'.length = m)
    (h : (Nat.beq span'.length 24 && Nat.beq comb'.length 24 &&
      span'.all (fun s => Nat.blt s.1 m && Nat.blt s.2 nb) &&
      CFSG.KLie.CT.allN 24 (fun l => Nat.beq (vmF 24 (packL (span'.map (slotKn nb TL base'))) (comb'.getD l 0))
        (Nat.shiftLeft 1 l))) = true) :
    spanOK (TL.map (unpackR 24)).toArray nb base' span' comb' = true := by
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨hs, hc⟩, ha⟩, hv⟩ := h
  unfold spanOK
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, beq_iff_eq]
  refine ⟨⟨⟨hs, hc⟩, ?_⟩, ?_⟩
  · intro s hm
    have := List.all_eq_true.1 ha s hm
    simp only [Bool.and_eq_true] at this
    exact ⟨hb ▸ Eq.mp Nat.blt_eq this.1, Eq.mp Nat.blt_eq this.2⟩
  · intro l hl'
    have hm : span'.map (slotN (TL.map (unpackR 24)).toArray base') = span'.map (slotKn nb TL base') :=
      List.map_congr_left fun s _ => slot_eqn hl base' s
    rw [hm, toArray_packL (by rw [List.length_map, hs]) (fun v hv => by
      obtain ⟨s, -, rfl⟩ := List.mem_map.1 hv
      exact slotKn_lt nb TL base' s), CFSG.KC.F2W.vecMulN_unpackR]
    have := allN_true' hv l hl'
    rw [Nat.eq_of_beq_eq_true this]
    rfl

theorem lvlOK_of_selC {xs : Std.HashSet Nat} {cs : Array (Array Nat)} {b : List Nat} {i : Nat}
    {conds : List Cond} {sel : List Nat} {cnt : Nat}
    (h : lvlOK xs cs b i (selC conds sel) cnt = true) : lvlOK xs cs b i conds cnt = true := by
  unfold lvlOK candList at h ⊢
  rw [foldl_filter (fun (c : Cond) x => typN xs (combN cs c.1 (fN cs (b.take i) c.2) x) ==
    typN xs (combN cs c.1 (fN cs (b.take i) c.2) (b.getD i 0)))] at h ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  exact ⟨h.1, Nat.le_trans (filter_length_le_selC _ conds sel _) h.2⟩

theorem boundOK_of_sel {span' : List (Nat × Nat)} {comb' : List Nat} {Sel : List (List Nat)}
    {NP : List Nat} (hl : TL.length = nb)
    (hb : base'.length = m) (hc : conds'.length = m) (hn : cnts'.length = m)
    (hCF : CF = (List.range m).map fun i =>
      storeSel nb XB TL (base'.take i) (base'.getD i 0) (conds'.getD i []) (Sel.getD i []))
    (hN : ∀ i < m, memK XB (base'.getD i 0) = true ∧ (CN.getD i []).length = 9 ∧
      (CN.getD i []).sum ≤ cnts'.getD i 0)
    (hch : ∀ n < 9 * m, lvlChunkP nb XB TL CF NP CertificateChecks.KernelCo1B.CV.F CN n = true)
    (hs : (Nat.beq span'.length 24 && Nat.beq comb'.length 24 &&
      span'.all (fun s => Nat.blt s.1 m && Nat.blt s.2 nb) &&
      CFSG.KLie.CT.allN 24 (fun l => Nat.beq (vmF 24 (packL (span'.map (slotKn nb TL base'))) (comb'.getD l 0))
        (Nat.shiftLeft 1 l))) = true) :
    boundOK (TL.map (unpackR 24)).toArray nb base' conds' cnts' span' comb' = true := by
  unfold boundOK
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨⟨by simp [hl], by rw [hc, hb]⟩, by rw [hn, hb]⟩, fun i hi => ?_⟩, span_okn hl hb hs⟩
  obtain ⟨h1, h2, h3⟩ := hN i (by omega)
  have hgs : ∀ j < m, ((List.range m).map fun j => selC (conds'.getD j []) (Sel.getD j [])).getD j [] =
      selC (conds'.getD j []) (Sel.getD j []) := fun j hj => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
    rfl
  have hCF' : CF = (List.range m).map fun j => storeKn nb XB TL (base'.take j) (base'.getD j 0)
      (((List.range m).map fun j => selC (conds'.getD j []) (Sel.getD j [])).getD j []) := by
    rw [hCF]
    exact List.map_congr_left fun j hj => by rw [hgs j (List.mem_range.1 hj)]; rfl
  have h := lvl_okn hl hCF' (fun n hn => (lvlChunkP_eq _ _ _ _ NP _ _ n).symm.trans (hch n hn))
    (by omega) h1 h2 h3
  rw [hgs i (by omega)] at h
  exact lvlOK_of_selC h

end Bound

theorem hflag : (kDag ext).2.2 = true := by
  rw [CertificateChecks.KernelCo1ThreeK.kDagB_eq]

theorem nd_eq {i : Nat} (h1 : 0 < i) (h2 : i ≤ 91) :
    nd (kDag ext) i = unpackR 24 (CertificateChecks.KernelCo1ThreeK.KZ.M (i - 1)) := by
  rw [nd, CertificateChecks.KernelCo1ThreeK.kDagB_eq,
    List.getD_eq_getElem _ _ (by simp only [List.length_map, List.length_range]; omega),
    List.getElem_map, List.getElem_range, unpackR_eq_unpack]

theorem ndI_eq {i : Nat} (h1 : 0 < i) (h2 : i ≤ 91) :
    ndI (kDag ext) i = unpackR 24 (CertificateChecks.KernelCo1ThreeK.KZ.MI (i - 1)) := by
  rw [ndI, CertificateChecks.KernelCo1ThreeK.kDagB_eq,
    List.getD_eq_getElem _ _ (by simp only [List.length_map, List.length_range]; omega),
    List.getElem_map, List.getElem_range, unpackR_eq_unpack]

theorem a_eq : nd (kDag ext) 88 = unpackR 24 AK := nd_eq (by decide) (by decide)
theorem b_eq : nd (kDag ext) 89 = unpackR 24 BK := nd_eq (by decide) (by decide)
theorem x_eq : nd (kDag ext) 90 = unpackR 24 XK := nd_eq (by decide) (by decide)
theorem z_eq : nd (kDag ext) 91 = unpackR 24 ZK := nd_eq (by decide) (by decide)

theorem evalW_eq (w : List Int) : evalW (kDag ext) [88, 89, 90, 91] w = unpackR 24 (wK w) := by
  have h1 : [88, 89, 90, 91].map (nd (kDag ext)) = RS4.map (unpackR 24) := by
    simp only [List.map_cons, List.map_nil, a_eq, b_eq, x_eq, z_eq]
    rfl
  have h2 : [88, 89, 90, 91].map (ndI (kDag ext)) = IS4.map (unpackR 24) := by
    simp only [List.map_cons, List.map_nil, ndI_eq (i := 88) (by decide) (by decide),
      ndI_eq (i := 89) (by decide) (by decide), ndI_eq (i := 90) (by decide) (by decide),
      ndI_eq (i := 91) (by decide) (by decide)]
    rfl
  rw [evalW, h1, h2, word_sound]
  rfl

theorem evalW2_eq (w : List Int) :
    evalW (kDag ext) [88, 89] w = unpackR 24 (wordK (RS4.take 2) (IS4.take 2) w) := by
  have h1 : [88, 89].map (nd (kDag ext)) = (RS4.take 2).map (unpackR 24) := by
    simp only [List.map_cons, List.map_nil, a_eq, b_eq]
    rfl
  have h2 : [88, 89].map (ndI (kDag ext)) = (IS4.take 2).map (unpackR 24) := by
    simp only [List.map_cons, List.map_nil, ndI_eq (i := 88) (by decide) (by decide),
      ndI_eq (i := 89) (by decide) (by decide)]
    rfl
  rw [evalW, h1, h2, word_sound]

theorem mul_unpackW' (A B : Nat) : mul (unpackR 24 A) (unpackR 24 B) = unpackR 24 (mulWK A B) :=
  CFSG.KC.F2W.mul_unpackW A B

theorem wf_unpackR (X : Nat) : wf (unpackR 24 X) = true := by
  rw [unpackR_eq_unpack]
  unfold wf
  rw [Bool.and_eq_true]
  refine ⟨by simp [CFSG.KS.Raw.unpack], ?_⟩
  rw [Array.all_iff_forall]
  intro i hi _
  simp only [CFSG.KS.Raw.unpack, Array.getElem_ofFn, CFSG.KC.Enum.pg, decide_eq_true_eq]
  unfold CFSG.KS.mask
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem not_of_notB {b : Bool} (h : notB b = true) : (!b) = true := by
  cases b
  · rfl
  · exact absurd h Bool.false_ne_true

theorem kOrd' : eqK (powWK XK 3) oneK = true ∧ eqK (powWK ZK 3) oneK = true ∧
    notB (eqK XK oneK) = true ∧ eqK XK (CertificateChecks.KernelCo1ThreeK.R.M 1) = true := by
  have h := kOrd
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem kCom' : eqK (mulWK XK AK) (mulWK AK XK) = true ∧ eqK (mulWK XK BK) (mulWK BK XK) = true ∧
    eqK (mulWK ZK AK) (mulWK AK ZK) = true ∧ eqK (mulWK ZK BK) (mulWK BK ZK) = true ∧
    eqK (mulWK XK ZK) (mulWK ZK XK) = true ∧ notB (eqK (mulWK AK BK) (mulWK BK AK)) = true := by
  have h := kCom
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem c_wf1 : wf (nd (kDag ext) 90) = true := by
  rw [x_eq]
  exact wf_unpackR _

theorem c_wf2 : wf (one ()) = true := by
  rw [CFSG.KC.Co1B.one_eq]
  exact wf_unpackR _

theorem c_root : (nd (kDag ext) 90 == rootRows3B ()) = true := by
  unfold rootRows3B
  rw [x_eq, CertificateChecks.KernelCo1ThreeK.rootRows_eq (by decide), ← unpackR_eq_unpack,
    beq_unpack]
  exact kOrd'.2.2.2

theorem c_ne : (nd (kDag ext) 90 != one ()) = true := by
  rw [x_eq, CFSG.KC.Co1B.one_eq, bne, beq_unpack]
  exact not_of_notB kOrd'.2.2.1

theorem c_powx : (pow (nd (kDag ext) 90) 3 == one ()) = true := by
  rw [x_eq, pow_unpack', CFSG.KC.Co1B.one_eq, beq_unpack]
  exact kOrd'.1

theorem c_powz : (pow (nd (kDag ext) 91) 3 == one ()) = true := by
  rw [z_eq, pow_unpack', CFSG.KC.Co1B.one_eq, beq_unpack]
  exact kOrd'.2.1

theorem c_xa : (mul (nd (kDag ext) 90) (nd (kDag ext) 88) ==
    mul (nd (kDag ext) 88) (nd (kDag ext) 90)) = true := by
  rw [x_eq, a_eq, mul_unpackW', mul_unpackW', beq_unpack]
  exact kCom'.1

theorem c_xb : (mul (nd (kDag ext) 90) (nd (kDag ext) 89) ==
    mul (nd (kDag ext) 89) (nd (kDag ext) 90)) = true := by
  rw [x_eq, b_eq, mul_unpackW', mul_unpackW', beq_unpack]
  exact kCom'.2.1

theorem c_za : (mul (nd (kDag ext) 91) (nd (kDag ext) 88) ==
    mul (nd (kDag ext) 88) (nd (kDag ext) 91)) = true := by
  rw [z_eq, a_eq, mul_unpackW', mul_unpackW', beq_unpack]
  exact kCom'.2.2.1

theorem c_zb : (mul (nd (kDag ext) 91) (nd (kDag ext) 89) ==
    mul (nd (kDag ext) 89) (nd (kDag ext) 91)) = true := by
  rw [z_eq, b_eq, mul_unpackW', mul_unpackW', beq_unpack]
  exact kCom'.2.2.2.1

theorem c_xz : (mul (nd (kDag ext) 90) (nd (kDag ext) 91) ==
    mul (nd (kDag ext) 91) (nd (kDag ext) 90)) = true := by
  rw [x_eq, z_eq, mul_unpackW', mul_unpackW', beq_unpack]
  exact kCom'.2.2.2.2.1

theorem c_wfab : wf (mul (nd (kDag ext) 88) (nd (kDag ext) 89)) = true := by
  rw [a_eq, b_eq, mul_unpackW']
  exact wf_unpackR _

theorem c_wfba : wf (mul (nd (kDag ext) 89) (nd (kDag ext) 88)) = true := by
  rw [a_eq, b_eq, mul_unpackW']
  exact wf_unpackR _

theorem c_ab : (mul (nd (kDag ext) 88) (nd (kDag ext) 89) !=
    mul (nd (kDag ext) 89) (nd (kDag ext) 88)) = true := by
  rw [a_eq, b_eq, mul_unpackW', mul_unpackW', bne, beq_unpack]
  exact not_of_notB kCom'.2.2.2.2.2

theorem kZT' : CFSG.KS.SporSch.M24.gtPinK ZM 2 20 ZT.N ZT.P ZT.PAR ZT.LAB ZT.W ZT.S = true ∧
    ZT.N = 9 := by
  have h := kZT
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact h

theorem ZG_eq : [nd (kDag ext) 90, nd (kDag ext) 91].toArray = gensArr 2 ZM := by
  rw [x_eq, z_eq]
  apply Array.ext (by simp [gensArr])
  intro i h1 h2
  have hi : i < 2 := by simpa using h1
  interval_cases i <;> simp [gensArr, ZM, XK, ZK, unpackR_eq_unpack]

theorem gt_eq : gtBFS [nd (kDag ext) 90, nd (kDag ext) 91].toArray 20 =
    bfsTree ZT.N ZT.P ZT.PAR ZT.LAB := by
  rw [ZG_eq]
  exact (gtBFS_of_K kZT'.1).1

theorem c_gt : gtOK [nd (kDag ext) 90, nd (kDag ext) 91].toArray
    (gtBFS [nd (kDag ext) 90, nd (kDag ext) 91].toArray 20) = true := by
  rw [gt_eq, ZG_eq]
  exact (gtBFS_of_K kZT'.1).2

theorem c_size : decide ((gtBFS [nd (kDag ext) 90, nd (kDag ext) 91].toArray 20).pts.size = 9) =
    true := by
  rw [gt_eq, decide_eq_true_iff]
  simp [bfsTree, kZT'.2]

theorem c_rels : (relsW.all fun w => (gtBFS [nd (kDag ext) 90, nd (kDag ext) 91].toArray 20).pts.contains
    (evalW (kDag ext) [88, 89] w)) = true := by
  rw [gt_eq, List.all_eq_true]
  intro w hw
  rw [evalW2_eq]
  obtain ⟨hw', hK⟩ := bfsMemK_sound (List.all_eq_true.1 kRel w hw)
  exact contains_bfsTree hw' (by rw [hK, unpackR_eq_unpack])

theorem kI {w : List Int} (hw : w ∈ [wu1, wv1, wu2, wv2]) :
    andB (andB (canK (wK w)) (canK (wK (invW w)))) (Nat.beq (mulK (wK w) (wK (invW w))) oneK) =
      true := by
  rw [andB_eq', andB_eq']
  exact List.all_eq_true.1 kInv w hw

theorem inv_eval {w : List Int} (hw : w ∈ [wu1, wv1, wu2, wv2]) :
    inv (evalW (kDag ext) [88, 89, 90, 91] w) = unpackR 24 (wK (invW w)) := by
  rw [evalW_eq]
  exact inv_sound' (kI hw)

theorem c_inv {w : List Int} (hw : w ∈ [wu1, wv1, wu2, wv2]) :
    (mul (evalW (kDag ext) [88, 89, 90, 91] w) (inv (evalW (kDag ext) [88, 89, 90, 91] w)) ==
      one ()) = true := by
  rw [inv_eval hw, evalW_eq, mul_unpack, Nat.eq_of_beq_eq_true (andB_true (kI hw)).2, ← CFSG.KC.Co1B.one_eq]
  exact beq_self_eq_true _

theorem kCm' : eqK (mulK (mulK (wK (invW wu1)) (wK (invW wv1))) (mulK (wK wu1) (wK wv1)))
      (powWK XK 2) = true ∧
    eqK (mulK (mulK (wK (invW wu2)) (wK (invW wv2))) (mulK (wK wu2) (wK wv2))) ZK = true := by
  have h := kCm
  simp only [Bool.and_eq_true] at h
  exact h

theorem c_cm1 : (mul (mul (inv (evalW (kDag ext) [88, 89, 90, 91] wu1))
    (inv (evalW (kDag ext) [88, 89, 90, 91] wv1)))
    (mul (evalW (kDag ext) [88, 89, 90, 91] wu1) (evalW (kDag ext) [88, 89, 90, 91] wv1)) ==
      pow (nd (kDag ext) 90) 2) = true := by
  rw [inv_eval (by simp), inv_eval (by simp), evalW_eq, evalW_eq, x_eq, mul_unpack, mul_unpack,
    mul_unpack, pow_unpack', beq_unpack]
  exact kCm'.1

theorem c_cm2 : (mul (mul (inv (evalW (kDag ext) [88, 89, 90, 91] wu2))
    (inv (evalW (kDag ext) [88, 89, 90, 91] wv2)))
    (mul (evalW (kDag ext) [88, 89, 90, 91] wu2) (evalW (kDag ext) [88, 89, 90, 91] wv2)) ==
      nd (kDag ext) 91) = true := by
  rw [inv_eval (by simp), inv_eval (by simp), evalW_eq, evalW_eq, z_eq, mul_unpack, mul_unpack,
    mul_unpack, beq_unpack]
  exact kCm'.2

theorem kT' : eqK (getL 0 K.T 0) (trK 24 (powWK XK 0)) = true ∧
    eqK (getL 0 K.T 1) (trK 24 (powWK XK 1)) = true ∧
    eqK (getL 0 K.T 2) (trK 24 (powWK XK 2)) = true ∧ K.T.length = 3 := by
  have h := kT
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem cs1 : colsOf (powList (nd (kDag ext) 90) 3) = (K.T.map (unpackR 24)).toArray := by
  obtain ⟨h0, h1, h2, hl⟩ := kT'
  obtain ⟨a, b, c, hK⟩ : ∃ a b c, K.T = [a, b, c] := List.length_eq_three.1 hl
  rw [hK] at h0 h1 h2
  have hp : ∀ e, transposeRows 24 (pow (unpackR 24 XK) e) = unpackR 24 (trK 24 (powWK XK e)) :=
    fun e => by rw [pow_unpack', CFSG.KC.F2W.transposeRows_unpackR]
  rw [x_eq, hK, colsOf, powList, List.map_toArray, List.map_map]
  refine congrArg List.toArray ?_
  have hr : List.range 3 = [0, 1, 2] := rfl
  rw [hr]
  simp only [List.map_cons, List.map_nil, Function.comp_apply, hp]
  rw [← beq_of_eqK h0, ← beq_of_eqK h1, ← beq_of_eqK h2]
  rfl

theorem kNF {i : Nat} (hi : i < 14) : memK XB (base.getD i 0) = true ∧
    (KP.CNs.getD i []).length = 9 ∧ (KP.CNs.getD i []).sum ≤ cnts.getD i 0 := by
  have h := kNs
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  have h' := allN_true' h.2 i hi
  simp only [Bool.and_eq_true, Nat.beq_eq] at h'
  exact ⟨h'.1.1, h'.1.2, Nat.le_of_ble_eq_true h'.2⟩

theorem chunks1 : ∀ n < 126,
    lvlChunkP 3 XB K.T KP.CFs KP.NP CertificateChecks.KernelCo1B.CV.F KP.CNs n = true := by
  intro n hn
  rcases Nat.lt_or_ge n 27 with h | h
  · interval_cases n
    exacts [ch17330pA0, ch17330pA1, ch17330pA2, ch17330pA3, ch17330pA4, ch17330pA5, ch17330pA6,
      ch17330pA7, ch17330pA8, ch17330pA9, ch17330pA10, ch17330pA11, ch17330pA12, ch17330pA13,
      ch17330pA14, ch17330pA15, ch17330pA16, ch17330pA17, ch17330pA18, ch17330pA19, ch17330pA20,
      ch17330pA21, ch17330pA22, ch17330pA23, ch17330pA24, ch17330pA25, ch17330pA26]
  rcases Nat.lt_or_ge n 54 with h' | h'
  · interval_cases n
    exacts [ch17330pA27, ch17330pA28, ch17330pA29, ch17330pA30, ch17330pA31, ch17330pA32,
      ch17330pA33, ch17330pA34, ch17330pA35, ch17330pA36, ch17330pA37, ch17330pA38, ch17330pA39,
      ch17330pA40, ch17330pA41, ch17330pA42, ch17330pA43, ch17330pA44, ch17330pA45, ch17330pA46,
      ch17330pA47, ch17330pA48, ch17330pA49, ch17330pA50, ch17330pA51, ch17330pA52, ch17330pA53]
  rcases Nat.lt_or_ge n 81 with h'' | h''
  · interval_cases n
    exacts [ch17330pA54, ch17330pA55, ch17330pA56, ch17330pA57, ch17330pA58, ch17330pA59,
      ch17330pA60, ch17330pA61, ch17330pA62, ch17330pA63, ch17330pA64, ch17330pA65, ch17330pA66,
      ch17330pA67, ch17330pA68, ch17330pA69, ch17330pA70, ch17330pA71, ch17330pA72, ch17330pA73,
      ch17330pA74, ch17330pA75, ch17330pA76, ch17330pA77, ch17330pA78, ch17330pA79, ch17330pA80]
  rcases Nat.lt_or_ge n 108 with h3 | h3
  · interval_cases n
    exacts [ch17330pA81, ch17330pA82, ch17330pA83, ch17330pA84, ch17330pA85, ch17330pA86,
      ch17330pA87, ch17330pA88, ch17330pA89, ch17330pA90, ch17330pA91, ch17330pA92, ch17330pA93,
      ch17330pA94, ch17330pA95, ch17330pA96, ch17330pA97, ch17330pA98, ch17330pA99, ch17330pA100,
      ch17330pA101, ch17330pA102, ch17330pA103, ch17330pA104, ch17330pA105, ch17330pA106,
      ch17330pA107]
  · interval_cases n
    exacts [ch17330pA108, ch17330pA109, ch17330pA110, ch17330pA111, ch17330pA112, ch17330pA113,
      ch17330pA114, ch17330pA115, ch17330pA116, ch17330pA117, ch17330pA118, ch17330pA119,
      ch17330pA120, ch17330pA121, ch17330pA122, ch17330pA123, ch17330pA124, ch17330pA125]

theorem c_bound1 : boundOK (colsOf (powList (nd (kDag ext) 90) 3)) 3 base conds cnts span comb =
    true := by
  rw [cs1]
  exact boundOK_of_sel (m := 14) kT'.2.2.2 rfl rfl rfl (of_decide_eq_true kCFs)
    (fun i hi => kNF hi) chunks1 kSpan

theorem kT2' : K.T2.length = 12 ∧ ∀ i < 12, eqK (getL 0 K.T2 i) (trK 24 (getL 0 PT i)) = true := by
  have h := kT2
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact ⟨h.1, allN_true' h.2⟩

theorem cs2 : colsOf (ptRows3B (nd (kDag ext) 88) (nd (kDag ext) 89) (nd (kDag ext) 90)
    (nd (kDag ext) 91)) = (K.T2.map (unpackR 24)).toArray := by
  have hpt : ptRows3B (unpackR 24 AK) (unpackR 24 BK) (unpackR 24 XK) (unpackR 24 ZK) =
      PT.map (unpackR 24) := by
    simp only [ptRows3B, PT, List.map_cons, List.map_nil, mul_unpackW']
  have hPT : PT.length = 12 := rfl
  obtain ⟨hl, hall⟩ := kT2'
  rw [a_eq, b_eq, x_eq, z_eq, hpt, colsOf, List.map_toArray, List.map_map]
  refine congrArg List.toArray ?_
  apply List.ext_getElem (by simp [hl, hPT])
  intro i h1 h2
  have hi : i < 12 := by simpa [hPT] using h1
  have e := beq_of_eqK (hall i hi)
  rw [CFSG.KC.Co1B.getL_eq, CFSG.KC.Co1B.getL_eq, List.getElem?_eq_getElem (by rw [hl]; exact hi),
    List.getElem?_eq_getElem (by rw [hPT]; exact hi), Option.getD_some, Option.getD_some] at e
  rw [List.getElem_map, List.getElem_map, Function.comp_apply, CFSG.KC.F2W.transposeRows_unpackR, e]

theorem kN2F {i : Nat} (hi : i < 3) : memK XB (base2.getD i 0) = true ∧
    (KP.CNs2.getD i []).length = 9 ∧ (KP.CNs2.getD i []).sum ≤ cnts2.getD i 0 := by
  have h := kNs2
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  have h' := allN_true' h.2 i hi
  simp only [Bool.and_eq_true, Nat.beq_eq] at h'
  exact ⟨h'.1.1, h'.1.2, Nat.le_of_ble_eq_true h'.2⟩

theorem chunks2 : ∀ n < 27,
    lvlChunkP 12 XB K.T2 KP.CFs2 KP.NP2 CertificateChecks.KernelCo1B.CV.F KP.CNs2 n = true := by
  intro n hn
  interval_cases n
  exacts [ch17330pB0, ch17330pB1, ch17330pB2, ch17330pB3, ch17330pB4, ch17330pB5, ch17330pB6,
    ch17330pB7, ch17330pB8, ch17330pB9, ch17330pB10, ch17330pB11, ch17330pB12, ch17330pB13,
    ch17330pB14, ch17330pB15, ch17330pB16, ch17330pB17, ch17330pB18, ch17330pB19, ch17330pB20,
    ch17330pB21, ch17330pB22, ch17330pB23, ch17330pB24, ch17330pB25, ch17330pB26]

theorem c_bound2 : boundOK (colsOf (ptRows3B (nd (kDag ext) 88) (nd (kDag ext) 89)
    (nd (kDag ext) 90) (nd (kDag ext) 91))) 12 base2 conds2 cnts2 span2 comb2 = true := by
  rw [cs2]
  exact boundOK_of_sel (m := 3) kT2'.1 rfl rfl rfl (of_decide_eq_true kCFs2)
    (fun i hi => kN2F hi) chunks2 kSpan2

theorem c_prod1 : decide (cnts.prod ≤ 58786560) = true := by decide
theorem c_prod2 : decide (cnts2.prod ≤ 9) = true := by decide

open Certificates in
open CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeB in
theorem c17330 : threeBCheck () = true := by
  unfold threeBCheck
  simp only [hflag, c_wf1, c_wf2, c_root, c_ne, c_powx, c_powz, c_xa, c_xb, c_za, c_zb, c_xz,
    c_wfab, c_wfba, c_ab, c_gt, c_size, c_rels, c_inv (w := wu1) (by simp),
    c_inv (w := wv1) (by simp), c_inv (w := wu2) (by simp), c_inv (w := wv2) (by simp), c_cm1,
    c_cm2, c_bound1, c_bound2, c_prod1, c_prod2, Bool.and_self]

end CertificateChecks.KernelCo1B.Bound17330

end
