module

public import CFSG.Sporadic.Co2I301.Inputs
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo2Cent
public import CFSG.Sporadic.Co2Schreier.Centralizers
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicHolds
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
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
public import CFSG.RankThree.PartTwo.KFacts.K426Kit
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
public import Certificates.Certificate13636Base
public import Certificates.Certificate16018
public import Certificates.Certificate2323
public import Certificates.Certificate6006
public import Certificates.Certificate8026Base
public import Certificates.Certificate9124

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.Sporadic.Co2I301.SpecAux

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Monster.B.Mathieu CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.Sporadic.Co2Cert
  CFSG.Sporadic.Co2Schreier CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2T
  CFSG.HardMathSupport.Dickson.I271 CFSG.HardMathSupport.Dickson.I271.Co2Cent
  CFSG.Sporadic.Co2I301

private theorem invCand_eq_foldl (n : ℕ) (t : Array ℕ) :
    invCand n t = (List.range n).foldl (fun r i => r.set! t[i]! i) (Array.replicate n 0) := by
  unfold invCand
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size]
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, bind_pure, List.range_eq_range']
  rfl

private theorem rep_invCand {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : Rep n t g) :
    Rep n (invCand n t) g⁻¹ := by
  have key : ∀ k ≤ n, ((List.range k).foldl (fun r i => r.set! t[i]! i)
      (Array.replicate n 0)).size = n ∧ ∀ i < k, ((List.range k).foldl (fun r i => r.set! t[i]! i)
      (Array.replicate n 0))[t[i]!]! = i := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      obtain ⟨hs, hi⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      set r := (List.range k).foldl (fun r i => r.set! t[i]! i) (Array.replicate n 0)
      have htk : t[k]! < n := ht.lt (by omega)
      refine ⟨by rw [Array.size_set!, hs], fun i hik => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hik with hlt | rfl
      · have hne : t[i]! ≠ t[k]! := by
          intro e
          rw [ht.apply (by omega : i < n), ht.apply (by omega : k < n)] at e
          have := g.injective (Fin.ext e)
          simp at this
          omega
        rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hne)]
        exact hi i hlt
      · rw [Array.getElem!_set!_self _ _ _ (by rw [hs]; exact htk)]
  intro x
  obtain ⟨hs, hi⟩ := key n le_rfl
  rw [invCand_eq_foldl]
  have e : t[(g⁻¹ x : Fin n).val]! = x.val := by
    rw [ht.apply (g⁻¹ x).2]
    simp
  rw [← e, hi _ (g⁻¹ x).2]

private theorem comm2300_iff {t u : Array ℕ} {G H : Equiv.Perm (Fin 2300)} (ht : Rep 2300 t G)
    (hu : Rep 2300 u H) : comm2300 t u = true ↔ Commute G H :=
  eqA_iff (rep_compA ht hu) (rep_compA hu ht)

private theorem rep_conj2300 {g gi t : Array ℕ} {G T : Equiv.Perm (Fin 2300)} (hg : Rep 2300 g G)
    (hgi : Rep 2300 gi G⁻¹) (ht : Rep 2300 t T) : Rep 2300 (conj2300 g gi t) (G * T * G⁻¹) := by
  rw [mul_assoc]
  exact rep_compA hg (rep_compA ht hgi)

private structure SmallFacts : Prop where
  validH : validA 2300 (i301H ()) = true
  inPH : inP (levels ()) (i301H ()) = true
  validD : validA 2300 (i301D ()) = true
  validS : validA 2300 (i301S ()) = true
  validB2 : validA 2300 (i301B2 ()) = true
  validB3 : validA 2300 (i301B3 ()) = true
  validXB : validA 2300 (dElts ())[1]! = true
  conjD : eqA 2300 (i301D ()) (conj2300 (i301H ()) (invCand 2300 (i301H ())) (dElts ())[1]!) = true
  chainK0 : caseChainOK2P 2300 (k0Arrs ()) k0Base k0Words (i301K1 ()) (i301K2 ()) = true
  orbK0 : (rawOrbitSizes 2300 (k0Arrs ()) k0Base).prod = 360
  zD : comm2300 zArr (i301D ()) = true
  zS : comm2300 zArr (i301S ()) = true
  zB2 : comm2300 zArr (i301B2 ()) = true
  zB3 : comm2300 zArr (i301B3 ()) = true
  zK1 : comm2300 zArr (i301K1 ()) = true
  zK2 : comm2300 zArr (i301K2 ()) = true
  dS : comm2300 (i301D ()) (i301S ()) = true
  dB2 : comm2300 (i301D ()) (i301B2 ()) = true
  dB3 : comm2300 (i301D ()) (i301B3 ()) = true
  dK1 : comm2300 (i301D ()) (i301K1 ()) = true
  dK2 : comm2300 (i301D ()) (i301K2 ()) = true
  b2B3 : comm2300 (i301B2 ()) (i301B3 ()) = true
  powD : eqA 2300 (powArr 2300 (i301D ()) 3) (idA 2300) = true
  powB2 : eqA 2300 (powArr 2300 (i301B2 ()) 3) (idA 2300) = true
  powB3 : eqA 2300 (powArr 2300 (i301B3 ()) 3) (idA 2300) = true
  sqS : eqA 2300 (compA 2300 (i301S ()) (i301S ())) (idA 2300) = true
  indep : allLt 27 (fun t => t == 0 || !(eqA 2300 (compA 2300 (powArr 2300 (i301D ()) (t % 3))
      (compA 2300 (powArr 2300 (i301B2 ()) (t / 3 % 3)) (powArr 2300 (i301B3 ()) (t / 9))))
      (idA 2300))) = true
  siftK1 : siftA 2300 (rawLevels 2300 (co2LArrs ()) co2LBase) co2LBase 0
    (conj2300 (invCand 2300 (i301H ())) (i301H ()) (i301K1 ())) = true
  siftK2 : siftA 2300 (rawLevels 2300 (co2LArrs ()) co2LBase) co2LBase 0
    (conj2300 (invCand 2300 (i301H ())) (i301H ()) (i301K2 ())) = true
  siftS : siftA 2300 (rawLevels 2300 (co2LArrs ()) co2LBase) co2LBase 0
    (conj2300 (invCand 2300 (i301H ())) (i301H ()) (i301S ())) = true
  inB2 : inK0 (rawLevels 2300 (k0Arrs ()) k0Base) (i301B2 ()) = true
  inB3 : inK0 (rawLevels 2300 (k0Arrs ()) k0Base) (i301B3 ()) = true
  inSK1 : inK0 (rawLevels 2300 (k0Arrs ()) k0Base) (conj2300 (i301S ()) (i301S ()) (i301K1 ())) =
    true
  inSK2 : inK0 (rawLevels 2300 (k0Arrs ()) k0Base) (conj2300 (i301S ()) (i301S ()) (i301K2 ())) =
    true
  pow512 : allLt 6 (fun t => t % 3 == 0 || !(eqA 2300
    (powArr 2300 (dzElts (i301D ()) zArr)[t]! 512) (idA 2300))) = true
  o6K : allLt 6 (fun j => (i301K1 ())[o6.getD j 0]! == o6.getD (sigma1.getD j 0) 0 &&
    (i301K2 ())[o6.getD j 0]! == o6.getD (sigma2.getD j 0) 0) = true

section Facts

variable [Fact (smallCheck () = true)]

private theorem smallFacts : SmallFacts := by
  have h : smallCheck () = true := Fact.out
  simp only [smallCheck, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, -⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36⟩

local notation "PH" => permOfArr 2300 (i301H ())
local notation "PD" => permOfArr 2300 (i301D ())
local notation "PS" => permOfArr 2300 (i301S ())
local notation "PB₂" => permOfArr 2300 (i301B2 ())
local notation "PB₃" => permOfArr 2300 (i301B3 ())
local notation "PK₁" => permOfArr 2300 (i301K1 ())
local notation "PK₂" => permOfArr 2300 (i301K2 ())
local notation "PK₀" => Subgroup.closure {permOfArr 2300 (i301K1 ()), permOfArr 2300 (i301K2 ())}

private theorem rep_H : Rep 2300 (i301H ()) PH := rep_of_validA smallFacts.validH

private theorem rep_Hi : Rep 2300 (invCand 2300 (i301H ())) PH⁻¹ :=
  rep_inv_of_validA smallFacts.validH

private theorem rep_D : Rep 2300 (i301D ()) PD := rep_of_validA smallFacts.validD

private theorem rep_S : Rep 2300 (i301S ()) PS := rep_of_validA smallFacts.validS

private theorem rep_B2 : Rep 2300 (i301B2 ()) PB₂ := rep_of_validA smallFacts.validB2

private theorem rep_B3 : Rep 2300 (i301B3 ()) PB₃ := rep_of_validA smallFacts.validB3

private theorem k0Arrs_size : (k0Arrs ()).size = 5 := by simp [k0Arrs]

private theorem k0Base_lt : ∀ v ∈ k0Base.toList, v < 2300 := by decide

private theorem k0Base_eq : ((finBase2300 k0Base).map Fin.val).toArray = k0Base :=
  finBase2300_map_eq k0Base k0Base_lt

private theorem k0Base_nodup : (finBase2300 k0Base).Nodup := by unfold finBase2300; decide

private theorem chainK0 : caseChainOK2P 2300 (k0Arrs ()) ((finBase2300 k0Base).map Fin.val).toArray
    k0Words (i301K1 ()) (i301K2 ()) = true := by
  rw [k0Base_eq]
  exact smallFacts.chainK0

private theorem k0_inv : ∀ j < (k0Arrs ()).size,
    isInvA 2300 (k0Arrs ())[j]! (rawInvs 2300 (k0Arrs ()))[j]! = true :=
  (chainCheckFacts (caseChainOK2P_parts smallFacts.chainK0).1).strong_inv

private theorem rep_K1 : Rep 2300 (i301K1 ()) PK₁ :=
  (rep_permOfArr (k0_inv 0 (by rw [k0Arrs_size]; norm_num))).1

private theorem rep_K2 : Rep 2300 (i301K2 ()) PK₂ :=
  (rep_permOfArr (k0_inv 1 (by rw [k0Arrs_size]; norm_num))).1

private theorem mem_K0_of_inK0 {t : Array ℕ} {G : Equiv.Perm (Fin 2300)} (hG : Rep 2300 t G)
    (h : inK0 (rawLevels 2300 (k0Arrs ()) k0Base) t = true) : G ∈ PK₀ := by
  have hs : siftA 2300 (rawLevels 2300 (k0Arrs ()) ((finBase2300 k0Base).map Fin.val).toArray)
      ((finBase2300 k0Base).map Fin.val).toArray 0 t = true := by
    rw [k0Base_eq]
    exact h
  exact mem_closure_two_of_siftG (by norm_num) (by rw [k0Arrs_size]; norm_num) k0Base_nodup rep_K1
    rep_K2 chainK0 hG hs

private theorem card_K0_aux : Nat.card PK₀ = 360 := by
  rw [card_closure_two_of_chainOK (by norm_num) (by rw [k0Arrs_size]; norm_num) k0Base_nodup
    rep_K1 rep_K2 chainK0, k0Base_eq]
  exact smallFacts.orbK0

private theorem eq_one_of_fix_base_aux :
    ∀ g ∈ PK₀, (∀ b ∈ finBase2300 k0Base, g b = b) → g = 1 := by
  intro g hg hfix
  obtain ⟨hc, e0, e1⟩ := caseChainOK2P_parts chainK0
  have hk : 2 ≤ (k0Arrs ()).size := by rw [k0Arrs_size]; norm_num
  have hA := chainArrays_ofArrays (hn := (by norm_num : 1 ≤ 2300)) (k := 2) (hk := hk)
    (hb := k0Base_nodup) (W := k0Words) (chainCheckFacts hc).strong_inv
  have hQ := (validSchreier_of_chainOK hA (by norm_num) hc).1
  have horig := originalSubgroup_ofArrays_twoP (hn := (by norm_num : 1 ≤ 2300)) (hk := hk)
    (hb := k0Base_nodup) hc rep_K1 rep_K2 e0 e1
  set Q := RawSchreierDatum.ofArrays 2300 (by norm_num) (k0Arrs ()) 2 hk (finBase2300 k0Base)
    k0Base_nodup k0Words
  have hgQ : g ∈ Q.originalSubgroup := by rw [horig]; exact hg
  have hlen : Q.base.toList.length = Q.baseCount := by simp
  have hbase : Q.base.toList = finBase2300 k0Base := RawSchreierDatum.ofArrays_base_toList
  have hmem : g ∈ Q.levelSubgroup Q.baseCount := by
    refine (Q.mem_levelSubgroup_iff hQ _ le_rfl g).2 ⟨hgQ, fun b hb => hfix b ?_⟩
    rw [List.take_of_length_le hlen.le, hbase] at hb
    exact hb
  rw [Q.levelSubgroup_terminal_eq_bot hQ] at hmem
  exact hmem

private theorem mem_Lsub_of_sift {t : Array ℕ} {G : Equiv.Perm (Fin 2300)} (hG : Rep 2300 t G)
    (h : siftA 2300 (rawLevels 2300 (co2LArrs ()) co2LBase) co2LBase 0 t = true) : G ∈ Lsub :=
  co2_mem_Lsub_of_sift hG h

private theorem Lsub_le_P : Lsub ≤ co2P := fun _ hl =>
  (Subgroup.mem_inf.1 (co2CaseB_spec.2.2.2.2.1 hl)).2

private theorem hP_mem_aux : PH ∈ co2P := mem_co2P_of_inP rep_H smallFacts.inPH

private theorem dP_eq_aux : PD = PH * co2XB * PH⁻¹ :=
  eq_of_eqA rep_D (rep_conj2300 rep_H rep_Hi rep_XB) smallFacts.conjD

private theorem conj_mem_Lsub {t : Array ℕ} {T : Equiv.Perm (Fin 2300)} (ht : Rep 2300 t T)
    (h : siftA 2300 (rawLevels 2300 (co2LArrs ()) co2LBase) co2LBase 0
      (conj2300 (invCand 2300 (i301H ())) (i301H ()) t) = true) : PH⁻¹ * T * PH ∈ Lsub := by
  have hr : Rep 2300 (conj2300 (invCand 2300 (i301H ())) (i301H ()) t) (PH⁻¹ * T * PH) := by
    rw [mul_assoc]
    exact rep_compA rep_Hi (rep_compA ht rep_H)
  exact mem_Lsub_of_sift hr h

private theorem mem_P_of_conj {T : Equiv.Perm (Fin 2300)} (hT : PH⁻¹ * T * PH ∈ co2P) :
    T ∈ co2P := by
  have := co2P.mul_mem (co2P.mul_mem hP_mem_aux hT) (co2P.inv_mem hP_mem_aux)
  rwa [show PH * (PH⁻¹ * T * PH) * PH⁻¹ = T by group] at this

private theorem k1_mem_P : PK₁ ∈ co2P :=
  mem_P_of_conj (Lsub_le_P (conj_mem_Lsub rep_K1 smallFacts.siftK1))

private theorem k2_mem_P : PK₂ ∈ co2P :=
  mem_P_of_conj (Lsub_le_P (conj_mem_Lsub rep_K2 smallFacts.siftK2))

private theorem K0_le_P : PK₀ ≤ co2P := by
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact k1_mem_P
  · exact k2_mem_P

private theorem gens_mem_locC_aux : PD ∈ locC ∧ PS ∈ locC ∧ PB₂ ∈ locC ∧ PB₃ ∈ locC ∧ PK₁ ∈ locC ∧
    PK₂ ∈ locC := by
  have F := smallFacts
  have mem : ∀ {t : Array ℕ} {G : Equiv.Perm (Fin 2300)}, Rep 2300 t G → G ∈ co2P →
      comm2300 zArr t = true → G ∈ locC := by
    intro t G ht hG hc
    rw [locC_eq_centralizer]
    exact Subgroup.mem_inf.2 ⟨hG, Subgroup.mem_centralizer_singleton_iff.2
      ((comm2300_iff rep_z ht).1 hc).eq.symm⟩
  have hdP : PD ∈ co2P := by
    rw [dP_eq_aux]
    exact co2P.mul_mem (co2P.mul_mem hP_mem_aux co2CaseB_spec.2.2.1) (co2P.inv_mem hP_mem_aux)
  exact ⟨mem rep_D hdP F.zD,
    mem rep_S (mem_P_of_conj (Lsub_le_P (conj_mem_Lsub rep_S F.siftS))) F.zS,
    mem rep_B2 (K0_le_P (mem_K0_of_inK0 rep_B2 F.inB2)) F.zB2,
    mem rep_B3 (K0_le_P (mem_K0_of_inK0 rep_B3 F.inB3)) F.zB3,
    mem rep_K1 k1_mem_P F.zK1, mem rep_K2 k2_mem_P F.zK2⟩

private theorem gens_mem_U0_aux : PK₁ ∈ Lsub.map (MulAut.conj PH).toMonoidHom ∧
    PK₂ ∈ Lsub.map (MulAut.conj PH).toMonoidHom ∧ PS ∈ Lsub.map (MulAut.conj PH).toMonoidHom := by
  have F := smallFacts
  have mem : ∀ {T : Equiv.Perm (Fin 2300)}, PH⁻¹ * T * PH ∈ Lsub →
      T ∈ Lsub.map (MulAut.conj PH).toMonoidHom := fun {T} h =>
    Subgroup.mem_map.2 ⟨_, h, by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group⟩
  exact ⟨mem (conj_mem_Lsub rep_K1 F.siftK1), mem (conj_mem_Lsub rep_K2 F.siftK2),
    mem (conj_mem_Lsub rep_S F.siftS)⟩

private theorem s_mul_s : PS * PS = 1 :=
  eq_of_eqA (rep_compA rep_S rep_S) rep_idA smallFacts.sqS

private theorem mem_K0_facts_aux :
    PB₂ ∈ PK₀ ∧ PB₃ ∈ PK₀ ∧ PS * PK₁ * PS⁻¹ ∈ PK₀ ∧ PS * PK₂ * PS⁻¹ ∈ PK₀ := by
  have F := smallFacts
  have hsi : PS⁻¹ = PS := inv_eq_of_mul_eq_one_right s_mul_s
  have hSi : Rep 2300 (i301S ()) PS⁻¹ := by
    rw [hsi]
    exact rep_S
  exact ⟨mem_K0_of_inK0 rep_B2 F.inB2, mem_K0_of_inK0 rep_B3 F.inB3,
    mem_K0_of_inK0 (rep_conj2300 rep_S hSi rep_K1) F.inSK1,
    mem_K0_of_inK0 (rep_conj2300 rep_S hSi rep_K2) F.inSK2⟩

private theorem commute_facts_aux :
    Commute PD PS ∧ Commute PD PB₂ ∧ Commute PD PB₃ ∧ Commute PD PK₁ ∧
    Commute PD PK₂ ∧ Commute PB₂ PB₃ ∧ Commute locZ PD ∧ Commute locZ PS ∧ Commute locZ PB₂ ∧
    Commute locZ PB₃ ∧ Commute locZ PK₁ ∧ Commute locZ PK₂ := by
  have F := smallFacts
  exact ⟨(comm2300_iff rep_D rep_S).1 F.dS, (comm2300_iff rep_D rep_B2).1 F.dB2,
    (comm2300_iff rep_D rep_B3).1 F.dB3, (comm2300_iff rep_D rep_K1).1 F.dK1,
    (comm2300_iff rep_D rep_K2).1 F.dK2, (comm2300_iff rep_B2 rep_B3).1 F.b2B3,
    (comm2300_iff rep_z rep_D).1 F.zD, (comm2300_iff rep_z rep_S).1 F.zS,
    (comm2300_iff rep_z rep_B2).1 F.zB2, (comm2300_iff rep_z rep_B3).1 F.zB3,
    (comm2300_iff rep_z rep_K1).1 F.zK1, (comm2300_iff rep_z rep_K2).1 F.zK2⟩

private theorem indep_spec (t : ℕ) (ht : t < 27) :
    t = 0 ∨ PD ^ (t % 3) * (PB₂ ^ (t / 3 % 3) * PB₃ ^ (t / 9)) ≠ 1 := by
  have h := allLt_spec smallFacts.indep ht
  have hr := rep_compA (rep_powArr rep_D (t % 3))
    (rep_compA (rep_powArr rep_B2 (t / 3 % 3)) (rep_powArr rep_B3 (t / 9)))
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  rcases h with h | h
  · exact Or.inl h
  · refine Or.inr fun e => ?_
    rw [(eqA_iff hr rep_idA).2 e] at h
    exact Bool.noConfusion h

private theorem pow_facts_aux : PD ^ 3 = 1 ∧ PD ≠ 1 ∧ PB₂ ^ 3 = 1 ∧ PB₃ ^ 3 = 1 ∧ PS ^ 2 = 1 := by
  have F := smallFacts
  refine ⟨eq_of_eqA (rep_powArr rep_D 3) rep_idA F.powD, ?_,
    eq_of_eqA (rep_powArr rep_B2 3) rep_idA F.powB2,
    eq_of_eqA (rep_powArr rep_B3 3) rep_idA F.powB3, by rw [sq]; exact s_mul_s⟩
  have h := (indep_spec 1 (by norm_num)).resolve_left one_ne_zero
  norm_num at h
  exact h

private theorem indep_facts_aux :
    ∀ i j k : ℕ, i < 3 → j < 3 → k < 3 → PD ^ i * PB₂ ^ j * PB₃ ^ k = 1 →
    i = 0 ∧ j = 0 ∧ k = 0 := by
  intro i j k hi hj hk h
  rcases indep_spec (i + 3 * j + 9 * k) (by omega) with h0 | h0
  · omega
  · exfalso
    apply h0
    rw [show (i + 3 * j + 9 * k) % 3 = i by omega, show (i + 3 * j + 9 * k) / 3 % 3 = j by omega,
      show (i + 3 * j + 9 * k) / 9 = k by omega, ← mul_assoc]
    exact h

private theorem getElem!_ofFn_arr {m : ℕ} (f : Fin m → Array ℕ) {i : ℕ} (hi : i < m) :
    (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos (Array.ofFn f) i (by simpa using hi), Array.getElem_ofFn]

private theorem rep_dzElts {t : ℕ} (ht : t < 6) :
    Rep 2300 (dzElts (i301D ()) zArr)[t]! (PD ^ (t % 3) * locZ ^ (t / 3)) := by
  rw [dzElts, getElem!_ofFn_arr _ ht]
  exact rep_compA (rep_powArr rep_D _) (rep_powArr rep_z _)

private theorem pow512_ne_one_aux :
    ∀ i j : ℕ, 0 < i → i < 3 → j < 2 → (PD ^ i * locZ ^ j) ^ 512 ≠ 1 := by
  intro i j hi0 hi hj e
  have ht : i + 3 * j < 6 := by omega
  have h := allLt_spec smallFacts.pow512 ht
  have hr := rep_dzElts ht
  rw [show (i + 3 * j) % 3 = i by omega, show (i + 3 * j) / 3 = j by omega] at hr
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  rcases h with h | h
  · omega
  · rw [(eqA_iff (rep_powArr hr 512) rep_idA).2 e] at h
    exact Bool.noConfusion h

private theorem k_o6_aux (j : Fin 6) (x : Fin 2300) (hx : (x : ℕ) = o6.getD j 0) :
    (PK₁ x : ℕ) = o6.getD (sigma1.getD j 0) 0 ∧ (PK₂ x : ℕ) = o6.getD (sigma2.getD j 0) 0 := by
  have h := allLt_spec smallFacts.o6K j.2
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rw [← rep_K1 x, ← rep_K2 x, hx]
  exact h

theorem hP_mem {h : Equiv.Perm (Fin 2300)} (eh : h = permOfArr 2300 (i301H ())) : h ∈ co2P := by
  subst eh
  exact hP_mem_aux

theorem dP_eq {h d : Equiv.Perm (Fin 2300)} (eh : h = permOfArr 2300 (i301H ()))
    (ed : d = permOfArr 2300 (i301D ())) : d = h * co2XB * h⁻¹ := by
  subst eh ed
  exact dP_eq_aux

theorem gens_mem_locC {d s b2 b3 k1 k2 : Equiv.Perm (Fin 2300)}
    (ed : d = permOfArr 2300 (i301D ())) (es : s = permOfArr 2300 (i301S ()))
    (eb2 : b2 = permOfArr 2300 (i301B2 ())) (eb3 : b3 = permOfArr 2300 (i301B3 ()))
    (ek1 : k1 = permOfArr 2300 (i301K1 ())) (ek2 : k2 = permOfArr 2300 (i301K2 ())) :
    d ∈ locC ∧ s ∈ locC ∧ b2 ∈ locC ∧ b3 ∈ locC ∧ k1 ∈ locC ∧ k2 ∈ locC := by
  subst ed es eb2 eb3 ek1 ek2
  exact gens_mem_locC_aux

theorem gens_mem_U0 {h s k1 k2 : Equiv.Perm (Fin 2300)} {U : Subgroup (Equiv.Perm (Fin 2300))}
    (eh : h = permOfArr 2300 (i301H ())) (es : s = permOfArr 2300 (i301S ()))
    (ek1 : k1 = permOfArr 2300 (i301K1 ())) (ek2 : k2 = permOfArr 2300 (i301K2 ()))
    (eU : U = Lsub.map (MulAut.conj h).toMonoidHom) : k1 ∈ U ∧ k2 ∈ U ∧ s ∈ U := by
  subst eh es ek1 ek2 eU
  exact gens_mem_U0_aux

theorem mem_K0_facts {s b2 b3 k1 k2 : Equiv.Perm (Fin 2300)}
    {K : Subgroup (Equiv.Perm (Fin 2300))} (es : s = permOfArr 2300 (i301S ()))
    (eb2 : b2 = permOfArr 2300 (i301B2 ())) (eb3 : b3 = permOfArr 2300 (i301B3 ()))
    (ek1 : k1 = permOfArr 2300 (i301K1 ())) (ek2 : k2 = permOfArr 2300 (i301K2 ()))
    (eK : K = Subgroup.closure {k1, k2}) :
    b2 ∈ K ∧ b3 ∈ K ∧ s * k1 * s⁻¹ ∈ K ∧ s * k2 * s⁻¹ ∈ K := by
  subst es eb2 eb3 ek1 ek2 eK
  exact mem_K0_facts_aux

theorem commute_facts {d s b2 b3 k1 k2 : Equiv.Perm (Fin 2300)}
    (ed : d = permOfArr 2300 (i301D ())) (es : s = permOfArr 2300 (i301S ()))
    (eb2 : b2 = permOfArr 2300 (i301B2 ())) (eb3 : b3 = permOfArr 2300 (i301B3 ()))
    (ek1 : k1 = permOfArr 2300 (i301K1 ())) (ek2 : k2 = permOfArr 2300 (i301K2 ())) :
    Commute d s ∧ Commute d b2 ∧ Commute d b3 ∧ Commute d k1 ∧ Commute d k2 ∧ Commute b2 b3 ∧
      Commute locZ d ∧ Commute locZ s ∧ Commute locZ b2 ∧ Commute locZ b3 ∧ Commute locZ k1 ∧
      Commute locZ k2 := by
  subst ed es eb2 eb3 ek1 ek2
  exact commute_facts_aux

theorem pow_facts {d s b2 b3 : Equiv.Perm (Fin 2300)} (ed : d = permOfArr 2300 (i301D ()))
    (es : s = permOfArr 2300 (i301S ())) (eb2 : b2 = permOfArr 2300 (i301B2 ()))
    (eb3 : b3 = permOfArr 2300 (i301B3 ())) :
    d ^ 3 = 1 ∧ d ≠ 1 ∧ b2 ^ 3 = 1 ∧ b3 ^ 3 = 1 ∧ s ^ 2 = 1 := by
  subst ed es eb2 eb3
  exact pow_facts_aux

theorem indep_facts {d b2 b3 : Equiv.Perm (Fin 2300)} (ed : d = permOfArr 2300 (i301D ()))
    (eb2 : b2 = permOfArr 2300 (i301B2 ())) (eb3 : b3 = permOfArr 2300 (i301B3 ())) :
    ∀ i j k : ℕ, i < 3 → j < 3 → k < 3 → d ^ i * b2 ^ j * b3 ^ k = 1 →
      i = 0 ∧ j = 0 ∧ k = 0 := by
  subst ed eb2 eb3
  exact indep_facts_aux

theorem card_K0 {k1 k2 : Equiv.Perm (Fin 2300)} {K : Subgroup (Equiv.Perm (Fin 2300))}
    (ek1 : k1 = permOfArr 2300 (i301K1 ())) (ek2 : k2 = permOfArr 2300 (i301K2 ()))
    (eK : K = Subgroup.closure {k1, k2}) : Nat.card K = 360 := by
  subst ek1 ek2 eK
  exact card_K0_aux

theorem k_o6 {k1 k2 : Equiv.Perm (Fin 2300)} (ek1 : k1 = permOfArr 2300 (i301K1 ()))
    (ek2 : k2 = permOfArr 2300 (i301K2 ())) (j : Fin 6) (x : Fin 2300)
    (hx : (x : ℕ) = o6.getD j 0) :
    (k1 x : ℕ) = o6.getD (sigma1.getD j 0) 0 ∧ (k2 x : ℕ) = o6.getD (sigma2.getD j 0) 0 := by
  subst ek1 ek2
  exact k_o6_aux j x hx

theorem eq_one_of_fix_base {k1 k2 : Equiv.Perm (Fin 2300)} {K : Subgroup (Equiv.Perm (Fin 2300))}
    (ek1 : k1 = permOfArr 2300 (i301K1 ())) (ek2 : k2 = permOfArr 2300 (i301K2 ()))
    (eK : K = Subgroup.closure {k1, k2}) :
    ∀ g ∈ K, (∀ b ∈ finBase2300 k0Base, g b = b) → g = 1 := by
  subst ek1 ek2 eK
  exact eq_one_of_fix_base_aux

theorem pow512_ne_one {d : Equiv.Perm (Fin 2300)} (ed : d = permOfArr 2300 (i301D ())) :
    ∀ i j : ℕ, 0 < i → i < 3 → j < 2 → (d ^ i * locZ ^ j) ^ 512 ≠ 1 := by
  subst ed
  exact pow512_ne_one_aux

end Facts

end CFSG.Sporadic.Co2I301.SpecAux
