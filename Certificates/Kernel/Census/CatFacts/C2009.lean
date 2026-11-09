
module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallConfP45Inputs
public meta import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3P45
public meta import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallConfChecks2
public import Certificates.Data.Kernel.Census.CatFacts.C2009Defs
public import Certificates.Data.Kernel.Census.CatFacts.C2009Orb
import CFSG.Certificates.Kernel.Census.CatFacts.PkWordSound
import Certificates.Kernel.Census.CatFacts.C2009L
import Certificates.Kernel.Census.CatFacts.C2009A0
import Certificates.Kernel.Census.CatFacts.C2009A1
import Certificates.Kernel.Census.CatFacts.C2009A2
import Certificates.Kernel.Census.CatFacts.C2009A3
import Certificates.Kernel.Census.CatFacts.C2009P
import Certificates.Kernel.Census.CatFacts.C2009K1
import Certificates.Kernel.Census.CatFacts.C2009K2
import Certificates.Kernel.Census.CatFacts.C2009K3

public section

namespace CertificateChecks.KernelCatFacts

open CFSG.ComponentClassification.CatFactsSmall CFSG.ComponentClassification.CatFactsSmall.PSp43
  CFSG.Certificates.Kernel.PkEnum CFSG.Certificates.Kernel.CatFacts CFSG.GH74.KGroups
  CFSG.Sporadic.Schreier CFSG.Certificates

local notation "PX" => Equiv.Perm (Fin 45)

theorem forceA1_eq {β : Sort _} (k : CA → β) : forceA1 k = k cA0 := by
  rw [← cA1_eq]
  unfold forceA1
  simp only [forceL_eq, forceLL_eq, forceV_eq, forceLv_eq]

theorem forceA2_eq {β : Sort _} (k : CA → β) : forceA2 k = k cA0 := by
  rw [← cA1_eq]
  unfold forceA2
  simp only [forceLL_eq, forceLv_eq]

theorem forceIC_eq {β : Sort _} (k : CA → β) : forceIC k = k cA0 := by
  rw [← cA1_eq]
  unfold forceIC
  simp only [forceLL_eq]

theorem siftW_lv0 (Q : RawSchreierDatum 45) (w : List (VP 45)) :
    siftW (lv0 Q) w = Q.sift (pkpW w) 0 :=
  (sift_pkpW Q w 0).symm

theorem pkpW_conjW (w : List (VP 45)) (a : VP 45) :
    pkpW (conjW w a) = pkpW w * pkp a * (pkpW w)⁻¹ := by
  rw [conjW, pkpW_append, pkpW_cons, pkpW_invW, mul_assoc]

theorem conjCodes_map (S : List PX) (ws : List (List ℤ)) (s : PX) :
    (conjCodes (S.map codeV) ws (codeV s)).map pkpW =
      ws.map fun w => (evalCodes S w)⁻¹ * s * evalCodes S w := by
  unfold conjCodes
  rw [List.map_map]
  apply List.map_congr_left
  intro w _
  rw [Function.comp_apply, pkpW_append, pkpW_cons, pkpW_invW, pkpW_codesW, pkp_codeV, mul_assoc]

theorem vXYF_eq : vXYF = [x45, y45, f45].map codeV := rfl

theorem tabs_eq : [tab x45, tab y45, tab f45] = [x45, y45, f45] := by
  rw [tab_eq, tab_eq, tab_eq]

theorem tabs2_eq : [tab x45, tab y45] = [x45, y45] := by
  rw [tab_eq, tab_eq]

theorem cls1_eq : cA0.cls1.map pkpW = cfCls1C := by
  change (conjCodes vXYF cfCls1W (codeV s045)).map pkpW = _
  rw [vXYF_eq, conjCodes_map, cfCls1C, cfCls1, List.map_map, tabs_eq]
  apply List.map_congr_left
  intro w _
  simp only [Function.comp_apply, tab_eq]

theorem cls2_eq : cA0.cls2.map pkpW = cfCls2C := by
  change (conjCodes vXYF cfCls2W (codeV (s045 * cfZ * cfTau))).map pkpW = _
  rw [vXYF_eq, conjCodes_map, cfCls2C, cfCls2, List.map_map, tabs_eq]
  apply List.map_congr_left
  intro w _
  simp only [Function.comp_apply, tab_eq]

theorem icls1_eq : cA0.icls1.map pkpW = cfICls1C := by
  change (conjCodes (vXYF.take 2) cfICls1W (codeV cfZ)).map pkpW = _
  rw [show vXYF.take 2 = [x45, y45].map codeV from rfl, conjCodes_map, cfICls1C, cfICls1,
    List.map_map, tabs2_eq]
  apply List.map_congr_left
  intro w _
  simp only [Function.comp_apply, tab_eq]

theorem icls2_eq : cA0.icls2.map pkpW = cfICls2C := by
  change (conjCodes (vXYF.take 2) cfICls2W (codeV (cfZ * cfTau))).map pkpW = _
  rw [show vXYF.take 2 = [x45, y45].map codeV from rfl, conjCodes_map, cfICls2C, cfICls2,
    List.map_map, tabs2_eq]
  apply List.map_congr_left
  intro w _
  simp only [Function.comp_apply, tab_eq]

theorem cls1P_eq : cls1P = cfCls1C := cls1_eq

theorem tA_eq : cA0.tA = transL QA45 := rfl

theorem lQQ_eq : cA0.lQQ = lv0 QQ45 := rfl

theorem lQR_eq : cA0.lQR = lv0 cfQR := rfl

theorem lQE_eq : cA0.lQE = lv0 cfQE := rfl

theorem lQP_eq : cA0.lQP = lv0 QP45 := rfl

theorem all_codeV (L : List PX) (f : PX → Bool) : (L.map codeV).all (fun a => f (pkp a)) = L.all f := by
  rw [List.all_map]
  congr 1
  funext a
  rw [Function.comp_apply, pkp_codeV]

theorem pA_eq (w : List (VP 45)) : pA cA0 w =
    ((!(q0gens.all fun q => QQ45.sift (pkpW w * q * (pkpW w)⁻¹) 0) || QQ45.sift (pkpW w) 0 ||
      QQ45.sift (g045⁻¹ * pkpW w) 0) &&
    (!(cfHgens.all fun h => cfQH.sift (pkpW w * h * (pkpW w)⁻¹) 0) || cfQR.sift (pkpW w) 0) &&
    (!(cfEgens.all fun e => decide (e * pkpW w = pkpW w * e)) || cfQE.sift (pkpW w) 0) &&
    (!decide (pkpW w * pkpW w = 1) || QP45.sift (pkpW w) 0 || decide (pkpW w ∈ cfCls1C) ||
      decide (pkpW w ∈ cfCls2C))) := by
  have hq : (cA0.q0.all fun q => siftW cA0.lQQ (conjW w q)) =
      q0gens.all fun q => QQ45.sift (pkpW w * q * (pkpW w)⁻¹) 0 := by
    change ((q0gens.map codeV).all fun q => siftW (lv0 QQ45) (conjW w q)) = _
    simp only [siftW_lv0, pkpW_conjW]
    exact all_codeV q0gens (fun q => QQ45.sift (pkpW w * q * (pkpW w)⁻¹) 0)
  have hh : (cA0.h.all fun h => siftW cA0.lQH (conjW w h)) =
      cfHgens.all fun h => cfQH.sift (pkpW w * h * (pkpW w)⁻¹) 0 := by
    change ((cfHgens.map codeV).all fun h => siftW (lv0 cfQH) (conjW w h)) = _
    simp only [siftW_lv0, pkpW_conjW]
    exact all_codeV cfHgens (fun h => cfQH.sift (pkpW w * h * (pkpW w)⁻¹) 0)
  have he1 : (cA0.e.all fun e => eqW (e :: w) (w ++ [e])) =
      cfEgens.all fun e => decide (e * pkpW w = pkpW w * e) := by
    change ((cfEgens.map codeV).all fun e => eqW (e :: w) (w ++ [e])) = _
    simp only [eqW_eq, pkpW_cons, pkpW_append]
    exact all_codeV cfEgens (fun e => decide (e * pkpW w = pkpW w * e))
  have hg : siftW cA0.lQQ (cA0.g0i :: w) = QQ45.sift (g045⁻¹ * pkpW w) 0 := by
    change siftW (lv0 QQ45) (invV (codeV g045) :: w) = _
    rw [siftW_lv0, pkpW_cons, pkp_invV, pkp_codeV]
  unfold pA
  rw [hq, hh, he1, hg]
  simp only [lQQ_eq, lQR_eq, lQE_eq, lQP_eq, siftW_lv0, isOneW_eq, pkpW_append, memW_eq, cls1_eq,
    cls2_eq]

theorem pP_eq (w : List (VP 45)) : pP cA0 w =
    (!decide (pkpW w * pkpW w = 1) || decide (pkpW w = 1) || decide (pkpW w ∈ cfICls1C) ||
      decide (pkpW w ∈ cfICls2C)) := by
  unfold pP
  rw [isOneW_eq, isOneW_eq, pkpW_append, memW_eq, memW_eq, icls1_eq, icls2_eq]

theorem chunksA : ∀ j < 45, chunkA j = true := by
  intro j hj
  interval_cases j
  · exact chunkA0
  · exact chunkA1
  · exact chunkA2
  · exact chunkA3
  · exact chunkA4
  · exact chunkA5
  · exact chunkA6
  · exact chunkA7
  · exact chunkA8
  · exact chunkA9
  · exact chunkA10
  · exact chunkA11
  · exact chunkA12
  · exact chunkA13
  · exact chunkA14
  · exact chunkA15
  · exact chunkA16
  · exact chunkA17
  · exact chunkA18
  · exact chunkA19
  · exact chunkA20
  · exact chunkA21
  · exact chunkA22
  · exact chunkA23
  · exact chunkA24
  · exact chunkA25
  · exact chunkA26
  · exact chunkA27
  · exact chunkA28
  · exact chunkA29
  · exact chunkA30
  · exact chunkA31
  · exact chunkA32
  · exact chunkA33
  · exact chunkA34
  · exact chunkA35
  · exact chunkA36
  · exact chunkA37
  · exact chunkA38
  · exact chunkA39
  · exact chunkA40
  · exact chunkA41
  · exact chunkA42
  · exact chunkA43
  · exact chunkA44

theorem chunksI : ∀ j < 45, chunkI j = true := by
  intro j hj
  interval_cases j
  · exact chunkI0
  · exact chunkI1
  · exact chunkI2
  · exact chunkI3
  · exact chunkI4
  · exact chunkI5
  · exact chunkI6
  · exact chunkI7
  · exact chunkI8
  · exact chunkI9
  · exact chunkI10
  · exact chunkI11
  · exact chunkI12
  · exact chunkI13
  · exact chunkI14
  · exact chunkI15
  · exact chunkI16
  · exact chunkI17
  · exact chunkI18
  · exact chunkI19
  · exact chunkI20
  · exact chunkI21
  · exact chunkI22
  · exact chunkI23
  · exact chunkI24
  · exact chunkI25
  · exact chunkI26
  · exact chunkI27
  · exact chunkI28
  · exact chunkI29
  · exact chunkI30
  · exact chunkI31
  · exact chunkI32
  · exact chunkI33
  · exact chunkI34
  · exact chunkI35
  · exact chunkI36
  · exact chunkI37
  · exact chunkI38
  · exact chunkI39
  · exact chunkI40
  · exact chunkI41
  · exact chunkI42
  · exact chunkI43
  · exact chunkI44

theorem pA_split (C : CA) (w : List (VP 45)) : pA C w = (pA1 C w && pA2 C w) := rfl

theorem blockA_all : ∀ j < ((transL QA45).headD []).length,
    (blockW (transL QA45) j).all (pA cA0) = true := by
  intro j hj
  rw [nA2009K] at hj
  have h1 := chunksA j hj
  have h2 := chunksI j hj
  unfold chunkA at h1
  unfold chunkI at h2
  rw [forceA1_eq, List.all_eq_true] at h1
  rw [forceA2_eq, List.all_eq_true] at h2
  rw [List.all_eq_true]
  intro w hw
  rw [pA_split, h1 w hw, h2 w hw]
  rfl

theorem scanA : (elemsT QA45).all (fun x =>
    (!(q0gens.all fun q => QQ45.sift (x * q * x⁻¹) 0) || QQ45.sift x 0 ||
      QQ45.sift (g045⁻¹ * x) 0) &&
    (!(cfHgens.all fun h => cfQH.sift (x * h * x⁻¹) 0) || cfQR.sift x 0) &&
    (!(cfEgens.all fun e => decide (e * x = x * e)) || cfQE.sift x 0) &&
    (!decide (x * x = 1) || QP45.sift x 0 || decide (x ∈ cfCls1C) ||
      decide (x ∈ cfCls2C))) = true := by
  refine elemsT_all_of_blocks QA45 (by decide) _ fun j hj => ?_
  have h := blockA_all j hj
  rw [List.all_eq_true] at h ⊢
  intro w hw
  have h1 := h w hw
  rw [pA_eq] at h1
  exact h1

theorem sylP2009 : ((elemsT cfQR).filter fun x => QP45.sift x 0).length = 64 ∧
    ((elemsT cfQR).filter fun x => QP45.sift x 0).all (fun y => !decide (y * y = 1) ||
      decide (y = 1) || decide (y ∈ cfICls1C) || decide (y ∈ cfICls2C)) = true := by
  simp only [elemsT_eq_elemsV, sift_eq_siftP, siftP_QP45]
  refine ⟨sylLen2009K, ?_⟩
  have h := sylChk2009_ok
  unfold sylChk2009 at h
  rw [forceIC_eq, List.all_eq_true] at h
  rw [List.all_eq_true]
  intro y hy
  have h1 := h y hy
  rw [pP_eq, pkpW_single, pkp_codeV] at h1
  exact h1

theorem all_and {α : Type*} {L : List α} {p q : α → Bool}
    (h : L.all (fun x => p x && q x) = true) : L.all p = true ∧ L.all q = true := by
  simp only [List.all_eq_true, Bool.and_eq_true] at h ⊢
  exact ⟨fun x hx => (h x hx).1, fun x hx => (h x hx).2⟩

theorem getD_map_pkp (O : List (VP 45)) (i : Nat) :
    (O.map pkp).getD i 1 = pkp (O.getD i (oneV 45)) := by
  induction O generalizing i with
  | nil => exact (pkp_oneV 45).symm
  | cons a O ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem mem_iff_getD {α : Type*} (L : List α) (d : α) (y : α) :
    y ∈ L ↔ ∃ i < L.length, L.getD i d = y := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, List.getD_eq_getElem _ _ hi⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, (List.getD_eq_getElem _ _ hi).symm⟩

theorem keyV45_congr {a b : VP 45} (h : pkp a = pkp b) : keyV45 a = keyV45 b := by
  unfold keyV45
  congr 1
  apply List.map_congr_left
  intro i hi
  have ha := imgW_eq [a] ⟨i, List.mem_range.1 hi⟩
  have hb := imgW_eq [b] ⟨i, List.mem_range.1 hi⟩
  rw [pkpW_single] at ha hb
  rw [h] at ha
  exact ha.trans hb.symm

theorem orbCertL_of (S O : List (VP 45)) (cl : List (List Nat)) (tr : List (Nat × Nat))
    (K : List Nat) (x : VP 45) (h : orbOK45 S O cl tr K x = true) (hK : K.Nodup) :
    OrbCertL (S.map pkp) (pkp x) (O.map pkp) := by
  simp only [orbOK45, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h0, hx⟩, hcl⟩, htr⟩, hkey⟩ := h
  have hcl' : ∀ i < O.length, ∀ k < S.length, (cl.getD i []).getD k 0 < O.length ∧
      (pkp (S.getD k (oneV 45)))⁻¹ * pkp (O.getD i (oneV 45)) * pkp (S.getD k (oneV 45)) =
        pkp (O.getD ((cl.getD i []).getD k 0) (oneV 45)) := by
    intro i hi k hk
    have h1 := List.all_eq_true.1 (List.all_eq_true.1 hcl i (List.mem_range.2 hi)) k
      (List.mem_range.2 hk)
    simp only [Bool.and_eq_true, Nat.blt_eq, eqW_eq, decide_eq_true_eq, pkpW_cons, pkpW_nil,
      mul_one, pkp_invV, ← mul_assoc] at h1
    exact h1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hk : (O.map keyV45).Nodup := hkey ▸ hK
    refine List.Nodup.of_map (fun σ => keyV45 (codeV σ)) ?_
    rw [List.map_map]
    have e : O.map ((fun σ => keyV45 (codeV σ)) ∘ pkp) = O.map keyV45 :=
      List.map_congr_left fun a _ => by
        rw [Function.comp_apply]
        exact keyV45_congr (pkp_codeV (pkp a))
    rw [e]
    exact hk
  · rw [List.length_map]
    simpa only [Nat.blt_eq] using h0
  · rw [getD_map_pkp]
    simp only [eqW_eq, decide_eq_true_eq, pkpW_single] at hx
    exact hx.symm
  · intro o ho g hg
    obtain ⟨i, hi, rfl⟩ := (mem_iff_getD _ 1 o).1 ho
    obtain ⟨k, hk, rfl⟩ := (mem_iff_getD _ 1 g).1 hg
    rw [List.length_map] at hi hk
    obtain ⟨hj, he⟩ := hcl' i hi k hk
    rw [getD_map_pkp, getD_map_pkp, he]
    exact (mem_iff_getD _ 1 _).2 ⟨_, by rw [List.length_map]; exact hj, getD_map_pkp _ _⟩
  · intro i hi hpos
    rw [List.length_map] at hi
    have h1 := List.all_eq_true.1 htr i (List.mem_range.2 hi)
    simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at h1
    rcases h1 with h1 | ⟨⟨hp, hg⟩, hc⟩
    · omega
    refine ⟨_, hp, (S.map pkp).getD (tr.getD i (0, 0)).2 1,
      (mem_iff_getD _ 1 _).2 ⟨_, by rw [List.length_map]; exact hg, rfl⟩, ?_⟩
    obtain ⟨-, he⟩ := hcl' _ (hp.trans hi) _ hg
    rw [hc] at he
    rw [getD_map_pkp, getD_map_pkp, getD_map_pkp, he]

theorem orbChkTZ_eq : orbOK45 vXYF (orbTZN.map mkVP) orbTZCl orbTZTr orbTZK
    (codeV (cfTau * cfZ)) = orbChkTZ := by
  unfold orbChkTZ
  rw [forceL_eq, forceL_eq, forceV_eq]

theorem orbChkZ_eq : orbOK45 vXYF (orbZN.map mkVP) orbZCl orbZTr orbZK (codeV cfZ) = orbChkZ := by
  unfold orbChkZ
  rw [forceL_eq, forceL_eq, forceV_eq]

theorem vXYF_pkp : vXYF.map pkp = [x45, y45, f45] := by
  rw [vXYF_eq, List.map_map]
  simp only [List.map_cons, List.map_nil, Function.comp_apply, pkp_codeV]

theorem orbTZ_cert : OrbCertL [x45, y45, f45] (cfTau * cfZ) cfOrbTZ := by
  have h := orbCertL_of _ _ _ _ _ _ (orbChkTZ_eq.trans orbChkTZ_ok) orbTZK_nodup
  rw [vXYF_pkp, pkp_codeV, List.map_map] at h
  exact h

theorem orbZ_cert : OrbCertL [x45, y45, f45] cfZ cfOrbZ := by
  have h := orbCertL_of _ _ _ _ _ _ (orbChkZ_eq.trans orbChkZ_ok) orbZK_nodup
  rw [vXYF_pkp, pkp_codeV, List.map_map] at h
  exact h

theorem suppE : (cfOz.all fun p => decide (p.1.support.card = 40)) = true ∧
    (cfOzt.all fun p => decide (p.1.support.card = 32)) = true ∧ cfZ.support.card = 40 ∧
    (cfZ * cfTau).support.card = 32 := by
  decide +kernel

theorem all_dedup_map {α β : Type*} [DecidableEq β] (L : List α) (f : α → β) (p : β → Bool) :
    (L.map f).dedup.all p = L.all fun a => p (f a) := by
  apply Bool.eq_iff_iff.2
  simp only [List.all_eq_true, List.mem_dedup, List.mem_map]
  constructor
  · intro h a ha
    exact h _ ⟨a, ha, rfl⟩
  · rintro h _ ⟨a, ha, rfl⟩
    exact h a ha

theorem any_dedup_map {α β : Type*} [DecidableEq β] (L : List α) (f : α → β) (p : β → Bool) :
    (L.map f).dedup.any p = L.any fun a => p (f a) := by
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true, List.mem_dedup, List.mem_map]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, h⟩
    exact ⟨a, ha, h⟩
  · rintro ⟨a, ha, h⟩
    exact ⟨_, ⟨a, ha, rfl⟩, h⟩

theorem split4 {α : Type*} (L : List α) :
    L = L.take 32 ++ ((L.drop 32).take 32 ++ ((L.drop 64).take 32 ++ L.drop 96)) := by
  have h1 : L.drop 64 = (L.drop 32).drop 32 := by rw [List.drop_drop]
  have h2 : L.drop 96 = ((L.drop 32).drop 32).drop 32 := by rw [List.drop_drop, List.drop_drop]
  rw [h2, h1, List.take_append_drop, List.take_append_drop, List.take_append_drop]

theorem normal_all : (elemsV cfQR).all normT = true := by
  rw [split4 (elemsV cfQR)]
  simp only [List.all_append, normal2009K0, normal2009K1, normal2009K2, normal2009K3,
    Bool.and_self]

theorem valid_of {k : Nat} (hn : 1 ≤ 45) (gens : List PX) (words : List (List ℤ))
    (base : Vector (Fin 45) k) (hbase : base.toList.Nodup) (N : Nat)
    (h : schP (certificate hn gens words base hbase) = true ∧
      orderV (certificate hn gens words base hbase) = N) :
    (certificate hn gens words base hbase).check = true ∧
      (certificate hn gens words base hbase).orderCertificate = N :=
  ⟨check_certificate_of _ _ _ _ _ h.1, (orderCertificate_eq_orderV _).trans h.2⟩

open Certificates in
open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.CatFactsSmall in
open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.GH74.KGroups CFSG.Certificates in
open CFSG.Sporadic.Schreier Subgroup CFSG.ComponentClassification.GSThmB in
theorem facts2009 : ((elemsT QA45).all (fun x => !(q0gens.all fun q =>
      QQ45.sift (x * q * x⁻¹) 0) || QQ45.sift x 0 || QQ45.sift (g045⁻¹ * x) 0) = true
    )
    ∧ ((q0gens.all fun q => decide (q * cfTau = cfTau * q) &&
      decide (q * cfZ = cfZ * q)) = true ∧ g045⁻¹ * cfZ * g045 = cfZ
    )
    ∧ ((elemsT QQ45).all (fun w => !QL45.sift w 0 || !decide (w * w = 1) ||
      decide (w = 1) || decide (w = cfZ) ||
      (elemsT QQ45).any (fun v => QL45.sift v 0 && !decide (w * v = v * w))) = true
    )
    ∧ (cfQH.check = true ∧ cfQH.orderCertificate = 64)
    ∧ (cfQR.check = true ∧ cfQR.orderCertificate = 128)
    ∧ ((elemsT QA45).all (fun x => !(cfHgens.all fun h =>
      cfQH.sift (x * h * x⁻¹) 0) || cfQR.sift x 0) = true
    )
    ∧ ((cfRgens.all fun x => QA45.sift x 0 &&
      decide (x * (cfTau * cfZ) = cfTau * cfZ * x)) = true ∧
      (elemsT cfQR).all (fun x => !(cfRgens.all fun g => decide (g * x = x * g)) ||
        decide (x = 1) || decide (x = cfTau * cfZ)) = true ∧
      cfQR.sift (cfTau * cfZ) 0 = true ∧ (cfTau * cfZ) * (cfTau * cfZ) = 1
    )
    ∧ (((elemsT QQ45).filter fun x => QL45.sift x 0).length = 8 ∧
      ((elemsT QL45).filter fun x => decide (x * cfTau = cfTau * x)).length = 24 ∧
      OrbCertL [x45, y45, f45] (cfTau * cfZ) cfOrbTZ ∧
      ((elemsT cfQR).filter fun x => decide (x * cfZ = cfZ * x)).length = 64 ∧
      OrbCertL [x45, y45, f45] cfZ cfOrbZ
    )
    ∧ ((q0gens.all fun q => QL45.sift q 0 || QL45.sift (q * cfTau⁻¹) 0 ||
      QL45.sift (q * s045⁻¹) 0 || QL45.sift (q * s045⁻¹ * cfTau⁻¹) 0) = true ∧
      QQ45.sift cfTau 0 = true ∧ QQ45.sift s045 0 = true
    )
    ∧ (cfQR.sift cfTzu 0 = true ∧ cfQR.sift cfTzv 0 = true ∧
      cfTzu * cfTzv * cfTzu⁻¹ * cfTzv⁻¹ = cfTau * cfZ ∧ QP45.sift cfK0 0 = true ∧
      cfK0⁻¹ * cfZ * cfK0 = cfTau
    )
    ∧ (cfQD1.check = true ∧ cfQD1.orderCertificate = 8 ∧ cfQD2.check = true ∧
      cfQD2.orderCertificate = 8 ∧ cfQD12.check = true ∧ cfQD12.orderCertificate = 64
    )
    ∧ (orderIs cfR1 4 = true ∧ orderIs cfR2 4 = true ∧ cfS1 * cfS1 = 1 ∧
      cfS2 * cfS2 = 1 ∧ cfS1 * cfR1 * cfS1⁻¹ = cfR1⁻¹ ∧ cfS2 * cfR2 * cfS2⁻¹ = cfR2⁻¹ ∧
      cfR1 * cfR1 = cfZ ∧ cfR2 * cfR2 = cfTau ∧ cfZ * cfZ = 1 ∧ cfTau * cfTau = 1 ∧
      ([cfR1, cfS1, cfR2, cfS2].all fun x => cfQR.sift x 0 && decide (x * cfZ = cfZ * x)) = true ∧
      ([cfR1, cfS1].all fun x => [cfR2, cfS2].all fun y => decide (y * x = x * y)) = true ∧
      ((List.range 4).all fun k => !decide (cfS1 = cfR1 ^ k)) = true ∧
      ((List.range 4).all fun k => !decide (cfS2 = cfR2 ^ k)) = true ∧
      (elemsT cfQD1).all (fun x => decide (x = 1) || !cfQD2.sift x 0) = true ∧
      (elemsT cfQD1).all (fun x => decide ((cfR1 * x = x * cfR1 ∧ cfS1 * x = x * cfS1) ↔
        (x = 1 ∨ x = cfZ))) = true ∧
      (elemsT cfQD2).all (fun x => decide ((cfR2 * x = x * cfR2 ∧ cfS2 * x = x * cfS2) ↔
        (x = 1 ∨ x = cfTau))) = true
    )
    ∧ (cfQF1.check = true ∧ cfQF1.orderCertificate = 16 ∧ cfQF2.check = true ∧
      cfQF2.orderCertificate = 16 ∧ cfQF3.check = true ∧ cfQF3.orderCertificate = 16 ∧
      cfQRz.check = true ∧ cfQRz.orderCertificate = 64
    )
    ∧ ((cfFgens.all fun x => cfQR.sift x 0 && decide (x * cfZ = cfZ * x)) = true ∧
      (elemsT cfQF1).all (fun x => decide (x * x = 1)) = true ∧
      (elemsT cfQF2).all (fun x => decide (x * x = 1)) = true ∧
      (elemsT cfQF3).all (fun x => decide (x * x = 1)) = true ∧
      cfQRz.sift cfZ 0 = true ∧ cfQRz.sift cfTau 0 = true ∧ cfQRz.sift cfR1 0 = true ∧
      cfQRz.sift cfR2 0 = true ∧ (cfFgens.all fun x => decide (x * cfZ = cfZ * x) &&
        decide (x * cfTau = cfTau * x)) = true ∧
      (elemsT cfQRz).all (fun x => !(cfFgens.all fun g => decide (g * x = x * g)) ||
        (decide (x = 1) || decide (x = cfZ) || decide (x = cfTau) || decide (x = cfZ * cfTau))) =
        true ∧
      (elemsT cfQRz).all (fun x => decide (x * x = 1) || decide (x * x = cfZ) ||
        decide (x * x = cfTau) || decide (x * x = cfZ * cfTau)) = true
    )
    ∧ (cfQE.check = true ∧ cfQE.orderCertificate = 16)
    ∧ ((cfEgens.all fun x => cfQR.sift x 0 && QP45.sift x 0) = true ∧
      (elemsT cfQE).all (fun x => decide (x * x = 1)) = true ∧ cfQE.sift cfZ 0 = true ∧
      cfQE.sift cfTau 0 = true
    )
    ∧ (((elemsT cfQR).filter fun x => QP45.sift x 0).all (fun x =>
      !decide (x * x = 1) || cfQE.sift x 0 || decide ((((elemsT cfQR).filter fun x =>
        QP45.sift x 0).filter fun y => decide (y * y = 1) && decide (y * x = x * y)).length <
          16)) = true
    )
    ∧ ((elemsT QA45).all (fun x => !(cfEgens.all fun e =>
      decide (e * x = x * e)) || cfQE.sift x 0) = true
    )
    ∧ ((cfOz.all fun p => decide (p.2⁻¹ * cfZ * p.2 = p.1) && QA45.sift p.2 0 &&
        (cfEgens.all fun e => cfQE.sift (p.2 * e * p.2⁻¹) 0)) = true ∧
      (cfOzt.all fun p => decide (p.2⁻¹ * (cfZ * cfTau) * p.2 = p.1) && QA45.sift p.2 0 &&
        (cfEgens.all fun e => cfQE.sift (p.2 * e * p.2⁻¹) 0)) = true ∧
      (cfOz.map Prod.fst).Nodup ∧ (cfOzt.map Prod.fst).Nodup ∧
      (elemsT cfQE).all (fun w => decide (w = 1) || decide (w ∈ cfOz.map Prod.fst) ||
        decide (w ∈ cfOzt.map Prod.fst)) = true ∧
      (cfOz.all fun p => cfQE.sift p.1 0) = true ∧ (cfOzt.all fun p => cfQE.sift p.1 0) = true
    )
    ∧ (((cfOz.all fun p => decide (p.1.support.card = 40)) = true ∧
        (cfOzt.all fun p => decide (p.1.support.card = 32)) = true ∧ cfZ.support.card = 40 ∧
        (cfZ * cfTau).support.card = 32) ∧
      (cfFgens.all fun x => cfEgens.all fun e => cfQE.sift (x * e * x⁻¹) 0) = true ∧
      cfOzKd * cfOztKe * cfZ = cfZ * (cfOzKd * cfOztKe) ∧ orderIs (cfOzKd * cfOztKe) 3 = true
    )
    ∧ ((cfEgens.all fun x => decide (x ∈ cfOzt.map Prod.fst)) = true)
    ∧ ((elemsT cfQR).all (fun w => !decide (w * w = 1) || QP45.sift w 0 ||
      (fun y => decide (y ∈ cfCls1C)) w ||
      (elemsT cfQR).any (fun r => !decide (w * (r * w * r⁻¹) = r * w * r⁻¹ * w)) ||
      decide (((elemsT cfQR).filter fun y => decide (y * y = 1) &&
        !(fun y => decide (y ∈ cfCls1C)) y &&
        (elemsT cfQR).all fun r => decide (y * (r * w * r⁻¹) = r * w * r⁻¹ * y)).length < 16)) =
        true
    )
    ∧ ((elemsT cfQE).all (fun e => decide (e * s045 * e⁻¹ * s045⁻¹ = 1) ||
        decide (e * s045 * e⁻¹ * s045⁻¹ = cfCE)) = true ∧ s045 * s045 = 1 ∧
      cfQE.sift cfE1 0 = true ∧ cfE1 * s045 * cfE1⁻¹ * s045⁻¹ = cfCE ∧ cfCE * cfCE = 1 ∧
      cfCE ≠ 1 ∧ cfQR.sift cfEe 0 = true ∧ QP45.sift cfEe 0 = true ∧
      cfEn1 * cfEn2 * cfEn1⁻¹ * cfEn2⁻¹ = cfEe ∧ cfEe * cfEe = 1 ∧
      (cfEgens.all fun g => decide (g * cfEe = cfEe * g)) = false ∧ QA45.sift cfEn1 0 = true ∧
      QA45.sift cfEn2 0 = true ∧ (cfEgens.all fun e => cfQE.sift (cfEn1 * e * cfEn1⁻¹) 0) = true ∧
      (cfEgens.all fun e => cfQE.sift (cfEn2 * e * cfEn2⁻¹) 0) = true
    )
    ∧ ((elemsT QA45).all (fun y => !decide (y * y = 1) || QP45.sift y 0 ||
      decide (y ∈ cfCls1C) || decide (y ∈ cfCls2C)) = true ∧
      ((elemsT cfQR).filter fun x => QP45.sift x 0).length = 64 ∧
      ((elemsT cfQR).filter fun x => QP45.sift x 0).all (fun y => !decide (y * y = 1) ||
        decide (y = 1) || decide (y ∈ cfICls1C) || decide (y ∈ cfICls2C)) = true
    )
    ∧ ((elemsT cfQR).all (fun x => !decide (x * x = 1) || decide (x = 1) ||
      decide (x ∈ cfB) || decide (((elemsT cfQR).filter fun y => decide (y * y = 1) &&
        decide (y * x = x * y)).length < 32)) = true
    ) := by
  obtain ⟨hA, h23a⟩ := all_and scanA
  obtain ⟨hA, h17⟩ := all_and hA
  obtain ⟨h0, h5⟩ := all_and hA
  refine ⟨h0, comm2009K, ?_, valid_of _ _ _ _ _ _ qh2009K, valid_of _ _ _ _ _ _ qr2009K, h5, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, valid_of _ _ _ _ _ _ qe2009K, ?_, ?_, h17, ?_, ⟨?_, ?_⟩, ?_, ?_,
    ?_, ⟨h23a, sylP2009⟩, ?_⟩
  · simp only [elemsT_eq_elemsV, sift_eq_siftP]
    exact z2009K
  · simp only [elemsT_eq_elemsV, sift_eq_siftP]
    exact r2009K
  · obtain ⟨d1, d2, d3⟩ := card2009K
    refine ⟨?_, ?_, orbTZ_cert, ?_, orbZ_cert⟩
    · simp only [elemsT_eq_elemsV, sift_eq_siftP]
      exact d1
    · rw [elemsT_eq_elemsV]
      exact d2
    · rw [elemsT_eq_elemsV]
      exact d3
  · simp only [sift_eq_siftP]
    exact qeq2009K
  · simp only [sift_eq_siftP]
    exact elt2009K
  · obtain ⟨a1, a2, a3, a4, a5, a6⟩ := qd2009K
    exact ⟨check_certificate_of _ _ _ _ _ a1, (orderCertificate_eq_orderV _).trans a2,
      check_certificate_of _ _ _ _ _ a3, (orderCertificate_eq_orderV _).trans a4,
      check_certificate_of _ _ _ _ _ a5, (orderCertificate_eq_orderV _).trans a6⟩
  · simp only [elemsT_eq_elemsV, sift_eq_siftP]
    exact d2009K
  · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := qf2009K
    exact ⟨check_certificate_of _ _ _ _ _ a1, (orderCertificate_eq_orderV _).trans a2,
      check_certificate_of _ _ _ _ _ a3, (orderCertificate_eq_orderV _).trans a4,
      check_certificate_of _ _ _ _ _ a5, (orderCertificate_eq_orderV _).trans a6,
      check_certificate_of _ _ _ _ _ a7, (orderCertificate_eq_orderV _).trans a8⟩
  · simp only [elemsT_eq_elemsV, sift_eq_siftP]
    exact f2009K
  · simp only [elemsT_eq_elemsV, sift_eq_siftP, siftP_QP45]
    exact e2009K
  · simp only [elemsT_eq_elemsV, sift_eq_siftP, siftP_QP45]
    exact eUniq2009K
  · simp only [elemsT_eq_elemsV, sift_eq_siftP, siftP_QA45]
    exact orb2009K
  · exact suppE
  · simp only [sift_eq_siftP]
    exact nz2009K
  · exact esub2009K
  · simp only [elemsT_eq_elemsV, sift_eq_siftP, ← cls1P_eq, siftP_QP45]
    have h := normal_all
    unfold normT at h
    simp only [all_dedup_map, any_dedup_map] at h
    exact h
  · simp only [elemsT_eq_elemsV, sift_eq_siftP, siftP_QP45, siftP_QA45]
    exact misc2009K
  · rw [elemsT_eq_elemsV]
    exact e32_2009K

end CertificateChecks.KernelCatFacts
