module

public import Certificates.Kernel.Co1FiveComp.Chk
public import Certificates.Kernel.Co1FiveK.GlueB
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1FiveBase
public import CFSG.Certificates.Kernel.Co1Seven.CenSound
public import Certificates.Certificate3024
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1Cen2BData
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1EndData

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1FiveComp

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Schreier
  CFSG.Sporadic.Co1.InvNative CFSG.Sporadic.Co1.TwoBNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1F Timmesfeld.Co1Five Timmesfeld.Co1FiveComp
open CertificateChecks.KernelCo1FiveK
open CFSG.KS.SporSch.M24 (mul_unpackW eqU_of gtBFS_of_K gensArr bfsTree word_eq_wordWK eqU wordWK)
open CFSG.KC.Co1B (mulWK)
open Timmesfeld.Co1SevenPerfect (encW)

local notation "U" => CFSG.KS.Raw.unpack 24 24
@[expose] noncomputable def isL : List (Array Nat) := (List.range 137).map fun i => U (D.MI i)

local notation "IS" => isL

theorem dag_eq5 : gDag CFSG.Sporadic.Co1Schreier.Native.aR CFSG.Sporadic.Co1Schreier.Native.bR =
    (rs, IS, true) := gDag_eq

theorem gRows_eq : gRows = rs := congrArg Prod.fst dag_eq5

theorem part2 : a0Row rs (repA.getD 1 0) = CFSG.HardMathSupport.Dickson.I271.TabCo1.repD0 := by
  have h := CFSG.KS.Raw.toArray_eq_of_bindListK c10145kD0
  rw [Array.toArray_toList] at h
  rw [a0Row_rs]
  exact h.symm

theorem part3_mem : ∀ j < 3, rowAt rs (idxD.getD j 0) ∈ (qTree rs).pts := by
  intro j hj
  have h := CFSG.KS.SporSch.M24.MatL.allN_iff.1 c10145kMem j hj
  obtain ⟨i, hi, he⟩ := List.any_eq_true.1 h
  have hi' : i < QT.N := by
    rw [qN]
    exact List.mem_range.1 hi
  have hs : i < (qTree rs).pts.size := by
    rw [size_qTree]
    exact hi'
  rw [dK_rs hj, ← Nat.eq_of_beq_eq_true he, ← pts_qTree hi', getElem!_pos _ i hs]
  exact Array.getElem_mem hs

theorem part3 :
    (List.range 3).all (fun j => (qTree rs).pts.contains (rowAt rs (idxD.getD j 0))) = true := by
  rw [List.all_eq_true]
  intro j hj
  exact Array.contains_iff_mem.2 (part3_mem j (List.mem_range.1 hj))

theorem word_U {w : List Int} (h1 : CFSG.KS.SporSch.M24.lettersK 137 (encW w) = true)
    (h2 : CFSG.Sporadic.Co1Schreier.Native.decWord (encW w) = w) :
    CFSG.Sporadic.Co1Schreier.Native.word rs IS w = U (wordWK D.M D.MI (encW w)) := by
  have e := word_eq_wordWK (M := D.M) (MI := D.MI) h1
  rw [h2] at e
  exact e

theorem compKAt_word {i : Nat} (h : compKAt D.M D.MI B1 B2 i = true) :
    CFSG.Sporadic.Co1Schreier.Native.word rs IS sWords[i]! = U (SG D.M D.MI i) := by
  unfold compKAt at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact word_U h.1.1.1.1.1.1.2 h.1.1.1.1.2

theorem hB1 : a0Row rs (repA.getD 1 0) = U B1 := a0Row_rs _

theorem hB2 : a0Row rs (repB.getD 1 0) = U B2 := a0Row_rs _

theorem perfAt_K {i : Nat} (h : compKAt D.M D.MI B1 B2 i = true) :
    (decide ((sIdx[i]!).1 < 5) && decide ((sIdx[i]!).2 < 5) && perfAt rs IS i) = true := by
  have hw := compKAt_word h
  unfold compKAt at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hj, hk⟩, hnz⟩, -⟩, hl2⟩, -⟩, hd2⟩, hc1⟩, hc2⟩, he⟩ := h
  have hcw := word_U hl2 hd2
  unfold commW5 at hcw he
  unfold perfAt
  dsimp only
  rw [hw, hcw, hj, hk, hnz, hB1, hB2, mul_unpackW, mul_unpackW, mul_unpackW, mul_unpackW]
  unfold SG
  rw [Nat.eq_of_beq_eq_true hc1, Nat.eq_of_beq_eq_true hc2, ← Nat.eq_of_beq_eq_true he]
  simp

theorem sRows_eq : (sRows rs IS).toArray = gensArr 5 (SG D.M D.MI) := by
  rw [← toArray_gensArr]
  congr 1
  unfold sRows
  have e : sWords.toList = (List.range 5).map fun i => sWords[i]! := by rfl
  rw [e, List.map_map]
  apply List.map_congr_left
  intro i hi
  rw [Function.comp_apply]
  exact compKAt_word (CFSG.KS.SporSch.M24.MatL.allN_iff.1 c10145kPerf i (List.mem_range.1 hi))

theorem a5OK_true : a5OK rs IS = true := by
  obtain ⟨hT, hok⟩ := gtBFS_of_K c10145kST
  unfold a5OK
  rw [sRows_eq, hT, Bool.and_eq_true, Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨hok, ?_⟩, fun i hi =>
    perfAt_K (CFSG.KS.SporSch.M24.MatL.allN_iff.1 c10145kPerf i (List.mem_range.1 hi))⟩
  simp [bfsTree, Nat.eq_of_beq_eq_true c10145kSTN]

theorem comm_of_relIndex_five {G : Type*} [Group G] {A Q : Subgroup G} (hAQ : A ≤ Q)
    (hidx : A.relIndex Q = 5) (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) {x r t : G} (hx : x ∈ A)
    (hr : r ∈ Q) (hrA : r ∉ A) (hxr : x * r = r * x) (ht : t ∈ Q) : x * t = t * x := by
  have hAH : A ≤ Q ⊓ Subgroup.centralizer {x} := fun a ha =>
    ⟨hAQ ha, Subgroup.mem_centralizer_singleton_iff.2 (hA a ha x hx)⟩
  have hm := Subgroup.relIndex_mul_relIndex A (Q ⊓ Subgroup.centralizer {x}) Q hAH inf_le_left
  rw [hidx] at hm
  have hdvd : (Q ⊓ Subgroup.centralizer {x}).relIndex Q ∣ 5 :=
    ⟨A.relIndex (Q ⊓ Subgroup.centralizer {x}), by rw [← hm, mul_comm]⟩
  rcases (Nat.dvd_prime (by norm_num)).1 hdvd with h1 | h5
  · exact (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.relIndex_eq_one.1 h1 ht).2).symm
  · rw [h5] at hm
    have h1 : A.relIndex (Q ⊓ Subgroup.centralizer {x}) = 1 := by omega
    exact absurd (Subgroup.relIndex_eq_one.1 h1
      ⟨hr, Subgroup.mem_centralizer_singleton_iff.2 hxr.symm⟩) hrA

section Cen

theorem hG5 : GOK := globalOK_eq_true

theorem A0_le_Q5 : A0 hG5 ≤ Qsub := by
  have hG := hG5
  have hflag := (globalOK_parts hG).1
  obtain ⟨hok, -, -⟩ := qOK_parts (globalOK_parts hG).2.1
  have : Finite ↥GA := Nat.finite_of_card_ne_zero (by rw [card_GA_eq]; norm_num)
  have hmem : ∀ j < 3, rowAt gRows (idxD.getD j 0) ∈ (qTree gRows).pts := by
    rw [gRows_eq]
    exact part3_mem
  have hd : ∀ i : Fin 3, dE i ∈ Qsub := by
    intro i
    obtain ⟨k, hk, hkrow⟩ := Array.getElem_of_mem (hmem i.val i.2)
    refine CFSG.Sporadic.Co1Block.mem_closure_of_prodTree μG μG_injective hok qG (qG_rep hG)
      (i := k) hk ?_
    rw [μG_apply, getElem!_pos _ k hk, hkrow]
    exact (rep_gE hflag _).symm
  rintro _ ⟨a, rfl⟩
  have ea : a = Multiplicative.ofAdd (Multiplicative.toAdd a) := rfl
  rw [ea, φ_apply, vecProd_eq]
  exact Qsub.mul_mem (Qsub.pow_mem (hd 0) _)
    (Qsub.mul_mem (Qsub.pow_mem (hd 1) _) (Qsub.pow_mem (hd 2) _))

theorem relIndex_A0_Q5 : (A0 hG5).relIndex Qsub = 5 := by
  have h := Subgroup.relIndex_mul_card (A0 hG5) Qsub
  rw [inf_eq_left.2 A0_le_Q5, card_A0 hG5, card_Qsub hG5] at h
  omega

theorem cenOK_true : cenOK gRows = true := by
  have hG := hG5
  have hflag := (globalOK_parts hG).1
  obtain ⟨hok, -, -⟩ := qOK_parts (globalOK_parts hG).2.1
  have : Finite ↥GA := Nat.finite_of_card_ne_zero (by rw [card_GA_eq]; norm_num)
  obtain ⟨f, hfrow, -, hfeq⟩ :=
    CFSG.Sporadic.Co1Block.prodTree_closure_eq μG μG_injective hok qG (qG_rep hG)
  have eQ : idxQ = [67, 68, 69] := by with_unfolding_all rfl
  have h3 : (qGens gRows).toArray.size = 3 := by simp [qGens, eQ]
  have hqt : qG 1 = gE 68 := by
    unfold qG
    rw [eQ]
    rfl
  have htQ : gE 68 ∈ Qsub := by
    rw [← hqt]
    exact Subgroup.subset_closure ⟨1, by rw [Set.mem_setOf_eq, h3]; norm_num, rfl⟩
  have htrep : MRep (U (QM 1)) ((gE 68 : ↥GA) : GL24) := by
    have h := rep_gE hflag 68
    rw [gRows_eq, rowAt_rs (by norm_num)] at h
    exact h
  have hcnt : ((List.range 125).filter fun k =>
      eqU (mulWK (AT k) (QM 1)) (mulWK (QM 1) (AT k))).length ≤ 5 := by
    have h := c10145kCen
    unfold cenK at h
    exact Nat.le_of_ble_eq_true h
  have hpt : ∀ j (hj : j < (qTree gRows).pts.size), (qTree gRows).pts[j] = U (QT.P j) := by
    rw [gRows_eq]
    intro j hj
    have hj' : j < QT.N := by
      rw [← size_qTree]
      exact hj
    rw [← getElem!_pos _ j hj]
    exact pts_qTree hj'
  unfold cenOK
  simp only [Array.all_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  intro i hi
  have hq : MRep (qTree gRows).pts[i] ((f i : ↥GA) : GL24) := by
    unfold MRep
    rw [← μG_apply, hfrow i hi, getElem!_pos _ i hi]
  have hqv : validRows (qTree gRows).pts[i] = true := by
    rw [hpt i hi]
    exact CFSG.KC.Co1End.validRows_unpack _
  by_cases hc : ((List.range 125).map (a0Row gRows)).contains (qTree gRows).pts[i] = true
  · exact Or.inl hc
  right
  have hrA : f i ∉ A0 hG := by
    rintro ⟨a, ha⟩
    apply hc
    have hk := idx3_lt (Multiplicative.toAdd a)
    have hrk := rep_a0Row hG hk
    rw [vec3_idx3, ofAdd_toAdd, ha] at hrk
    rw [rows_eq_of_mrep hqv (validRows_a0Row hG _) hq hrk]
    exact List.contains_iff_mem.2 (List.mem_map.2 ⟨_, List.mem_range.2 hk, rfl⟩)
  have hfi : f i ∈ Qsub := by
    have hr : f i ∈ (Subgroup.closure (qG '' {l | l < (qGens gRows).toArray.size}) : Set ↥GA) := by
      rw [hfeq]
      exact ⟨i, hi, rfl⟩
    exact hr
  rw [List.filter_map, List.length_map, ← List.countP_eq_length_filter]
  refine le_trans ?_ hcnt
  rw [← List.countP_eq_length_filter]
  apply List.countP_mono_left
  intro k hk hcomm
  have hk' := List.mem_range.1 hk
  simp only [Function.comp_apply, beq_iff_eq] at hcomm
  have hx := rep_a0Row hG hk'
  have hxr :
      φ hG (Multiplicative.ofAdd (vec3 k)) * f i = f i * φ hG (Multiplicative.ofAdd (vec3 k)) := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    have h1 := hx.mul hq
    have h2 := hq.mul hx
    rw [← hcomm] at h2
    exact h1.eq h2
  have hxt := comm_of_relIndex_five A0_le_Q5 relIndex_A0_Q5 (A0_comm hG) ⟨_, rfl⟩ hfi hrA hxr htQ
  have hqtv : validRows (U (QM 1)) = true := CFSG.KC.Co1End.validRows_unpack _
  have he : Native.mul (a0Row gRows k) (U (QM 1)) = Native.mul (U (QM 1)) (a0Row gRows k) := by
    refine rows_eq_of_mrep (validRows_mul' (validRows_a0Row hG k) hqtv)
      (validRows_mul' hqtv (validRows_a0Row hG k)) (hx.mul htrep) ?_
    have e : ((φ hG (Multiplicative.ofAdd (vec3 k)) : ↥GA) : GL24) * ((gE 68 : ↥GA) : GL24) =
        ((gE 68 : ↥GA) : GL24) * ((φ hG (Multiplicative.ofAdd (vec3 k)) : ↥GA) : GL24) := by
      rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hxt]
    rw [e]
    exact htrep.mul hx
  rw [gRows_eq, a0Row_rs, ← AT_a0K hk', mul_unpackW, mul_unpackW] at he
  exact eqU_of he

theorem compOK_eq_true :
    compOK CFSG.Sporadic.Co1Schreier.Native.aR CFSG.Sporadic.Co1Schreier.Native.bR = true := by
  have h4 := cenOK_true
  rw [gRows_eq] at h4
  unfold compOK
  dsimp only
  rw [dag_eq5]
  dsimp only
  rw [part2, beq_self_eq_true, part3, h4, a5OK_true]
  rfl

end Cen

end CertificateChecks.KernelCo1FiveComp

end
