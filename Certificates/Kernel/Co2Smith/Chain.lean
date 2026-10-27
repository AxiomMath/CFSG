module

public import Certificates.Kernel.Co2Smith.Psi
public import CFSG.Certificates.Kernel.Spor.RawSound
public import CFSG.Certificates.Kernel.Spor.StrongOfSound
public import CFSG.Certificates.Kernel.Spor.RawTreeDefs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co1F2 CFSG.KC.Co2Smith CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.Sporadic.Co2Smith.Native CFSG.Sporadic.Co2Cert CFSG.Monster.B.Co2.Native
open CFSG.Certificates.Native

theorem foldl_strongOf (n : Nat) : ∀ (ds : List (List Int)) (A : Array (Array Nat)),
    (ds.foldl (fun p w => (p.1.push (wordA n p.1 p.2 w), p.2.push (invCand n (wordA n p.1 p.2 w))))
      (A, A.map (invCand n))).1 =
      ds.foldl (fun S w => S.push (wordA n S (rawInvs n S) w)) A
  | [], A => rfl
  | w :: ds, A => by
    have h := foldl_strongOf n ds (A.push (wordA n A (A.map (invCand n)) w))
    rw [Array.map_push] at h
    exact h

theorem range_map_drop (W : Array (List Int)) (k : Nat) :
    (List.range (W.size - k)).map (fun j => W[k + j]!) = W.toList.drop k := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, List.getElem_drop, Array.getElem_toList]
    rw [getElem!_pos W (k + i) (by simp at h1; omega)]

theorem extend_eq (O : Array (Array Nat)) (W : Array (List Int)) :
    glExtend O W = (CFSG.YGroups.ModelNative.strongOf 2300 O (W.toList.drop O.size).toArray).1 := by
  unfold glExtend CFSG.YGroups.ModelNative.strongOf
  rw [List.foldl_toArray]
  have h := foldl_strongOf 2300 (W.toList.drop O.size) O
  simp only at h ⊢
  rw [h, ← range_map_drop, List.foldl_map]

theorem chainBinds_of {ws : List (List Nat)} {base : List Nat} {W : Array (List Int)}
    {kS nb BP : Nat} {PS PSI G : Nat → Nat} {D : List (List Int)}
    (hw : ∀ i < ws.length, ∀ k ∈ ws[i]!, k < 22)
    (hG : ∀ i < ws.length,
      bindVK (KernelSporSch.Co2M.PV 0) (G i) (trK 22 (wK LP ws[i]!)) = true)
    (hO : ∀ i < ws.length,
      pcomp 2300 12 (mask 12) (pcomp 2300 12 (mask 12) CK (G i)) CIK = PS i)
    (hD : W.toList.drop ws.length = D)
    (hbs : base.toArray.size = nb) (hbt : ∀ t < nb, base.toArray[t]! = pg 12 (mask 12) BP t)
    (hh : headK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) PS PSI kS ws.length D nb BP = true) :
    Binds 2300 12 PS kS nb BP (glExtend (glOrig ws) W) base.toArray ∧
      ∀ i < ws.length, glPsiArr (glR ws[i]!) = unpack 2300 12 (PS i) := by
  have hR : ∀ i < ws.length, glR ws[i]! = unpackR 22 (wK LP ws[i]!) := fun i hi => glR_eq (hw i hi)
  have hpsi : ∀ i < ws.length, glPsiArr (glR ws[i]!) = unpack 2300 12 (PS i) := by
    intro i hi
    rw [hR i hi, psi_eq (hG i hi), hO i hi]
  have hOs : (glOrig ws).size = ws.length := by simp [glOrig]
  have hOget : ∀ j < ws.length, (glOrig ws)[j]! = unpack 2300 12 (PS j) := by
    intro j hj
    rw [← hpsi j hj]
    unfold glOrig
    rw [getElem!_pos _ j (by simpa using hj), List.getElem_toArray, List.getElem_map,
      getElem!_pos ws j hj]
  have hst := strongOf_bind (O := glOrig ws) ⟨hOs, hOget⟩ hh
  have hS : glExtend (glOrig ws) W =
      (CFSG.YGroups.ModelNative.strongOf 2300 (glOrig ws) D.toArray).1 := by
    rw [extend_eq, hOs, hD]
  refine ⟨?_, hpsi⟩
  rw [hS]
  exact ⟨by norm_num, by norm_num, by norm_num, hst.1, hst.2, hbs, hbt⟩

theorem chainOK_of {ws : List (List Nat)} {base : List Nat} {W : Array (List Int)}
    {ord kS nb BP NS CH : Nat} {PS PSI LR TR TRI G : Nat → Nat} {D : List (List Int)}
    (hw : ∀ i < ws.length, ∀ k ∈ ws[i]!, k < 22)
    (hG : ∀ i < ws.length,
      bindVK (KernelSporSch.Co2M.PV 0) (G i) (trK 22 (wK LP ws[i]!)) = true)
    (hO : ∀ i < ws.length,
      pcomp 2300 12 (mask 12) (pcomp 2300 12 (mask 12) CK (G i)) CIK = PS i)
    (hD : W.toList.drop ws.length = D)
    (hW : W = CFSG.Sporadic.Schreier.Co3.Native.wordsArr ws.length kS D)
    (hbs : base.toArray.size = nb) (hbt : ∀ t < nb, base.toArray[t]! = pg 12 (mask 12) BP t)
    (hh : headK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) PS PSI kS ws.length D nb BP = true)
    (hl : LevelsOK 2300 12 PS PSI LR TR TRI kS nb BP)
    (hNS : 2300 ≤ NS * CH)
    (hs : ∀ i < nb, ∀ s < NS, schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) PS PSI LR TR TRI
      kS BP nb i (stepsAt 2300 12 PS kS BP i) (s * CH) CH = true)
    (hord : ((List.range nb).map fun i => rcnt (LR i)).prod = ord) :
    glChainOK ws base W ord = true := by
  have hR : ∀ i < ws.length, glR ws[i]! = unpackR 22 (wK LP ws[i]!) := fun i hi => glR_eq (hw i hi)
  obtain ⟨hb, hpsi⟩ := chainBinds_of hw hG hO hD hbs hbt hh
  have hhd := Orb.rawHeadOK_of hb hh
  have hp : allN kS (fun j => permOK 2300 12 (mask 12) (2300 * 12) (PS j) (PSI j)) = true := by
    have h := hh
    unfold headK at h
    simp only [Orb.bAnd_eq, Bool.and_eq_true] at h
    exact h.2.2.2.2.1
  unfold glChainOK
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨⟨⟨⟨fun w hw' => ?_, hhd.1⟩, ?_⟩, ?_⟩, ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw'
    rw [← getElem!_pos ws i hi, hR i hi]
    exact permOK_of (hG i hi)
  · rw [CFSG.Monster.B.Co2.allLt_iff]
    intro i hi
    rw [hpsi i hi, hb.2.2.2.2.1 i (by have := hhd.1; rw [hb.2.2.2.1] at this; omega)]
    exact eqA_self _
  · have h := rawChainK_sound (chunks := 1) hb hh hl hNS hs
    rw [← hW] at h
    exact h
  · rw [rawOrbitSizesK_sound hb hp hl, hord]

end CertificateChecks.KernelCo2Smith
