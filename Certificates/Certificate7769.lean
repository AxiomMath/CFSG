module

public import CFSG.Milestones.ASVolI.F48.Rest.U52Inputs
import Certificates.Kernel.U52.GlueX
import Certificates.Kernel.U52.ChainSub
import CFSG.Certificates.Kernel.Misc.PtOrbFSound
import CFSG.Certificates.Kernel.Spor.RawSiftK
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.LieType.BorelTits.CompleteFlag

set_option maxRecDepth 400000

namespace CertificateChecks.Batch7769

open CFSG.ASVolI CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.WordF CFSG.KC.PtOrb
  CertificateChecks.KernelU52 CertificateChecks.KernelU52G

noncomputable def qP2 (j : Nat) : Nat := LP (j + j / 2)

noncomputable def hAP (j : Nat) : Nat :=
  evFK 462 9 (mask 9) (pidn 462 9) CX.S CX.SI (burnsideF48t_u52HA.getD j [])

noncomputable def hBP (j : Nat) : Nat :=
  evFK 462 9 (mask 9) (pidn 462 9) CX.S CX.SI (burnsideF48t_u52HB.getD j [])

noncomputable def qA (j i : Nat) : Nat := nIf(Nat.blt i 3, LP i, hAP j)

noncomputable def qB (j i : Nat) : Nat := nIf(Nat.blt i 3, qP2 i, hBP j)

abbrev R : Nat := 40

theorem siPerm : allN 6 (fun j => permOK 462 9 (mask 9) (462 * 9) (CX.SI j) (CX.S j)) = true := by
  quickRfl

theorem hPerm : allN 2 (fun j => permOK 462 9 (mask 9) (462 * 9) (hAP j)
    (pinvS 462 9 (mask 9) (hAP j))) = true ∧
    allN 2 (fun j => permOK 462 9 (mask 9) (462 * 9) (hBP j)
      (pinvS 462 9 (mask 9) (hBP j))) = true :=
  ⟨by quickRfl, by quickRfl⟩

theorem cX0 : orbClosed (fun j => pg 9 (mask 9) (CX.S j)) 6 462 R 0 = true := by quickRfl
theorem cX1 : orbClosed (fun j => pg 9 (mask 9) (CX.S j)) 6 462 R 165 = true := by quickRfl
theorem cP1a : orbClosed (fun j => pg 9 (mask 9) (LP j)) 3 462 R 165 = true := by quickRfl
theorem cP1b : orbClosed (fun j => pg 9 (mask 9) (LP j)) 3 462 R 1 = true := by quickRfl
theorem cP1c : orbClosed (fun j => pg 9 (mask 9) (LP j)) 3 462 R 15 = true := by quickRfl
theorem cP2a : orbClosed (fun j => pg 9 (mask 9) (qP2 j)) 3 462 R 166 = true := by quickRfl
theorem cP2b : orbClosed (fun j => pg 9 (mask 9) (qP2 j)) 3 462 R 175 = true := by quickRfl
theorem cA : ∀ j < 2, orbClosed (fun i => pg 9 (mask 9) (qA j i)) 4 462 R 0 = true := by
  intro j hj
  interval_cases j <;> quickRfl
theorem cB : ∀ j < 2, orbClosed (fun i => pg 9 (mask 9) (qB j i)) 4 462 R 165 = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem vX0 : bitsIs (closeF (fun j => pg 9 (mask 9) (CX.S j)) 6 462 R (Nat.shiftLeft 1 0)) 462
    (fun y => Nat.blt y 165) = true := by quickRfl
theorem vX1 : bitsIs (closeF (fun j => pg 9 (mask 9) (CX.S j)) 6 462 R (Nat.shiftLeft 1 165)) 462
    (fun y => Nat.ble 165 y) = true := by quickRfl
theorem vP1a : popIs (closeF (fun j => pg 9 (mask 9) (LP j)) 3 462 R (Nat.shiftLeft 1 165)) 462 9 =
    true := by quickRfl
theorem vP1b : popIs (closeF (fun j => pg 9 (mask 9) (LP j)) 3 462 R (Nat.shiftLeft 1 1)) 462 128 =
    true := by quickRfl
theorem vP1c : popIs (closeF (fun j => pg 9 (mask 9) (LP j)) 3 462 R (Nat.shiftLeft 1 15)) 462 36 =
    true := by quickRfl
theorem vP1d : bitsIs (Nat.lor (closeF (fun j => pg 9 (mask 9) (LP j)) 3 462 R (Nat.shiftLeft 1 1))
    (closeF (fun j => pg 9 (mask 9) (LP j)) 3 462 R (Nat.shiftLeft 1 15))) 462
    (fun y => bAnd(Nat.blt 0 y, Nat.blt y 165)) = true := by quickRfl
theorem vP2a : popIs (closeF (fun j => pg 9 (mask 9) (qP2 j)) 3 462 R (Nat.shiftLeft 1 166)) 462 40 =
    true := by quickRfl
theorem vP2b : popIs (closeF (fun j => pg 9 (mask 9) (qP2 j)) 3 462 R (Nat.shiftLeft 1 175)) 462
    256 = true := by quickRfl
theorem vP2c : bitsIs (Nat.lor (closeF (fun j => pg 9 (mask 9) (qP2 j)) 3 462 R (Nat.shiftLeft 1 166))
    (closeF (fun j => pg 9 (mask 9) (qP2 j)) 3 462 R (Nat.shiftLeft 1 175))) 462
    (fun y => Nat.blt 165 y) = true := by quickRfl
theorem vA : ∀ j < 2, bitsIs (closeF (fun i => pg 9 (mask 9) (qA j i)) 4 462 R (Nat.shiftLeft 1 0))
    462 (fun y => Nat.blt y 165) = true := by
  intro j hj
  interval_cases j <;> quickRfl
theorem vB : ∀ j < 2, bitsIs (closeF (fun i => pg 9 (mask 9) (qB j i)) 4 462 R (Nat.shiftLeft 1 165))
    462 (fun y => Nat.ble 165 y) = true := by
  intro j hj
  interval_cases j <;> quickRfl
theorem vH : Nat.beq (pg 9 (mask 9) (hAP 0) 0) 1 = true ∧ Nat.beq (pg 9 (mask 9) (hAP 1) 0) 15 = true ∧
    Nat.beq (pg 9 (mask 9) (hBP 0) 165) 166 = true ∧
    Nat.beq (pg 9 (mask 9) (hBP 1) 165) 175 = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

private theorem bS0 : allN 4 (fun j => Nat.beq
    (evFK 462 9 (mask 9) (pidn 462 9) LP LPI (burnsideF48t_u52SW.getD j [])) (CS0.S j)) = true := by
  quickRfl

private theorem kS0 : allN 2 (fun i => burnsideF48t_u52SW.all fun w =>
    siftK 462 9 (mask 9) (462 * 9) (pidn 462 9) CS0.LR CS0.TRI CS0.BP 3 0
      (pcomp 462 9 (mask 9) (pcomp 462 9 (mask 9) (LP i)
        (evFK 462 9 (mask 9) (pidn 462 9) LP LPI w)) (LPI i))) = true := by
  quickRfl

theorem rSI : ∀ j < 6, Rng 462 9 (CX.SI j) := fun j hj => rng_of_permOK (allN_spec siPerm j hj)

theorem hA_eq {j : Nat} (hj : j < 2) :
    (burnsideF48t_u52HArr burnsideF48t_u52HA)[j]! = unpack 462 9 (hAP j) := by
  simp only [burnsideF48t_u52HArr]
  rw [getD_map_toArray _ _ [] (by simpa [burnsideF48t_u52HA] using hj)]
  exact (evA_unpack (k := 6) (by norm_num) (by norm_num) g_eq gi_eq
    (fun i hi x hx => ⟨rS i hi x hx, rSI i hi x hx⟩) _).1

theorem hB_eq {j : Nat} (hj : j < 2) :
    (burnsideF48t_u52HArr burnsideF48t_u52HB)[j]! = unpack 462 9 (hBP j) := by
  simp only [burnsideF48t_u52HArr]
  rw [getD_map_toArray _ _ [] (by simpa [burnsideF48t_u52HB] using hj)]
  exact (evA_unpack (k := 6) (by norm_num) (by norm_num) g_eq gi_eq
    (fun i hi x hx => ⟨rS i hi x hx, rSI i hi x hx⟩) _).1

theorem hArr_size : (burnsideF48t_u52HArr burnsideF48t_u52HA).size = 2 ∧
    (burnsideF48t_u52HArr burnsideF48t_u52HB).size = 2 := by
  simp [burnsideF48t_u52HArr, burnsideF48t_u52HA, burnsideF48t_u52HB]

theorem gX : (burnsideF48t_u52Gens ()).size = 6 := by decide +kernel

theorem p1_eq : ∀ j < 3, burnsideF48t_u52P1Arr[j]! = unpack 462 9 (LP j) := by
  intro j hj
  rw [← l_eq j (by omega)]
  interval_cases j <;> rfl

theorem p2_eq : ∀ j < 3, burnsideF48t_u52P2Arr[j]! = unpack 462 9 (qP2 j) := by
  intro j hj
  rw [qP2, ← l_eq (j + j / 2) (by omega)]
  interval_cases j <;> rfl

theorem pP1 : ∀ j < 3, permOK 462 9 (mask 9) (462 * 9) (LP j) (LPI j) = true :=
  fun j hj => allN_spec lpPerm j (by omega)

theorem pP2 : ∀ j < 3, permOK 462 9 (mask 9) (462 * 9) (qP2 j) (LPI (j + j / 2)) = true :=
  fun j hj => allN_spec lpPerm _ (by omega)

theorem push_last {a : Array (Array Nat)} (ha : a.size = 3) (t : Array Nat) : (a.push t)[3]! = t := by
  rw [getElem!_pos _ 3 (by rw [Array.size_push, ha]; norm_num), Array.getElem_push]
  simp [ha]

theorem pushA_eq {j : Nat} (hj : j < 2) : ∀ i < 4,
    (burnsideF48t_u52P1Arr.push (burnsideF48t_u52HArr burnsideF48t_u52HA)[j]!)[i]! =
      unpack 462 9 (qA j i) := by
  intro i hi
  interval_cases i
  · exact p1_eq 0 (by norm_num)
  · exact p1_eq 1 (by norm_num)
  · exact p1_eq 2 (by norm_num)
  · rw [push_last rfl]
    exact hA_eq hj

theorem pushB_eq {j : Nat} (hj : j < 2) : ∀ i < 4,
    (burnsideF48t_u52P2Arr.push (burnsideF48t_u52HArr burnsideF48t_u52HB)[j]!)[i]! =
      unpack 462 9 (qB j i) := by
  intro i hi
  interval_cases i
  · exact p2_eq 0 (by norm_num)
  · exact p2_eq 1 (by norm_num)
  · exact p2_eq 2 (by norm_num)
  · rw [push_last rfl]
    exact hB_eq hj

theorem pA {j : Nat} (hj : j < 2) : ∀ i < 4,
    permOK 462 9 (mask 9) (462 * 9) (qA j i) (nIf(Nat.blt i 3, LPI i, pinvS 462 9 (mask 9) (hAP j))) =
      true := by
  intro i hi
  interval_cases i
  · exact pP1 0 (by norm_num)
  · exact pP1 1 (by norm_num)
  · exact pP1 2 (by norm_num)
  · exact allN_spec hPerm.1 j hj

theorem pB {j : Nat} (hj : j < 2) : ∀ i < 4,
    permOK 462 9 (mask 9) (462 * 9) (qB j i)
      (nIf(Nat.blt i 3, LPI (i + i / 2), pinvS 462 9 (mask 9) (hBP j))) = true := by
  intro i hi
  interval_cases i
  · exact pP2 0 (by norm_num)
  · exact pP2 1 (by norm_num)
  · exact pP2 2 (by norm_num)
  · exact allN_spec hPerm.2 j hj

theorem sizeA (j : Nat) :
    (burnsideF48t_u52P1Arr.push (burnsideF48t_u52HArr burnsideF48t_u52HA)[j]!).size = 4 := rfl

theorem sizeB (j : Nat) :
    (burnsideF48t_u52P2Arr.push (burnsideF48t_u52HArr burnsideF48t_u52HB)[j]!).size = 4 := rfl

theorem orbX0 : ∀ p : Fin 462, p ∈ MulAction.orbit
    (CFSG.Sporadic.HNOddCore.arrGen 462 (burnsideF48t_u52Gens ())) (0 : Fin 462) ↔
      (p : ℕ) < 165 := fun p =>
  (mem_orbit_arrGen_iff (O := burnsideF48t_u52Gens ()) (k := 6) (x := 0) gX g_eq gPerm
    (by norm_num) cX0 p).trans (by rw [bitsIs_spec vX0 p p.2, Nat.blt_eq])

theorem orbX1 : ∀ p : Fin 462, p ∈ MulAction.orbit
    (CFSG.Sporadic.HNOddCore.arrGen 462 (burnsideF48t_u52Gens ())) (165 : Fin 462) ↔
      165 ≤ (p : ℕ) := fun p =>
  (mem_orbit_arrGen_iff (O := burnsideF48t_u52Gens ()) (k := 6) (x := 165) gX g_eq gPerm
    (by norm_num) cX1 p).trans (by rw [bitsIs_spec vX1 p p.2, Nat.ble_eq])

theorem cardP1 : Nat.card (MulAction.orbit (CFSG.Sporadic.HNOddCore.arrGen 462
      burnsideF48t_u52P1Arr) (165 : Fin 462)) = 9 ∧
    Nat.card (MulAction.orbit (CFSG.Sporadic.HNOddCore.arrGen 462 burnsideF48t_u52P1Arr)
      (1 : Fin 462)) = 128 ∧
    Nat.card (MulAction.orbit (CFSG.Sporadic.HNOddCore.arrGen 462 burnsideF48t_u52P1Arr)
      (15 : Fin 462)) = 36 :=
  ⟨(card_orbit_arrGen (O := burnsideF48t_u52P1Arr) (k := 3) (x := 165) rfl p1_eq pP1
      (by norm_num) cP1a).trans (popIs_spec vP1a),
    (card_orbit_arrGen (O := burnsideF48t_u52P1Arr) (k := 3) (x := 1) rfl p1_eq pP1
      (by norm_num) cP1b).trans (popIs_spec vP1b),
    (card_orbit_arrGen (O := burnsideF48t_u52P1Arr) (k := 3) (x := 15) rfl p1_eq pP1
      (by norm_num) cP1c).trans (popIs_spec vP1c)⟩

theorem coverP1 : ∀ p : Fin 462, 1 ≤ (p : ℕ) → (p : ℕ) < 165 →
    p ∈ MulAction.orbit (CFSG.Sporadic.HNOddCore.arrGen 462 burnsideF48t_u52P1Arr) (1 : Fin 462) ∨
      p ∈ MulAction.orbit (CFSG.Sporadic.HNOddCore.arrGen 462 burnsideF48t_u52P1Arr)
        (15 : Fin 462) := by
  intro p h1 h2
  have h : (Nat.lor (closeF (fun j => pg 9 (mask 9) (LP j)) 3 462 R (Nat.shiftLeft 1 1))
      (closeF (fun j => pg 9 (mask 9) (LP j)) 3 462 R (Nat.shiftLeft 1 15))).testBit p = true := by
    rw [bitsIs_spec vP1d p p.2, Nat.blt_eq.mpr (by omega : 0 < (p : ℕ))]
    exact Nat.blt_eq.mpr h2
  have h' : (closeF (fun j => pg 9 (mask 9) (LP j)) 3 462 R (Nat.shiftLeft 1 1) |||
      closeF (fun j => pg 9 (mask 9) (LP j)) 3 462 R (Nat.shiftLeft 1 15)).testBit p = true := h
  rw [Nat.testBit_or, Bool.or_eq_true] at h'
  rcases h' with h' | h'
  · exact Or.inl ((mem_orbit_arrGen_iff (O := burnsideF48t_u52P1Arr) (k := 3) (x := 1) rfl p1_eq
      pP1 (by norm_num) cP1b p).2 h')
  · exact Or.inr ((mem_orbit_arrGen_iff (O := burnsideF48t_u52P1Arr) (k := 3) (x := 15) rfl p1_eq
      pP1 (by norm_num) cP1c p).2 h')

theorem cardP2 : Nat.card (MulAction.orbit (CFSG.Sporadic.HNOddCore.arrGen 462
      burnsideF48t_u52P2Arr) (166 : Fin 462)) = 40 ∧
    Nat.card (MulAction.orbit (CFSG.Sporadic.HNOddCore.arrGen 462 burnsideF48t_u52P2Arr)
      (175 : Fin 462)) = 256 :=
  ⟨(card_orbit_arrGen (O := burnsideF48t_u52P2Arr) (k := 3) (x := 166) rfl p2_eq pP2
      (by norm_num) cP2a).trans (popIs_spec vP2a),
    (card_orbit_arrGen (O := burnsideF48t_u52P2Arr) (k := 3) (x := 175) rfl p2_eq pP2
      (by norm_num) cP2b).trans (popIs_spec vP2b)⟩

theorem coverP2 : ∀ p : Fin 462, 166 ≤ (p : ℕ) →
    p ∈ MulAction.orbit (CFSG.Sporadic.HNOddCore.arrGen 462 burnsideF48t_u52P2Arr) (166 : Fin 462) ∨
      p ∈ MulAction.orbit (CFSG.Sporadic.HNOddCore.arrGen 462 burnsideF48t_u52P2Arr)
        (175 : Fin 462) := by
  intro p h1
  have h : (Nat.lor (closeF (fun j => pg 9 (mask 9) (qP2 j)) 3 462 R (Nat.shiftLeft 1 166))
      (closeF (fun j => pg 9 (mask 9) (qP2 j)) 3 462 R (Nat.shiftLeft 1 175))).testBit p = true := by
    rw [bitsIs_spec vP2c p p.2]
    exact Nat.blt_eq.mpr (by omega)
  have h' : (closeF (fun j => pg 9 (mask 9) (qP2 j)) 3 462 R (Nat.shiftLeft 1 166) |||
      closeF (fun j => pg 9 (mask 9) (qP2 j)) 3 462 R (Nat.shiftLeft 1 175)).testBit p = true := h
  rw [Nat.testBit_or, Bool.or_eq_true] at h'
  rcases h' with h' | h'
  · exact Or.inl ((mem_orbit_arrGen_iff (O := burnsideF48t_u52P2Arr) (k := 3) (x := 166) rfl p2_eq
      pP2 (by norm_num) cP2a p).2 h')
  · exact Or.inr ((mem_orbit_arrGen_iff (O := burnsideF48t_u52P2Arr) (k := 3) (x := 175) rfl p2_eq
      pP2 (by norm_num) cP2b p).2 h')

theorem orbA : ∀ j < 2, ∀ p : Fin 462, p ∈ MulAction.orbit (CFSG.Sporadic.HNOddCore.arrGen 462
    (burnsideF48t_u52P1Arr.push (burnsideF48t_u52HArr burnsideF48t_u52HA)[j]!)) (0 : Fin 462) ↔
      (p : ℕ) < 165 := fun j hj p =>
  (mem_orbit_arrGen_iff (k := 4) (x := 0) (sizeA j) (pushA_eq hj) (pA hj) (by norm_num) (cA j hj)
    p).trans (by rw [bitsIs_spec (vA j hj) p p.2, Nat.blt_eq])

theorem orbB : ∀ j < 2, ∀ p : Fin 462, p ∈ MulAction.orbit (CFSG.Sporadic.HNOddCore.arrGen 462
    (burnsideF48t_u52P2Arr.push (burnsideF48t_u52HArr burnsideF48t_u52HB)[j]!)) (165 : Fin 462) ↔
      165 ≤ (p : ℕ) := fun j hj p =>
  (mem_orbit_arrGen_iff (k := 4) (x := 165) (sizeB j) (pushB_eq hj) (pB hj) (by norm_num)
    (cB j hj) p).trans (by rw [bitsIs_spec (vB j hj) p p.2, Nat.ble_eq])

theorem hVal : ((burnsideF48t_u52HArr burnsideF48t_u52HA)[0]!)[0]! = 1 ∧
    ((burnsideF48t_u52HArr burnsideF48t_u52HA)[1]!)[0]! = 15 ∧
    ((burnsideF48t_u52HArr burnsideF48t_u52HB)[0]!)[165]! = 166 ∧
    ((burnsideF48t_u52HArr burnsideF48t_u52HB)[1]!)[165]! = 175 := by
  rw [hA_eq (by norm_num), hA_eq (by norm_num), hB_eq (by norm_num), hB_eq (by norm_num),
    getElem!_unpack, getElem!_unpack, getElem!_unpack, getElem!_unpack]
  have h0 : (0 : Nat) < 462 := by norm_num
  have h1 : (165 : Nat) < 462 := by norm_num
  simp only [h0, h1, if_true]
  obtain ⟨h1, h2, h3, h4⟩ := vH
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3,
    Nat.eq_of_beq_eq_true h4⟩

private theorem oS0 : (burnsideF48t_u52S0Arr ()).size = 4 ∧
    ∀ j < 4, (burnsideF48t_u52S0Arr ())[j]! = unpack 462 9 (CS0.S j) := by
  have hl : burnsideF48t_u52SW.length = 4 := by decide +kernel
  refine ⟨by simp [burnsideF48t_u52S0Arr, hl], fun j hj => ?_⟩
  rw [burnsideF48t_u52S0Arr, getD_map_toArray _ _ [] (by omega), ev_eq,
    Nat.eq_of_beq_eq_true (allN_spec bS0 j hj)]

private theorem s0Binds : Binds 462 9 CS0.S 6 3 CS0.BP
    (CFSG.Sporadic.HNOddCore.strongArrs 462 (burnsideF48t_u52S0Arr ()) burnsideF48t_u52WS0)
    (burnsideF48t_u52BaseS0.map Fin.val).toArray :=
  binds_of (O := burnsideF48t_u52S0Arr ()) (W := burnsideF48t_u52WS0)
    (base := burnsideF48t_u52BaseS0) oS0 (by decide +kernel) (by norm_num)
    ⟨by decide +kernel, by decide +kernel⟩ CS0.head

private theorem siftS0_eq {G : Nat} (hG : Canon 462 9 G) (hr : Rng 462 9 G) :
    burnsideF48t_sift 462 (burnsideF48t_u52LevS0 ()) burnsideF48t_u52BaseS0 (unpack 462 9 G) =
      siftK 462 9 (mask 9) (462 * 9) (pidn 462 9) CS0.LR CS0.TRI CS0.BP 3 0 G := by
  rw [burnsideF48t_sift, burnsideF48t_u52LevS0, burnsideF48t_levels, burnsideF48t_baseArr]
  exact sift_unpack s0Binds (Orb.head_facts CS0.head).1 CS0.hl hG hr

theorem s0Norm : burnsideF48t_u52S0NormOK () = true := by
  unfold burnsideF48t_u52S0NormOK
  dsimp only
  refine CFSG.ONSchreier.allBelowN_iff.2 fun i hi => ?_
  have e : burnsideF48t_u52S0Arr () = (burnsideF48t_u52SW.map fun w =>
      unpack 462 9 (evFK 462 9 (mask 9) (pidn 462 9) LP LPI w)).toArray := by
    simp only [burnsideF48t_u52S0Arr, ev_eq]
  have h := List.all_eq_true.1 (allN_spec kS0 i hi)
  rw [e, l_eq i (by omega), li_eq i (by omega), List.all_toArray, List.all_eq_true]
  intro s hs
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hs
  rw [pcE _ (rE w), pcE _ (rL i (by omega)).2,
    siftS0_eq (cPC _ _) (rPC (rPC (rL i (by omega)).1 (rE w)) (rL i (by omega)).2)]
  exact h w hw

end CertificateChecks.Batch7769

public section

namespace Certificates

open CertificateChecks.Batch7769 in
open CFSG CFSG.ASVolI CFSG.Sporadic.HNOddCore in
theorem certificate7769 :
    (∀ p : Fin 462, p ∈ MulAction.orbit (CFSG.Sporadic.HNOddCore.arrGen 462 (burnsideF48t_u52Gens ())) (0 : Fin 462) ↔
      (p : ℕ) < 165) ∧
    (∀ p : Fin 462, p ∈ MulAction.orbit (CFSG.Sporadic.HNOddCore.arrGen 462 (burnsideF48t_u52Gens ())) (165 : Fin 462) ↔
      165 ≤ (p : ℕ)) ∧
    Nat.card (MulAction.orbit (CFSG.Sporadic.HNOddCore.arrGen 462 burnsideF48t_u52P1Arr) (165 : Fin 462)) = 9 ∧
    Nat.card (MulAction.orbit (CFSG.Sporadic.HNOddCore.arrGen 462 burnsideF48t_u52P1Arr) (1 : Fin 462)) = 128 ∧
    Nat.card (MulAction.orbit (CFSG.Sporadic.HNOddCore.arrGen 462 burnsideF48t_u52P1Arr) (15 : Fin 462)) = 36 ∧
    (∀ p : Fin 462, 1 ≤ (p : ℕ) → (p : ℕ) < 165 →
      p ∈ MulAction.orbit (CFSG.Sporadic.HNOddCore.arrGen 462 burnsideF48t_u52P1Arr) (1 : Fin 462) ∨
        p ∈ MulAction.orbit (CFSG.Sporadic.HNOddCore.arrGen 462 burnsideF48t_u52P1Arr) (15 : Fin 462)) ∧
    (burnsideF48t_u52HArr burnsideF48t_u52HA).size = 2 ∧
    ((burnsideF48t_u52HArr burnsideF48t_u52HA)[0]!)[0]! = 1 ∧
    ((burnsideF48t_u52HArr burnsideF48t_u52HA)[1]!)[0]! = 15 ∧
    (∀ j < 2, ∀ p : Fin 462, p ∈ MulAction.orbit (CFSG.Sporadic.HNOddCore.arrGen 462
      (burnsideF48t_u52P1Arr.push (burnsideF48t_u52HArr burnsideF48t_u52HA)[j]!)) (0 : Fin 462) ↔
        (p : ℕ) < 165) ∧
    Nat.card (MulAction.orbit (CFSG.Sporadic.HNOddCore.arrGen 462 burnsideF48t_u52P2Arr) (166 : Fin 462)) = 40 ∧
    Nat.card (MulAction.orbit (CFSG.Sporadic.HNOddCore.arrGen 462 burnsideF48t_u52P2Arr) (175 : Fin 462)) = 256 ∧
    (∀ p : Fin 462, 166 ≤ (p : ℕ) →
      p ∈ MulAction.orbit (CFSG.Sporadic.HNOddCore.arrGen 462 burnsideF48t_u52P2Arr) (166 : Fin 462) ∨
        p ∈ MulAction.orbit (CFSG.Sporadic.HNOddCore.arrGen 462 burnsideF48t_u52P2Arr) (175 : Fin 462)) ∧
    (burnsideF48t_u52HArr burnsideF48t_u52HB).size = 2 ∧
    ((burnsideF48t_u52HArr burnsideF48t_u52HB)[0]!)[165]! = 166 ∧
    ((burnsideF48t_u52HArr burnsideF48t_u52HB)[1]!)[165]! = 175 ∧
    (∀ j < 2, ∀ p : Fin 462, p ∈ MulAction.orbit (CFSG.Sporadic.HNOddCore.arrGen 462
      (burnsideF48t_u52P2Arr.push (burnsideF48t_u52HArr burnsideF48t_u52HB)[j]!)) (165 : Fin 462) ↔
        165 ≤ (p : ℕ)) ∧
    burnsideF48t_u52S0NormOK () = true :=
  ⟨orbX0, orbX1, cardP1.1, cardP1.2.1, cardP1.2.2, coverP1, hArr_size.1, hVal.1, hVal.2.1, orbA,
    cardP2.1, cardP2.2, coverP2, hArr_size.2, hVal.2.2.1, hVal.2.2.2, orbB, s0Norm⟩

end Certificates

end
