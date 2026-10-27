module

public import Certificates.Kernel.Co2Smith.Mark
public import Certificates.Kernel.Co2Smith.RootK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co1F2 CFSG.KC.Co2InvS CFSG.KC.Co2Smith CFSG.Sporadic.Co2Smith
open CFSG.Sporadic.Co2Smith.Native CFSG.Sporadic.SmallF2.Native

theorem elWords_ok : (glX61Word.all (· < 22) && glD0hWord.all (· < 22) &&
    glD1hWord.all (· < 22) && glUWord.all (· < 22)) = true := by decide +kernel

theorem glAl_eq : glAl = unpackR 22 alK := glR_eq (by decide)
theorem glGa_eq : glGa = unpackR 22 gaK := glR_eq (by decide)

theorem el_eqs : glX61 = unpackR 22 x61K ∧ glD0h = unpackR 22 d0K ∧ glD1h = unpackR 22 d1K ∧
    glU = unpackR 22 uK := by
  have h := elWords_ok
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨glR_eq h.1.1.1, glR_eq h.1.1.2, glR_eq h.1.2, glR_eq h.2⟩

theorem glConj_unpack (A B : Nat) : glConj (unpackR 22 A) (unpackR 22 B) = unpackR 22 (cjK A B) := by
  rw [glConj, mulRows_unpack, mulRows_unpack]
  rfl

theorem frame_eqs : glW1 = unpackR 22 w1K ∧ glW2 = unpackR 22 w2K ∧ glW3 = unpackR 22 w3K ∧
    glX52 = unpackR 22 x52K ∧ glX43 = unpackR 22 x43K ∧ glX25 = unpackR 22 x25K ∧
    glX34 = unpackR 22 x34K ∧ glW0 = unpackR 22 w0K := by
  obtain ⟨h61, h0, h1, -⟩ := el_eqs
  have e1 : glW1 = unpackR 22 w1K := by rw [glW1, glZ_eq, h61, glConj_unpack]; rfl
  have e2 : glW2 = unpackR 22 w2K := by rw [glW2, h1, e1, glConj_unpack]; rfl
  have e3 : glW3 = unpackR 22 w3K := by rw [glW3, h0, e2, glConj_unpack]; rfl
  have e52 : glX52 = unpackR 22 x52K := by rw [glX52, h1, h61, glConj_unpack]; rfl
  have e43 : glX43 = unpackR 22 x43K := by rw [glX43, h0, e52, glConj_unpack]; rfl
  have e25 : glX25 = unpackR 22 x25K := by rw [glX25, h1, glZ_eq, glConj_unpack]; rfl
  have e34 : glX34 = unpackR 22 x34K := by rw [glX34, h0, e25, glConj_unpack]; rfl
  refine ⟨e1, e2, e3, e52, e43, e25, e34, ?_⟩
  rw [glW0, e1, e2, e3, mulRows_unpack, mulRows_unpack]
  rfl

theorem nf_k : (glPosNF.size == 4 && (List.range 4).all fun i =>
    (glPosNF[i]!).toList.all fun w => w.all (· < 22)) = true := by decide +kernel

theorem nf_ok {i : Nat} (hi : i < 4) (t : Nat) : ∀ k ∈ (glPosNF[i]!)[t]!, k < 22 := by
  have h := nf_k
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  intro k hk
  by_cases ht : t < (glPosNF[i]!).size
  · rw [getElem!_pos _ t ht] at hk
    exact h.2 i hi _ (Array.getElem_mem_toList ht) k hk
  · rw [getElem!_neg _ t ht] at hk
    exact absurd hk List.not_mem_nil

theorem glPosRows_eq (i t : Nat) : glPosRows i t = unpackR 22 (posK i t) := by
  obtain ⟨-, -, -, -⟩ := el_eqs
  obtain ⟨-, -, e3, -⟩ := frame_eqs
  have hx24 : ∀ t, glX24R t = unpackR 22 (x24K t) := by
    intro t
    rw [glX24R, glGD, glDG, glGa_eq, el_eqs.2.2.1, glR_eq (nf_ok (by decide) t), mulRows_unpack,
      mulRows_unpack, mulRows_unpack, mulRows_unpack]
    rfl
  unfold glPosRows posK
  by_cases h0 : (t == 0) = true
  · rw [if_pos h0, if_pos h0, idRows_eq]
  · rw [if_neg h0, if_neg h0]
    by_cases h4 : i < 4
    · rw [if_pos h4, if_pos h4, glR_eq (nf_ok h4 t)]
    · rw [if_neg h4, if_neg h4]
      by_cases h5 : (i == 4) = true
      · rw [if_pos h5, if_pos h5, hx24]
      · rw [if_neg h5, if_neg h5, e3, hx24, glConj_unpack]

theorem glLongRows_eq (k : Nat) : glLongRows k = unpackR 22 (longK k) := by
  obtain ⟨h61, -, -, -⟩ := el_eqs
  obtain ⟨-, -, -, e52, e43, e25, e34, -⟩ := frame_eqs
  unfold glLongRows longK
  by_cases c0 : (k == 0) = true
  · rw [if_pos c0, if_pos c0, glZ_eq]
    rfl
  rw [if_neg c0, if_neg c0]
  by_cases c1 : (k == 1) = true
  · rw [if_pos c1, if_pos c1, e25]
  rw [if_neg c1, if_neg c1]
  by_cases c2 : (k == 2) = true
  · rw [if_pos c2, if_pos c2, e34]
  rw [if_neg c2, if_neg c2]
  by_cases c3 : (k == 3) = true
  · rw [if_pos c3, if_pos c3, h61]
  rw [if_neg c3, if_neg c3]
  by_cases c4 : (k == 4) = true
  · rw [if_pos c4, if_pos c4, e52]
  rw [if_neg c4, if_neg c4, e43]

theorem glRootRows_eq (r t : Nat) : glRootRows r t = unpackR 22 (rootK r t) := by
  obtain ⟨-, -, -, -, -, -, -, e0⟩ := frame_eqs
  unfold glRootRows rootK
  split_ifs
  · exact idRows_eq
  · exact glPosRows_eq r t
  · rw [e0, glPosRows_eq, glConj_unpack]
  · exact glLongRows_eq _

theorem glProdRows_eq (l : List (Nat × Nat)) : glProdRows l = unpackR 22 (prodK l) := by
  unfold glProdRows prodK
  induction l with
  | nil => exact idRows_eq
  | cons p l ih => rw [List.foldr_cons, List.foldr_cons, ih, glRootRows_eq, mulRows_unpack]

theorem glCommRows_unpack (A B : Nat) :
    glCommRows (unpackR 22 A) (unpackR 22 B) = unpackR 22 (comm4K A B) := by
  rw [glCommRows, mulRows_unpack, mulRows_unpack, mulRows_unpack]
  rfl

theorem glFrameConjRows_eq (k : Nat) : glFrameConjRows k = unpackR 22 (frameConjK k) := by
  obtain ⟨-, h0, h1, -⟩ := el_eqs
  obtain ⟨e1, -⟩ := frame_eqs
  unfold glFrameConjRows frameConjK
  split_ifs <;> simp only [idRows_eq, h0, h1, e1, mulRows_unpack]

theorem glMaps_unpack (A : Nat) {x y : Nat} (hx : x < 2300) (hy : y < 2300) :
    glMaps (unpackR 22 A) x y = mapsK A x y := by
  rw [glMaps, mapsK, KernelSporSch.Co2M.V_get hx, KernelSporSch.Co2M.V_get hy]
  rfl

theorem rootPar_ok : glRootParOK = true := by
  rw [← rootPar_k]
  unfold glRootParOK rootParK
  simp only [glRootRows_eq, glAl_eq, glGa_eq, mulRows_unpack, glConj_unpack, beq_unpack]

theorem rootComm_ok : glRootCommOK = true := by
  rw [← rootComm_k]
  unfold glRootCommOK rootCommK
  simp only [glRootRows_eq, glCommRows_unpack, glProdRows_eq, beq_unpack]

theorem chart_ok : glChartOK = true := by
  rw [← chart_k]
  unfold glChartOK chartK
  simp only [glRootRows_eq, glLongRows_eq, glFrameConjRows_eq, glZ_eq, commRows_unpack,
    mulRows_unpack, beq_unpack]
  rfl

theorem uOK_ok : glUOK = true := by
  have hm : ((List.range 18).all fun r => (glParams r).all fun t =>
      glMaps (glRootRows r t) 80 80) = ((List.range 18).all fun r => (glParams r).all fun t =>
      mapsK (rootK r t) 80 80) := by
    simp only [glRootRows_eq, glMaps_unpack _ (by decide : 80 < 2300) (by decide : 80 < 2300)]
  rw [← uOK_k]
  unfold glUOK uOKK
  rw [hm]
  simp only [glRootRows_eq, el_eqs.2.2.2, glZ_eq, glCommRows_unpack, commRows_unpack,
    mulRows_unpack, beq_unpack]
  rfl

theorem frame_ok : glFrameOK = true := by
  obtain ⟨h61, h0, h1, -⟩ := el_eqs
  obtain ⟨-, -, -, -, e43, -, e34, -⟩ := frame_eqs
  rw [← frame_k]
  unfold glFrameOK frameK
  simp only [glLongRows_eq, h61, h0, h1, e43, e34, glZ_eq, idRows_eq, mulRows_unpack,
    powRows_unpack, commRows_unpack, beq_unpack]
  rfl

theorem root_ok : glRootOK = true := by
  unfold glRootOK
  rw [rootPar_ok, rootComm_ok, chart_ok, uOK_ok, frame_ok]
  rfl

end CertificateChecks.KernelCo2Smith
