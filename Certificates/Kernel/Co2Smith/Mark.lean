module

public import Certificates.Kernel.Co2Smith.Letters
public import Certificates.Kernel.Co2Smith.MarkK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co1F2 CFSG.KC.Co2InvS CFSG.KC.Co2Smith CFSG.Sporadic.Co2Smith
open CFSG.Sporadic.Co2Smith.Native CFSG.Sporadic.SmallF2.Native

theorem mkLet_ok : glMkLetOK = true := by
  simp only [glMkLetOK, glMkWordOK, ← Array.all_toList]
  decide +kernel

theorem mkR_ok : glMkROK = true := by
  simp only [glMkROK, glMkR, glMkRWord, glR, glZ, glRows_eqK]
  decide +kernel

theorem mkOrb_ok : glMkOrbOK = true := by
  simp only [glMkOrbOK, glMkR, glMkRWord, glR, glZ, glRows_eqK]
  decide +kernel

theorem mkGen_ok : glMkGenOK = true := by
  simp only [glMkGenOK, glMkGenListOK, glMkGens, glMkT, glR, glZ, glRows_eqK]
  decide +kernel

theorem mkWords_ok : (glWit0.all (fun e => e.2.2.all (· < 22) && decide (e.2.1 < 3)) &&
    glWit1.all (fun e => e.2.all (· < 22)) && glWit2.all (fun e => e.2.all (· < 22)) &&
    (List.range 36).all (fun i => (glMkRWord i).all (· < 22))) = true := by
  decide +kernel

theorem mkR_get {i : Nat} (hi : i < 36) : glMkR[i]! = unpackR 22 (wK LP (glMkRWord i)) := by
  have h := mkWords_ok
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  unfold glMkR
  rw [getElem!_pos _ i (by simp [hi]), Array.getElem_ofFn]
  exact glR_eq (h.2 i hi)

theorem mkF_eq : glMkF = unpackR 22 (wK LP [12]) := glR_eq (by decide)

theorem glZ_eq : glZ = unpackR 22 (wK LP [0]) := glR_eq (by decide)

theorem c0_pred (G : Nat) (h : c0PredK (wK LP [12]) (wK LP [0]) reflK G = true) :
    ((!(commRows (unpackR 22 G) glMkF && mulRows 22 (unpackR 22 G) (unpackR 22 G) == idRows 22 &&
        unpackR 22 G != idRows 22) || unpackR 22 G == glZ) &&
      glMkR.any fun y => mulRows 22 y (unpackR 22 G) == mulRows 22 (unpackR 22 G) glZ) = true := by
  unfold c0PredK at h
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · rw [mkF_eq, glZ_eq, commRows_unpack, mulRows_unpack, idRows_eq, beq_unpack, bne_unpack,
      beq_unpack]
    exact h1
  · rw [List.any_eq_true] at h2
    obtain ⟨Y, hY, hYG⟩ := h2
    unfold reflK at hY
    rw [List.mem_map] at hY
    obtain ⟨i, hi, rfl⟩ := hY
    rw [List.mem_range] at hi
    rw [Array.any_eq_true]
    have hs : i < glMkR.size := by simp [glMkR, hi]
    refine ⟨i, hs, ?_⟩
    rw [← getElem!_pos glMkR i hs, mkR_get hi, glZ_eq, mulRows_unpack, mulRows_unpack, beq_unpack]
    exact hYG

theorem mkC0_ok : glMkC0OK = true := by
  have hK := c0_k
  have hw := mkWords_ok
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hw
  obtain ⟨⟨⟨hw0, hw1⟩, hw2⟩, -⟩ := hw
  unfold c0K at hK
  simp only [List.all_eq_true] at hK
  unfold glMkC0OK
  simp only [Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [mkF_eq, powRows_unpack, idRows_eq, beq_unpack]
    decide +kernel
  · rw [mkF_eq, idRows_eq, bne_unpack]
    decide +kernel
  · rw [List.all_eq_true]
    intro g hg
    unfold glMkC0Rows glMkA0 at hg
    simp only [List.mem_flatMap, List.mem_map] at hg
    obtain ⟨a, ⟨e, he, rfl⟩, e₁, he₁, e₂, he₂, rfl⟩ := hg
    have h0 := hw0 e he
    rw [glR_eq h0.1, glForm_eq h0.2, glR_eq (hw1 e₁ he₁), glR_eq (hw2 e₂ he₂), mulRows_unpack,
      mulRows_unpack, mulRows_unpack]
    exact c0_pred _ (hK e he e₁ he₁ e₂ he₂)

theorem mark_ok : glMarkOK = true := by
  unfold glMarkOK
  rw [mkLet_ok, mkR_ok, mkOrb_ok, mkC0_ok, mkGen_ok]
  rfl

end CertificateChecks.KernelCo2Smith
