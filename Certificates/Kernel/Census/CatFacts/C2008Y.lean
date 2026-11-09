module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallConfA8Inputs
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3A8Data
public import Certificates.Data.Kernel.Census.CatFacts.PkDefs
public import Certificates.Kernel.Census.CatFacts.OrbPre

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelCatFacts

open CFSG.ComponentClassification.CatFactsSmall CFSG.ComponentClassification.CatFactsSmall.A8
  CFSG.Certificates.Kernel.PkEnum CFSG.GH74.KGroups CFSG.Certificates CFSG.Sporadic.Schreier

@[expose] def fQ : Fin 8 → Fin 3 := ![0, 0, 1, 1, 1, 1, 2, 2]

@[expose] def labQ0 (i : Fin 8) : Nat := (fQ i).val

@[expose] def fH : Fin 8 → Fin 2 := ![0, 0, 1, 1, 1, 1, 0, 0]

@[expose] def labH (i : Fin 8) : Nat := (fH i).val

@[expose] def sQ : Equiv.Perm (Fin 8) := List.formPerm [0, 6] * List.formPerm [1, 7]

@[expose] def sH : Equiv.Perm (Fin 8) :=
  List.formPerm [0, 2] * List.formPerm [1, 3] * List.formPerm [6, 4] * List.formPerm [7, 5]

@[expose] def WQ : RawSchreierDatum 8 :=
  certificate (by decide) ([List.formPerm [0, 1], sQ, List.formPerm [6, 7], List.formPerm [2, 3],
    List.formPerm [3, 4], List.formPerm [4, 5]].map tab) [] #v[0, 6, 2, 3, 4] (by decide)

@[expose] def WH : RawSchreierDatum 8 :=
  certificate (by decide) ([List.formPerm [0, 1], List.formPerm [1, 6], List.formPerm [6, 7],
    List.formPerm [2, 3], List.formPerm [3, 4], List.formPerm [4, 5], sH].map tab) []
    #v[0, 1, 6, 2, 3, 4] (by decide)

theorem fin8_cases {P : Fin 8 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4)
    (h5 : P 5) (h6 : P 6) (h7 : P 7) : ∀ i, P i := by
  intro i
  fin_cases i
  exacts [h0, h1, h2, h3, h4, h5, h6, h7]

theorem WQ_sch : schP WQ = true := by decide +kernel

theorem WH_sch : schP WH = true := by decide +kernel

theorem WQ_ok : ValidSchreier WQ := check_certificate_of _ _ _ _ _ WQ_sch

theorem WH_ok : ValidSchreier WH := check_certificate_of _ _ _ _ _ WH_sch

theorem WQ_stab : ((elemsV WQ).filter fun y => (List.finRange 8).all fun i => fQ (y i) == fQ i).length =
    96 := by decide +kernel

theorem WH_stab : ((elemsV WH).filter fun y => (List.finRange 8).all fun i => fH (y i) == fH i).length =
    576 := by decide +kernel

theorem prodQ : ∏ i, (Fintype.card {a // fQ a = i}).factorial = 96 := by decide +kernel

theorem prodH : ∏ i, (Fintype.card {a // fH a = i}).factorial = 576 := by decide +kernel

theorem sQ_sift : siftP WQ sQ 0 = true := by decide +kernel

theorem sH_sift : siftP WH sH 0 = true := by decide +kernel

theorem labOK_QQ8 : labOK QQ8 labQ0 = true := by decide +kernel

theorem labOK_cfQH : labOK cfQH labH = true := by decide +kernel

theorem labOK_cfQE : labOK cfQE labH = true := by decide +kernel

theorem young_Q {x : Equiv.Perm (Fin 8)} (h1 : labQ0 (x 1) = labQ0 (x 0))
    (h3 : labQ0 (x 3) = labQ0 (x 2)) (h4 : labQ0 (x 4) = labQ0 (x 2))
    (h5 : labQ0 (x 5) = labQ0 (x 4)) (h7 : labQ0 (x 7) = labQ0 (x 6)) :
    (∀ i, fQ (x i) = fQ i) ∨ (∀ i, fQ (sQ (x i)) = fQ i) := by
  have hle : ∀ y, labQ0 y ≤ 2 := by decide +kernel
  have hsw : ∀ y, labQ0 (sQ y) = 2 - labQ0 y := by decide +kernel
  have hfib : ∀ a b c : Fin 8, labQ0 a = labQ0 b → labQ0 a = labQ0 c → labQ0 a ≠ 1 →
      a = b ∨ a = c ∨ b = c := by decide +kernel
  have hv : labQ0 0 = 0 ∧ labQ0 1 = 0 ∧ labQ0 2 = 1 ∧ labQ0 3 = 1 ∧ labQ0 4 = 1 ∧
      labQ0 5 = 1 ∧ labQ0 6 = 2 ∧ labQ0 7 = 2 := by decide +kernel
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7⟩ := hv
  have hmid : labQ0 (x 2) = 1 := by
    by_contra hne
    rcases hfib (x 2) (x 3) (x 4) h3.symm h4.symm hne with e | e | e
    · exact absurd (x.injective e) (by decide)
    · exact absurd (x.injective e) (by decide)
    · exact absurd (x.injective e) (by decide)
  have hc : ∀ i, labQ0 (x i) = labQ0 (x 0) ∨ labQ0 (x i) = labQ0 (x 2) ∨
      labQ0 (x i) = labQ0 (x 6) := by
    intro i
    revert i
    apply fin8_cases <;> omega
  have hz := hc (x.symm 0)
  have ht := hc (x.symm 6)
  rw [Equiv.apply_symm_apply, v0] at hz
  rw [Equiv.apply_symm_apply, v6] at ht
  have hu := hle (x 0)
  have hw := hle (x 6)
  have hcase : (labQ0 (x 0) = 0 ∧ labQ0 (x 6) = 2) ∨ (labQ0 (x 0) = 2 ∧ labQ0 (x 6) = 0) := by
    omega
  rcases hcase with ⟨a, b⟩ | ⟨a, b⟩
  · left
    intro i
    apply Fin.ext
    change labQ0 (x i) = labQ0 i
    revert i
    apply fin8_cases <;> omega
  · right
    intro i
    apply Fin.ext
    change labQ0 (sQ (x i)) = labQ0 i
    rw [hsw]
    revert i
    apply fin8_cases <;> omega

theorem young_H {x : Equiv.Perm (Fin 8)} (h1 : labH (x 1) = labH (x 0))
    (h6 : labH (x 6) = labH (x 0)) (h7 : labH (x 7) = labH (x 0))
    (h3 : labH (x 3) = labH (x 2)) (h4 : labH (x 4) = labH (x 2))
    (h5 : labH (x 5) = labH (x 2)) :
    (∀ i, fH (x i) = fH i) ∨ (∀ i, fH (sH (x i)) = fH i) := by
  have hle : ∀ y, labH y ≤ 1 := by decide +kernel
  have hsw : ∀ y, labH (sH y) = 1 - labH y := by decide +kernel
  have hv : labH 0 = 0 ∧ labH 1 = 0 ∧ labH 2 = 1 ∧ labH 3 = 1 ∧ labH 4 = 1 ∧
      labH 5 = 1 ∧ labH 6 = 0 ∧ labH 7 = 0 := by decide +kernel
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7⟩ := hv
  have hc : ∀ i, labH (x i) = labH (x 0) ∨ labH (x i) = labH (x 2) := by
    intro i
    revert i
    apply fin8_cases <;> omega
  have hz := hc (x.symm 0)
  have ho := hc (x.symm 2)
  rw [Equiv.apply_symm_apply, v0] at hz
  rw [Equiv.apply_symm_apply, v2] at ho
  have hu := hle (x 0)
  have hw := hle (x 2)
  have hcase : (labH (x 0) = 0 ∧ labH (x 2) = 1) ∨ (labH (x 0) = 1 ∧ labH (x 2) = 0) := by
    omega
  rcases hcase with ⟨a, b⟩ | ⟨a, b⟩
  · left
    intro i
    apply Fin.ext
    change labH (x i) = labH i
    revert i
    apply fin8_cases <;> omega
  · right
    intro i
    apply Fin.ext
    change labH (sH (x i)) = labH i
    rw [hsw]
    revert i
    apply fin8_cases <;> omega

theorem memWQ_of {x : Equiv.Perm (Fin 8)}
    (h : (∀ i, fQ (x i) = fQ i) ∨ (∀ i, fQ (sQ (x i)) = fQ i)) : x ∈ WQ.originalSubgroup := by
  have hc := WQ_stab.trans prodQ.symm
  rcases h with h | h
  · exact mem_of_stab WQ_ok fQ hc h
  · have hs : sQ * x ∈ WQ.originalSubgroup := mem_of_stab WQ_ok fQ hc (y := sQ * x) fun i => h i
    have hs0 : sQ ∈ WQ.originalSubgroup :=
      (mem_iff_sift WQ WQ_ok sQ).2 ((sift_eq_siftP _ _ _).trans sQ_sift)
    rw [← inv_mul_cancel_left sQ x]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hs0) hs

theorem memWH_of {x : Equiv.Perm (Fin 8)}
    (h : (∀ i, fH (x i) = fH i) ∨ (∀ i, fH (sH (x i)) = fH i)) : x ∈ WH.originalSubgroup := by
  have hc := WH_stab.trans prodH.symm
  rcases h with h | h
  · exact mem_of_stab WH_ok fH hc h
  · have hs : sH * x ∈ WH.originalSubgroup := mem_of_stab WH_ok fH hc (y := sH * x) fun i => h i
    have hs0 : sH ∈ WH.originalSubgroup :=
      (mem_iff_sift WH WH_ok sH).2 ((sift_eq_siftP _ _ _).trans sH_sift)
    rw [← inv_mul_cancel_left sH x]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hs0) hs

theorem memWQ {x : Equiv.Perm (Fin 8)} (hp : preT labQ0 q0gens x = true) :
    x ∈ WQ.originalSubgroup := by
  have e1 := preT_apply hp (q := List.formPerm [0, 1]) (by simp [q0gens]) 0
  have e3 := preT_apply hp (q := List.formPerm [2, 3]) (by simp [q0gens]) 2
  have e4 := preT_apply hp (q := List.formPerm [2, 4, 3, 5]) (by simp [q0gens]) 2
  have e5 := preT_apply hp (q := List.formPerm [4, 5]) (by simp [q0gens]) 4
  have e7 := preT_apply hp (q := List.formPerm [6, 7]) (by simp [q0gens]) 6
  have p1 : (List.formPerm [0, 1] : Equiv.Perm (Fin 8)) 0 = 1 := by decide
  have p3 : (List.formPerm [2, 3] : Equiv.Perm (Fin 8)) 2 = 3 := by decide
  have p4 : (List.formPerm [2, 4, 3, 5] : Equiv.Perm (Fin 8)) 2 = 4 := by decide
  have p5 : (List.formPerm [4, 5] : Equiv.Perm (Fin 8)) 4 = 5 := by decide
  have p7 : (List.formPerm [6, 7] : Equiv.Perm (Fin 8)) 6 = 7 := by decide
  rw [p1] at e1
  rw [p3] at e3
  rw [p4] at e4
  rw [p5] at e5
  rw [p7] at e7
  exact memWQ_of (young_Q e1 e3 e4 e5 e7)

theorem memWH {x : Equiv.Perm (Fin 8)} (hp : preT labH cfHgens x = true) :
    x ∈ WH.originalSubgroup := by
  have e1 := preT_apply hp (q := List.formPerm [0, 1]) (by simp [cfHgens, q0gens]) 0
  have e3 := preT_apply hp (q := List.formPerm [2, 3]) (by simp [cfHgens, q0gens]) 2
  have e4 := preT_apply hp (q := List.formPerm [2, 4, 3, 5]) (by simp [cfHgens, q0gens]) 2
  have e5 := preT_apply hp (q := List.formPerm [4, 5]) (by simp [cfHgens, q0gens]) 4
  have e6 := preT_apply hp (q := List.formPerm [6, 7]) (by simp [cfHgens, q0gens]) 6
  have e7 := preT_apply hp (q := g08) (by simp [cfHgens]) 0
  have p1 : (List.formPerm [0, 1] : Equiv.Perm (Fin 8)) 0 = 1 := by decide
  have p3 : (List.formPerm [2, 3] : Equiv.Perm (Fin 8)) 2 = 3 := by decide
  have p4 : (List.formPerm [2, 4, 3, 5] : Equiv.Perm (Fin 8)) 2 = 4 := by decide
  have p5 : (List.formPerm [4, 5] : Equiv.Perm (Fin 8)) 4 = 5 := by decide
  have p6 : (List.formPerm [6, 7] : Equiv.Perm (Fin 8)) 6 = 7 := by decide
  have p7 : g08 0 = 7 := by decide
  rw [p1] at e1
  rw [p3] at e3
  rw [p4] at e4
  rw [p5] at e5
  rw [p6] at e6
  rw [p7] at e7
  exact memWH_of (young_H e1 (by omega) e7 e3 e4 (by omega))

theorem memWE {x : Equiv.Perm (Fin 8)} (hp : preT labH cfEgens x = true) :
    x ∈ WH.originalSubgroup := by
  have a0 := preT_apply hp (q := cfEgensa) (by simp [cfEgens]) 0
  have a1 := preT_apply hp (q := cfEgensa) (by simp [cfEgens]) 1
  have b0 := preT_apply hp (q := cfEgensb) (by simp [cfEgens]) 0
  have b2 := preT_apply hp (q := cfEgensb) (by simp [cfEgens]) 2
  have b3 := preT_apply hp (q := cfEgensb) (by simp [cfEgens]) 3
  have c2 := preT_apply hp (q := cfEgensc) (by simp [cfEgens]) 2
  have pa0 : cfEgensa 0 = 7 := by decide
  have pa1 : cfEgensa 1 = 6 := by decide
  have pb0 : cfEgensb 0 = 6 := by decide
  have pb2 : cfEgensb 2 = 5 := by decide
  have pb3 : cfEgensb 3 = 4 := by decide
  have pc2 : cfEgensc 2 = 3 := by decide
  rw [pa0] at a0
  rw [pa1] at a1
  rw [pb0] at b0
  rw [pb2] at b2
  rw [pb3] at b3
  rw [pc2] at c2
  exact memWH_of (young_H (by omega) b0 a0 c2 (by omega) b2)

end CertificateChecks.KernelCatFacts

end
