module

public import CFSG.Monster.B.TwoA.Amalgam.DistThreeTraceCentInputs
public import Certificates.Kernel.MonsterB.Co2Mem
public import Certificates.Kernel.MonsterB.Cent3126Data
public import CFSG.Certificates.Kernel.MonsterB.Co2LinSound
public import CFSG.Monster.B.TwoA.Amalgam.DataBase

public section

open CFSG.Monster.B.TwoA.Co2Inv CFSG.Monster.B.TwoA.Amalgam CFSG.Monster.B.TwoA CFSG.Monster.B
open CFSG.Monster.VisCert.Native CFSG.KC.Co2Mem CertificateChecks.Cent3126
  CertificateChecks.KernelMonB

namespace CertificateChecks.Batch3126

open CFSG.Monster.B.TwoA.Co2Inv CFSG.Monster.B.TwoA.Amalgam CFSG.Monster.B.TwoA CFSG.Monster.B
open CFSG.Monster.VisCert.Native CFSG.KC.Co2Mem CertificateChecks.Cent3126
  CertificateChecks.KernelMonB

set_option maxRecDepth 100000

@[expose] def cQ : Array Nat := ((List.range 22).map fun t => 2 ^ (22 + t)).toArray

@[expose] def outF (v : ℕ) : ℕ := actGo centP₁ v 22 0 ^^^ actGo cQ (actGo centP₂ v 22 0) 22 0

theorem arr_eq {a b : Array ℕ} (h : a.toList = b.toList) : a = b := Array.toList_inj.1 h

theorem comm_lists : ∀ w ∈ centWords, (rowsMul (centRowsOf w) (Unitary.genRows 6)).toList =
    (rowsMul (Unitary.genRows 6) (centRowsOf w)).toList := by
  decide +kernel

theorem centCheck_comm : ∀ w ∈ centWords,
    rowsMul (centRowsOf w) (Unitary.genRows 6) = rowsMul (Unitary.genRows 6) (centRowsOf w) :=
  fun w hw => arr_eq (comm_lists w hw)

theorem centCheck_rel :
    (∀ t < 22, centP₁[t]! = relRow centRel₁ t ∧ centP₂[t]! = relRow centRel₂ t) ∧
    Co2.Native.actD 22 centP₁ centW0 = 0 ∧ Co2.Native.actD 22 centP₂ centW0 = 0 ∧
    (∀ t < 22, centP₁[t]! < 2 ^ 22 ∧ centP₂[t]! < 2 ^ 22) ∧
    (∀ i ∈ centRel₁, i < 28) ∧ (∀ i ∈ centRel₂, i < 28) ∧ (∀ i ∈ centSel, i < 28) ∧
    centWords.length = 28 ∧ centSel.length = 22 ∧ centW0 < 2 ^ 22 := by
  decide +kernel

theorem kEinv : ∀ t < 22, actGo cE cEinv[t]! 22 0 = 2 ^ t ∧ cEinv[t]! < 2 ^ 22 := by
  decide +kernel

theorem kId : ∀ t < 22, Co2Inv.idRows[t]! = 2 ^ t := by decide +kernel

theorem kO : ∀ t < 22, cO[t]! = outF cE[t]! := by decide +kernel

theorem kEch : (∀ i < 3, cO[i]! = 0) ∧
    (∀ i < 22, 3 ≤ i → 2 ^ cH[i]! ≤ cO[i]! ∧ cO[i]! < 2 ^ (cH[i]! + 1)) ∧
    (∀ i < 21, 3 ≤ i → cH[i]! < cH[i + 1]!) := by
  decide +kernel

theorem kCands : ∀ z < 8, centCands.contains (actGo cE z 22 0) = true := by decide +kernel

theorem actGo_zero (rows : Array ℕ) : ∀ n, actGo rows 0 n 0 = 0 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => rw [actGo_succ, ih]; simp

theorem outF_xor (a b : ℕ) : outF (a ^^^ b) = outF a ^^^ outF b := by
  unfold outF
  rw [CFSG.KC.CoPair.actGo_xor, CFSG.KC.CoPair.actGo_xor, CFSG.KC.CoPair.actGo_xor,
    CFSG.KC.CoPair.xor_xor_xor]

theorem cands_of {y : ℕ} (hy : y < 2 ^ 22) (h1 : Co2.Native.actD 22 centP₁ y = 0)
    (h2 : Co2.Native.actD 22 centP₂ y = 0) : centCands.contains y = true := by
  have hEy : actGo cE (actGo cEinv y 22 0) 22 0 = y := by
    have := actGo_hom (F := fun v => actGo cE v 22 0)
      (fun a b => CFSG.KC.CoPair.actGo_xor cE a b 22)
      (N := cEinv) (C := Co2Inv.idRows) y 22 (fun t ht => by rw [kId t ht, (kEinv t ht).1])
    rw [this]
    exact actGo_unit kId hy
  have hO : actGo cO (actGo cEinv y 22 0) 22 0 = 0 := by
    rw [← actGo_hom outF_xor _ 22 kO, hEy]
    change Co2.Native.actD 22 centP₁ y ^^^ actGo cQ (Co2.Native.actD 22 centP₂ y) 22 0 = 0
    rw [h1, h2, actGo_zero, Nat.xor_self]
  obtain ⟨e1, e2, e3⟩ := kEch
  have hbits := (actGo_echelon (O := cO) (h := fun i => cH[i]!) (k := 3) e1
    (fun i h1 h2 => e2 i h2 h1) (fun i h1 h2 => e3 i (by omega) h1) (actGo cEinv y 22 0)
    (n := 22)).2.2 hO
  have hlt : actGo cEinv y 22 0 < 2 ^ 22 := actGo_lt y 22 fun t ht => (kEinv t ht).2
  have h8 : actGo cEinv y 22 0 < 2 ^ 3 := by
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    rcases Nat.lt_or_ge i 22 with h | h
    · exact hbits i hi h
    · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) h))
  rw [← hEy]
  exact kCands _ h8

theorem centCheck_brute : Nat.all (2 ^ 22) (fun y _ =>
    !(Co2.Native.actD 22 centP₁ y == 0 && Co2.Native.actD 22 centP₂ y == 0) ||
      centCands.contains y) = true := by
  change CFSG.Monster.B.Co2.Native.allLt (2 ^ 22) (fun y =>
    !(Co2.Native.actD 22 centP₁ y == 0 && Co2.Native.actD 22 centP₂ y == 0) ||
      centCands.contains y) = true
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro y hy
  cases h1 : (Co2.Native.actD 22 centP₁ y == 0)
  · rfl
  cases h2 : (Co2.Native.actD 22 centP₂ y == 0)
  · rfl
  exact cands_of hy (beq_iff_eq.1 h1) (beq_iff_eq.1 h2)

theorem centCheck_basis : frows centW0 = Co2Inv.idRows := arr_eq (by decide +kernel)

theorem not_mem_6204 : ∀ j < 2300, Co2.Native.vectors[j]! ≠ 6204 := by
  have h : memK 2300 24 (Co2V.F 0) 6204 = false := by decide +kernel
  intro j hj e
  have : memK 2300 24 (Co2V.F 0) 6204 = true :=
    (memK_iff _ _ _ _).2 ⟨j, hj, by rw [← e, vectors_getElem! hj]; rfl⟩
  rw [h] at this
  exact Bool.false_ne_true this

theorem centCheck_cases : ∀ y ∈ centCands,
    frows y = Co2Inv.idRows ∨ frows y = Unitary.genRows 6 ∨
      (Co2.Native.actD 22 (frows y) 6144 ≠ 6144 ∧ Co2.Native.actD 22 (frows y) 6144 < 2 ^ 22) ∨
      (Co2.Native.actD 22 (frows y) 60 < 2 ^ 22 ∧
        ∀ j < 2300, Co2.Native.vectors[j]! ≠ Co2.Native.actD 22 (frows y) 60) := by
  intro y hy
  simp only [centCands, List.mem_cons, List.not_mem_nil, or_false] at hy
  have c4 : ∀ y, Co2.Native.actD 22 (frows y) 60 = 6204 →
      (Co2.Native.actD 22 (frows y) 60 < 2 ^ 22 ∧
      ∀ j < 2300, Co2.Native.vectors[j]! ≠ Co2.Native.actD 22 (frows y) 60) := fun y e => by
    rw [e]
    exact ⟨by norm_num, not_mem_6204⟩
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inr (Or.inl (by decide +kernel)))
  · exact Or.inr (Or.inr (Or.inl (by decide +kernel)))
  · exact Or.inr (Or.inr (Or.inl (by decide +kernel)))
  · exact Or.inr (Or.inr (Or.inl (by decide +kernel)))
  · exact Or.inr (Or.inr (Or.inr (c4 _ (by decide +kernel))))
  · exact Or.inr (Or.inl (arr_eq (by decide +kernel)))
  · exact Or.inr (Or.inr (Or.inr (c4 _ (by decide +kernel))))
  · exact Or.inl (arr_eq (by decide +kernel))

end CertificateChecks.Batch3126

namespace Certificates

open CertificateChecks.Batch3126 in
open CFSG.Monster.B.TwoA.Co2Inv CFSG.Monster.B.TwoA.Amalgam CFSG.Monster.B.TwoA CFSG.Monster.B in
theorem certificate3126 : (∀ w ∈ centWords,
       rowsMul (centRowsOf w) (Unitary.genRows 6) = rowsMul (Unitary.genRows 6) (centRowsOf w))
    ∧ ((∀ t < 22, centP₁[t]! = relRow centRel₁ t ∧ centP₂[t]! = relRow centRel₂ t) ∧
       Co2.Native.actD 22 centP₁ centW0 = 0 ∧ Co2.Native.actD 22 centP₂ centW0 = 0 ∧
       (∀ t < 22, centP₁[t]! < 2 ^ 22 ∧ centP₂[t]! < 2 ^ 22) ∧
       (∀ i ∈ centRel₁, i < 28) ∧ (∀ i ∈ centRel₂, i < 28) ∧ (∀ i ∈ centSel, i < 28) ∧
       centWords.length = 28 ∧ centSel.length = 22 ∧ centW0 < 2 ^ 22)
    ∧ (Nat.all (2 ^ 22) (fun y _ =>
       !(Co2.Native.actD 22 centP₁ y == 0 && Co2.Native.actD 22 centP₂ y == 0) ||
         centCands.contains y) = true)
    ∧ (frows centW0 = Co2Inv.idRows)
    ∧ (∀ y ∈ centCands,
       frows y = Co2Inv.idRows ∨ frows y = Unitary.genRows 6 ∨
         (Co2.Native.actD 22 (frows y) 6144 ≠ 6144 ∧ Co2.Native.actD 22 (frows y) 6144 < 2 ^ 22) ∨
         (Co2.Native.actD 22 (frows y) 60 < 2 ^ 22 ∧
           ∀ j < 2300, Co2.Native.vectors[j]! ≠ Co2.Native.actD 22 (frows y) 60)) :=
  ⟨centCheck_comm, centCheck_rel, centCheck_brute, centCheck_basis, centCheck_cases⟩

end Certificates
