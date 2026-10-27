module

public import CFSG.Quasithin.Background.HMathieuCodeCentInputs
import Certificates.Kernel.MathieuAut.K7061
import CFSG.Certificates.Kernel.MathieuAut.ColsKUse

public section

open CFSG.KS.MathieuAut CFSG.Quasithin.H.Mathieu CertificateChecks.KernelMathieuAut

namespace Certificates

open CFSG CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.Monster.Code CFSG.Blueprint in
theorem certificate7061 :
    (∀ a ∈ centC11H ++ centC11S, inAutOK a = true ∧ a[0]! = 0)
    ∧ (∀ a ∈ centC11H, actC11 a 1299 = 1299)
    ∧ (∀ m < 2048, (∀ a ∈ centC11H, actC11 a m = m) → m = 0 ∨ m = 1299)
    ∧ (∀ m < 2048, m ∈ combos (centC11S.map fun a => actC11 a 1299))
    ∧ (∀ a ∈ centC10H ++ centC10S, inAutOK a = true ∧ a[0]! = 0 ∧ a[1]! = 1)
    ∧ (∀ a ∈ centC10H, actC10 a 608 = 608)
    ∧ (∀ m < 1024, (∀ a ∈ centC10H, actC10 a m = m) → m = 0 ∨ m = 608)
    ∧ (∀ m < 1024, m ∈ combos (centC10S.map fun a => actC10 a 608))
    ∧ (∀ e < 4096,
       (∀ p < 24, ∃ q < 24, syndCols.getD q 0 = syndCols.getD p 0 ^^^ e) → e = 0)
    ∧ (∀ e < 1024,
       (∀ p < 24, ∃ q < 24, cc10Cols.getD q 0 = cc10Cols.getD p 0 ^^^ e) → e = 0) := by
  have m11 := memK_spec (P := fun a => a[0]! == 0) k7061_memC11
  have m10 := memK_spec (P := fun a => a[0]! == 0 && a[1]! == 1) k7061_memC10
  have hH11 : ∀ a ∈ centC11H, a.size = 24 := fun a ha => (m11 a (List.mem_append_left _ ha)).1
  have hS11 : ∀ a ∈ centC11S, a.size = 24 := fun a ha => (m11 a (List.mem_append_right _ ha)).1
  have hH10 : ∀ a ∈ centC10H, a.size = 24 := fun a ha => (m10 a (List.mem_append_left _ ha)).1
  have hS10 : ∀ a ∈ centC10S, a.size = 24 := fun a ha => (m10 a (List.mem_append_right _ ha)).1
  have c11 : ∀ a : Array ℕ, a.size = 24 → ∀ m, actC11 a m = actM (colsC11 a.toList) m :=
    fun _ ha m => actC11_eq_cols ha m
  have c10 : ∀ a : Array ℕ, a.size = 24 → ∀ m, actC10 a m = actM (colsC10 a.toList) m :=
    fun _ ha m => actC10_eq_cols ha m
  refine ⟨fun a ha => ?_, fun a ha => ?_, fun m hm h => ?_, fun m hm => ?_, fun a ha => ?_,
    fun a ha => ?_, fun m hm h => ?_, fun m hm => ?_,
    fun e _ he => transOK_spec k7061_syndCols.1 k7061_syndCols.2 e he,
    fun e _ he => transOK_spec k7061_cc10Cols.1 k7061_cc10Cols.2 e he⟩
  · obtain ⟨-, h1, h2⟩ := m11 a ha
    simp only [beq_iff_eq] at h2
    exact ⟨h1, h2⟩
  · rw [c11 a (hH11 a ha)]
    simpa using List.all_eq_true.1 k7061_fix0C11 a ha
  · simpa using fixAll_cols_spec c11 hH11 k7061_fixC11 m hm fun a ha => by simp [h a ha]
  · rw [map_act_cols c11 hS11]
    exact spanAll_spec k7061_spanC11 m hm
  · obtain ⟨-, h1, h2⟩ := m10 a ha
    simp only [Bool.and_eq_true, beq_iff_eq] at h2
    exact ⟨h1, h2⟩
  · rw [c10 a (hH10 a ha)]
    simpa using List.all_eq_true.1 k7061_fix0C10 a ha
  · simpa using fixAll_cols_spec c10 hH10 k7061_fixC10 m hm fun a ha => by simp [h a ha]
  · rw [map_act_cols c10 hS10]
    exact spanAll_spec k7061_spanC10 m hm

end Certificates
