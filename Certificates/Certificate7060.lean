module

public import CFSG.Quasithin.Background.HMathieuCentInputs
import Certificates.Kernel.MathieuAut.K7060
import CFSG.Certificates.Kernel.MathieuAut.ColsKUse

public section

open CFSG.KS.MathieuAut CFSG.Quasithin.H.Mathieu CFSG.Decide CertificateChecks.KernelMathieuAut

namespace Certificates

open CFSG CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.Monster.Code in
theorem certificate7060 :
    (∀ a ∈ cent22H ++ cent22S, inAutOK a = true ∧ a[0]! = 0 ∧ a[1]! = 1)
    ∧ (∀ a ∈ cent22H, act10 a 48 = 48)
    ∧ (∀ m < 1024, (∀ a ∈ cent22H, act10 a m = m) → m = 0 ∨ m = 48)
    ∧ (∀ m < 1024, m ∈ combos (cent22S.map fun a => act10 a 48))
    ∧ (o2Masks22.Nodup)
    ∧ (∃ i < 12, syndM (permM swap01Arr (Bmask i)) ≠ 0)
    ∧ (∀ a ∈ cent11H ++ cent11S, inAutOK a = true ∧ a[0]! = 0)
    ∧ (∀ a ∈ cent11H, act11 a 95 = 95)
    ∧ (∀ m < 2048, (∀ a ∈ cent11H, act11 a m = m) → m = 0 ∨ m = 95)
    ∧ (∀ m < 2048, m ∈ combos (cent11S.map fun a => act11 a 95))
    ∧ (∀ i j k l : Fin 24, i ≠ j → k ≠ l →
       pairImg11 i j = pairImg11 k l → (i = k ∧ j = l) ∨ (i = l ∧ j = k)) := by
  have m22 := memK_spec (P := fun a => a[0]! == 0 && a[1]! == 1) k7060_mem22
  have m11 := memK_spec (P := fun a => a[0]! == 0) k7060_mem11
  have hH22 : ∀ a ∈ cent22H, a.size = 24 := fun a ha => (m22 a (List.mem_append_left _ ha)).1
  have hS22 : ∀ a ∈ cent22S, a.size = 24 := fun a ha => (m22 a (List.mem_append_right _ ha)).1
  have hH11 : ∀ a ∈ cent11H, a.size = 24 := fun a ha => (m11 a (List.mem_append_left _ ha)).1
  have hS11 : ∀ a ∈ cent11S, a.size = 24 := fun a ha => (m11 a (List.mem_append_right _ ha)).1
  have c10 : ∀ a : Array ℕ, a.size = 24 → ∀ m, act10 a m = actM (cols10 a.toList) m :=
    fun _ ha m => act10_eq_cols ha m
  have c11 : ∀ a : Array ℕ, a.size = 24 → ∀ m, act11 a m = actM (cols11 a.toList) m :=
    fun _ ha m => act11_eq_cols ha m
  refine ⟨fun a ha => ?_, fun a ha => ?_, fun m hm h => ?_, fun m hm => ?_,
    nodup_of_bitsetNodup_nat k7060_o2Masks22, k7060_swap01, fun a ha => ?_, fun a ha => ?_,
    fun m hm h => ?_, fun m hm => ?_,
    pairImg11_inj_of_nodup (nodup_of_bitsetNodup_nat k7060_o2Masks24)⟩
  · obtain ⟨-, h1, h2⟩ := m22 a ha
    simp only [Bool.and_eq_true, beq_iff_eq] at h2
    exact ⟨h1, h2⟩
  · rw [c10 a (hH22 a ha)]
    simpa using List.all_eq_true.1 k7060_fix0_22 a ha
  · simpa using fixAll_cols_spec c10 hH22 k7060_fix22 m hm fun a ha => by simp [h a ha]
  · rw [map_act_cols c10 hS22]
    exact spanAll_spec k7060_span22 m hm
  · obtain ⟨-, h1, h2⟩ := m11 a ha
    simp only [beq_iff_eq] at h2
    exact ⟨h1, h2⟩
  · rw [c11 a (hH11 a ha)]
    simpa using List.all_eq_true.1 k7060_fix0_11 a ha
  · simpa using fixAll_cols_spec c11 hH11 k7060_fix11 m hm fun a ha => by simp [h a ha]
  · rw [map_act_cols c11 hS11]
    exact spanAll_spec k7060_span11 m hm

end Certificates
