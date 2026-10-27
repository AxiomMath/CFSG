module

public import CFSG.Quasithin.Background.HMathieuO2CertInputs
import Certificates.Kernel.MathieuAut.K7066
import CFSG.Certificates.Kernel.MathieuAut.ColsKUse

public section

open CFSG.KS.MathieuAut CFSG.Quasithin.H.Mathieu CertificateChecks.KernelMathieuAut

namespace Certificates

open CFSG CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.Monster.Code in
theorem certificate7066 :
    (∀ a ∈ o2H0_10 ++ o2H1_10 ++ o2S_10 ++ o2C_10.map Prod.fst,
       inAutOK a = true ∧ a[0]! = 0 ∧ a[1]! = 1 ∧ a[2]! = 2)
    ∧ (∀ m < 2 ^ 10, (∀ a ∈ o2H0_10, act10 a m = m) → m = 0 ∨ m = 48)
    ∧ (∀ a ∈ o2H1_10, act10 a 16 = 16 ∨ act10 a 16 = 16 ^^^ 48)
    ∧ (∀ m < 2 ^ 10, (∀ a ∈ o2H1_10, act10 a m = m ∨ act10 a m = m ^^^ 48) →
       m = 0 ∨ m = 48 ∨ m = 16 ∨ m = 16 ^^^ 48)
    ∧ (∀ m < 2 ^ 10, m ∈ combos (48 :: o2S_10.map fun a => act10 a 16))
    ∧ (∀ m < 2 ^ 10, m ∈ combos (o2C_10.map fun p => act10 p.1 p.2 ^^^ p.2))
    ∧ (actM cc10Cols (pairMask 0 ((2 : Fin 24) : ℕ)) = 48)
    ∧ (∀ a ∈ o2H0_11 ++ o2H1_11 ++ o2S_11 ++ o2C_11.map Prod.fst,
       inAutOK a = true ∧ a[0]! = 0 ∧ a[1]! = 1)
    ∧ (∀ m < 2 ^ 11, (∀ a ∈ o2H0_11, act11 a m = m) → m = 0 ∨ m = 95)
    ∧ (∀ a ∈ o2H1_11, act11 a 63 = 63 ∨ act11 a 63 = 63 ^^^ 95)
    ∧ (∀ m < 2 ^ 11, (∀ a ∈ o2H1_11, act11 a m = m ∨ act11 a m = m ^^^ 95) →
       m = 0 ∨ m = 95 ∨ m = 63 ∨ m = 63 ^^^ 95)
    ∧ (∀ m < 2 ^ 11, m ∈ combos (95 :: o2S_11.map fun a => act11 a 63))
    ∧ (∀ m < 2 ^ 11, m ∈ combos (o2C_11.map fun p => act11 p.1 p.2 ^^^ p.2))
    ∧ (pairImg11 ((0 : Fin 24) : ℕ) ((1 : Fin 24) : ℕ) = 95) := by
  have m10 := memK_spec (P := fun a => a[0]! == 0 && a[1]! == 1 && a[2]! == 2) k7066_mem10
  have m11 := memK_spec (P := fun a => a[0]! == 0 && a[1]! == 1) k7066_mem11
  have hH0_10 : ∀ a ∈ o2H0_10, a.size = 24 := fun a ha => (m10 a (by simp [ha])).1
  have hH1_10 : ∀ a ∈ o2H1_10, a.size = 24 := fun a ha => (m10 a (by simp [ha])).1
  have hS10 : ∀ a ∈ o2S_10, a.size = 24 := fun a ha => (m10 a (by simp [ha])).1
  have hC10 : ∀ p ∈ o2C_10, p.1.size = 24 := fun p hp =>
    (m10 p.1 (List.mem_append_right _ (List.mem_map_of_mem hp))).1
  have hH0_11 : ∀ a ∈ o2H0_11, a.size = 24 := fun a ha => (m11 a (by simp [ha])).1
  have hH1_11 : ∀ a ∈ o2H1_11, a.size = 24 := fun a ha => (m11 a (by simp [ha])).1
  have hS11 : ∀ a ∈ o2S_11, a.size = 24 := fun a ha => (m11 a (by simp [ha])).1
  have hC11 : ∀ p ∈ o2C_11, p.1.size = 24 := fun p hp =>
    (m11 p.1 (List.mem_append_right _ (List.mem_map_of_mem hp))).1
  have c10 : ∀ a : Array ℕ, a.size = 24 → ∀ m, act10 a m = actM (cols10 a.toList) m :=
    fun _ ha m => act10_eq_cols ha m
  have c11 : ∀ a : Array ℕ, a.size = 24 → ∀ m, act11 a m = actM (cols11 a.toList) m :=
    fun _ ha m => act11_eq_cols ha m
  refine ⟨fun a ha => ?_, fun m hm h => ?_, fun a ha => ?_, fun m hm h => ?_, fun m hm => ?_,
    fun m hm => ?_, k7066_pair10, fun a ha => ?_, fun m hm h => ?_, fun a ha => ?_,
    fun m hm h => ?_, fun m hm => ?_, fun m hm => ?_, k7066_pair11⟩
  · obtain ⟨-, h1, h2⟩ := m10 a ha
    simp only [Bool.and_eq_true, beq_iff_eq] at h2
    exact ⟨h1, h2.1.1, h2.1.2, h2.2⟩
  · simpa using fixAll_cols_spec c10 hH0_10 k7066_fix0_10 m hm fun a ha => by simp [h a ha]
  · rw [c10 a (hH1_10 a ha)]
    have h1 := List.all_eq_true.1 k7066_h1_10 a ha
    simpa only [Bool.or_eq_true, beq_iff_eq] using h1
  · have h1 := fixAll_cols_spec c10 hH1_10 k7066_fix1_10 m hm fun a ha => by
      simpa only [Bool.or_eq_true, beq_iff_eq] using h a ha
    simp only [Bool.or_eq_true, beq_iff_eq] at h1
    rcases h1 with ((h1 | h1) | h1) | h1 <;> simp [h1]
  · rw [map_act_cols c10 hS10]
    exact spanAll_spec k7066_span10 m hm
  · have e : (o2C_10.map fun p => act10 p.1 p.2 ^^^ p.2) =
        o2C_10.map fun p => actM (cols10 p.1.toList) p.2 ^^^ p.2 :=
      List.map_congr_left fun p hp => by rw [c10 p.1 (hC10 p hp)]
    rw [e]
    exact spanAll_spec k7066_comm10 m hm
  · obtain ⟨-, h1, h2⟩ := m11 a ha
    simp only [Bool.and_eq_true, beq_iff_eq] at h2
    exact ⟨h1, h2⟩
  · simpa using fixAll_cols_spec c11 hH0_11 k7066_fix0_11 m hm fun a ha => by simp [h a ha]
  · rw [c11 a (hH1_11 a ha)]
    have h1 := List.all_eq_true.1 k7066_h1_11 a ha
    simpa only [Bool.or_eq_true, beq_iff_eq] using h1
  · have h1 := fixAll_cols_spec c11 hH1_11 k7066_fix1_11 m hm fun a ha => by
      simpa only [Bool.or_eq_true, beq_iff_eq] using h a ha
    simp only [Bool.or_eq_true, beq_iff_eq] at h1
    rcases h1 with ((h1 | h1) | h1) | h1 <;> simp [h1]
  · rw [map_act_cols c11 hS11]
    exact spanAll_spec k7066_span11 m hm
  · have e : (o2C_11.map fun p => act11 p.1 p.2 ^^^ p.2) =
        o2C_11.map fun p => actM (cols11 p.1.toList) p.2 ^^^ p.2 :=
      List.map_congr_left fun p hp => by rw [c11 p.1 (hC11 p hp)]
    rw [e]
    exact spanAll_spec k7066_comm11 m hm

end Certificates
