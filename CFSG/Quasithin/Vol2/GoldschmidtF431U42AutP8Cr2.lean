module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8Tr
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8Cr1

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem conj_central {f : X} (hfc : ∀ x : X, x * f = f * x) (x : X) : x⁻¹ * f * x = f := by
  rw [mul_assoc, ← hfc x, ← mul_assoc, inv_mul_cancel, one_mul]

theorem exists_two_normal (R T E : Subgroup X) (f ρ z : X) (hR2 : IsPGroup 2 R)
    (hRidx : ¬ 2 ∣ R.index) (hTi : T.relIndex R = 2) (hEi : E.relIndex R = 2)
    (hfc : ∀ x : X, x * f = f * x) (hf2 : f ^ 2 = 1) (hρR : ρ ∈ R) (hρ2 : ρ ^ 2 = f)
    (hzR : z ∈ R) (hz2 : z ^ 2 = 1) (hρz : ρ * z * ρ⁻¹ = f * z)
    (nf1 : ∀ a : X, a⁻¹ * ρ * a ∉ T) (nf2 : ∀ a : X, a⁻¹ * z * a ∉ E)
    (nf3 : ∀ a : X, a⁻¹ * (ρ * z) * a ∉ E) :
    ∃ A B : Subgroup X, A.Normal ∧ B.Normal ∧ A.index = 2 ∧ B.index = 2 ∧ A ≠ B ∧
      (∀ x : X, x ^ 2 ∈ A) ∧ (∀ x : X, x ^ 2 ∈ B) := by
  let P : Sylow 2 X := hR2.toSylow hRidx
  have hP : (P : Subgroup X) = R := rfl
  have hρ4 : ρ ^ 4 = 1 := by
    calc ρ ^ 4 = (ρ ^ 2) ^ 2 := by rw [← pow_mul]
      _ = 1 := by rw [hρ2, hf2]
  have hρz2 : (ρ * z) ^ 2 = 1 := by
    have h1 : (ρ * z) ^ 2 = (ρ * z * ρ⁻¹) * ρ ^ 2 * z := by rw [pow_two ρ, pow_two]; group
    rw [h1, hρz, hρ2]
    calc f * z * f * z = f * (z * f) * z := by rw [mul_assoc f z f]
      _ = f * (f * z) * z := by rw [hfc z]
      _ = f ^ 2 * z ^ 2 := by simp only [pow_two, mul_assoc]
      _ = 1 := by rw [hf2, hz2, one_mul]
  obtain ⟨N₁, hN₁, hi₁, hs₁, hg₁⟩ := thompson_transfer_quartic P (Q := T) (by rw [hP]; exact hTi)
    (g := ρ) (by rw [hP]; exact hρR) hρ4
    (fun x => by rw [hρ2]; exact conj_central hfc x) nf1
  obtain ⟨N₂, hN₂, hi₂, hs₂, hg₂⟩ := thompson_transfer_quartic P (Q := E) (by rw [hP]; exact hEi)
    (g := z) (by rw [hP]; exact hzR)
    (by calc z ^ 4 = (z ^ 2) ^ 2 := by rw [← pow_mul]
          _ = 1 := by rw [hz2, one_pow])
    (fun x => by rw [hz2]; simp) nf2
  obtain ⟨N₃, hN₃, hi₃, hs₃, hg₃⟩ := thompson_transfer_quartic P (Q := E) (by rw [hP]; exact hEi)
    (g := ρ * z) (by rw [hP]; exact R.mul_mem hρR hzR)
    (by calc (ρ * z) ^ 4 = ((ρ * z) ^ 2) ^ 2 := by rw [← pow_mul]
          _ = 1 := by rw [hρz2, one_pow])
    (fun x => by rw [hρz2]; simp) nf3
  rcases ne_of_three hi₃ hg₁ hg₂ hg₃ with h | h
  · exact ⟨N₁, N₂, hN₁, hN₂, hi₁, hi₂, h, hs₁, hs₂⟩
  · exact ⟨N₂, N₃, hN₂, hN₃, hi₂, hi₃, h, hs₂, hs₃⟩

end CFSG.Quasithin.H13.F431.U42Aut
