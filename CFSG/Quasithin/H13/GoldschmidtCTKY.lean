module

public import CFSG.Quasithin.H13.A5Sit15c

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.A5.Orth
open CFSG.Quasithin.H13.A5 (eq_one_of_conj_eq_mul)

namespace A5SitPf15

variable {G : Type} [Group G] [Finite G] {T V V₁ V₃ L₁ H : Subgroup G}
  {S : A5Sit G T V V₁ V₃ L₁ H} {SY : A5SitY S L₁} (P : A5SitPf15 S SY)
include P

theorem commute_y {y : G} (hyI : y ∈ V ⊔ conjSub P.g⁻¹ V) (hy3 : y ^ 3 = 1) {d : G} (hdT : d ∈ T)
    (hdU : ∀ u ∈ conjClosure V₃ H, d * u = u * d) : y * d * y⁻¹ = d := by
  have hyH : y ∈ H := P.I_le_H hyI
  obtain ⟨z, hz1, hzV⟩ := S.exists_V1_eq
  have hzC : z = P.C.z := by
    rcases (P.Cz z).1 ((hzV z).2 (Or.inr rfl)) with h | h
    · exact absurd h hz1
    · exact h
  have hdQ : d ∈ pCoreOf 2 H := by
    refine (S.mem_Q_iff (S.T_le_H hdT)).2 fun u hu => ?_
    have := (hdU u hu).symm
    rw [← this, mul_inv_cancel_right, mul_inv_cancel]
    exact Subgroup.one_mem _
  have hdN := P.Q_le_NI hdQ
  set k := y * d * y⁻¹ * d⁻¹ with hk
  have hkI : k ∈ V ⊔ conjSub P.g⁻¹ V := by
    have h1 : d * y⁻¹ * d⁻¹ ∈ V ⊔ conjSub P.g⁻¹ V :=
      (Subgroup.mem_normalizer_iff.mp hdN _).mp ((V ⊔ conjSub P.g⁻¹ V).inv_mem hyI)
    have := (V ⊔ conjSub P.g⁻¹ V).mul_mem hyI h1
    simpa [hk, mul_assoc] using this
  have hkC : ∀ u ∈ conjClosure V₃ H, k * u = u * k := by
    intro u hu
    have hdu : ∀ x ∈ conjClosure V₃ H, d * x = x * d := hdU
    have hy' : y⁻¹ * u * y ∈ conjClosure V₃ H := by
      have := (Subgroup.mem_normalizer_iff.mp
        (le_normalizer_conjClosure V₃ H (H.inv_mem hyH)) u).mp hu
      simpa using this
    have h1 := hdu _ hy'
    have h2 := hdu u hu
    have hdinv : d⁻¹ * u = u * d⁻¹ := by
      calc d⁻¹ * u = d⁻¹ * (u * d) * d⁻¹ := by group
        _ = d⁻¹ * (d * u) * d⁻¹ := by rw [h2]
        _ = u * d⁻¹ := by group
    calc k * u = y * d * y⁻¹ * (d⁻¹ * u) := by rw [hk]; group
      _ = y * d * y⁻¹ * (u * d⁻¹) := by rw [hdinv]
      _ = y * (d * (y⁻¹ * u * y)) * y⁻¹ * d⁻¹ := by group
      _ = y * ((y⁻¹ * u * y) * d) * y⁻¹ * d⁻¹ := by rw [h1]
      _ = u * k := by rw [hk]; group
  have hkQ : k ∈ pCoreOf 2 H := by
    refine (S.mem_Q_iff (P.I_le_H hkI)).2 fun u hu => ?_
    rw [hkC u hu, mul_inv_cancel_right, mul_inv_cancel]
    exact Subgroup.one_mem _
  have hkU : k ∈ conjClosure V₃ H := by
    rw [← P.I_inf_Q]
    exact ⟨hkI, hkQ⟩
  have hkV1 := P.mem_V1_of_central hkU hkC
  rcases (hzV k).1 hkV1 with h | h
  · rw [hk] at h
    calc y * d * y⁻¹ = y * d * y⁻¹ * d⁻¹ * d := by group
      _ = d := by rw [h, one_mul]
  · exfalso
    apply hz1
    have hz2 : z * z = 1 := by
      rw [hzC, ← pow_two]
      exact P.C.z_sq
    refine eq_one_of_conj_eq_mul (d := d) hy3 hz2 ?_ ?_
    · rw [hzC]
      exact P.comm_z hyH
    · rw [← h, hk]
      group

end A5SitPf15

end CFSG.Quasithin.H13
