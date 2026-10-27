module

public import CFSG.LieType.SteinbergBRSmallAltSylow

public section

namespace CFSG.Quasithin.ModB

open CFSG.LieType.SteinbergBR.SmallAlt Equiv Equiv.Perm Subgroup

theorem card_alt_six : Nat.card (alternatingGroup (Fin 6)) = 2 ^ 3 * 45 := by
  have := card_alternating (m := 6) (by norm_num)
  rw [show Nat.factorial 6 = 720 by decide] at this
  omega

theorem alt6_sylow_not_comm (Q : Sylow 2 (alternatingGroup (Fin 6))) :
    ¬ ∀ a ∈ (Q : Subgroup (alternatingGroup (Fin 6))), ∀ b ∈ (Q : Subgroup (alternatingGroup (Fin 6))),
      a * b = b * a := by
  intro hab
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := finSubgroup a6P a6P_mul a6P_inv a6P_one with hP
  have hcard : Nat.card P = 8 := card_finSubgroup _ _ _ _ a6P_injective
    fun i => (mem_alternatingGroup).2 (a6P_sign i)
  have hf : (Nat.card (alternatingGroup (Fin 6))).factorization 2 = 3 := by
    rw [card_alt_six]; decide +kernel
  let PV : Sylow 2 (alternatingGroup (Fin 6)) := Sylow.ofCard P (by rw [hcard, hf]; norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 6)) PV Q
  have h1 : ((g • PV : Sylow 2 (alternatingGroup (Fin 6))) : Subgroup (alternatingGroup (Fin 6))) =
      (Q : Subgroup (alternatingGroup (Fin 6))) := by rw [hg]
  rw [Sylow.coe_subgroup_smul] at h1
  have hPV : (PV : Subgroup (alternatingGroup (Fin 6))) = P := Sylow.coe_ofCard _ _
  rw [hPV] at h1
  have hmem : ∀ x : alternatingGroup (Fin 6), x ∈ P → g * x * g⁻¹ ∈ (Q : Subgroup (alternatingGroup (Fin 6))) := by
    intro x hx
    rw [← h1, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simpa [mul_assoc] using hx
  let x : alternatingGroup (Fin 6) := ⟨a6P 4, (mem_alternatingGroup).2 (a6P_sign 4)⟩
  let y : alternatingGroup (Fin 6) := ⟨a6P 6, (mem_alternatingGroup).2 (a6P_sign 6)⟩
  have hx : x ∈ P := ⟨4, rfl⟩
  have hy : y ∈ P := ⟨6, rfl⟩
  have h2 := hab _ (hmem x hx) _ (hmem y hy)
  have h3 : x * y = y * x := by
    have : g * (x * y) * g⁻¹ = g * (y * x) * g⁻¹ := by
      calc g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
        _ = (g * y * g⁻¹) * (g * x * g⁻¹) := h2
        _ = g * (y * x) * g⁻¹ := by group
    simpa using this
  have h4 : a6P 4 * a6P 6 ≠ a6P 6 * a6P 4 := by decide +kernel
  exact h4 (congrArg Subtype.val h3)

end CFSG.Quasithin.ModB
