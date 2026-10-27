module

public import CFSG.Quasithin.H13.GoldschmidtU43EVR1

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

namespace JWSetup

variable [Finite G] {z : G} (S : JWSetup z) (r : S.Rho)

@[expose] noncomputable def crd (m : ↥S.Mg) : Fin 4 → ZMod 3 :=
  (Equiv.ofBijective _ (evC_basis_bijective r)).symm m

theorem evC_crd (m : ↥S.Mg) : evC (basis r) (S.crd r m) = m :=
  (Equiv.ofBijective _ (evC_basis_bijective r)).apply_symm_apply m

theorem crd_evC (a : Fin 4 → ZMod 3) : S.crd r (evC (basis r) a) = a :=
  (Equiv.ofBijective _ (evC_basis_bijective r)).symm_apply_apply a

theorem crd_mul (m m' : ↥S.Mg) : S.crd r (m * m') = S.crd r m + S.crd r m' := by
  have h : m * m' = evC (basis r) (S.crd r m + S.crd r m') := by
    rw [evC_add (x := basis r) (fun _ => S.pow_three_M _), S.evC_crd, S.evC_crd]
  rw [h, S.crd_evC]

theorem crd_one : S.crd r (1 : ↥S.Mg) = 0 := by
  have h : (1 : ↥S.Mg) = evC (basis r) 0 := (evC_zero _).symm
  rw [h, S.crd_evC]

theorem crd_inv (m : ↥S.Mg) : S.crd r m⁻¹ = - S.crd r m := by
  have h : m⁻¹ = evC (basis r) (- S.crd r m) := by
    have := evC_neg (x := basis r) (fun _ => S.pow_three_M _) (S.crd r m)
    rw [S.evC_crd] at this
    exact this.symm
  rw [h, S.crd_evC]

@[expose] noncomputable def σ₁M : ↥S.Mg := ⟨(S.σ₁ : G), S.Tg_le_Mg S.σ₁G_mem_Tg⟩

@[expose] noncomputable def σ₂M : ↥S.Mg := ⟨(S.σ₂ : G), S.Tg_le_Mg S.σ₂G_mem_Tg⟩

@[expose] noncomputable def ρM : ↥S.Mg := ⟨r.ρ, r.mem_Mg⟩

@[expose] noncomputable def ρ₂M : ↥S.Mg := ⟨S.rho2 r.ρ, S.rho2_mem_Mg r.mem_Mg⟩

theorem crd_ρM : S.crd r (S.ρM r) = ![0, 0, 1, 0] := by
  have h : S.ρM r = evC (basis r) ![0, 0, 1, 0] := by
    have := evC_unit (x := basis r) ![0, 0, 1, 0] 2 (by funext i; fin_cases i <;> simp)
    rw [this]
    rfl
  rw [h, S.crd_evC]

theorem crd_ρ₂M : S.crd r (S.ρ₂M r) = ![0, 0, 0, 1] := by
  have h : S.ρ₂M r = evC (basis r) ![0, 0, 0, 1] := by
    have := evC_unit (x := basis r) ![0, 0, 0, 1] 3 (by funext i; fin_cases i <;> simp)
    rw [this]
    rfl
  rw [h, S.crd_evC]

theorem basis_zero : basis r 0 = S.σ₁M * S.σ₂M := Subtype.ext (by
  show S.sigG = (S.σ₁ : G) * (S.σ₂ : G)
  exact sigG_eq S)

theorem basis_one : basis r 1 = S.σ₁M * S.σ₂M⁻¹ := Subtype.ext (by
  show S.sigp = (S.σ₁ : G) * (S.σ₂ : G)⁻¹
  exact sigp_eq S)

theorem σ₁M_pow_three : S.σ₁M ^ 3 = 1 := S.pow_three_M _

theorem σ₂M_pow_three : S.σ₂M ^ 3 = 1 := S.pow_three_M _

theorem evC_σ₁ : evC (basis r) ![2, 2, 0, 0] = S.σ₁M := by
  have h2 : (2 : ZMod 3).val = 2 := rfl
  have h0 : (0 : ZMod 3).val = 0 := rfl
  have e : evC (basis r) ![2, 2, 0, 0] = basis r 0 ^ 2 * basis r 1 ^ 2 := by
    simp [evC, Fin.prod_univ_four, h2, h0]
  rw [e, S.basis_zero r, S.basis_one r]
  have h3 := S.σ₁M_pow_three
  have h4 := S.σ₂M_pow_three
  calc (S.σ₁M * S.σ₂M) ^ 2 * (S.σ₁M * S.σ₂M⁻¹) ^ 2
      = (S.σ₁M ^ 2 * S.σ₁M ^ 2) * (S.σ₂M ^ 2 * (S.σ₂M⁻¹) ^ 2) := by
        rw [mul_pow, mul_pow, mul_mul_mul_comm]
    _ = S.σ₁M ^ 3 * S.σ₁M := by
        have hs2 : S.σ₂M ^ 2 * (S.σ₂M⁻¹) ^ 2 = 1 := by
          rw [← mul_pow, mul_inv_cancel, one_pow]
        rw [hs2, mul_one, ← pow_add, ← pow_succ]
    _ = S.σ₁M := by rw [h3, one_mul]

theorem evC_σ₂ : evC (basis r) ![2, 1, 0, 0] = S.σ₂M := by
  have h2 : (2 : ZMod 3).val = 2 := rfl
  have h1 : (1 : ZMod 3).val = 1 := rfl
  have h0 : (0 : ZMod 3).val = 0 := rfl
  have e : evC (basis r) ![2, 1, 0, 0] = basis r 0 ^ 2 * basis r 1 := by
    simp [evC, Fin.prod_univ_four, h2, h1, h0]
  rw [e, S.basis_zero r, S.basis_one r]
  have h3 := S.σ₁M_pow_three
  have h4 := S.σ₂M_pow_three
  calc (S.σ₁M * S.σ₂M) ^ 2 * (S.σ₁M * S.σ₂M⁻¹)
      = (S.σ₁M ^ 2 * S.σ₁M) * (S.σ₂M ^ 2 * S.σ₂M⁻¹) := by
        rw [mul_pow, mul_mul_mul_comm]
    _ = S.σ₁M ^ 3 * S.σ₂M := by
        rw [← pow_succ, pow_two S.σ₂M, mul_assoc, mul_inv_cancel, mul_one]
    _ = S.σ₂M := by rw [h3, one_mul]

theorem crd_σ₁M : S.crd r S.σ₁M = ![2, 2, 0, 0] := by
  rw [← S.evC_σ₁ r, S.crd_evC]

theorem crd_σ₂M : S.crd r S.σ₂M = ![2, 1, 0, 0] := by
  rw [← S.evC_σ₂ r, S.crd_evC]

theorem mem_Ag_of_mem_Mg_inf_V3 {V₃ : Subgroup G} (hV : S.IsV3 V₃) (hAU : (S.A : G) ∈ Uz z)
    {x : G} (hxM : x ∈ S.Mg) (hxV : x ∈ V₃) : x ∈ S.Ag r := by
  set m : ↥S.Mg := ⟨x, hxM⟩ with hm
  set c := S.crd r m with hc
  have hmc : evC (basis r) c = m := S.evC_crd r m
  set n : ZMod 3 := c 0 - c 1 with hn
  have k0 : ∀ a b : ZMod 3, a = 2 * (a + b) + (a - b) * 2 := by decide
  have k1 : ∀ a b : ZMod 3, b = 2 * (a + b) + (a - b) * 1 := by decide
  have hdec : c = vec3 (c 0 + c 1) (c 2) (c 3) + n • ![2, 1, 0, 0] := by
    ext i
    fin_cases i
    · simpa [vec3, hn] using k0 (c 0) (c 1)
    · simpa [vec3, hn] using k1 (c 0) (c 1)
    · simp [vec3]
    · simp [vec3]
  have hm2 : m = evC (basis r) (vec3 (c 0 + c 1) (c 2) (c 3)) * S.σ₂M ^ n.val := by
    rw [← hmc, hdec, evC_add (x := basis r) (fun _ => S.pow_three_M _),
      evC_smul (x := basis r) (fun _ => S.pow_three_M _), S.evC_σ₂ r, ← hdec]
  have hA : ((evC (basis r) (vec3 (c 0 + c 1) (c 2) (c 3)) : ↥S.Mg) : G) ∈ S.Ag r :=
    S.evC_vec3_mem_Ag r _ _ _
  have hσn : (S.σ₂ : G) ^ n.val ∈ V₃ := by
    have h1 : x = ((evC (basis r) (vec3 (c 0 + c 1) (c 2) (c 3)) : ↥S.Mg) : G) *
        (S.σ₂ : G) ^ n.val := by
      have := congrArg Subtype.val hm2
      simpa [hm, σ₂M] using this
    have h2 : (S.σ₂ : G) ^ n.val = (((evC (basis r) (vec3 (c 0 + c 1) (c 2) (c 3)) : ↥S.Mg) :
        G))⁻¹ * x := by
      rw [h1]
      group
    rw [h2]
    exact mul_mem (inv_mem (S.Ag_le_V3 hV hAU r hA)) hxV
  have hn0 : n = 0 := by
    by_contra hne
    apply S.σ₂_not_mem_Vg hAU
    apply hV.le
    have h3 : (S.σ₂ : G) ^ 3 = 1 := S.pow_three_Tg S.σ₂G_mem_Tg
    have hval : n.val = 1 ∨ n.val = 2 := by
      have hlt : n.val < 3 := ZMod.val_lt n
      have hne' : n.val ≠ 0 := fun h => hne ((ZMod.val_eq_zero n).mp h)
      omega
    rcases hval with h | h
    · rw [h, pow_one] at hσn
      exact hσn
    · rw [h] at hσn
      have : (S.σ₂ : G) = ((S.σ₂ : G) ^ 2) ^ 2 := by
        calc (S.σ₂ : G) = (S.σ₂ : G) ^ 3 * (S.σ₂ : G) := by rw [h3, one_mul]
          _ = ((S.σ₂ : G) ^ 2) ^ 2 := by group
      rw [this]
      exact pow_mem hσn 2
  have hc01 : c = vec3 (c 0 + c 1) (c 2) (c 3) := by
    have h := hdec
    rw [hn0, zero_smul, add_zero] at h
    exact h
  have hmeq : m = evC (basis r) (vec3 (c 0 + c 1) (c 2) (c 3)) := by
    rw [← hc01, hmc]
  have : x = ((evC (basis r) (vec3 (c 0 + c 1) (c 2) (c 3)) : ↥S.Mg) : G) := by
    have := congrArg Subtype.val hmeq
    simpa [hm] using this
  rw [this]
  exact hA

theorem comm_sigma2_mem_Ag {V₃ : Subgroup G} (hV : S.IsV3 V₃) (hAU : (S.A : G) ∈ Uz z)
    {x : G} (hxV : x ∈ V₃) (hxN : x ∈ S.Ng) :
    (S.σ₂ : G) * x * (S.σ₂ : G)⁻¹ * x⁻¹ ∈ S.Ag r := by
  have hσ₂M : (S.σ₂ : G) ∈ S.Mg := S.Tg_le_Mg S.σ₂G_mem_Tg
  have hσ₂C : (S.σ₂ : G) ∈ S.Cg1 := by
    rw [Cg1, Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val S.σ₁σ₂_comm.symm
  apply S.mem_Ag_of_mem_Mg_inf_V3 r hV hAU
  · have h1 : x * (S.σ₂ : G)⁻¹ * x⁻¹ ∈ S.Mg := by
      have := (S.mem_Ng.mp hxN _).mp (S.Mg.inv_mem hσ₂M)
      simpa using this
    have e : (S.σ₂ : G) * x * (S.σ₂ : G)⁻¹ * x⁻¹ = (S.σ₂ : G) * (x * (S.σ₂ : G)⁻¹ * x⁻¹) := by
      group
    rw [e]
    exact S.Mg.mul_mem hσ₂M h1
  · have h1 : (S.σ₂ : G) * x * (S.σ₂ : G)⁻¹ ∈ V₃ := hV.conj _ hσ₂C x hxV
    exact V₃.mul_mem h1 (V₃.inv_mem hxV)

end JWSetup

end CFSG.Quasithin.H13.U43
