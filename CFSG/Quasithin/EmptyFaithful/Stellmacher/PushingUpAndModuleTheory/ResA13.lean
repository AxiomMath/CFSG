module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ResA12
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ResA9

public section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.F53

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CosetGeom Equiv CFSG.Quasithin.F53Mod
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace ConfR

open SFourC

variable {δ μ : Geo H M} {U : Subgroup G}

theorem exists_psi (hA : F53Amalgam H M S) (h : ConfR δ μ U) :
    ∃ ψ : ↥(stab δ) →* Perm (Fin 5), Function.Surjective ψ ∧
      ∀ x : ↥(stab δ), ψ x = 1 ↔ (x : G) ∈ Qv δ := by
  obtain ⟨n, ψ, hn, hs, hk⟩ := exists_quotHom hA δ
  rcases hn with ⟨rfl, -⟩ | ⟨-, hv'⟩
  · exact ⟨ψ, hs, hk⟩
  · rw [h.vtype_delta hA] at hv'; exact absurd hv' (by decide)

theorem data (hA : F53Amalgam H M S) (h : ConfR δ μ U) :
    ∃ (c : G) (V₀ : Subgroup G) (ψ : ↥(stab δ) →* Perm (Fin 5)) (_hcU : c ∈ U),
      KData (Qv δ) V₀ c ∧ Function.Surjective ψ ∧
      (∀ x : ↥(stab δ), ψ x = 1 ↔ (x : G) ∈ Qv δ) ∧
      ∃ q ∈ Qv μ, ∃ hq : q ∈ stab δ, Perm.sign (ψ ⟨q, hq⟩) = -1 := by
  obtain ⟨T, C, hS⟩ := h.pushing_up hA
  obtain ⟨eT⟩ := hS.perm
  obtain ⟨ψ, hψs, hker⟩ := h.exists_psi hA
  have hKd := h.kData hA hS eT cyc4_pow_three cyc4_ne_one
  have hcX : tau eT cyc4 ∈ stab δ := tau_mem_stab hS h eT cyc4
  have hX : stab δ ≤ Subgroup.normalizer ((Qv δ : Subgroup G) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (stab δ)
  have hK2 : IsPGroup 2 (Qv δ) := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) (stab δ)
  refine ⟨tau eT cyc4, klein4.map (tau eT), ψ, hS.le_T (tau_mem eT cyc4), hKd, hψs, hker, ?_⟩
  obtain ⟨q, hqR, hqK, w, hw, z, hz, hqe⟩ := h.exists_q0 hS eT
  have hqP : q ∈ Qv μ := (h.sig.R_le_P hqR).1
  have hqU : q ∈ U := (h.sig.R_le_P hqR).2
  have hqX : q ∈ stab δ := h.sig.le_stab hqU
  refine ⟨q, hqP, hqX, ?_⟩
  have hψq1 : ψ ⟨q, hqX⟩ ≠ 1 := fun h1 => hqK ((hker _).mp h1)
  have hψc1 := psi_c_ne_one hX hKd ψ hψs hker hK2 hcX
  have hψc3 : ψ ⟨tau eT cyc4, hcX⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨tau eT cyc4, hcX⟩ : ↥(stab δ)) ^ 3 = 1 := Subtype.ext (by simpa using hKd.c3)
    rw [this, map_one]
  have hcomm : ψ ⟨tau eT cyc4, hcX⟩ * ψ ⟨q, hqX⟩ = ψ ⟨q, hqX⟩ * ψ ⟨tau eT cyc4, hcX⟩ := by
    have hzc : z * tau eT cyc4 = tau eT cyc4 * z := (hS.comm _ (tau_mem eT cyc4) z hz).symm
    have hV : tau eT cyc4 * q * (tau eT cyc4)⁻¹ * q⁻¹ ∈ klein4.map (tau eT) := by
      rw [hqe]
      have hv : tau eT w ∈ klein4.map (tau eT) := ⟨w, hw, rfl⟩
      have h1 := hKd.V_norm _ hv
      have h2 : tau eT cyc4 * (tau eT w * z) * (tau eT cyc4)⁻¹ * (tau eT w * z)⁻¹ =
          (tau eT cyc4 * tau eT w * (tau eT cyc4)⁻¹) * (tau eT w)⁻¹ := by
        calc tau eT cyc4 * (tau eT w * z) * (tau eT cyc4)⁻¹ * (tau eT w * z)⁻¹
            = (tau eT cyc4 * tau eT w * (tau eT cyc4)⁻¹) * (tau eT cyc4 * z * (tau eT cyc4)⁻¹) *
                z⁻¹ * (tau eT w)⁻¹ := by group
          _ = _ := by rw [← hzc]; group
      rw [h2]
      exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hv)
    have hVK : tau eT cyc4 * q * (tau eT cyc4)⁻¹ * q⁻¹ ∈ Qv δ := hKd.V_le hV
    have hk1 : tau eT cyc4 * q * (tau eT cyc4)⁻¹ * q⁻¹ ∈ stab δ :=
      (CFSG.LieType.BorelTits.pCoreOf_le 2 (stab δ)) hVK
    have := (hker ⟨_, hk1⟩).mpr hVK
    have e2 : (⟨tau eT cyc4 * q * (tau eT cyc4)⁻¹ * q⁻¹, hk1⟩ : ↥(stab δ)) =
        ⟨tau eT cyc4, hcX⟩ * ⟨q, hqX⟩ * ⟨tau eT cyc4, hcX⟩⁻¹ * ⟨q, hqX⟩⁻¹ := rfl
    rw [e2, map_mul, map_mul, map_mul, map_inv, map_inv] at this
    calc ψ ⟨tau eT cyc4, hcX⟩ * ψ ⟨q, hqX⟩
        = (ψ ⟨tau eT cyc4, hcX⟩ * ψ ⟨q, hqX⟩ * (ψ ⟨tau eT cyc4, hcX⟩)⁻¹ * (ψ ⟨q, hqX⟩)⁻¹) *
            (ψ ⟨q, hqX⟩ * ψ ⟨tau eT cyc4, hcX⟩) := by group
      _ = ψ ⟨q, hqX⟩ * ψ ⟨tau eT cyc4, hcX⟩ := by rw [this, one_mul]
  have hψq8 : ψ ⟨q, hqX⟩ ^ 8 = 1 := by
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) U ⟨q, hqR⟩
    have hk' : q ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    refine pow_eight_of_two_pow_perm5 (k := k) ?_
    rw [← map_pow]
    have : (⟨q, hqX⟩ : ↥(stab δ)) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk')
    rw [this, map_one]
  exact sign_neg_of_comm hψc3 hψc1 hcomm hψq8 hψq1

end ConfR

end CFSG.Quasithin.F53
