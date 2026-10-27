module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ResA18

public section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.F53

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CosetGeom Equiv CFSG.Quasithin.F53Mod
open CFSG.Quasithin.F53Push
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace ConfR

variable {δ μ : Geo H M} {U : Subgroup G}

theorem rdata (hA : F53Amalgam H M S) (h : ConfR δ μ U) :
    ∃ (c : G) (V₀ : Subgroup G), c ∈ U ∧ orderOf c = 3 ∧ V₀ ≤ OoOf δ ∧ Nat.card V₀ = 4 ∧
      ⁅OoOf δ, Subgroup.zpowers c⁆ = V₀ ∧ (∀ x ∈ pCoreOf 2 U, c * x * c⁻¹ * x⁻¹ ∈ V₀) ∧
      U ≤ Subgroup.normalizer (V₀ : Set G) ∧ Qv μ ⊔ Subgroup.zpowers c = U := by
  obtain ⟨T, C, hS⟩ := h.pushing_up hA
  obtain ⟨hV4, -, -, -, -, -, -, ⟨c, hcT, hc3⟩, hcomm, -⟩ := h.A2 hA hS
  obtain ⟨hVO, hOc⟩ := h.V0_le_Oo hA hS
  have hRc := (hcomm c hcT hc3).2
  refine ⟨c, pCoreOf 2 T, hS.le_T hcT, hc3, hVO, hV4, hOc c hcT hc3, ?_, ?_, ?_⟩
  · intro x hx
    have : ⁅c, x⁆ ∈ ⁅Subgroup.zpowers c, pCoreOf 2 U⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers c) hx
    rw [Subgroup.commutator_comm, hRc] at this
    simpa [commutatorElement_def] using this
  ·
    have hVn : T ≤ Subgroup.normalizer (pCoreOf 2 T : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 T
    have hy : ∀ z ∈ C, ∀ y ∈ pCoreOf 2 T, z * y * z⁻¹ = y := fun z hz y hy => by
      have := hS.comm y (CFSG.LieType.BorelTits.pCoreOf_le 2 T hy) z hz
      calc z * y * z⁻¹ = y * z * z⁻¹ := by rw [← this]
        _ = y := by group
    have hCn : C ≤ Subgroup.normalizer (pCoreOf 2 T : Set G) := by
      intro z hz
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hyV; rw [hy z hz y hyV]; exact hyV
      · intro hyV
        have h2 : z⁻¹ * (z * y * z⁻¹) * z⁻¹⁻¹ ∈ pCoreOf 2 T := by
          rw [hy z⁻¹ (C.inv_mem hz) _ hyV]; exact hyV
        simpa [mul_assoc] using h2
    rw [← hS.sup]
    exact sup_le hVn hCn
  · have hcP : c ∉ Qv μ := by
      intro hc
      obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) (stab μ) ⟨c, hc⟩
      have hk' : c ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have h1 : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
      rw [hc3] at h1
      have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h1)
      omega
    have hcU : c ∈ U := hS.le_T hcT
    have hX : Qv μ ⊔ Subgroup.zpowers c ≤ U :=
      sup_le h.hQ ((Subgroup.zpowers_le).mpr hcU)
    have hlt : Qv μ ≠ Qv μ ⊔ Subgroup.zpowers c := fun e =>
      hcP (e ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers c))
    have hrel : (Qv μ).relIndex U = 3 := by
      have h1 := Subgroup.relIndex_mul_card (Qv μ) U
      rw [inf_of_le_left h.hQ, h.card_U hA] at h1
      have hpos : 0 < Nat.card (Qv μ) := Nat.card_pos
      nlinarith
    have hmul := Subgroup.relIndex_mul_relIndex (Qv μ) (Qv μ ⊔ Subgroup.zpowers c) U le_sup_left hX
    have hne1 : (Qv μ).relIndex (Qv μ ⊔ Subgroup.zpowers c) ≠ 1 := fun e =>
      hlt (Subgroup.relIndex_eq_one.mp e |> fun hh => le_antisymm le_sup_left hh)
    have h3 : (Qv μ ⊔ Subgroup.zpowers c).relIndex U = 1 := by
      rw [hrel] at hmul
      have hd : (Qv μ).relIndex (Qv μ ⊔ Subgroup.zpowers c) ∣ 3 := ⟨_, hmul.symm⟩
      rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h1
      · exact absurd h1 hne1
      · rw [h1] at hmul; omega
    exact le_antisymm hX (Subgroup.relIndex_eq_one.mp h3)

end ConfR

end CFSG.Quasithin.F53
