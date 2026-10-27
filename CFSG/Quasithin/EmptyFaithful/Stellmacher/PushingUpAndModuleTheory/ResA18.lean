module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ResA17
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ResA15

public section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.F53

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CosetGeom Equiv
open CFSG.Quasithin.F53Push
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace ConfR

open SFourC

variable {δ μ : Geo H M} {U T C : Subgroup G}

theorem V0_le_Oo (hA : F53Amalgam H M S) (h : ConfR δ μ U) (hS : SFourC U T C) :
    pCoreOf 2 T ≤ OoOf δ ∧
      ∀ c ∈ T, orderOf c = 3 → ⁅OoOf δ, Subgroup.zpowers c⁆ = pCoreOf 2 T := by
  obtain ⟨eT⟩ := hS.perm
  obtain ⟨ψ, hψs, hker⟩ := h.exists_psi hA
  have hV := pCoreOf_T eT
  have hX : stab δ ≤ Subgroup.normalizer ((Qv δ : Subgroup G) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (stab δ)
  have hK2 : IsPGroup 2 (Qv δ) := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) (stab δ)
  have hKX : Qv δ ≤ stab δ := CFSG.LieType.BorelTits.pCoreOf_le 2 (stab δ)
  have key : ∀ c ∈ T, orderOf c = 3 →
      pCoreOf 2 T ≤ OoOf δ ∧ ⁅OoOf δ, Subgroup.zpowers c⁆ = pCoreOf 2 T := by
    intro c hcT hc3
    set c₀ := eT ⟨c, hcT⟩ with hc₀
    have hce : tau eT c₀ = c := mem_T_eq eT c hcT
    have hc3' : c ^ 3 = 1 := by rw [← hc3]; exact pow_orderOf_eq_one c
    have hc₀3 : c₀ ^ 3 = 1 := by
      apply tau_injective eT
      rw [map_pow, hce, map_one]
      exact hc3'
    have hc₀1 : c₀ ≠ 1 := by
      intro h1
      rw [h1, map_one] at hce
      have : orderOf c = 1 := by rw [← hce]; exact orderOf_one
      omega
    have hKd := h.kData hA hS eT hc₀3 hc₀1
    rw [hce] at hKd
    have hcX : c ∈ stab δ := h.sig.le_stab (hS.le_T hcT)
    have hL : pResidualOf 2 (stab δ) = conjClosure (stab δ) c :=
      pResidualOf_eq_conjClosure hX hKd ψ hψs hker hK2 hKX hcX
    have hO : OoOf δ = normClosure (stab δ) ((klein4).map (tau eT)) := by
      unfold OoOf; rw [hL]; exact commutator_eq_normClosure hX hKd ψ hψs hker hcX
    rw [hO, hV]
    exact ⟨V0_le_normClosure, commutator_N_c hX hKd ψ hψs hker hcX⟩
  refine ⟨?_, fun c hcT hc3 => (key c hcT hc3).2⟩
  have hc : orderOf (tau eT cyc4) = 3 := by
    rw [orderOf_injective (tau eT) (tau_injective eT), orderOf_cyc4]
  exact (key _ (tau_mem eT cyc4) hc).1

end ConfR

end CFSG.Quasithin.F53
