module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ResA15
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ResA11

public section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.F53

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CosetGeom Equiv CFSG.Quasithin.F53Mod
open CFSG.Quasithin.F53Push
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace ConfR

variable {δ μ : Geo H M} {U : Subgroup G}

theorem exists_edge_not_Qv (hA : F53Amalgam H M S) (h : ConfR δ μ U) :
    ∃ s ∈ stab δ ⊓ stab μ, s ∉ Qv μ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨-, -, -, h4⟩ := h.sig.counts hA h.normal_P h.hR
  have hle : stab δ ⊓ stab μ ≤ Qv δ ⊔ (Qv μ ⊓ U) := fun s hs =>
    Subgroup.mem_sup_right (by rw [h.inf_eq]; exact hcon s hs)
  have := Subgroup.relIndex_eq_one.mpr hle
  omega

theorem lemmaX (hA : F53Amalgam H M S) (h : ConfR δ μ U) :
    ∃ s : G, s ∈ stab δ ⊓ stab μ ∧ s ∉ Qv μ ∧
      (∃ l ∈ LOf δ, ∃ o ∈ OoOf δ, s = l * o) ∧
      ∀ A : Subgroup G, A ≤ Qv δ → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
        ∀ a ∈ A, ∀ b ∈ A, a * (s * b * s⁻¹) = (s * b * s⁻¹) * a := by
  obtain ⟨c, V₀, ψ, hcU, hKd, hψs, hker, q₀, hq₀P, hq₀X, hq₀sign⟩ := h.data hA
  have hcX : c ∈ stab δ := h.sig.le_stab hcU
  have hX : stab δ ≤ Subgroup.normalizer ((Qv δ : Subgroup G) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (stab δ)
  have hK2 : IsPGroup 2 (Qv δ) := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) (stab δ)
  have hKX : Qv δ ≤ stab δ := CFSG.LieType.BorelTits.pCoreOf_le 2 (stab δ)
  have hL : pResidualOf 2 (stab δ) = conjClosure (stab δ) c :=
    pResidualOf_eq_conjClosure hX hKd ψ hψs hker hK2 hKX hcX
  have hO : OoOf δ = normClosure (stab δ) V₀ := by
    unfold OoOf; rw [hL]; exact commutator_eq_normClosure hX hKd ψ hψs hker hcX
  have hcne := psi_c_ne_one hX hKd ψ hψs hker hK2 hcX
  have hQS : Qv μ ≤ stab δ ⊓ stab μ := by
    have := h.sig.P_le_edge hA
    rwa [h.inf_eq] at this
  obtain ⟨s₁, hs₁, hs₁P⟩ := h.exists_edge_not_Qv hA
  have hs₁X : s₁ ∈ stab δ := hs₁.1
  obtain ⟨s', hs'S, hs'P, hs'X, hs'sign⟩ : ∃ s' ∈ stab δ ⊓ stab μ, s' ∉ Qv μ ∧
      ∃ hs'X : s' ∈ stab δ, Perm.sign (ψ ⟨s', hs'X⟩) = 1 := by
    rcases Int.units_eq_one_or (Perm.sign (ψ ⟨s₁, hs₁X⟩)) with h1 | h1
    · exact ⟨s₁, hs₁, hs₁P, hs₁X, h1⟩
    · refine ⟨s₁ * q₀, (stab δ ⊓ stab μ).mul_mem hs₁ (hQS hq₀P), fun hmem => hs₁P ?_,
        (stab δ).mul_mem hs₁X hq₀X, ?_⟩
      · have := (Qv μ).mul_mem hmem ((Qv μ).inv_mem hq₀P)
        simpa using this
      · have e : (⟨s₁ * q₀, (stab δ).mul_mem hs₁X hq₀X⟩ : ↥(stab δ)) =
            ⟨s₁, hs₁X⟩ * ⟨q₀, hq₀X⟩ := rfl
        rw [e, map_mul, map_mul, h1, hq₀sign]
        decide
  obtain ⟨l', hl', hl'ψ⟩ := alt5_le_map_conjClosure ψ hψs hcX hKd.c3 hcne
    (Perm.mem_alternatingGroup.mpr hs'sign)
  have hl'c : (l' : G) ∈ conjClosure (stab δ) c := hl'
  have hqK : (l' : G)⁻¹ * s' ∈ Qv δ := by
    rw [← hker ⟨_, (stab δ).mul_mem ((stab δ).inv_mem l'.2) hs'X⟩]
    have e : (⟨(l' : G)⁻¹ * s', (stab δ).mul_mem ((stab δ).inv_mem l'.2) hs'X⟩ : ↥(stab δ)) =
        l'⁻¹ * ⟨s', hs'X⟩ := rfl
    rw [e, map_mul, map_inv, hl'ψ, inv_mul_cancel]
  obtain ⟨y, hy, o, ho, hqyo⟩ := exists_decomp hX hKd ψ hψs hker hK2 hcX hqK
  have hyK : y ∈ Qv δ := hy.1
  have hoK : o ∈ Qv δ := normClosure_le_K hX hKd ho
  have hyo : y * o = o * y := (normClosure_central hX hKd ho hyK).symm
  refine ⟨(l' : G) * o, ?_, ?_, ⟨l', ?_, o, ?_, rfl⟩, ?_⟩
  ·
    have hs'' : (l' : G) * o = s' * y⁻¹ := by
      have : s' = (l' : G) * (y * o) := by rw [← hqyo]; group
      rw [this, hyo]; group
    rw [hs'']
    exact (stab δ ⊓ stab μ).mul_mem hs'S ((stab δ ⊓ stab μ).inv_mem
      (hQS (h.hQδ hyK)))
  · intro hmem
    have hs'' : s' = ((l' : G) * o) * y := by
      have : s' = (l' : G) * (y * o) := by rw [← hqyo]; group
      rw [this, hyo]; group
    exact hs'P (hs'' ▸ (Qv μ).mul_mem hmem (h.hQδ hyK))
  · unfold LOf; rw [hL]; exact hl'c
  · rw [hO]; exact ho
  · intro A hAK hAc a ha b hb
    exact lemmaX_core hX hKd ψ hψs hker hK2 hcX hl'c ho hAK hAc a ha b hb

end ConfR

end CFSG.Quasithin.F53
