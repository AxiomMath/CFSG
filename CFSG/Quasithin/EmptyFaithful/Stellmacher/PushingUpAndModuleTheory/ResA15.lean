module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ResA14
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ResA13

public section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.F53

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CosetGeom Equiv CFSG.Quasithin.F53Mod
open CFSG.Quasithin.F53Push
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

@[expose] def LOf (δ : Geo H M) : Subgroup G := pResidualOf 2 (stab δ)

@[expose] def OoOf (δ : Geo H M) : Subgroup G := ⁅Qv δ, pResidualOf 2 (stab δ)⁆

@[expose] def L1Of (δ : Geo H M) : Subgroup G :=
  Qv δ ⊓ Subgroup.centralizer (pResidualOf 2 (stab δ) : Set G)

section Core

variable {X K V₀ : Subgroup G} {c : G}
  (hX : X ≤ Subgroup.normalizer (K : Set G)) (hKd : KData K V₀ c)
  (ψ : ↥X →* Perm (Fin 5)) (hψs : Function.Surjective ψ)
  (hker : ∀ x : ↥X, ψ x = 1 ↔ (x : G) ∈ K)

include hX hKd hψs hker

theorem pResidualOf_eq_conjClosure (hK2 : IsPGroup 2 K) (hKX : K ≤ X) (hcX : c ∈ X) :
    pResidualOf 2 X = conjClosure X c := by
  rw [pResidualOf_eq_oTwoRes]
  refine le_antisymm (oTwoRes_le_conjClosure ψ hψs hKX hK2 hker hcX hKd.c3
    (psi_c_ne_one hX hKd ψ hψs hker hK2 hcX)) ?_
  unfold conjClosure
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨g, hg, rfl⟩
  refine Subgroup.subset_closure ⟨X.mul_mem (X.mul_mem hg hcX) (X.inv_mem hg), 3, by decide, ?_⟩
  rw [conj_pow, hKd.c3]; group

end Core

namespace ConfR

variable {δ μ : Geo H M} {U : Subgroup G}

theorem A3 (hA : F53Amalgam H M S) (h : ConfR δ μ U) :
    ∃ (c : G) (V₀ : Subgroup G), c ∈ U ∧ c ^ 3 = 1 ∧ c ≠ 1 ∧ V₀ ≤ OoOf δ ∧
      Nat.card V₀ = 4 ∧ IsElemAbelian 2 V₀ ∧
      ⁅OoOf δ, Subgroup.zpowers c⁆ = V₀ ∧ ⁅Qv δ, Subgroup.zpowers c⁆ = V₀ ∧
      OoOf δ ≤ Qv δ ∧ IsElemAbelian 2 (OoOf δ) ∧
      (∀ o ∈ OoOf δ, ∀ k ∈ Qv δ, o * k = k * o) ∧
      stab δ ≤ Subgroup.normalizer ((OoOf δ : Subgroup G) : Set G) ∧
      IsOrthSec (stab δ) ⊥ (OoOf δ) ∧
      stab δ ≤ Subgroup.normalizer ((L1Of δ : Subgroup G) : Set G) ∧
      Qv δ = OoOf δ ⊔ L1Of δ ∧ OoOf δ ⊓ L1Of δ = ⊥ ∧ ⁅Qv δ, Qv δ⁆ ≤ L1Of δ := by
  obtain ⟨c, V₀, ψ, hcU, hKd, hψs, hker, -⟩ := h.data hA
  have hcX : c ∈ stab δ := h.sig.le_stab hcU
  have hX : stab δ ≤ Subgroup.normalizer ((Qv δ : Subgroup G) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (stab δ)
  have hK2 : IsPGroup 2 (Qv δ) := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) (stab δ)
  have hKX : Qv δ ≤ stab δ := CFSG.LieType.BorelTits.pCoreOf_le 2 (stab δ)
  have hL : pResidualOf 2 (stab δ) = conjClosure (stab δ) c :=
    pResidualOf_eq_conjClosure hX hKd ψ hψs hker hK2 hKX hcX
  have hO : OoOf δ = normClosure (stab δ) V₀ := by
    unfold OoOf; rw [hL]; exact commutator_eq_normClosure hX hKd ψ hψs hker hcX
  have hL1 : L1Of δ = Qv δ ⊓ Subgroup.centralizer (conjClosure (stab δ) c : Set G) := by
    unfold L1Of; rw [hL]
  refine ⟨c, V₀, hcU, hKd.c3, hKd.cne, ?_, hKd.V_card, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · rw [hO]; exact V0_le_normClosure
  · exact ⟨⟨⟨fun a b => Subtype.ext (by
      have := hKd.V_cen a.1 a.2 b.1 (hKd.V_le b.2); exact this)⟩⟩,
      fun x hx => by rw [pow_two]; exact hKd.V_sq x hx⟩
  · rw [hO]; exact commutator_N_c hX hKd ψ hψs hker hcX
  · exact commutator_K_c hX hKd ψ hψs hker hcX
  · rw [hO]; exact normClosure_le_K hX hKd
  · rw [hO]; exact normClosure_isElemAbelian hX hKd ψ hψs hker
  · intro o ho k hk
    rw [hO] at ho
    exact normClosure_central hX hKd ho hk
  · rw [hO]; exact (isSec_normClosure hX hKd).normN
  · rw [hO]; exact isOrthSec_normClosure hX hKd ψ hψs hker hK2 hcX
  · rw [hL1]; exact normalizer_L1 hX hKd ψ hψs hker hcX
  · rw [hO, hL1]; exact K_eq_sup hX hKd ψ hψs hker hK2 hcX
  · rw [hO, hL1, ← inf_assoc, inf_eq_left.mpr (normClosure_le_K hX hKd)]
    exact normClosure_inf_centralizer hX hKd ψ hψs hker hK2 hcX
  · rw [hL1]; exact commutator_K_le hX hKd ψ hψs hker hcX

end ConfR

end CFSG.Quasithin.F53
