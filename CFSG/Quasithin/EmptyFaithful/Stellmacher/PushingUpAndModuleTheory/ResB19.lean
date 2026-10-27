module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.BaumannS3
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ResB17

public section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.F53

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CosetGeom Equiv CFSG.Quasithin.F53Mod
open CFSG.Quasithin.F53Push
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace ConfR

variable {δ μ : Geo H M} {U : Subgroup G}

theorem rplane (hA : F53Amalgam H M S) (h : ConfR δ μ U) (fr : OrthFrame δ μ) :
    ∃ (c : G) (hcU : c ∈ U) (V₀ : Subgroup G), orderOf c = 3 ∧ V₀ ≤ OoOf δ ∧
      (∀ x ∈ pCoreOf 2 U, c * x * c⁻¹ * x⁻¹ ∈ V₀) ∧ U ≤ Subgroup.normalizer (V₀ : Set G) ∧
      Qv μ ⊔ Subgroup.zpowers c = U ∧ IsThreeCyc (fr.Ψ ⟨c, h.sig.le_stab hcU⟩) ∧
      V₀ = (planeOf (fr.Ψ ⟨c, h.sig.le_stab hcU⟩)).map fr.γ := by
  obtain ⟨c, V₀, hcU, hc3, hVO, -, hOc, hRc, hUV, hUX⟩ := h.rdata hA
  refine ⟨c, hcU, V₀, hc3, hVO, hRc, hUV, hUX, h.isThreeCyc hA fr hcU hc3, ?_⟩
  rw [← hOc]
  exact fr.comm_Oo_zpowers _

theorem edge_normalizer (hA : F53Amalgam H M S) (h : ConfR δ μ U) {V₀ : Subgroup G}
    (hVZ : V₀ ≤ CFSG.Quasithin.conjClosure (quasithinOmegaOneCenter (Qv μ ⊓ U)) U)
    {g : G} (hg : g ∈ stab μ) (hne : ⁅V₀, conjSub g V₀⁆ ≠ ⊥) :
    g * g ∈ Subgroup.normalizer (pCoreOf 2 U : Set G) ∧
      g ∉ Subgroup.normalizer (pCoreOf 2 U : Set G) := by
  have hPH := h.sig.pushHyp hA
  obtain ⟨e⟩ := h.sig.shape_three_of_not_le hA h.normal_P h.hR
  have he : Nonempty (OTwoQuot U ≃* Equiv.Perm (Fin 3)) := ⟨e⟩
  have hnc := h.sig.noCharNormal hA h.normal_P
  have hB := baumannS3_holds G _ _ _ hPH he hnc
  have hy : g ∈ Subgroup.normalizer ((Qv μ ⊓ U : Subgroup G) : Set G) := h.normal_P hg
  have hne' : ⁅CFSG.Quasithin.conjClosure (quasithinOmegaOneCenter (Qv μ ⊓ U)) U,
      cj g (CFSG.Quasithin.conjClosure (quasithinOmegaOneCenter (Qv μ ⊓ U)) U)⁆ ≠ ⊥ := by
    intro hbot
    apply hne
    rw [eq_bot_iff, ← hbot]
    exact Subgroup.commutator_mono hVZ (conjSub_mono g hVZ)
  obtain ⟨h1, h2, -, -⟩ := prop41_s3 hPH he hnc hB hy hne'
  exact ⟨h1, h2⟩

end ConfR

end CFSG.Quasithin.F53
