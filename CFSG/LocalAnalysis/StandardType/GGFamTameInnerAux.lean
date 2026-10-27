module

public import CFSG.LocalAnalysis.StandardType.GGFamTameRangeSpan

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement

theorem famInner_orbit_commutator_mem_commutator_CQ
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hρ : ∀ γ ∈ kernelRoots χ, S.ρ γ ∈ kernelRoots χ) (i : KernelComponent χ) {s : ℕ} [NeZero s]
    (hs : (S.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[s] '' componentRoots χ i =
      componentRoots χ i)
    (hmin : ∀ k, 0 < k → k < s →
      (S.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[k] '' componentRoots χ i ≠
        componentRoots χ i)
    (σ : L ≃+* L) (hsL : ∃ u : Lˣ, u ^ 2 ≠ 1)
    (hF : ∀ d : L, σ d = d → d ≠ 0 → d = 1) {g g' : ModGL τ L}
    (hg : g ∈ rootSpan τ L (componentRoots χ i))
    (hg' : g' ∈ rootSpan τ L (componentRoots χ i))
    (hgZ : frobGL σ g * g⁻¹ ∈ (famOrbitFamily S hρ i hs hmin).Z)
    (hgZ' : frobGL σ g' * g'⁻¹ ∈ (famOrbitFamily S hρ i hs hmin).Z) :
    ⁅g, g'⁆ ∈ ⁅CQ σ i, CQ σ i⁆ := by
  have hU := famRangeSpan_unionRootSpan_singleton_eq (L := L) (χ := χ) i
  exact commutator_mem_commutator_CQ (σ := σ) (i := i) hsL hF
    (fun z hz a ha => famRangeSpan_orbit_centralizer_hyp S hρ i hs hmin z hz a ha)
    (by rw [hU]; exact hg) (by rw [hU]; exact hg') hgZ hgZ'

end CFSG.StandardType.TableCRes
