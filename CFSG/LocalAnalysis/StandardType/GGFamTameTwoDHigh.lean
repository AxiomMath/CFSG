module

public import CFSG.LocalAnalysis.StandardType.GGFamTameLang
public import CFSG.LocalAnalysis.StandardType.GGFamTameOrbit
public import CFSG.LocalAnalysis.StandardType.GGFamTameTransfer
public import CFSG.LocalAnalysis.StandardType.GGFamIsolation
public import CFSG.LocalAnalysis.StandardType.GGFamTameTwoDHighAux
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTamePrime

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.RootAut
open scoped commutatorElement

theorem image_componentRoots_eq_of_rank_gt_half
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hρ : ∀ γ ∈ kernelRoots χ, S.ρ γ ∈ kernelRoots χ) (i : KernelComponent χ)
    (hr : τ.rank < 2 * compRank (componentRoots χ i)) :
    S.ρ '' componentRoots χ i = componentRoots χ i :=
  famTwoDHigh_image_componentRoots_eq_of_rank_gt_half S hρ i hr

theorem langFamTame_twoD_high
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) (hp2 : p ≠ 2) {ι : Type}
    {a : ι → Fin τ.rank → Lˣ} (hT : ∀ u, rootDiagUnit τ (a u) ∈ S.D.torus)
    (hap : ∀ u j, a u j ^ p = 1) (h1 : ∃ u, rootDiagUnit τ (a u) ≠ 1)
    (i : KernelComponent (famCharHom a))
    (hk : twistKindM S.ρ (famCharHom a) i = .twoD)
    (h5 : 5 ≤ compRank (componentRoots (famCharHom a) i)) :
    CFSG.IsQuasisimple (rationalComponentM S.ρ S.Γ (famCharHom a) i) := by
  classical
  have hρ : ∀ γ ∈ kernelRoots (famCharHom a), S.ρ γ ∈ kernelRoots (famCharHom a) :=
    fun γ hγ => rho_mem_kernelRoots_famChar S a hT hγ
  have hΨ : IsRootComponent (componentRoots (famCharHom a) i) := isRootComponent_componentRoots i
  have hst : (S.ρ : (Fin τ.rank → ℤ) → _) '' componentRoots (famCharHom a) i =
      componentRoots (famCharHom a) i := by
    refine image_componentRoots_eq_of_rank_gt_half S hρ i ?_
    have h8 := CFSG.HardMathSupport.Timmesfeld.RootAut.rank_le_eight τ
    omega
  obtain ⟨v, hv, hmaps, hpos, hG⟩ :=
    famTwoDHigh_exists_isGraphTwist (M := ι → Lˣ) (χ := famCharHom a) S hρ i hk h5
  obtain ⟨_, b, j, _, _, _, hcomp⟩ := exists_isolating_element hτ a hp hp2 hap i
  have hv_b : v ∈ componentWeylGroup (componentRoots (rootCharHom b) j) := by
    rw [hcomp]; exact hv
  have hfin : (componentRoots (famCharHom a) i).Finite := famTwoDHigh_finite_of_isRootComponent hΨ
  have hiso := S.iform_rhoTwist v
  have hinj := injective_of_iform _ hiso
  have hf : IsIsometry (componentRoots (famCharHom a) i) (S.rhoTwist v) :=
    ⟨(hfin.injOn_iff_bijOn_of_mapsTo hmaps).1 hinj.injOn, fun γ _ δ _ => hiso γ δ,
      fun γ _ => map_neg _ γ⟩
  have hΔ_b : ∀ β ∈ simpleRoots (componentRoots (rootCharHom b) j),
      S.rhoTwist v β ∈ simpleRoots (componentRoots (rootCharHom b) j) := by
    intro β hβ
    rw [hcomp] at hβ ⊢
    exact hf.apply_mem_simpleRoots hΨ hpos hβ
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  letI : Fact r.Prime := ⟨hr⟩
  haveI : CharP L r := hchar
  obtain ⟨y, hyZ_b, hyM, hyv, hpin_b⟩ := S.exists_twoD_pin (a := b) hq j hv_b hΔ_b
  have hyZ_fam : y ∈ torusGroup τ L ⊔ rootSpan τ L (componentRoots (famCharHom a) i) := by
    rw [← hcomp]; exact hyZ_b
  have hpin_fam : ∀ β ∈ simpleRoots (componentRoots (famCharHom a) i), ∀ A : SL2 L,
      y * S.D.step (rootSL2 τ L β A) * y⁻¹ =
        rootSL2 τ L (S.rhoTwist v β)
          (Matrix.SpecialLinearGroup.map (iterateFrobenius L r e) A) := by
    intro β hβ A
    rw [← hcomp] at hβ
    exact hpin_b β hβ A
  exact famTwoDHigh_isQuasisimple_rationalComponentM (M := ι → Lˣ) (χ := famCharHom a)
    (Or.inr hτ) S hρ i hst hq (by omega) hmaps hpos hG hyZ_fam hyM hyv hpin_fam

end CFSG.StandardType.TableCRes
