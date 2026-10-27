module

public import CFSG.LocalAnalysis.StandardType.GGFamTypeACovers
public import CFSG.LocalAnalysis.StandardType.GGFamTypeAFrames

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Steinberg.Adjoint
  CFSG.ClassicalInvolution.WeakCT CFSG.Timmesfeld CFSG.Assembly.LowTwoRank
  CFSG.RankThree.Classical2
open scoped MatrixGroups commutatorElement

theorem fam_fieldSL_rankOne
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hρ : ∀ γ ∈ kernelRoots χ, S.ρ γ ∈ kernelRoots χ) (i : KernelComponent χ)
    (hr1 : compRank (componentRoots χ i) = 1)
    (hn : (componentRoots χ i).ncard = 2)
    (hq : CFSG.IsQuasisimple ↥(rationalComponentM S.ρ S.Γ χ i)) :
    GGCompFieldAtSL (S.D.q ^ componentOrbitLength S.ρ (componentRoots χ i))
      (rationalComponentM S.ρ S.Γ χ i) := by
  obtain ⟨K, hKfield, hKfin, f, hf, hcard, hfield, _hchrK, h4, g, hgsurj, hgker⟩ :=
    fam_exists_slCover_rankOne S hρ i hr1 hn hq
  letI : Field K := hKfield
  letI : Finite K := hKfin
  have hchr : ringChar L = 2 := ringChar.eq L 2
  have hfld : (2 : ℕ) ^ f = S.D.q ^ componentOrbitLength S.ρ (componentRoots χ i) := by
    rw [← hchr]; exact hfield
  have hK2 : Nat.card K = 2 ^ f := by simpa [hchr] using hcard
  have hmain : GGCompFieldAtSL (2 ^ f)
      (rationalComponentM S.ρ S.Γ χ i) :=
    ggCompFieldAtSL_of_slCover (X := rationalComponentM S.ρ S.Γ χ i)
      hf hK2 (le_refl 2) (fun _ => h4) hq g hgsurj hgker
  simpa [hfld] using hmain

theorem fam_fieldSL_splitFrame
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hρ : ∀ γ ∈ kernelRoots χ, S.ρ γ ∈ kernelRoots χ) (i : KernelComponent χ) {ν : ℕ}
    (hν : 3 ≤ ν) {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}
    (hψ : IsSLFrame ψ σ) (hΨ : componentRoots χ i = frameRoots σ)
    (π : Equiv.Perm (Fin ν))
    (hπ : ∀ x y, x ≠ y → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots χ i)] (σ x y) = σ (π x) (π y))
    (hq : CFSG.IsQuasisimple ↥(rationalComponentM S.ρ S.Γ χ i)) :
    GGCompFieldAtSL (S.D.q ^ componentOrbitLength S.ρ (componentRoots χ i))
      (rationalComponentM S.ρ S.Γ χ i) := by
  obtain ⟨K, hKfield, hKfin, f, hf, hcard, hfield, _hchrK, g, hgsurj, hgker⟩ :=
    fam_exists_slCover_splitFrame S hρ i hν hψ hΨ π hπ
  letI : Field K := hKfield
  letI : Finite K := hKfin
  have hchr : ringChar L = 2 := ringChar.eq L 2
  have hfld : (2 : ℕ) ^ f = S.D.q ^ componentOrbitLength S.ρ (componentRoots χ i) := by
    rw [← hchr]; exact hfield
  have hK2 : Nat.card K = 2 ^ f := by simpa [hchr] using hcard
  have hK4 : ν = 2 → 4 ≤ Nat.card K := by
    intro hν2; omega
  have hmain : GGCompFieldAtSL (2 ^ f)
      (rationalComponentM S.ρ S.Γ χ i) :=
    ggCompFieldAtSL_of_slCover (X := rationalComponentM S.ρ S.Γ χ i)
      hf hK2 (le_trans (by norm_num) hν) hK4 hq g hgsurj hgker
  simpa [hfld] using hmain

theorem fam_fieldSL_unitaryFrame
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hρ : ∀ γ ∈ kernelRoots χ, S.ρ γ ∈ kernelRoots χ) (i : KernelComponent χ) {ν : ℕ}
    (hν : 3 ≤ ν) {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}
    (hψ : IsSLFrame ψ σ) (hΨ : componentRoots χ i = frameRoots σ)
    (π : Equiv.Perm (Fin ν))
    (hπ : ∀ x y, x ≠ y → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots χ i)] (σ x y) = σ (π y) (π x))
    (hq : CFSG.IsQuasisimple ↥(rationalComponentM S.ρ S.Γ χ i)) :
    GGCompFieldAtSL (S.D.q ^ componentOrbitLength S.ρ (componentRoots χ i))
      (rationalComponentM S.ρ S.Γ χ i) := by
  have hchr : ringChar L = 2 := ringChar.eq L 2
  have hcover := fam_exists_suCover_unitaryFrame S hρ i hν hψ hΨ π hπ hq
  rw [hchr] at hcover
  obtain ⟨K, hKfield, hKfin, f, hf, hcard, hfield, _hchrK, h32, g, hgsurj, hgker⟩ := hcover
  letI : Field K := hKfield
  letI : Finite K := hKfin
  have hmain : GGCompFieldAtSL (2 ^ f)
      (rationalComponentM S.ρ S.Γ χ i) :=
    ggCompFieldAtSL_of_suCover (X := rationalComponentM S.ρ S.Γ χ i)
      hf hcard hν h32 hq g hgsurj hgker
  rw [hfield] at hmain
  exact hmain

theorem langFamRatFieldSL_typeA
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) {ι : Type} {a : ι → Fin τ.rank → Lˣ}
    (hT : ∀ u, rootDiagUnit τ (a u) ∈ S.D.torus) (hap : ∀ u j, a u j ^ p = 1)
    (h1 : ∃ u, rootDiagUnit τ (a u) ≠ 1) (i : KernelComponent (famCharHom a))
    (hA : 1 ≤ compRank (componentRoots (famCharHom a) i) ∧
      (componentRoots (famCharHom a) i).ncard = compRank (componentRoots (famCharHom a) i) *
        (compRank (componentRoots (famCharHom a) i) + 1))
    (hq : CFSG.IsQuasisimple ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i)) :
    CFSG.StandardType.GGCompFieldAtSL
      (S.D.q ^ componentOrbitLength S.ρ (componentRoots (famCharHom a) i))
      (rationalComponentM S.ρ S.Γ (famCharHom a) i) := by
  have hρ : ∀ γ ∈ kernelRoots (famCharHom a), S.ρ γ ∈ kernelRoots (famCharHom a) :=
    fun γ hγ => rho_mem_kernelRoots_famChar S a hT hγ
  rcases fam_typeA_frame_cases hτ S hp hT hap h1 i hA with
      ⟨hr1, hn⟩ | ⟨ν, ψ, σ, π, hν, hψ, hΨ, hπ⟩ | ⟨ν, ψ, σ, π, hν, hψ, hΨ, hπ⟩
  · exact fam_fieldSL_rankOne S hρ i hr1 hn hq
  · exact fam_fieldSL_splitFrame S hρ i hν hψ hΨ π hπ hq
  · exact fam_fieldSL_unitaryFrame S hρ i hν hψ hΨ π hπ hq

end CFSG.StandardType.TableCRes
