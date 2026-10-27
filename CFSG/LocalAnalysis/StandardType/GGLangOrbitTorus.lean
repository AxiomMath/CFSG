module

public import CFSG.LocalAnalysis.StandardType.GGLatEigenOrbit
public import CFSG.LocalAnalysis.StandardType.GGLangRatStep
public import CFSG.LocalAnalysis.StandardType.GGStepTwoToralLatIndex
public import CFSG.LocalAnalysis.StandardType.GGLangWSLGamma
public import CFSG.HardMathSupport.Timmesfeld.RootAut.Count

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.AlgebraicGroups CFSG.StandardType.LangRat

variable {N : ℕ}

@[expose] def latOrbitSumZ (S : Matrix (Fin N) (Fin N) ℤ) (π : Equiv.Perm (Fin N))
    (α : Fin N → ℤ) : Fin N → ℤ :=
  fun j => latCorootZ S α j + if latPerm π α = α then 0 else latCorootZ S (latPerm π α) j

theorem latOrbitSum_eq_latOrbitSumZ (p : ℕ) (S : Matrix (Fin N) (Fin N) ℤ)
    (π : Equiv.Perm (Fin N)) (α : Fin N → ℤ) :
    latOrbitSum p S π α = fun j => (latOrbitSumZ S π α j : ZMod p) := by
  funext j
  by_cases hfix : latPerm π α = α
  · simp [latOrbitSum, latOrbitSumZ, hfix]
  · simp [latOrbitSum, latOrbitSumZ, hfix, Int.cast_add]

theorem latCorootZ_smul_symmetrizedCartan_of_ne
    (τ : Tag) {k : ℤ} (hk : k ≠ 0)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    latCorootZ (k • τ.symmetrizedCartan) α = fun m => corootPair α (Pi.single m 1) := by
  funext m
  have hden : latGram (k • τ.symmetrizedCartan) α α ≠ 0 := by
    rw [StepTwoToralIndex.latGram_smul_symmetrizedCartan]
    exact mul_ne_zero hk (iform_self_pos_of_isRoot hα).ne'
  have hnum : 2 * latGram (k • τ.symmetrizedCartan) (Pi.single m 1) α =
      corootPair α (Pi.single m 1) * latGram (k • τ.symmetrizedCartan) α α := by
    calc
      2 * latGram (k • τ.symmetrizedCartan) (Pi.single m 1) α =
          2 * (k * iform (Pi.single m 1) α) := by
            rw [StepTwoToralIndex.latGram_smul_symmetrizedCartan]
      _ = k * (2 * iform (Pi.single m 1) α) := by ring
      _ = k * (2 * iform α (Pi.single m 1)) := by rw [iform_comm (Pi.single m 1) α]
      _ = k * (corootPair α (Pi.single m 1) * iform α α) := by rw [corootPair_mul hα]
      _ = corootPair α (Pi.single m 1) * (k * iform α α) := by ring
      _ = corootPair α (Pi.single m 1) * latGram (k • τ.symmetrizedCartan) α α := by
            rw [StepTwoToralIndex.latGram_smul_symmetrizedCartan]
  rw [latCorootZ]
  exact Int.ediv_eq_of_eq_mul_left hden hnum

theorem rootDiagUnit_latCorootZ_mem_rationalComponent
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {f : ℕ} (hq : S.D.q = 2 ^ f) (hAlg : S.IsAlgebraic) {Fr : L →+* L} {w : WeylGroup τ}
    (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
    (hn : S.D.n = canonicalRep (coxeterSystem τ) L w)
    (hw : ∀ v : Fin τ.rank → ℤ, w • v = -v)
    {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a)) {α : Fin τ.rank → ℤ}
    (hα : α ∈ componentRoots (rootCharHom a) i)
    (hρα : S.ρ α = α ∨ S.ρ α = -α)
    (k : ℤ) (hk : k ≠ 0) (Smat : Matrix (Fin τ.rank) (Fin τ.rank) ℤ)
    (hSmat : Smat = k • τ.symmetrizedCartan)
    {ζ : Lˣ} (ht : Units.map Fr.toMonoidHom ζ = ζ⁻¹)
    {m : ℕ} (hm : Odd m) (hζm : ζ ^ m = 1) :
    rootDiagUnit τ (fun j => ζ ^ latCorootZ Smat α j) ∈
      rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  have hαr : IsRoot τ α := (isRootComponent_componentRoots i).isRoot α hα
  have hcor : latCorootZ Smat α = fun j => corootPair α (Pi.single j 1) := by
    rw [hSmat]
    exact latCorootZ_smul_symmetrizedCartan_of_ne τ hk hαr
  have hdiag : rootDiagUnit τ (fun j => ζ ^ latCorootZ Smat α j) = rootSL2 τ L α (HSL ζ) := by
    rw [hcor]
    exact (CFSG.RankThree.PartOne.rootSL2_HSL_eq_rootDiagUnit hαr _
      (fun δ _ => by
        have hδ : δ = ∑ i, δ i • (Pi.single i 1 : Fin τ.rank → ℤ) := by
          funext q
          simp [Finset.sum_apply, Pi.single_apply]
        conv_lhs => rw [hδ]
        exact CFSG.HardMathSupport.Timmesfeld.RootAut.corootPair_sum hαr Finset.univ δ
          (fun i => Pi.single i 1)) ζ).symm
  rw [hdiag]
  exact rootSL2_HSL_mem_rationalComponent_of_entrywise_step' S hτ hq hAlg hΦ hn hw i hα hρα
    ht hm hζm

end CFSG.StandardType
