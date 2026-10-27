module

public import CFSG.LocalAnalysis.StandardType.GGFamTwoDModel
public import CFSG.LocalAnalysis.StandardType.GGFamIsolation
public import CFSG.LocalAnalysis.StandardType.GGFamTameTransfer
public import CFSG.LocalAnalysis.StandardType.GGExcCompSLDefs
public import CFSG.LocalAnalysis.StandardType.GGFamTameTwoDHigh

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.RankThree.Lattice
  CFSG.RankThree.PartOne.KE

theorem langFamRatFieldSL_outerD_high
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) {ι : Type} {a : ι → Fin τ.rank → Lˣ}
    (hT : ∀ u, rootDiagUnit τ (a u) ∈ S.D.torus) (hap : ∀ u j, a u j ^ p = 1)
    (h1 : ∃ u, rootDiagUnit τ (a u) ≠ 1) (i : KernelComponent (famCharHom a))
    (hD : 5 ≤ compRank (componentRoots (famCharHom a) i) ∧
      (componentRoots (famCharHom a) i).ncard =
        2 * compRank (componentRoots (famCharHom a) i) *
          (compRank (componentRoots (famCharHom a) i) - 1))
    (hout : ¬ twistInner (componentRoots (famCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (famCharHom a) i)]))
    (hq : CFSG.IsQuasisimple ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i)) :
    CFSG.StandardType.GGCompFieldAtSL
      (S.D.q ^ componentOrbitLength S.ρ (componentRoots (famCharHom a) i))
      (rationalComponentM S.ρ S.Γ (famCharHom a) i) := by
  classical
  have hq' : CFSG.Open.IsQuasisimple ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i) :=
    ⟨hq.1.commutator_eq_top, hq.2.1⟩
  have hp2 : p ≠ 2 := by
    obtain ⟨u, hu⟩ := h1
    have hne := ringChar_ne_of_pow_eq_one hp (hap u) hu
    rintro rfl
    exact hne (ringChar.eq L 2)
  obtain ⟨N, b, j, hN, hN2, hbN, hsel⟩ := exists_isolating_element hτ a hp hp2 hap i
  have hNL : (N : L) ≠ 0 :=
    natCast_ne_zero_of_ringChar_ne hN (by rw [ringChar.eq L 2]; exact fun h => hN2 h.symm)
  have hker : ∀ γ ∈ kernelRoots (famCharHom a), S.ρ γ ∈ kernelRoots (famCharHom a) :=
    fun γ hγ => rho_mem_kernelRoots_famChar S a hT hγ
  have hrank : τ.rank < 2 * compRank (componentRoots (famCharHom a) i) := by
    have h8 := rank_le_eight τ
    have h5 := hD.1
    omega
  have hstab := image_componentRoots_eq_of_rank_gt_half S hker i hrank
  have hρΨ : ∀ γ ∈ componentRoots (famCharHom a) i,
      S.ρ γ ∈ componentRoots (famCharHom a) i := fun γ hγ => by
    rw [← hstab]
    exact ⟨γ, hγ, rfl⟩
  have hfin : (componentRoots (famCharHom a) i).Finite :=
    (finite_setOf_isRoot τ).subset fun γ hγ => hγ.1.1
  have hs : componentOrbitLength S.ρ (componentRoots (famCharHom a) i) = 1 :=
    componentOrbitLength_eq_one hfin hρΨ
  have hout' : ¬ twistInner (componentRoots (famCharHom a) i)
      (S.ρ : (Fin τ.rank → ℤ) → _) := by
    simpa [hs, Function.iterate_one] using hout
  obtain ⟨m, e, hqe, hlie⟩ :=
    fam_lieModel_rationalComponent_of_twoD S hτ (famCharHom a) i hker hρΨ hD.1 hD.2 hout'
      b j hsel hN hNL hbN (fun _ _ => True)
      (fun r _ _ e m he hm5 _ => CompsPTwoDChainO.twoDChainRecog_all he (by omega)) trivial
  have h2 : ringChar L = 2 := ringChar.eq L 2
  rw [h2] at hqe hlie
  rw [hs, pow_one, ← hqe]
  exact ggCompFieldAtSL_of_lieModel hq' hlie (by decide)

end CFSG.StandardType.TableCRes
