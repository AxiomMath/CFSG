module

public import CFSG.LocalAnalysis.StandardType.GGFamOuterDHigh
public import CFSG.LocalAnalysis.StandardType.GGFamLabelDefs
public import CFSG.LocalAnalysis.StandardType.GGFamLabelKind

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.RankThree.Lattice

theorem langFamRatLabel_outerD_high
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
    FamLabelAt S (famCharHom a) i := by
  classical
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
  obtain ⟨e, hqe, hlie⟩ :=
    fam_lieModel_rationalComponent_of_twoD_rank S hτ (famCharHom a) i hker hρΨ hD.1 hD.2 hout'
      b j hsel hN hNL hbN (fun _ _ => True)
      (fun r _ _ e m he hm5 _ => CompsPTwoDChainO.twoDChainRecog_all he (by omega)) trivial
  have h2 : ringChar L = 2 := ringChar.eq L 2
  rw [h2] at hqe hlie
  have he1 : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h0 | hpos
    · exfalso
      rw [h0, pow_zero] at hqe
      have hq1 : 1 < S.D.q := S.hqpow.1.one_lt
      omega
    · exact hpos
  unfold FamLabelAt
  refine ⟨e, ?_, ?_⟩
  · rw [hs, pow_one]
    exact hqe
  · rw [twistKindOf_eq_twoD_of_five S.ρ (componentRoots (famCharHom a) i) hout hD.1 hD.2,
      componentLabel_twoD]
    exact ggCompLabelAt_twD (compRank (componentRoots (famCharHom a) i)) e (by omega) he1 hlie

end CFSG.StandardType.TableCRes

end
