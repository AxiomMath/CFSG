module

public import CFSG.LocalAnalysis.StandardType.GGFamE6OuterModel
public import CFSG.LocalAnalysis.StandardType.GGFamNoDiagram
public import CFSG.LocalAnalysis.StandardType.GGFamTameTwoDHigh

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.KE6
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups

open CFSG.HardMathSupport.Solomon.Coordinator.LieComp

theorem famOuterE_not_diagramSymm {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)}
    (h : (compRank Ψ = 7 ∧ Ψ.ncard = 126) ∨ (compRank Ψ = 8 ∧ Ψ.ncard = 240)) :
    ¬ HasDiagramSymmetryType Ψ := by
  rintro (⟨h2, hc⟩ | ⟨h4, hc⟩ | ⟨h6, hc⟩)
  · rcases h with ⟨hr, hn⟩ | ⟨hr, hn⟩ <;> rw [hn, hr] at hc <;> norm_num at hc
  · rcases h with ⟨hr, hn⟩ | ⟨hr, hn⟩ <;> rw [hn, hr] at hc <;> norm_num at hc
  · rcases h with ⟨hr, hn⟩ | ⟨hr, hn⟩ <;> omega

theorem fam_ratFieldSL_of_e6_pin
    {τ : Tag}
    [CFSG.RankThree.PartOne.KE6.M27Ok τ]
    [CFSG.RankThree.PartOne.KD4T.E6Sub τ]
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ : ℕ} (S : LangSetup τ L p₀)
    {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M)
    (i : KernelComponent χ) (v : WeylGroup τ)
    (hΨ : componentRoots χ i =
      (fun α => v • α) ''
        parabolicRoots τ (CFSG.RankThree.PartOne.KE6.e6Nodes τ))
    (hΨρ : ∀ γ ∈ componentRoots χ i, S.ρ γ ∈ componentRoots χ i)
    (hout : ¬ twistInner (componentRoots χ i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots χ i)]))
    (hq : CFSG.IsQuasisimple ↥(rationalComponentM S.ρ S.Γ χ i)) :
    CFSG.StandardType.GGCompFieldAtSL
      (S.D.q ^ componentOrbitLength S.ρ (componentRoots χ i))
      (rationalComponentM S.ρ S.Γ χ i) := by
  classical
  have hq' : CFSG.Open.IsQuasisimple ↥(rationalComponentM S.ρ S.Γ χ i) :=
    ⟨hq.1.commutator_eq_top, hq.2.1⟩
  obtain ⟨f, -, hfq, hlie⟩ :=
    fam_lieModel_rationalComponent_of_e6_outer S χ i v hΨ hΨρ hout
  have hfinΨ : (componentRoots χ i).Finite :=
    (finite_setOf_isRoot τ).subset fun α hα => hα.1.1
  have hs : componentOrbitLength S.ρ (componentRoots χ i) = 1 :=
    componentOrbitLength_eq_one hfinΨ hΨρ
  have h2 : ringChar L = 2 := ringChar.eq L 2
  rw [h2] at hlie hfq
  rw [hs, pow_one, ← hfq]
  exact CFSG.StandardType.ggCompFieldAtSL_of_lieModel hq' hlie (by decide)

theorem langFamRatFieldSL_outerE
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) (hp2 : p ≠ 2) {ι : Type}
    {a : ι → Fin τ.rank → Lˣ}
    (hT : ∀ u, rootDiagUnit τ (a u) ∈ S.D.torus) (hap : ∀ u j, a u j ^ p = 1)
    (i : KernelComponent (famCharHom a))
    (hE : 6 ≤ compRank (componentRoots (famCharHom a) i) ∧
      (componentRoots (famCharHom a) i).ncard =
        eRootCount (compRank (componentRoots (famCharHom a) i)))
    (hout : ¬ twistInner (componentRoots (famCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (famCharHom a) i)]))
    (hq : CFSG.IsQuasisimple ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i)) :
    CFSG.StandardType.GGCompFieldAtSL
      (S.D.q ^ componentOrbitLength S.ρ (componentRoots (famCharHom a) i))
      (rationalComponentM S.ρ S.Γ (famCharHom a) i) := by
  classical
  have hτ3 : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 :=
    hτ.elim (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr h))
  have hρ : ∀ γ ∈ kernelRoots (famCharHom a), S.ρ γ ∈ kernelRoots (famCharHom a) :=
    fun γ hγ => rho_mem_kernelRoots_famChar S a hT hγ
  have hstab : S.ρ '' componentRoots (famCharHom a) i = componentRoots (famCharHom a) i :=
    image_componentRoots_eq_of_rank_gt_half S hρ i (by
      have h8 := CFSG.HardMathSupport.Timmesfeld.RootAut.rank_le_eight τ
      have h6 := hE.1
      omega)
  have hΨρ : ∀ γ ∈ componentRoots (famCharHom a) i,
      S.ρ γ ∈ componentRoots (famCharHom a) i :=
    fun γ hγ => Set.image_subset_iff.1 (le_of_eq hstab) hγ
  obtain ⟨N, b, j, hN, hN2, hbN, hsel⟩ := exists_isolating_element hτ3 a hp hp2 hap i
  have hpN : (N : L) ≠ 0 :=
    natCast_ne_zero_of_ringChar_ne hN (by rw [ringChar.eq L 2]; exact Ne.symm hN2)
  have hEb : 6 ≤ compRank (componentRoots (rootCharHom b) j) ∧
      (componentRoots (rootCharHom b) j).ncard =
        eRootCount (compRank (componentRoots (rootCharHom b) j)) := by
    rw [hsel]; exact hE
  have houtb : ¬ twistInner (componentRoots (rootCharHom b) j)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom b) j)]) := by
    rw [hsel]; exact hout
  rcases hτ with rfl | rfl
  ·
    obtain ⟨v, μ, x, c, -, hc, -, hlen, hroots, hrank, hncard⟩ :=
      exists_cand_of_class kacE7 facts_E7 e7_tree e7_adj e7_check e7_lt e7_card S hN hpN hbN j
    have hcount : kacCount Tag.E7 kacE7.θ
        ((c.map (idxNode (r := Tag.E7.rank))).toFinset) = eRootCount c.length := by
      rw [← hncard, hEb.2, hrank]
    have hlen67 : c.length = 6 ∨ c.length = 7 := by
      have h6 := hEb.1
      rw [hrank] at h6
      rw [show Tag.E7.rank = 7 from rfl] at hlen
      omega
    rcases hlen67 with hc6 | hc7
    · have h72 : kacCount Tag.E7 kacE7.θ
          ((c.map (idxNode (r := Tag.E7.rank))).toFinset) = 72 := by
        rw [hcount, hc6]; rfl
      have hCeq := kacCount_E7_six ((c.map (idxNode (r := Tag.E7.rank))).toFinset)
        (by rw [e7_card c hc, hc6]) h72
      have hpin : componentRoots (famCharHom a) i =
          (fun α => v • α) '' parabolicRoots Tag.E7 (e6Nodes Tag.E7) := by
        rw [← hsel, hroots, hCeq, rootsOf_eq_parabolicRoots kacE7 facts_E7
          (J := e6Nodes Tag.E7) (by decide)
          (fun k => by simp only [e6Nodes, Set.mem_setOf_eq]; revert k; decide)]
      exact fam_ratFieldSL_of_e6_pin S (famCharHom a) i v hpin hΨρ hout hq
    · exfalso
      apply hout
      have hcomp : compRank (componentRoots (famCharHom a) i) = 7 := by
        rw [← hsel, hrank, hc7]
      have hnc : (componentRoots (famCharHom a) i).ncard = 126 := by
        rw [← hsel, hEb.2, hrank, hc7]; rfl
      exact fam_twistInner_of_noDiagram S (famCharHom a) i hρ
        (famOuterE_not_diagramSymm (Or.inl ⟨hcomp, hnc⟩))
  ·
    obtain ⟨v, μ, x, c, -, hc, -, hlen, hroots, hrank, hncard⟩ :=
      exists_cand_of_class kacE8 facts_E8 e8_tree e8_adj e8_check e8_lt e8_card S hN hpN hbN j
    have hcount : kacCount Tag.E8 kacE8.θ
        ((c.map (idxNode (r := Tag.E8.rank))).toFinset) = eRootCount c.length := by
      rw [← hncard, hEb.2, hrank]
    have hlen678 : c.length = 6 ∨ c.length = 7 ∨ c.length = 8 := by
      have h6 := hEb.1
      rw [hrank] at h6
      rw [show Tag.E8.rank = 8 from rfl] at hlen
      omega
    rcases hlen678 with hc6 | hc78
    · have h72 : kacCount Tag.E8 kacE8.θ
          ((c.map (idxNode (r := Tag.E8.rank))).toFinset) = 72 := by
        rw [hcount, hc6]; rfl
      have hCeq := kacCount_E8_six ((c.map (idxNode (r := Tag.E8.rank))).toFinset)
        (by rw [e8_card c hc, hc6]) h72
      have hpin : componentRoots (famCharHom a) i =
          (fun α => v • α) '' parabolicRoots Tag.E8 (e6Nodes Tag.E8) := by
        rw [← hsel, hroots, hCeq, rootsOf_eq_parabolicRoots kacE8 facts_E8
          (J := e6Nodes Tag.E8) (by decide)
          (fun k => by simp only [e6Nodes, Set.mem_setOf_eq]; revert k; decide)]
      exact fam_ratFieldSL_of_e6_pin S (famCharHom a) i v hpin hΨρ hout hq
    · exfalso
      apply hout
      have hcomp7 : compRank (componentRoots (famCharHom a) i) = c.length := by
        rw [← hsel, hrank]
      have hnc : (componentRoots (famCharHom a) i).ncard = eRootCount c.length := by
        rw [← hsel, hEb.2, hrank]
      rcases hc78 with hc7 | hc8
      · exact fam_twistInner_of_noDiagram S (famCharHom a) i hρ (famOuterE_not_diagramSymm
          (Or.inl ⟨by rw [hcomp7, hc7], by rw [hnc, hc7]; rfl⟩))
      · exact fam_twistInner_of_noDiagram S (famCharHom a) i hρ (famOuterE_not_diagramSymm
          (Or.inr ⟨by rw [hcomp7, hc8], by rw [hnc, hc8]; rfl⟩))

end CFSG.StandardType.TableCRes
