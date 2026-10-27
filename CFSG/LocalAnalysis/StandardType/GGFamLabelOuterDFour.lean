module

public import CFSG.LocalAnalysis.StandardType.GGFamOuterDFour
public import CFSG.LocalAnalysis.StandardType.GGFamLabelD4Selected
public import CFSG.LocalAnalysis.StandardType.GGFamLabelDefs
public import CFSG.LocalAnalysis.StandardType.GGFamLabelKind

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.RankThree.Lattice
  CFSG.RankThree.PartOne.KE

theorem langFamRatLabel_outerD_four
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) (hp2 : p ≠ 2) {ι : Type}
    {a : ι → Fin τ.rank → Lˣ}
    (hT : ∀ u, rootDiagUnit τ (a u) ∈ S.D.torus) (hap : ∀ u j, a u j ^ p = 1)
    (i : KernelComponent (famCharHom a))
    (hr : compRank (componentRoots (famCharHom a) i) = 4)
    (hc : (componentRoots (famCharHom a) i).ncard = 24)
    (hout : ¬ twistInner (componentRoots (famCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (famCharHom a) i)]))
    (hq : CFSG.IsQuasisimple ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i)) :
    FamLabelAt S (famCharHom a) i := by
  obtain ⟨b, j, v, hsel, hpin, hρΨ, hs, hout'⟩ :=
    fam_outerD_four_selected_data hτ S hp hp2 hT hap i hr hc hout
  obtain ⟨f, hf, hM⟩ :=
    fam_label_d4_selected hτ S (famCharHom a) i b j hsel v hpin hρΨ hout'
  rw [ringChar.eq L 2] at hf hM
  refine ⟨f, by rw [hs, pow_one, ← hf], ?_⟩
  rcases hM with ⟨hsq, hm⟩ | ⟨hsq, hm⟩
  · rw [twistKindOf_eq_twoD_of_D4 S.ρ _ hout hr hc (by rw [hs, mul_one]; exact hsq),
      componentLabel_twoD, hr]
    exact ggCompLabelAt_twD 4 f le_rfl hm.admissible.2.1 hm
  · rw [twistKindOf_eq_exc_of_D4 S.ρ _ hout hr hc (by rw [hs, mul_one]; exact hsq),
      componentLabel_exc_D4 _ f hr]
    exact ggCompLabelAt_triD4 f hm.admissible.2.1 hm

end CFSG.StandardType.TableCRes
