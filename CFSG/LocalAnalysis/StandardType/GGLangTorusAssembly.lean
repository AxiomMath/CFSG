module

public import CFSG.HardMathSupport.Timmesfeld.RootAut.Count
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.RankThree.PartOne.S11c.G2Torus
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Lemma83
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Cardinalities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
public import CFSG.Walter.Defs

public section

namespace CFSG.StandardType.LangRat

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable
  {L : Type} [Field L] {τ : Tag}

theorem rootDiagUnit_eq_prod_rootSL2_HSL
    (γl : List (Fin τ.rank → ℤ)) (hγ : ∀ γ ∈ γl, IsRoot τ γ)
    (t : (Fin τ.rank → ℤ) → Lˣ) {b : Fin τ.rank → Lˣ}
    (hb : ∀ j, b j = (γl.map fun γ => (t γ) ^ corootPair γ (Pi.single j 1)).prod) :
    rootDiagUnit τ b =
      (γl.map fun γ => rootSL2 τ L γ (HSL (t γ))).prod := by
  have hlin : ∀ (γ : Fin τ.rank → ℤ), IsRoot τ γ → ∀ δ : Fin τ.rank → ℤ,
      corootPair γ δ = ∑ i, δ i * corootPair γ (Pi.single i 1) := by
    intro γ hγr δ
    have hδ : δ = ∑ i, δ i • (Pi.single i 1 : Fin τ.rank → ℤ) := by
      funext k
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hδ]
    exact CFSG.HardMathSupport.Timmesfeld.RootAut.corootPair_sum hγr Finset.univ δ
      (fun i => Pi.single i 1)
  have hfactor : ∀ γ ∈ γl, rootSL2 τ L γ (HSL (t γ)) =
      rootDiagUnit τ (fun j => (t γ) ^ corootPair γ (Pi.single j 1)) := by
    intro γ hγm
    exact CFSG.RankThree.PartOne.rootSL2_HSL_eq_rootDiagUnit (hγ γ hγm) _
      (fun δ _ => hlin γ (hγ γ hγm) δ) (t γ)
  rw [List.map_congr_left hfactor]
  change rootDiagUnit τ b =
    (γl.map ((rootDiagUnitHom τ L) ∘ fun γ j =>
      (t γ) ^ corootPair γ (Pi.single j 1))).prod
  have h := map_list_prod (rootDiagUnitHom τ L)
    (γl.map fun γ => fun j => (t γ) ^ corootPair γ (Pi.single j 1))
  rw [List.map_map] at h
  rw [← h]
  congr 1
  funext j
  simpa [Pi.list_prod_apply, List.map_map, Function.comp_def] using hb j

end CFSG.StandardType.LangRat

end
