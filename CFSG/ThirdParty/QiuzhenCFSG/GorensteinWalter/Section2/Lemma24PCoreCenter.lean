module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CentralizerPCoreOfFstarPGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalizerEqOfNontrivialNormalInCoatom
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection8.theorem_8_1

namespace CFSG
end CFSG
open CFSG

/-!
# The p-core center used in Gorenstein--Walter Lemma 2.4

For the arrow `A ↝ M`, when `F*(A)` is a `p`-group, the ambient copy of
`Z(O_p(A))` is nontrivial, has normalizer `A`, lies in `M`, and is a
`p`-group.  These are the inputs used in the final application of
Glauberman's Theorem B.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The center of `O_p(A)`, mapped to the ambient group, has the four
properties required in the proof of Lemma 2.4. -/
public theorem lemma24_pCoreCenter_data
    {G : Type u} [Group G] [Finite G]
    {A M : Subgroup G} {p : ℕ}
    (hsimple : IsSimpleGroup G) (hA : IsCoatom A)
    (hAM : NormalizerControlledBy A M)
    (hp : p.Prime)
    (hAp : IsPGroup p (generalizedFittingSubgroupOf A)) :
    let Wint : Subgroup (↥A) := centerIn (G := ↥A) (pCore p (↥A))
    let W : Subgroup G := section8SubgroupInAmbient Wint
    W ≠ ⊥ ∧
      Subgroup.normalizer (W : Set G) = A ∧
        W ≤ M ∧ IsPGroup p W := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  rcases hAM with ⟨X, hXne, hXfit, hNXM⟩
  have hEbot : componentLayerOf A = ⊥ :=
    componentLayerOf_eq_bot_of_isPGroup A hp hAp
  have hFstar_eq_fit : generalizedFittingSubgroupOf A = fittingSubgroupOf A := by
    simp [generalizedFittingSubgroupOf, hEbot]
  have hfit_eq_core : fittingSubgroupOf A = qCoreOf A p :=
    (qCoreOf_eq_fittingSubgroupOf_of_isPGroup A hp hAp).symm
  have hFstar_eq_core :
      generalizedFittingSubgroupOf A = (pCore p (↥A)).map A.subtype := by
    rw [hFstar_eq_fit, hfit_eq_core]
    rfl
  have hXcore : X ≤ (pCore p (↥A)).map A.subtype := by
    rw [← hFstar_eq_core]
    exact hXfit.trans le_sup_left
  have hcoreNe : pCore p (↥A) ≠ ⊥ := by
    intro hbot
    apply hXne
    apply le_bot_iff.mp
    intro x hx
    have hxcore := hXcore hx
    rw [hbot, Subgroup.map_bot] at hxcore
    exact hxcore
  let Wint : Subgroup (↥A) := centerIn (G := ↥A) (pCore p (↥A))
  let W : Subgroup G := section8SubgroupInAmbient Wint
  have hWintNe : Wint ≠ ⊥ :=
    section8_centerIn_ne_bot_of_isPGroup
      (pCore_isPGroup (G := ↥A) (p := p)) hcoreNe
  have hWne : W ≠ ⊥ :=
    (section8SubgroupInAmbient_eq_bot_iff Wint).not.mpr hWintNe
  have hWintNormal : Wint.Normal := by
    let : (pCore p (↥A)).Normal := pCore_normal
    dsimp [Wint]
    unfold centerIn
    infer_instance
  have hWleA : W ≤ A := section8SubgroupInAmbient_le Wint
  have hWnormalA : (W.subgroupOf A).Normal :=
    section8SubgroupInAmbient_normal_in hWintNormal
  have hNW : Subgroup.normalizer (W : Set G) = A :=
    normalizer_eq_of_nontrivial_normal_in_coatom
      hsimple hA hWleA hWne hWnormalA
  have hWcentralizesX : W ≤ Subgroup.centralizer (X : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rcases Subgroup.mem_map.mp hw with ⟨wA, hwW, rfl⟩
    have hxcore := hXcore hx
    rcases Subgroup.mem_map.mp hxcore with ⟨xA, hxP, rfl⟩
    have hcommA : wA * xA = xA * wA := by
      have hwcenter : wA ∈ centerIn (G := ↥A) (pCore p (↥A)) := hwW
      exact ((Subgroup.mem_centralizer_iff.mp hwcenter.2) xA hxP).symm
    exact (congrArg Subtype.val hcommA).symm
  have hWM : W ≤ M :=
    (hWcentralizesX.trans (Subgroup.centralizer_le_normalizer (X : Set G))).trans hNXM
  have hWintp : IsPGroup p Wint :=
    (pCore_isPGroup (G := ↥A) (p := p)).to_le inf_le_left
  have hWp : IsPGroup p W := hWintp.map A.subtype
  exact ⟨hWne, hNW, hWM, hWp⟩

end CFSG.GorensteinWalter
