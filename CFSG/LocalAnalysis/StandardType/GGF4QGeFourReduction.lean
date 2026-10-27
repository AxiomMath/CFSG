module

public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourInputs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePresTags
public import CFSG.LocalAnalysis.StandardType.GGF4QTwoReduction
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRegionDefs
public import CFSG.LocalAnalysis.StandardType.GGForkA8NotRefl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveDataResDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylInfDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveMaxJoin

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly CFSG.LieType.Universal CFSG.StandardType.FrameRoute

theorem ggSecFiveData_of_centralImage
    {G : Type} [Group G] [Finite G] {p : ℕ} {B : Subgroup G}
    {x : G} {L D J : Subgroup G} {t : StatedLieTag} {n f : ℕ} (hrank : 3 ≤ bnRank t n)
    (h : GGCentralImage t n f (ggG0 p B x L D J)) : GGSecFiveData p B x L D J := by
  obtain ⟨ψ, hadm, hker, hrange⟩ := h
  exact Or.inr (Or.inr ⟨t, n, f, ggSecFivePres_of_psi_of_admissible hadm hrank ψ hker hrange⟩)

theorem GGSecFiveRouteCfg.singleton_of_reflMaxAt_F4
    (hRM : GGSecFiveReflMaxAt fun M => GGIsWeylMatrixF4 M)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hF4 : GGIsWeylMatrixF4 M)
    {y : G} {K : Subgroup G} (hNb : GGNbr p B x D J y K)
    (hWK : GGWeylOfType p CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs)) :
    GGSecFiveRouteCfg p B Bs x L D J {K} := by
  have hle : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦 :=
    sup_le le_sup_left (hRM G p B Bs x L D J 𝒦 hR ι M e hP hF4 y K hNb)
  obtain ⟨eK, -⟩ := hWK
  obtain ⟨e₀, rfl⟩ := hF4
  have hfin : Finite (MulAut ↥Bs) :=
    Finite.of_injective (fun (g : MulAut ↥Bs) (b : ↥Bs) => g b)
      (fun g h hgh => MulEquiv.ext (congrFun hgh))
  have hcard : Nat.card ↥(ggAutomizerJoin L Bs 𝒦) =
      Nat.card ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
    rw [← Nat.card_congr e.toEquiv, ← Nat.card_congr eK.toEquiv]
    exact Nat.card_congr (CoxeterMatrix.F₄.reindexGroupEquiv e₀).toEquiv
  have heq : ggAutomizerJoin L Bs {K} = ggAutomizerJoin L Bs 𝒦 := by
    rw [ggAutomizerJoin_singleton]
    exact Subgroup.eq_of_le_of_card_ge hle hcard.le
  refine ⟨hR.1, hR.2.1, hR.2.2.1, ⟨by simp, fun K' hK' => ⟨y, ?_⟩⟩, ?_, ?_⟩
  · rw [Finset.mem_singleton.mp hK']
    exact hNb
  · rw [heq]
    exact hR.2.2.2.2.1
  · intro 𝒦' h1 h2
    rw [heq]
    exact hR.2.2.2.2.2 𝒦' h1 h2

theorem ggSecFiveData_F4_qGeFour_of_routeInput
    (hEnds : GGF4QGeFourEndsInput) (hS1 : GGF4QGeFourF4Input)
    (hS2 : GGF4QGeFourTwE6Input) (hN2 : GGF4QGeFourE6FourRouteInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hR : GGSecFiveRestHyp p B Bs x L D J) (hW : GGSecFiveWeylCase' p B Bs x D J)
    {y : G} {K : Subgroup G} (hNb : GGNbr p B x D J y K)
    (hRC : GGSecFiveRouteCfg p B Bs x L D J {K}) (hT1 : ¬ GGSecFiveTier1Region p B Bs x L D J)
    (hWK : GGWeylOfType p CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs))
    (hq : ¬ GGInnerDiagOnLabel GGLabQTwo p Bs L) : GGSecFiveData p B x L D J := by
  rcases hEnds G p B Bs x L D J hR hW hq y K hNb hRC hT1 hWK with
    ⟨f, hf, hp, hL, hK⟩ | ⟨f, hf, hp, hL, hK⟩ | ⟨rfl, hL, hK⟩
  · exact ggSecFiveData_of_centralImage (by decide)
      (hS1 G p B Bs x L D J hR hW hq y K hNb hRC hWK f hf hp hL hK)
  · exact ggSecFiveData_of_centralImage (by decide)
      (hS2 G p B Bs x L D J hR hW hq y K hNb hRC hWK f hf hp hL hK)
  · exact ggSecFiveData_of_centralImage (by decide)
      (hN2 G B Bs x L D J hR hW hq y K hNb hRC hWK hL hK)

theorem ggSecFiveWeylF4ResInput_of_routeInputs
    (hFF : FF81bThmAAtFiveSixLab) (hG0 : FF81bG0Input) (hEndsL : GGF4QTwoEndsLInput)
    (hEndsK : GGF4QTwoEndsKInput) (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    (hEnds : GGF4QGeFourEndsInput) (hS1 : GGF4QGeFourF4Input) (hS2 : GGF4QGeFourTwE6Input)
    (hN2 : GGF4QGeFourE6FourRouteInput) (hLevi : GGSecFiveLeviData)
    (hA : GGSecFiveDataResAt fun M => GGIsWeylMatrixA M)
    (hB : GGSecFiveDataResAt fun M => GGIsWeylMatrixB M)
    (hD : GGSecFiveDataResAt fun M => GGIsWeylMatrixD M)
    (hE : GGSecFiveDataResAt fun M => GGIsWeylMatrixE M)
    (hG : GGSecFiveDataResAt fun M => GGIsWeylMatrixG2 M)
    (hRM : GGSecFiveReflMaxAt fun M => GGIsWeylMatrixF4 M) : GGSecFiveWeylF4ResInput := by
  intro G _ _ p B Bs x L D J hR hW hAt hNotReg
  by_cases hq : GGInnerDiagOnLabel GGLabQTwo p Bs L
  · have hp : p = 3 := p_eq_three_of_qTwo hR.1 hq
    subst hp
    exact ggSecFiveData_F4_qTwo hFF hG0 hEndsL hEndsK hTBF hWI hR
      (ggSecFiveWeylCase_of_prime_three hR.1 hW) hAt hq
  by_cases hLev : GGSecFiveLeviCase p B Bs x L D J
  · exact hLevi G p B Bs x L D J hR hW hLev
  obtain ⟨𝒦, hMax⟩ := exists_ggMaximalJoin hR hW
  have hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦 := ⟨hR, hW, hLev, hMax⟩
  obtain ⟨ι, M, hWM, e, hrefl⟩ := hMax.2.1
  have hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e := ⟨hWM, hrefl⟩
  rcases hWM with ⟨n, e', hn, hM | ⟨hn2, hM⟩ | ⟨hn4, hM⟩⟩ | hE6 | hE7 | hE8 | hF4 | hG2
  · exact hA G p B Bs x L D J 𝒦 hcfg hNotReg ι M e hpres ⟨n, e', hn, hM⟩
  · exact hB G p B Bs x L D J 𝒦 hcfg hNotReg ι M e hpres ⟨n, e', hn2, hM⟩
  · exact hD G p B Bs x L D J 𝒦 hcfg hNotReg ι M e hpres ⟨n, e', hn4, hM⟩
  · exact hE G p B Bs x L D J 𝒦 hcfg hNotReg ι M e hpres (Or.inl hE6)
  · exact hE G p B Bs x L D J 𝒦 hcfg hNotReg ι M e hpres (Or.inr (Or.inl hE7))
  · exact hE G p B Bs x L D J 𝒦 hcfg hNotReg ι M e hpres (Or.inr (Or.inr hE8))
  · obtain ⟨y, K, hNb, hWK⟩ := hAt
    exact ggSecFiveData_F4_qGeFour_of_routeInput hEnds hS1 hS2 hN2 hR hW hNb
      (GGSecFiveRouteCfg.singleton_of_reflMaxAt_F4 hRM hcfg hpres hF4 hNb hWK) hNotReg hWK hq
  · exact hG G p B Bs x L D J 𝒦 hcfg hNotReg ι M e hpres hG2

end CFSG.StandardType

end
