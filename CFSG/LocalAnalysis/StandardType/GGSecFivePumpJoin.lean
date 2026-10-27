module

public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
import CFSG.LocalAnalysis.StandardType.GGSecFiveMaxJoin

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggTBJ_automizer_le (hL : GGLBalanceInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hpJ : p ∣ Nat.card J) {X : Subgroup G}
    (hX : X = L ∨ X ∈ 𝒦) : ggAutomizer J Bs ≤ ggAutomizer X Bs := by
  refine ggAutomizer_mono Bs ?_
  rcases hX with rfl | hX
  · exact hcfg.1.1.2.2.1.2.2.2.2.2.1.1.trans inf_le_left
  · obtain ⟨y, hy⟩ := hcfg.2.2.2.1.2 X hX
    exact le_of_ggNbr hL hcfg.1.1.1 hcfg.1.1.2.2 hpJ hy

theorem ggSecFiveRouteCfg_singleton {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {y : G} {K : Subgroup G}
    (hK : GGNbr p B x D J y K)
    (hle : ggAutomizerJoin L Bs 𝒦 ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs) :
    GGSecFiveRouteCfg p B Bs x L D J {K} ∧
      ggAutomizerJoin L Bs {K} = ggAutomizerJoin L Bs 𝒦 := by
  obtain ⟨hR, hW, hnL, -, -, hmax⟩ := hcfg
  have hset : GGNbrSet p B x D J {K} := by
    refine ⟨by rw [Finset.card_singleton]; omega, fun K' hK' => ?_⟩
    rw [Finset.mem_singleton.mp hK']
    exact ⟨y, hK⟩
  have hWK : GGWeylReflectionGroup p (ggAutomizerJoin L Bs {K}) := by
    rw [ggAutomizerJoin_singleton]
    exact hR.2.2.2.2.1 y K hK (hW y K hK) (Or.inr hW)
  haveI : Finite (MulAut ↥Bs) := MulEquiv.finite_left
  have heq : ggAutomizerJoin L Bs {K} = ggAutomizerJoin L Bs 𝒦 :=
    (Subgroup.eq_of_le_of_card_ge (hle.trans_eq (ggAutomizerJoin_singleton L Bs K).symm)
      (hmax {K} hset hWK)).symm
  refine ⟨⟨hR, hW, hnL, hset, hWK, fun 𝒦' h1 h2 => ?_⟩, heq⟩
  rw [heq]
  exact hmax 𝒦' h1 h2

end CFSG.StandardType

end
