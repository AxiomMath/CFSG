module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoJoinPreimage
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoUnitaryAux
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
public import CFSG.LocalAnalysis.StandardType.GGTBFixDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

variable {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}

theorem GGSecFiveE6QTwoCfg.fix
    (hTBF : GGTBFixInput) (hC : GGSecFiveE6QTwoCfg 3 B Bs x L D J) :
    ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer L Bs, φ b = b) → (b : G) ∈ Subgroup.zpowers x := by
  obtain ⟨𝒦, hR, -⟩ := hC
  have hcfg : GGSecFiveRouteCfg' 3 B Bs x L D J 𝒦 := ggSecFiveRouteCfg'_of_routeCfg hR
  obtain ⟨y, K, hnbr⟩ := exists_ggNbr hR.1.1.1.2.2.2.2.2.2.2 hR.1.1.2.2
  exact hTBF G 3 B Bs x L D J hR.1.1 hR.1.2.1 hR.1.2.2.1 hR.1.2.2.2.1 y K hnbr
    (hcfg.2.1 y K hnbr) (Or.inr hcfg.2.1)

theorem GGSecFiveE6QTwoCfg.three_pow_five_le_card
    (hC : GGSecFiveE6QTwoCfg 3 B Bs x L D J) : 3 ^ 5 ≤ Nat.card Bs := by
  obtain ⟨-, -, -, hBs, -, -, -, -, -, -, hNT⟩ := e6QTwo_config_facts hC
  obtain ⟨K', hWeyl⟩ := GGSecFiveE6QTwoCfg.exists_weylOfType_E6_sup hC
  have hAind : ∀ φ ∈ ggAutomizer L Bs ⊔ ggAutomizer K' Bs, φ ∈ ggInduced ⊤ Bs := by
    intro φ hφ
    exact mem_ggInduced_top_of_mem_ggAutomizer
      (sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top) hφ)
  exact E6QTwo.three_pow_five_le_card hBs hNT hAind hWeyl

theorem GGSecFiveE6QTwoCfg.exists_join
    (hC : GGSecFiveE6QTwoCfg 3 B Bs x L D J) :
    ∃ A₀ : Subgroup (MulAut ↥Bs), ggAutomizer L Bs ≤ A₀ ∧ A₀ ≤ ggAutomizer ⊤ Bs ∧
      GGWeylOfType 3 CoxeterMatrix.E₆ A₀ ∧ Nat.card A₀ = 51840 ∧
      ∀ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K →
        Nat.card ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs) ≤ 51840 := by
  obtain ⟨𝒦, hR, -, ι, M, e, hP, ⟨e', rfl⟩, -⟩ := hC
  have hcardJoin : Nat.card ↥(ggAutomizerJoin L Bs 𝒦) = 51840 := by
    rw [← Nat.card_congr e.toEquiv, card_coxeterGroup_reindex, card_coxeterE6_group]
  refine ⟨ggAutomizerJoin L Bs 𝒦, ?_, ggAutomizerJoin_le_top L Bs 𝒦, ?_, hcardJoin, ?_⟩
  · exact le_sup_left
  · exact GGWeylOfType.of_reindex (M := CoxeterMatrix.E₆) (e := e') ⟨e, hP.2⟩
  · intro y K hnbr
    have hWK : GGWeylReflectionGroup 3 (ggAutomizer L Bs ⊔ ggAutomizer K Bs) :=
      hR.1.2.2.2.2.1 y K hnbr (hR.2.1 y K hnbr) (Or.inr hR.2.1)
    have hWK' : GGWeylReflectionGroup 3 (ggAutomizerJoin L Bs {K}) := by
      rwa [ggAutomizerJoin_singleton]
    have hle := hR.2.2.2.2.2 {K} (ggNbrSet_singleton hnbr) hWK'
    rw [ggAutomizerJoin_singleton, hcardJoin] at hle
    exact hle

end CFSG.StandardType

end
