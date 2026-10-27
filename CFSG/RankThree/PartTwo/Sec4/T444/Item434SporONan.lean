module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporKit
public import CFSG.Sporadic.ON
public import CFSG.RankThree.PartTwo.Sec4.Item47CoreOut
public import CFSG.RankThree.PartTwo.Sec4.Census.TwoCoverCensusResidual

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.LocalCores CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)

namespace Item434Spor

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}

theorem factorization_card_ON : (460815505920 : ℕ).factorization 3 = 4 := by
  rw [show (460815505920 : ℕ) = 3 ^ 4 * 5689080320 by norm_num,
    Item434AltPerm.factorization_three_pow_mul 4 (by norm_num)]

theorem false_of_onan_27
    (h : Ctx434Core G A M Q) (e₀ : layer G ⧸ Subgroup.center (layer G) ≃* Spor .ONan)
    (h27 : Nat.card h.layerStar = 27) : False := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  have b' : NativeSporadic.Carrier .ONan ≃* Spor .ONan := b
  have hcard : Nat.card (Spor .ONan) = 460815505920 := by
    rw [← Nat.card_congr b.toEquiv, CFSG.Sporadic.ON.card_ON]
  have : Finite (Spor .ONan) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have : IsSimpleGroup (layer G ⧸ Subgroup.center (layer G)) := h.isQuasisimple.2.1
  have : IsSimpleGroup (Spor .ONan) := e₀.symm.isSimpleGroup
  have hcen : Subgroup.center (Spor .ONan) = ⊥ :=
    center_eq_bot_of_simple (by rw [hcard]; norm_num)
  have hout : ¬ 3 ∣ Nat.card (Outer (Spor .ONan)) := by
    rw [← Nat.card_congr (equivalence b').toEquiv]
    exact inputs47Core_outON
  have hfac : (Nat.card (Spor .ONan)).factorization 3 = 4 := by
    rw [hcard, factorization_card_ON]
  obtain ⟨E, hE, hEc⟩ := exists_elemAbelian_sylow_of_three_lt_pRank
    Census.SporadicTwoCover.three_lt_pRank_onan hfac
  exact false_of_elemAbelian_sylow h e₀ hout hcen hE hEc (by rw [hEc, hfac]; norm_num) h27

end Item434Spor

section Families


theorem item434SporAtCard_onan_27 :
    Item434SporAtCard .ONan 27 := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL h27
  obtain ⟨e₀⟩ := hL
  exact (Item434Spor.false_of_onan_27 hc e₀ h27).elim

end Families

end CFSG.RankThree.PartTwo.Sec4
