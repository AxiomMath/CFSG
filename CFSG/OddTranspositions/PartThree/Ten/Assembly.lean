module

public import CFSG.OddTranspositions.PartThree.Ten.Steps
import CFSG.OddTranspositions.SixSixWreathClass
import CFSG.OddTranspositions.SixSixRad
import CFSG.OddTranspositions.FiveThreeQZ
import CFSG.OddTranspositions.PartThree.Ten.WreathEndgame
import CFSG.OddTranspositions.WidthOne
import CFSG.StronglyEmbedded.PSL2Facts
import CFSG.Timmesfeld.Bridge.Asc72Lift

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem exists_l2Wreath_class_of_blockKernel_ne_bot
    (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hK : blockKernel hC.alpha ≠ ⊥) :
    ∃ f m : ℕ, 2 ≤ f ∧ ∃ Φ : G ≃* L2Wreath f m,
      ∀ u ∈ D, ∃ i j : Fin m, i ≠ j ∧ (Φ u).right = Equiv.swap i j ∧
        (∀ k, k ≠ i → k ≠ j → (Φ u).left k = 1) ∧ (Φ u).left j = ((Φ u).left i)⁻¹ := by
  obtain ⟨u, hu⟩ := hC.setup.nonempty
  have htop : (⊤ : Subgroup G) ≠ ⊥ := by
    intro h
    apply hC.setup.oddT.ne_one hu
    have : u ∈ (⊤ : Subgroup G) := Subgroup.mem_top u
    rwa [h, Subgroup.mem_bot] at this
  obtain ⟨M, hM⟩ := exists_isMinimalNormal htop
  by_cases hMs : IsSimpleGroup M
  · exact absurd (blockKernel_eq_bot_of_simple_minimalNormal hC hrad hM hMs
      (centralizer_eq_bot_of_isSimpleGroup hC.setup hrad hM hMs)) hK
  · exact exists_l2Wreath_class_of_not_isSimpleGroup_minimalNormal hC hrad hM hMs

theorem TenHyp.dalpha_nonempty {hC : HypothesisC D} {f n : ℕ} (h : TenHyp hC f n) :
    (Dalpha D hC.alpha).Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have hHbot : Halpha D hC.alpha = ⊥ := by
    rw [Halpha, eq_bot_iff, Subgroup.closure_le]
    rintro x ⟨γ, hγ, -⟩
    rw [hne] at hγ
    exact absurd hγ (Set.notMem_empty _)
  obtain ⟨e⟩ := h.iso
  have hH1 : Nat.card (Halpha D hC.alpha) = 1 := by rw [hHbot, Subgroup.card_bot]
  have hidx : (Subgroup.center (Halpha D hC.alpha)).index = 1 :=
    Nat.dvd_one.mp (hH1 ▸ Subgroup.index_dvd_card _)
  have hW1 : Nat.card (L2Wreath f n) = 1 := by
    rw [← Nat.card_congr e.toEquiv]
    exact hidx
  rw [SemidirectProduct.card, Nat.card_perm, Nat.card_fin] at hW1
  have hpos : 0 < Nat.card (Fin n → CFSG.Theory.Comparator.PSL2Model f) := Nat.card_pos
  have hfact : 5 ≤ n.factorial := h.five_le.trans (Nat.self_le_factorial n)
  nlinarith

theorem theorem10_1_of_steps
    (h4 : TenFour) : Theorem10_1 := by
  have hW := tenWreathEndgame_holds
  intro G _ _ D hC hrad hradH f n hf hn hiso
  have hH : TenHyp hC f n := ⟨hrad, hradH, hf, hn, hiso⟩
  obtain ⟨β, hβ⟩ := hH.dalpha_nonempty
  obtain ⟨hB1, hBK⟩ := h4 G D hC f n hH β hβ
  have hK : blockKernel hC.alpha ≠ ⊥ := fun h => hB1 (le_bot_iff.mp (h ▸ hBK))
  obtain ⟨f', m, hf', Φ, hΦ⟩ := exists_l2Wreath_class_of_blockKernel_ne_bot hC hrad hK
  obtain ⟨rfl, rfl⟩ := hW G D hC f n hH f' m Φ hf' hΦ
  exact ⟨Φ⟩

theorem theorem10_1_of_tenFour
    (h4 : TenFour) : Theorem10_1 :=
  theorem10_1_of_steps h4

end CFSG.OddTranspositions.PartThree

end
