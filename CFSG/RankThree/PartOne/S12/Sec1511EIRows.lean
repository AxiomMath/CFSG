module

public import CFSG.RankThree.PartOne.S12.Sec1511EI
public import CFSG.RankThree.PartOne.S12.Sec1320
public import CFSG.RankThree.PartOne.S12.Sec138141
public import CFSG.RankThree.PartOne.S10.AmbientTheta

public section

namespace CFSG.RankThree.PartOne

open CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

namespace Sec1511

@[expose] def KFEIMovedL4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G) (f : ℕ),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) → E = A → ¬ IsLThreeTypeAt p L →
    1 ≤ f → p ∣ 2 ^ f + 1 → StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 4 2 f →
      ∀ t ∈ reflectionSet p E, autMovedInG E t ≤ lieGenerated p E

theorem kfEIMoved_of_inputs (hS1320 : Node1320Struct) (hKSp : KF1320Sp) (hKU : KF1320U)
    (hL4 : KFEIMovedL4) (hS141 : Node141Struct) (hKF : KF141)
    (hSchreier : SchreierFor InCatalog) (hTwoAction : TwoActionInputs)
    (h106 : SectionTenMaximalMovingThetaComponentsQuasisimple) (h11 : Sec11One)
    (h122 : Node122) (h122b : Node122b) (h123 : Node123) (h124 : Node124) (h125 : Node125)
    (h126 : Node126) (h127 : Node127) (h128 : Node128) (h129 : Node129) : KFEIMoved := by
  intro G _ _ p A c L E h15 hF hout hnot t ht
  have h := h15.h12
  have hp : p.Prime := h.prime
  have hp5 : 5 ≤ p := Sec12Three.five_le h
  have hEA : E = A := by
    rcases hout with ⟨-, -, -, -, -, hEA, -⟩ | ⟨-, -, -, -, -, hEA, -⟩ | ⟨-, -, -, -, -, hEA, -⟩ |
      ⟨-, -, -, -, -, hEA, -⟩ | h5
    · exact hEA
    · exact hEA
    · exact hEA
    · exact hEA
    · exact absurd h5 hnot
  have hF13 := Sec13Facts.of_nodes hSchreier hTwoAction h106 h11 h122 h122b h123 h124 h125 h126
    h127 h128 h129 h hnot
  obtain ⟨-, -, hZ⟩ := sec13_one_of_nodes h126 h127 h128 h129 h hnot
  by_cases hall : ∀ J : Subgroup G, J ∈ sectionTenZeroStar p A → IsLThreeTypeAt p J
  ·
    obtain ⟨hrow, hweyl, ⟨W⟩⟩ := hS141 G p A c L E h hF hF13 hnot hEA hall
    obtain ⟨f, hf1, hpf, hmodel⟩ := hrow
    have hL : Nonempty (torusImage E L ≃* Equiv.Perm (Fin 3)) := hweyl
    have hL6 : Nat.card (torusImage E L) = (3 : ℕ).factorial := by
      obtain ⟨e⟩ := hL
      rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
    obtain ⟨hK1, -, -⟩ := hKF G p A c L E f h hF hF13 hnot hf1 hpf hmodel hEA hall
    have hKall : ∀ t ∈ reflectionSet p E, KFAt p E f t := by
      intro t ht
      obtain ⟨w, hw, hwt, -⟩ := W.exists_conj_into_L hL6 ht ht
        (Sec138141.exists_fixed_self (by norm_num) W ht)
      exact KFAt.of_conj hw (hK1 _ (conj_mem_reflectionSet hp ht hw) hwt)
    exact (hKall t ht).2.2.2.1.trans (PhanAssembly.kZero_le_lieGenerated hKall ht)
  ·
    obtain ⟨J, hJ, hJn⟩ : ∃ J : Subgroup G, J ∈ sectionTenZeroStar p A ∧ ¬ IsLThreeTypeAt p J := by
      by_contra hcon
      exact hall fun J hJ => by_contra fun hJn => hcon ⟨J, hJ, hJn⟩
    obtain ⟨cJ, hcJA, hcJ1, hJc⟩ := mem_thetaComponentFamily_iff.mp
      ((sectionTenZeroStar_subset p A).2.2.1 hJ.2)
    have hJ' : Sec12Hyp G p A cJ J E :=
      ⟨h.setup, hcJA, hcJ1, ⟨⟨hJ, hZ hJ⟩, hJc⟩, h.E_elem, h.E_le, h.E_max⟩
    have hF12 := Sec12Facts.of_nodes h122 h122b h123 h124 h125 hJ'
    have hF13' := Sec13Facts.of_nodes hSchreier hTwoAction h106 h11 h122 h122b h123 h124 h125 h126
      h127 h128 h129 hJ' hnot
    obtain ⟨hrow, hweyl, t₁, t₂, t₃, hch⟩ := hS1320 G p A cJ J E hJ' hF12 hF13' hnot hEA hJn
    rcases hrow with ⟨f, hf1, hpf, hmodel⟩ | ⟨f, hf1, hpf, hmodel⟩ | ⟨f, hf1, hpf, hmodel⟩
    · obtain ⟨K₁, K₂, K₃, hk₁, hk₂, hk₃, -, -, -⟩ :=
        hKU G p A cJ J E f hJ' hF12 hF13' hnot hf1 hpf hmodel hEA hJn hweyl t₁ t₂ t₃ hch
      obtain ⟨hI, hmov⟩ := Sec1320.lieGenerated_eq hch hk₁ hk₂ hk₃
      exact (hmov t ht).trans hI.ge
    · obtain ⟨K₁, K₂, K₃, hk₁, hk₂, hk₃, -, -, -⟩ :=
        hKSp G p A cJ J E f hJ' hF12 hF13' hnot hf1 hpf hmodel hEA hJn hweyl t₁ t₂ t₃ hch
      obtain ⟨hI, hmov⟩ := Sec1320.lieGenerated_eq hch hk₁ hk₂ hk₃
      exact (hmov t ht).trans hI.ge
    · exact hL4 G p A cJ J E f hJ' hF12 hF13' hnot hEA hJn hf1 hpf hmodel t ht

end Sec1511

end CFSG.RankThree.PartOne
