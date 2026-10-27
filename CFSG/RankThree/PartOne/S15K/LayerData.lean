module

public import CFSG.RankThree.PartOne.S15K.ThetaLayer
public import CFSG.RankThree.PartOne.S15K.Defs
public import CFSG.RankThree.PartOne.S15K.L0cCore
public import CFSG.RankThree.PartOne.S12.Facts13

public section

namespace CFSG.RankThree.PartOne.S15K

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open CFSG.RankThree.PartOne

variable {G : Type} [Group G] [Finite G]

@[expose] def LayerData (p : ℕ) (E I : Subgroup G) : Prop :=
  ∀ b ∈ E, b ≠ 1 → ∃ (ι : Type) (Q : ι → Subgroup G),
    (∀ i, Q i ≤ I ⊓ Subgroup.centralizer ({b} : Set G)) ∧
    (∀ i, IsComponent ((Q i).subgroupOf (I ⊓ Subgroup.centralizer ({b} : Set G)))) ∧
    ⁅I ⊓ Subgroup.centralizer ({b} : Set G), I ⊓ Subgroup.centralizer ({b} : Set G)⁆ = ⨆ i, Q i ∧
    ∀ i, (∀ e ∈ E, ∃ x ∈ Q i, ∃ y ∈ Subgroup.centralizer (Q i : Set G), e = x * y) ∧
      ¬ p ∣ Nat.card ↥(Q i ⊓ Subgroup.centralizer (Q i : Set G))

@[expose] def LayerDataP (p : ℕ) (E I : Subgroup G) : Prop :=
  ∀ b ∈ E, b ≠ 1 → ∃ (ι : Type) (Q : ι → Subgroup G),
    (∀ i, Q i ≤ I ⊓ Subgroup.centralizer ({b} : Set G)) ∧
    (∀ i, IsComponent ((Q i).subgroupOf (I ⊓ Subgroup.centralizer ({b} : Set G)))) ∧
    ⁅I ⊓ Subgroup.centralizer ({b} : Set G), I ⊓ Subgroup.centralizer ({b} : Set G)⁆ = ⨆ i, Q i ∧
    (∀ i, (∀ e ∈ E, ∃ x ∈ Q i, ∃ y ∈ Subgroup.centralizer (Q i : Set G), e = x * y) ∧
      ¬ p ∣ Nat.card ↥(Q i ⊓ Subgroup.centralizer (Q i : Set G))) ∧
    ∀ i, PSylowIn p (Q i)

omit [Finite G] in
theorem LayerDataP.toLayerData {p : ℕ} {E I : Subgroup G} (h : LayerDataP p E I) : LayerData p E I := by
  intro b hb hb1
  obtain ⟨ι, Q, h1, h2, h3, h4, -⟩ := h b hb hb1
  exact ⟨ι, Q, h1, h2, h3, h4⟩

@[expose] def LayerDataW (p : ℕ) (E I : Subgroup G) : Prop :=
  ∀ b ∈ E, b ≠ 1 → ∃ (ι : Type) (Q : ι → Subgroup G),
    (∀ i, Q i ≤ I ⊓ Subgroup.centralizer ({b} : Set G)) ∧
    (∀ i, IsComponent ((Q i).subgroupOf (I ⊓ Subgroup.centralizer ({b} : Set G)))) ∧
    (∀ Y : Subgroup G, Y ≤ I ⊓ Subgroup.centralizer ({b} : Set G) → Group.IsPerfect ↥Y →
      Y ≤ ⨆ i, Q i) ∧
    ∀ i, (∀ e ∈ E, ∃ x ∈ Q i, ∃ y ∈ Subgroup.centralizer (Q i : Set G), e = x * y) ∧
      ¬ p ∣ Nat.card ↥(Q i ⊓ Subgroup.centralizer (Q i : Set G))

omit [Finite G] in
theorem LayerData.toW {p : ℕ} {E I : Subgroup G} (h : LayerData p E I) : LayerDataW p E I := by
  intro b hb hb1
  obtain ⟨ι, Q, h1, h2, h3, h4⟩ := h b hb hb1
  refine ⟨ι, Q, h1, h2, fun Y hYH hYperf => ?_, h4⟩
  rw [← h3]
  calc Y = ⁅Y, Y⁆ := ((Subgroup.isPerfect_iff).1 hYperf).symm
    _ ≤ ⁅I ⊓ Subgroup.centralizer ({b} : Set G), I ⊓ Subgroup.centralizer ({b} : Set G)⁆ :=
      Subgroup.commutator_mono hYH hYH

theorem LayerDataW.of_mem_thetaComponentsAt {p : ℕ} (hp : p.Prime) {E I : Subgroup G}
    (hL : LayerDataW p E I) {b : G} (hb : b ∈ E) (hb1 : b ≠ 1) {Y : Subgroup G}
    (hY : Y ∈ thetaComponentsAt p b) (hYI : Y ≤ I) :
    (∀ e ∈ E, ∃ x ∈ Y, ∃ y ∈ Subgroup.centralizer (Y : Set G), e = x * y) ∧
      ¬ p ∣ Nat.card ↥(Y ⊓ Subgroup.centralizer (Y : Set G)) := by
  obtain ⟨ι, Q, hQH, hQc, hperf, hQ⟩ := hL b hb hb1
  have hYC : Y ≤ Subgroup.centralizer ({b} : Set G) := (mem_thetaComponentsAt_iff.mp hY).1
  obtain ⟨i, rfl⟩ := eq_component_of_mem_thetaComponentsAt_of_perfect hp inf_le_right Q hQH hQc
    hperf hY (le_inf hYI hYC)
  exact hQ i

theorem LayerDataW.commute_of_mem_thetaComponentsAt {p : ℕ} (hp : p.Prime) {E I : Subgroup G}
    (hL : LayerDataW p E I) {b : G} (hb : b ∈ E) (hb1 : b ≠ 1) {Y₁ Y₂ : Subgroup G}
    (hY₁ : Y₁ ∈ thetaComponentsAt p b) (hY₁I : Y₁ ≤ I) (hY₂ : Y₂ ∈ thetaComponentsAt p b)
    (hY₂I : Y₂ ≤ I) (hne : Y₁ ≠ Y₂) : Y₁ ≤ Subgroup.centralizer (Y₂ : Set G) := by
  obtain ⟨ι, Q, hQH, hQc, hperf, -⟩ := hL b hb hb1
  have hY₁C : Y₁ ≤ Subgroup.centralizer ({b} : Set G) := (mem_thetaComponentsAt_iff.mp hY₁).1
  have hY₂C : Y₂ ≤ Subgroup.centralizer ({b} : Set G) := (mem_thetaComponentsAt_iff.mp hY₂).1
  obtain ⟨i, rfl⟩ := eq_component_of_mem_thetaComponentsAt_of_perfect hp inf_le_right Q hQH hQc
    hperf hY₁ (le_inf hY₁I hY₁C)
  obtain ⟨j, rfl⟩ := eq_component_of_mem_thetaComponentsAt_of_perfect hp inf_le_right Q hQH hQc
    hperf hY₂ (le_inf hY₂I hY₂C)
  rcases eq_or_commutator_eq_bot_of_components (hQH i) (hQH j) (hQc i) (hQc j) with h | h
  · exact absurd h hne
  · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h

omit [Finite G] in
theorem exists_mem_thetaComponentsAt_of_mem_thetaCompZeroE {p : ℕ} {E X : Subgroup G}
    (hX : X ∈ thetaCompZeroE p E) : ∃ b ∈ E, b ≠ 1 ∧ X ∈ thetaComponentsAt p b := by
  obtain ⟨B, hB, hXB⟩ := hX
  obtain ⟨b, hbB, hb1, hXb⟩ := mem_thetaComponentFamily_iff.mp hXB.1
  exact ⟨b, hB.1 hbB, hb1, hXb⟩

@[expose] def LayerRowOne : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    Outcome152One p E A (lieGenerated p E) → LayerDataP p E (lieGenerated p E)

@[expose] def LayerRowTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    Outcome152Two p E A (lieGenerated p E) → LayerDataP p E (lieGenerated p E)

@[expose] def LayerRowThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    Outcome152Three p E A (lieGenerated p E) → LayerData p E (lieGenerated p E)

@[expose] def LayerRowFour : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    Outcome152Four p E A (lieGenerated p E) → LayerData p E (lieGenerated p E)

@[expose] def LayerRowFive : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E →
    Outcome152Five p E A (lieGenerated p E) → LayerDataW p E (lieGenerated p E)

@[expose] def Sec13Avail : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → ¬ Outcome152Five p E A (lieGenerated p E) → Sec13Facts G p A c L E

theorem sec13Avail_of_nodes (hSchreier : SchreierFor InCatalog) (hTwoAction : TwoActionInputs)
    (h106 : SectionTenMaximalMovingThetaComponentsQuasisimple) (h11 : Sec11One)
    (h122 : Node122) (h122b : Node122b) (h123 : Node123) (h124 : Node124) (h125 : Node125)
    (h126 : Node126) (h127 : Node127) (h128 : Node128) (h129 : Node129) : Sec13Avail :=
  fun _ _ _ _ _ _ _ _ h hT =>
    Sec13Facts.of_nodes hSchreier hTwoAction h106 h11 h122 h122b h123 h124 h125 h126 h127 h128 h129
      h hT

theorem layerDataW_of_rows (hS13 : Sec13Avail) (h1 : LayerRowOne) (h2 : LayerRowTwo)
    (h3 : LayerRowThree) (h4 : LayerRowFour) (h5 : LayerRowFive) (G : Type) [Group G] [Finite G]
    (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G) (h15 : Sec15Hyp G p A c L E)
    (hF : Sec12Facts G p A c L E) (hout : Outcome152 p E A (lieGenerated p E)) :
    LayerDataW p E (lieGenerated p E) := by
  have hnot5 : ∀ {A' : Subgroup G}, E = A' → ¬ Outcome152Five p E A' (lieGenerated p E) := by
    rintro A' rfl ⟨-, -, -, -, -, -, hne, -⟩
    exact hne rfl
  rcases hout with hO | hO | hO | hO | hO
  · exact (h1 G p A c L E h15 hF (hS13 G p A c L E h15.h12 (hnot5 hO.choose_spec.2.2.2.2.1)) hO).toLayerData.toW
  · exact (h2 G p A c L E h15 hF (hS13 G p A c L E h15.h12 (hnot5 hO.choose_spec.2.2.2.2.1)) hO).toLayerData.toW
  · exact (h3 G p A c L E h15 hF (hS13 G p A c L E h15.h12 (hnot5 hO.choose_spec.2.2.2.2.1)) hO).toW
  · exact (h4 G p A c L E h15 hF (hS13 G p A c L E h15.h12 (hnot5 hO.choose_spec.2.2.2.2.1)) hO).toW
  · exact h5 G p A c L E h15 hF hO

theorem layerData_of_rows (hS13 : Sec13Avail) (h1 : LayerRowOne) (h2 : LayerRowTwo)
    (h3 : LayerRowThree) (h4 : LayerRowFour) (G : Type) [Group G] [Finite G]
    (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G) (h15 : Sec15Hyp G p A c L E)
    (hF : Sec12Facts G p A c L E) (hout : Outcome152 p E A (lieGenerated p E)) (hEA : E = A) :
    LayerData p E (lieGenerated p E) := by
  have hnot5 : ¬ Outcome152Five p E A (lieGenerated p E) := by
    subst hEA
    rintro ⟨-, -, -, -, -, -, hne, -⟩
    exact hne rfl
  have hnot5' : ∀ {A' : Subgroup G}, E = A' → ¬ Outcome152Five p E A' (lieGenerated p E) := by
    rintro A' rfl ⟨-, -, -, -, -, -, hne, -⟩
    exact hne rfl
  rcases hout with hO | hO | hO | hO | hO
  · exact (h1 G p A c L E h15 hF (hS13 G p A c L E h15.h12 (hnot5' hO.choose_spec.2.2.2.2.1)) hO).toLayerData
  · exact (h2 G p A c L E h15 hF (hS13 G p A c L E h15.h12 (hnot5' hO.choose_spec.2.2.2.2.1)) hO).toLayerData
  · exact h3 G p A c L E h15 hF (hS13 G p A c L E h15.h12 (hnot5' hO.choose_spec.2.2.2.2.1)) hO
  · exact h4 G p A c L E h15 hF (hS13 G p A c L E h15.h12 (hnot5' hO.choose_spec.2.2.2.2.1)) hO
  · exact absurd hO hnot5

theorem kf158Commc_of_layerRows (hS13 : Sec13Avail) (h1 : LayerRowOne) (h2 : LayerRowTwo)
    (h3 : LayerRowThree) (h4 : LayerRowFour) (h5 : LayerRowFive) : KF158Commc := by
  intro G _ _ p A c L E h15 hF hout b hb hb1 Y₁ _ hY₁ hY₁I Y₂ _ hY₂ hY₂I hne
  exact (layerDataW_of_rows hS13 h1 h2 h3 h4 h5 G p A c L E h15 hF hout).commute_of_mem_thetaComponentsAt
    h15.h12.prime hb hb1 hY₁ hY₁I hY₂ hY₂I hne

theorem kf157c_of_layerRows (hS13 : Sec13Avail) (h1 : LayerRowOne) (h2 : LayerRowTwo)
    (h3 : LayerRowThree) (h4 : LayerRowFour) (h5 : LayerRowFive) : KF157c := by
  intro G _ _ p A c L E h15 hF hout X hX hXI
  obtain ⟨b, hb, hb1, hXb⟩ := exists_mem_thetaComponentsAt_of_mem_thetaCompZeroE hX
  exact (layerDataW_of_rows hS13 h1 h2 h3 h4 h5 G p A c L E h15 hF hout).of_mem_thetaComponentsAt
    h15.h12.prime hb hb1 hXb hXI

end CFSG.RankThree.PartOne.S15K
