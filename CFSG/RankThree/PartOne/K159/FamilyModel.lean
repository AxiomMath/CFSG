module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartOne.S15K.LayerData

public section

namespace CFSG.RankThree.PartOne.K159

open CFSG CFSG.RankThree CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S15K

@[expose] def BlockModelFour (p : ℕ) (J : Type) [Group J] : Prop :=
  (∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), p ∣ Nat.card F - 1 ∧
      Nonempty (J ≃* Matrix.SpecialLinearGroup (Fin 2) F)) ∨
    (∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), p ∣ Nat.card K + 1 ∧
      Nonempty (J ≃* Matrix.SpecialLinearGroup (Fin 4) K))

theorem BlockModelFour.of_mulEquiv {p : ℕ} {J J' : Type} [Group J] [Group J'] (e : J ≃* J')
    (h : BlockModelFour p J) : BlockModelFour p J' := by
  rcases h with ⟨F, _, _, _, hpF, ⟨e'⟩⟩ | ⟨K, _, _, _, hpK, ⟨e'⟩⟩
  · exact Or.inl ⟨F, inferInstance, inferInstance, inferInstance, hpF, ⟨e.symm.trans e'⟩⟩
  · exact Or.inr ⟨K, inferInstance, inferInstance, inferInstance, hpK, ⟨e.symm.trans e'⟩⟩

variable {G : Type} [Group G] [Finite G]

@[expose] def LayerModelDataFour (p : ℕ) (E I : Subgroup G) : Prop :=
  ∀ b ∈ E, b ≠ 1 → ∃ (ι : Type) (Q : ι → Subgroup G),
    (∀ i, Q i ≤ I ⊓ Subgroup.centralizer ({b} : Set G)) ∧
    (∀ i, IsComponent ((Q i).subgroupOf (I ⊓ Subgroup.centralizer ({b} : Set G)))) ∧
    ⁅I ⊓ Subgroup.centralizer ({b} : Set G), I ⊓ Subgroup.centralizer ({b} : Set G)⁆ = ⨆ i, Q i ∧
    ∀ i, BlockModelFour p ↥(Q i) ∨ Q i ∉ thetaCompZeroE p E

theorem LayerModelDataFour.blockModelFour_of_mem_thetaCompZeroE {p : ℕ} (hp : p.Prime) {E I : Subgroup G}
    (hL : LayerModelDataFour p E I) {b : G} (hb : b ∈ E) (hb1 : b ≠ 1) {Y : Subgroup G}
    (hY0 : Y ∈ thetaCompZeroE p E) (hY : Y ∈ thetaComponentsAt p b) (hYI : Y ≤ I) :
    BlockModelFour p ↥Y := by
  obtain ⟨ι, Q, hQH, hQc, hder, hQT⟩ := hL b hb hb1
  have hYC : Y ≤ Subgroup.centralizer ({b} : Set G) := (mem_thetaComponentsAt_iff.mp hY).1
  obtain ⟨i, rfl⟩ := eq_component_of_mem_thetaComponentsAt hp inf_le_right Q hQH hQc hder hY
    (le_inf hYI hYC)
  exact (hQT i).resolve_right fun h => h hY0

@[expose] def KF158BlocksFourModel : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152Four p E A (lieGenerated p E) →
    ∀ b ∈ E, b ≠ 1 → ∀ Y ∈ thetaCompZeroE p E, Y ∈ thetaComponentsAt p b → Y ≤ lieGenerated p E →
      BlockModelFour p ↥Y

@[expose] def LayerRowFourModel : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    Outcome152Four p E A (lieGenerated p E) → LayerModelDataFour p E (lieGenerated p E)

theorem kf158BlocksFourModel_of_layer (hS13 : Sec13Avail) (hL : LayerRowFourModel) :
    KF158BlocksFourModel := by
  intro G _ _ p A c L E h15 hF hout b hb hb1 Y hY0 hYb hYI
  have hnot5 : ¬ Outcome152Five p E A (lieGenerated p E) := by
    obtain ⟨-, -, -, -, -, hEA, -⟩ := hout
    rintro ⟨-, -, -, -, -, -, hne, -⟩
    exact hne hEA
  have h13 := hS13 G p A c L E h15.h12 hnot5
  exact (hL G p A c L E h15 hF h13 hout).blockModelFour_of_mem_thetaCompZeroE h15.h12.prime hb hb1
    hY0 hYb hYI

end CFSG.RankThree.PartOne.K159
