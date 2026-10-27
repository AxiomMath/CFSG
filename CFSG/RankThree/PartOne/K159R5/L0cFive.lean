module

public import CFSG.RankThree.PartOne.K159R5.Rank
public import CFSG.RankThree.PartOne.S15K.L0c
import CFSG.RankThree.PartOne.S12.Sec1511Tools
import CFSG.RankThree.PartOne.S10.SelectedPrimeNormalizeThetaComponents
public import CFSG.RankThree.PartOne.S15K.LayerData

public section

namespace CFSG.RankThree.PartOne.K159R5

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S15K
open scoped commutatorElement

@[expose] def KF158BlocksFiveSyl : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152Five p E A (lieGenerated p E) →
    ∀ b ∈ E, b ≠ 1 → ∀ Y ∈ thetaCompZeroE p E, Y ∈ thetaComponentsAt p b → Y ≤ lieGenerated p E →
      SylAb p Y

variable {G : Type} [Group G] [Finite G]

theorem layerDataW_isQuasisimple {p : ℕ} (hp : p.Prime) {E I : Subgroup G}
    (hL : LayerDataW p E I) {b : G} (hb : b ∈ E) (hb1 : b ≠ 1) {Y : Subgroup G}
    (hY : Y ∈ thetaComponentsAt p b) (hYI : Y ≤ I) : IsQuasisimple ↥Y := by
  obtain ⟨ι, Q, hQH, hQc, hperf, -⟩ := hL b hb hb1
  have hYC : Y ≤ Subgroup.centralizer ({b} : Set G) := (mem_thetaComponentsAt_iff.mp hY).1
  obtain ⟨i, rfl⟩ := eq_component_of_mem_thetaComponentsAt_of_perfect hp inf_le_right Q hQH hQc
    hperf hY (le_inf hYI hYC)
  exact LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe (hQH i)) (hQc i).1

theorem kf158L0cRowFive_of_sylAb (hL5 : LayerRowFive) (hS : KF158BlocksFiveSyl) : KF158L0cRowFive := by
  intro G _ _ p A c L E h15 hF hout b hb hb1 z hz Y hY0 hYb hYI
  classical
  have h := h15.h12
  have hp := h.prime
  by_cases hXY : conjBy z Y = Y
  · rw [hXY]
    exact hY0
  exfalso
  have hL : LayerDataW p E (lieGenerated p E) := hL5 G p A c L E h15 hF hout
  have hE4 : Nat.card ↥E = p ^ 4 := by
    obtain ⟨-, -, -, -, -, h4, -⟩ := hout
    exact h4
  obtain ⟨hYin, hYZ⟩ := hL.of_mem_thetaComponentsAt hp hb hb1 hYb hYI
  have hYqs : IsQuasisimple ↥Y := layerDataW_isQuasisimple hp hL hb hb1 hYb hYI
  have hsyl : SylAb p Y := hS G p A c L E h15 hF hout b hb hb1 Y hY0 hYb hYI
  have hzb : z * b * z⁻¹ = b := by
    have := Subgroup.mem_centralizer_singleton_iff.1 hz
    calc z * b * z⁻¹ = (z * b) * z⁻¹ := rfl
      _ = (b * z) * z⁻¹ := by rw [← this]
      _ = b := by group
  have hY'b : conjBy z Y ∈ thetaComponentsAt p b := by
    have := conjBy_mem_thetaComponentsAt hp z b hYb
    rwa [hzb] at this
  have hEX : E ≤ Subgroup.normalizer (conjBy z Y : Set G) :=
    h.E_normalizes_thetaComponentsAt selected_prime_elements_normalize_theta_components hb hY'b
  have hYC : Y ≤ Subgroup.centralizer ({b} : Set G) := (mem_thetaComponentsAt_iff.mp hYb).1
  have hXC : conjBy z Y ≤ Subgroup.centralizer ({b} : Set G) := (mem_thetaComponentsAt_iff.mp hY'b).1
  have hXqs : IsQuasisimple ↥(conjBy z Y) :=
    LocalCores.isQuasisimple_of_mulEquiv
      (Y.equivMapOfInjective (MulAut.conj z).toMonoidHom (MulAut.conj z).injective) hYqs
  have hcY : IsComponent (Y.subgroupOf (Subgroup.centralizer ({b} : Set G))) :=
    ⟨LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hYC).symm hYqs,
      isSubnormal_of_mem_thetaComponentsAt hYb⟩
  have hcX : IsComponent ((conjBy z Y).subgroupOf (Subgroup.centralizer ({b} : Set G))) :=
    ⟨LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hXC).symm hXqs,
      isSubnormal_of_mem_thetaComponentsAt hY'b⟩
  have hcomm : ⁅conjBy z Y, Y⁆ = ⊥ :=
    (eq_or_commutator_eq_bot_of_components hXC hYC hcX hcY).resolve_left hXY
  have hXYc : conjBy z Y ≤ Subgroup.centralizer (Y : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
  have hXZ : ¬ p ∣ Nat.card ↥(conjBy z Y ⊓ Subgroup.centralizer (conjBy z Y : Set G)) := by
    have hZ'card : Nat.card ↥(conjBy z Y ⊓ Subgroup.centralizer (conjBy z Y : Set G)) =
        Nat.card ↥(Y ⊓ Subgroup.centralizer (Y : Set G)) := by
      rw [Equivariance.centralizer_conjBy]
      have : conjBy z Y ⊓ conjBy z (Subgroup.centralizer (Y : Set G)) =
          conjBy z (Y ⊓ Subgroup.centralizer (Y : Set G)) :=
        (Subgroup.map_inf Y (Subgroup.centralizer (Y : Set G)) (MulAut.conj z).toMonoidHom
          (MulAut.conj z).injective).symm
      rw [this]
      exact Subgroup.card_map_of_injective (MulAut.conj z).injective
    rw [hZ'card]
    exact hYZ
  have hXsyl : SylAb p (conjBy z Y) := SylAb.map (MulAut.conj z) hsyl
  have htr : ∀ P : Subgroup G, MaxEA p Y P →
      ∃ P' : Subgroup G, MaxEA p (conjBy z Y) P' ∧ Nat.card ↥P' = Nat.card ↥P :=
    fun P hP => ⟨conjBy z P, MaxEA.map (MulAut.conj z) hP,
      Subgroup.card_map_of_injective (MulAut.conj z).injective⟩
  obtain ⟨B, hB, hYB⟩ := hY0
  obtain ⟨-, S, hSY, hS1, hS2, hSN, hSc⟩ := hYB
  exact no_commuting_conjugate hp h.E_elem hE4 h.E_max_global (Sec1511.rank_le_three h) hYin hYZ hB.1
    hB.2.2.1 hSY hS1 hS2 hSN hSc hEX hXZ hXsyl htr hXYc hb hb1 hYC hXC

end CFSG.RankThree.PartOne.K159R5
