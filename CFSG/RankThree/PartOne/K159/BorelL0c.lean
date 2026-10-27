module

public import CFSG.RankThree.PartOne.K159.BorelConj
public import CFSG.RankThree.PartOne.S15K.L0c
import CFSG.RankThree.PartOne.S10.SelectedPrimeNormalizeThetaComponents
public import CFSG.RankThree.PartOne.S10.AmbientTheta
public import CFSG.RankThree.PartOne.S12.Sec12A
public import CFSG.RankThree.PartOne.S15K.Defs
public import CFSG.RankThree.PartOne.S15K.L0cCore

public section

namespace CFSG.RankThree.PartOne.K159

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.RankThree.PartOne.S15K
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem l0c_core_borel {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h15 : Sec15Hyp G p A c L E) (hnorm : SelectedPrimeElementsNormalizeThetaComponents)
    (hEA : E = A) {b : G} (hb : b ∈ E) (hb1 : b ≠ 1) {z : G}
    (hz : z ∈ Subgroup.centralizer ({b} : Set G)) {Y : Subgroup G} (hY0 : Y ∈ thetaCompZeroE p E)
    (hYb : Y ∈ thetaComponentsAt p b) (hBor : BorelFacts p Y) :
    conjBy z Y ∈ thetaCompZeroE p E := by
  classical
  have h := h15.h12
  have hp := h.prime
  have hp2 : p ≠ 2 := by
    have := h.three_lt
    omega
  have hE : IsElementaryAbelian p ↥E := h.E_elem
  obtain ⟨B, hB, -⟩ := hY0
  have hBE : B = E := by
    have hcard : Nat.card B = Nat.card E := by rw [hB.2.2.1, hEA, h.A_card]
    exact Subgroup.eq_of_le_of_card_ge hB.1 hcard.ge
  have hzb : z * b * z⁻¹ = b := by
    have := Subgroup.mem_centralizer_singleton_iff.1 hz
    calc z * b * z⁻¹ = (z * b) * z⁻¹ := rfl
      _ = (b * z) * z⁻¹ := by rw [← this]
      _ = b := by group
  have hY'b : conjBy z Y ∈ thetaComponentsAt p b := by
    have := conjBy_mem_thetaComponentsAt hp z b hYb
    rwa [hzb] at this
  have hEY' : E ≤ Subgroup.normalizer (conjBy z Y : Set G) :=
    h.E_normalizes_thetaComponentsAt hnorm hb hY'b
  have hFE : conjBy z (conjBy z⁻¹ E) = E := Equivariance.conjBy_conjBy_inv z E
  have hFel : IsElementaryAbelian p ↥(conjBy z⁻¹ E) :=
    Equivariance.isElementaryAbelian_map hE (MulAut.conj z⁻¹).toMonoidHom
  have hFmax : ∀ F' : Subgroup G, IsElementaryAbelian p ↥F' → conjBy z⁻¹ E ≤ F' →
      F' = conjBy z⁻¹ E := by
    intro F' hF' hFF'
    have h1 : IsElementaryAbelian p ↥(conjBy z F') :=
      Equivariance.isElementaryAbelian_map hF' (MulAut.conj z).toMonoidHom
    have h2 : E ≤ conjBy z F' := by
      rw [← hFE]
      exact Subgroup.map_mono hFF'
    have h3 : conjBy z F' = E := h.E_max_global _ h1 h2
    calc F' = conjBy z⁻¹ (conjBy z F') := (Equivariance.conjBy_inv_conjBy z F').symm
      _ = conjBy z⁻¹ E := by rw [h3]
  have hFY : conjBy z⁻¹ E ≤ Subgroup.normalizer (Y : Set G) := by
    have := Equivariance.conjBy_le_normalizer (w := z⁻¹) hEY'
    rwa [Equivariance.conjBy_inv_conjBy] at this
  obtain ⟨S, hSY, hS1, hS2, hSN, hSc⟩ :=
    exists_two_subgroup_of_borel hp hp2 (hE := hFel) hFmax hFY hBor
  refine ⟨B, hB, mem_thetaComponentFamily_iff.2 ⟨b, hBE ▸ hb, hb1, hY'b⟩, conjBy z S,
    Subgroup.map_mono hSY, Equivariance.conjBy_ne_bot hS1, hS2.map _, ?_, ?_⟩
  · have := Equivariance.conjBy_le_normalizer (w := z) hSN
    rwa [hFE, ← hBE] at this
  · have h1 : conjBy z S = conjBy z ⁅S, conjBy z⁻¹ E⁆ := congrArg (conjBy z) hSc
    have h2 : conjBy z ⁅S, conjBy z⁻¹ E⁆ = ⁅conjBy z S, conjBy z (conjBy z⁻¹ E)⁆ :=
      Subgroup.map_commutator _ _ _
    rw [hFE] at h2
    rw [hBE]
    exact h1.trans h2

@[expose] def KF158BlocksBorel : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E →
    (Outcome152One p E A (lieGenerated p E) ∨ Outcome152Two p E A (lieGenerated p E) ∨
      Outcome152Three p E A (lieGenerated p E)) →
    ∀ b ∈ E, b ≠ 1 → ∀ Y ∈ thetaCompZeroE p E, Y ∈ thetaComponentsAt p b → Y ≤ lieGenerated p E →
      BorelFacts p Y

theorem kf158L0c_of_borel (hBl : KF158BlocksBorel) (h4 : KF158L0cRowFour) (h5 : KF158L0cRowFive) :
    KF158L0c := by
  intro G _ _ p A c L E h15 hF hout b hb hb1 z hz Y hY0 hYb hYI
  by_cases h5' : Outcome152Five p E A (lieGenerated p E)
  · exact h5 G p A c L E h15 hF h5' b hb hb1 z hz Y hY0 hYb hYI
  by_cases h4' : Outcome152Four p E A (lieGenerated p E)
  · exact h4 G p A c L E h15 hF h4' b hb hb1 z hz Y hY0 hYb hYI
  have hout3 : Outcome152One p E A (lieGenerated p E) ∨ Outcome152Two p E A (lieGenerated p E) ∨
      Outcome152Three p E A (lieGenerated p E) := by
    rcases hout with h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact absurd h h4'
    · exact absurd h h5'
  have hEA : E = A := by
    rcases hout3 with h | h | h
    · obtain ⟨-, -, -, -, -, hEA, -⟩ := h
      exact hEA
    · obtain ⟨-, -, -, -, -, hEA, -⟩ := h
      exact hEA
    · obtain ⟨-, -, -, -, -, hEA, -⟩ := h
      exact hEA
  exact l0c_core_borel h15 selected_prime_elements_normalize_theta_components hEA hb hb1 hz hY0 hYb
    (hBl G p A c L E h15 hF hout3 b hb hb1 Y hY0 hYb hYI)

end CFSG.RankThree.PartOne.K159
