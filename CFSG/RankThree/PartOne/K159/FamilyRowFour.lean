module

public import CFSG.RankThree.PartOne.K159.FamilySL4
public import CFSG.RankThree.PartOne.K159.FamilyModel
public import CFSG.RankThree.PartOne.K159.BorelL0c
import CFSG.RankThree.PartOne.S10.SelectedPrimeNormalizeThetaComponents

public section

namespace CFSG.RankThree.PartOne.K159

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.RankThree.PartOne.S15K
open scoped Pointwise commutatorElement

theorem BlockModelFour.facts {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {J : Type} [Group J]
    (h : BlockModelFour p J) : BorelFactsGrp p J ∨ FamilyFactsGrp p J := by
  rcases h with ⟨F, _, _, _, hpF, ⟨e⟩⟩ | ⟨K, _, _, _, hpK, ⟨e⟩⟩
  · left
    have : Finite J := Finite.of_equiv _ e.symm.toEquiv
    have hSL := borelFactsGrp_specialLinear (K := F) (m := 2) hp hpF le_rfl (by omega)
    exact BorelFactsGrp.of_mulEquiv e.symm hSL
  · right
    exact FamilyFactsGrp.of_mulEquiv e.symm (familyFactsGrp_specialLinear_four hp (by omega) hpK)

variable {G : Type} [Group G] [Finite G]

theorem l0c_core_two {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h15 : Sec15Hyp G p A c L E) (hnorm : SelectedPrimeElementsNormalizeThetaComponents)
    (hEA : E = A) {b : G} (hb : b ∈ E) (hb1 : b ≠ 1) {z : G}
    (hz : z ∈ Subgroup.centralizer ({b} : Set G)) {Y : Subgroup G} (hY0 : Y ∈ thetaCompZeroE p E)
    (hYb : Y ∈ thetaComponentsAt p b) (hTwo : BorelFacts p Y ∨ FamilyFacts p Y) :
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
  obtain ⟨S, hSY, hS1, hS2, hSN, hSc⟩ : ∃ S : Subgroup G, S ≤ Y ∧ S ≠ ⊥ ∧ IsPGroup 2 ↥S ∧
      conjBy z⁻¹ E ≤ Subgroup.normalizer (S : Set G) ∧ S = ⁅S, conjBy z⁻¹ E⁆ := by
    rcases hTwo with hBor | hFam
    · exact exists_two_subgroup_of_borel hp hp2 (hE := hFel) hFmax hFY hBor
    · exact exists_two_subgroup_of_family hp hp2 (hE := hFel) hFmax hFY hFam
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

theorem kf158L0cRowFour_of_model (h : KF158BlocksFourModel) : KF158L0cRowFour := by
  intro G _ _ p A c L E h15 hF hout b hb hb1 z hz Y hY0 hYb hYI
  have hEA : E = A := by
    obtain ⟨-, -, -, -, -, hEA, -⟩ := hout
    exact hEA
  have hmodel := h G p A c L E h15 hF hout b hb hb1 Y hY0 hYb hYI
  have hp3 := h15.h12.three_lt
  exact l0c_core_two h15 selected_prime_elements_normalize_theta_components hEA hb hb1 hz hY0 hYb
    (hmodel.facts h15.h12.prime hp3)

theorem kf158L0c_of_borel_four (hBl : KF158BlocksBorel) (h4 : KF158BlocksFourModel)
    (h5 : KF158L0cRowFive) : KF158L0c :=
  kf158L0c_of_borel hBl (kf158L0cRowFour_of_model h4) h5

end CFSG.RankThree.PartOne.K159
