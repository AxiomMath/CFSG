module

public import CFSG.RankThree.GF2n.Parrott.CaseIISpinCoord
public import CFSG.RankThree.GF2n.Parrott.CaseIIF1Sylow
public import CFSG.RankThree.GF2n.Parrott.CaseIIF1Config
public import CFSG.RankThree.GF2n.Parrott.SpinStabW0
public import CFSG.RankThree.GF2n.Parrott.CaseIILFuv
public import CFSG.RankThree.GF2n.Parrott.CaseIITheorem1

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped Matrix

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "vA" => (⟨v, v_mem_A⟩ : A45)
local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
local notation "Mat8" => Matrix (Fin 8) (Fin 8) (ZMod 2)

variable {G : Type} [Group G] [Finite G] {z : G}

theorem exists_isSpinCoord_A (h : Tim79a.ParrottHypA z)
    (D : QuotientData (z := z) (J_subgroupOf_normal z))
    (hIII : ¬ ∃ σ₂ : ↥(H z), orderOf σ₂ = 3 ∧
      qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) ∧
      centralizerJ (sigma1Nine D) = centralizerJ σ₂) :
    ∃ κ : G → V, IsSpinCoord (qH D) κ := by
  obtain ⟨κ, hadd, hsurj, hker, hsq, hcomm, hact⟩ := exists_spinCoord_A h D hIII 1
  refine ⟨κ, ⟨qH_surjective D, fun y => ?_, hadd, hsurj, hker, hsq, hcomm, fun y hy j hj => ?_⟩⟩
  · rw [← J_mem_iff D y, Subgroup.mem_subgroupOf]
  · rw [hact y hy j hj, one_mul, inv_one, mul_one]

theorem not_isConj_z_of_mem_J_A (h : Tim79a.ParrottHypA z)
    (D : QuotientData (z := z) (J_subgroupOf_normal z))
    (hIII : ¬ ∃ σ₂ : ↥(H z), orderOf σ₂ = 3 ∧
      qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) ∧
      centralizerJ (sigma1Nine D) = centralizerJ σ₂) :
    ∀ j ∈ J z, orderOf j = 2 → j ∉ zpowers z → ¬ IsConj z j := by
  intro j hjJ hj2 hjz hzj
  obtain ⟨κ₀, hκ₀⟩ := exists_isSpinCoord_A h D hIII
  have hz2 : orderOf z = 2 := orderOf_z_A h
  have hz1 : z ≠ 1 := by
    intro e
    rw [e, orderOf_one] at hz2
    exact absurd hz2 (by decide)
  have hjj : j * j = 1 := by
    rw [← pow_two, ← hj2]
    exact pow_orderOf_eq_one j
  have hq : q (κ₀ j) = 0 := (hκ₀.mul_self_eq_one_iff hz1 hjJ).mp hjj
  have hne : κ₀ j ≠ 0 := by
    intro h0
    rcases (hκ₀.eq_zero_iff j hjJ).mp h0 with e | e
    · rw [e, orderOf_one] at hj2
      exact absurd hj2 (by decide)
    · exact hjz (e ▸ mem_zpowers z)
  obtain ⟨a, ha⟩ := exists_rhoA_mulVec_eq_spinSingBase (κ₀ j) hne hq
  have hκ := hκ₀.transport a
  have hinj : ∀ a : A45, ((rhoA a : GL8) : Mat8) = 1 → a = 1 := fun a ha =>
    rhoA_injective (by rw [map_one]; exact Units.ext ha)
  obtain ⟨y, hyj, hyz⟩ := exists_conj_eq_z_mul_of_isConj h hκ
    (fun _ ha' h' => eq_one_of_fixes_perp_spinSingBase ha' h')
    eq_zero_or_eq_spinSingBase_of_perp exists_b_spinSingBase_ne_zero hjJ ha hzj
  obtain ⟨W, ℬ, hc⟩ := spinStabConfig_of_conj_eq h hκ hinj exists_b_spinSingBase_ne_zero hjJ ha
    hyj hyz
  exact false_of_spinStab_config W ℬ hc.zero_mem hc.add_mem hc.base_mem hc.singular hc.invariant
    hc.mem_image hc.one_mem hc.mul_mem hc.normal hc.perp hc.flag hc.card hc.faithful

theorem exists_index_two_inf_eq_commutator_A_of_hv
    (h : Tim79a.ParrottHypA z) (D : QuotientData (z := z) (J_subgroupOf_normal z))
    (hIII : ¬ ∃ σ₂ : ↥(H z), orderOf σ₂ = 3 ∧
      qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) ∧
      centralizerJ (sigma1Nine D) = centralizerJ σ₂)
    (hv : (∀ (a : G) (ha : a ∈ H z), IsConj (qH D ⟨a, ha⟩) (uA * vA) → a * a ≠ 1) →
      ∀ (a : G) (ha : a ∈ H z), a * a = 1 → IsConj (qH D ⟨a, ha⟩) vA → ¬ IsConj z a) :
    ∃ G₀ : Subgroup G, G₀.Normal ∧ G₀.index = 2 ∧ z ∈ G₀ ∧ H z ⊓ G₀ = ⁅H z, H z⁆ :=
  exists_index_two_inf_eq_commutator_A_of_F1 h D hIII (not_isConj_z_of_mem_J_A h D hIII) hv

theorem parrott_lemma32_caseII
    (hThm1 : ∀ (G : Type) [Group G] [Finite G] (z : G) (h : Tim79a.ParrottHyp z)
      (hN : ((J z).subgroupOf (H z)).Normal) (D : QuotientData (z := z) hN),
      ParrottEqualityBranch (z := z) (D := D) h → H z ⊔ pPrimeCore 2 G = ⊤) :
    ∀ (K : Type) [Group K] [Finite K] (w : K), Tim79a.ParrottHypA w →
      ¬ (Subgroup.centralizer ({w} : Set K) ⊔ pPrimeCore 2 K = ⊤) →
      ∀ j ∈ J w, orderOf j = 2 → j ∉ Subgroup.zpowers w → ¬ IsConj w j := by
  intro K _ _ w h hne
  obtain ⟨D⟩ := h.quotient
  by_cases heq : ∃ σ₂ : ↥(H w), orderOf σ₂ = 3 ∧
      qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) ∧
      centralizerJ (sigma1Nine D) = centralizerJ σ₂
  · exact absurd (parrott_theorem1_caseII hThm1 h D heq) hne
  · exact not_isConj_z_of_mem_J_A h D heq

end CFSG.RankThree.GF2n.Parrott
