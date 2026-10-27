module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieD4Facts

public section

namespace CFSG.Quasithin.H13.Sec53F.TriD4

open scoped commutatorElement
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin
open CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4
open CFSG.QuasithinUnique.Vol2Native.A312L (exists_finset_card_four)

set_option linter.unusedSectionVars false

theorem commutator_le_perfectCore {G : Type*} [Group G] {P Q : Subgroup G} (hQP : Q ≤ P) :
    ⁅Q, perfectCore P⁆ ≤ perfectCore P := by
  refine Subgroup.commutator_le.2 fun q hq m hm => ?_
  have hn : q * m * q⁻¹ ∈ perfectCore P :=
    (Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer.trans
      (normalizer_le_normalizer_perfectCore P) (hQP hq)) m).1 hm
  have e : ⁅q, m⁆ = (q * m * q⁻¹) * m⁻¹ := by simp [commutatorElement_def, mul_assoc]
  rw [e]
  exact mul_mem hn (inv_mem hm)


variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ3 : σ.toRingHom ^ 3 = 1)

local notation "τ₀" => σ.toRingHom

include hσ3 in
theorem exists_card_four_fa0 (hK4 : 4 ≤ Nat.card K) :
    ∃ s : Finset ↥(orbitField TwistTag.D4 K τ₀ fa0), s.card = 4 := by
  have htop : orbitField TwistTag.D4 K τ₀ fa0 = ⊤ :=
    orbitField_D4_zero_eq_top σ (fun c => ringHom_apply_apply_apply_of_pow_three hσ3 c)
  have hc : 4 ≤ Nat.card ↥(orbitField TwistTag.D4 K τ₀ fa0) := by
    rw [htop, Nat.card_congr Subfield.topEquiv.toEquiv]
    exact hK4
  exact exists_finset_card_four hc

theorem exists_card_four_fa1 (hk4 : 4 ≤ Nat.card ↥(trialityFixedField K τ₀)) :
    ∃ s : Finset ↥(orbitField TwistTag.D4 K τ₀ fa1), s.card = 4 := by
  have hc : 4 ≤ Nat.card ↥(orbitField TwistTag.D4 K τ₀ fa1) := by
    have : Nat.card ↥(orbitField TwistTag.D4 K τ₀ fa1) = Nat.card ↥(trialityFixedField K τ₀) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun c =>
        (mem_orbitField_D4_one σ).trans (mem_trialityFixedField (K := K) (σ := τ₀)).symm)
    rw [this]
    exact hk4
  exact exists_finset_card_four hc

include hσ3 in
theorem Q0_le_perfectCore (hK4 : 4 ≤ Nat.card K) : Q0 σ ≤ perfectCore (P0 σ) :=
  (generation_a0 σ hσ3 (isPGroup_posUnipotent σ hσ3) hK4).trans
    (commutator_le_perfectCore (library_facts σ fa0 singleton_ne_univ_fa0).1)

include hσ3 in
theorem Q1_le_perfectCore (hk4 : 4 ≤ Nat.card ↥(trialityFixedField K τ₀)) :
    Q1 σ ≤ perfectCore (P1 σ) :=
  (generation_a1 σ hσ3 (isPGroup_posUnipotent σ hσ3) hk4).trans
    (commutator_le_perfectCore (library_facts σ fa1 singleton_ne_univ_fa1).1)

include hσ3 in
theorem posUnipotent_le_perfectCore_P0 (hK4 : 4 ≤ Nat.card K) :
    graphFixedPosUnipotent TwistTag.D4 K τ₀ ≤ perfectCore (P0 σ) := by
  obtain ⟨R, hRx, -, -, hMP, -, -⟩ :=
    levi_package σ fa0 (isPGroup_posUnipotent σ hσ3) (exists_card_four_fa0 σ hσ3 hK4)
  intro u hu
  have hu' : u ∈ (graphFixedPosUnipotent TwistTag.D4 K τ₀ : Set (ModGL TwistTag.D4.tag K)) := hu
  rw [(fixed_simple_positive_complement TwistTag.D4 K σ fa0).2.2.1] at hu'
  obtain ⟨v, hv, _, ⟨c, rfl⟩, rfl⟩ := hu'
  refine mul_mem (Q0_le_perfectCore σ hσ3 hK4 ?_) (hMP ⟨uSL c, hRx c⟩)
  rw [show Q0 σ = graphFixedSimpleComplement TwistTag.D4 K τ₀ fa0 from
    radical_eq_simpleComplement τ₀ fa0 supp_fa0]
  exact hv

include hσ3 in
theorem posUnipotent_le_perfectCore_P1 (hk4 : 4 ≤ Nat.card ↥(trialityFixedField K τ₀)) :
    graphFixedPosUnipotent TwistTag.D4 K τ₀ ≤ perfectCore (P1 σ) := by
  obtain ⟨R, hRx, -, -, hMP, -, -⟩ :=
    levi_package σ fa1 (isPGroup_posUnipotent σ hσ3) (exists_card_four_fa1 σ hk4)
  intro u hu
  have hu' : u ∈ (graphFixedPosUnipotent TwistTag.D4 K τ₀ : Set (ModGL TwistTag.D4.tag K)) := hu
  rw [(fixed_simple_positive_complement TwistTag.D4 K σ fa1).2.2.1] at hu'
  obtain ⟨v, hv, _, ⟨c, rfl⟩, rfl⟩ := hu'
  refine mul_mem (Q1_le_perfectCore σ hσ3 hk4 ?_) (hMP ⟨uSL c, hRx c⟩)
  rw [show Q1 σ = graphFixedSimpleComplement TwistTag.D4 K τ₀ fa1 from
    radical_eq_simpleComplement τ₀ fa1 supp_fa1]
  exact hv

end CFSG.Quasithin.H13.Sec53F.TriD4
