module

public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockOmegaIsoOneLinear
public import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagOmegaQuasisimple
public import CFSG.LocalAnalysis.StandardType.GGHalfCentGroup
public import CFSG.LocalAnalysis.StandardType.GGF4JoinMemberPSL
public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinSelectedPSU
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMOmegaSmall
public import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagOmegaFour

public section
namespace CFSG.StandardType.ClassicalBlocks

open CFSG CFSG.Assembly CFSG.Open CFSG.StandardType
open CFSG.StandardType.ClassicalPosition
open CFSG.Blueprint

section Guard

private theorem false_of_guarded_small_linear_model
    {X : Type} [Group X] {lab : LargeEvenLabel} (hg : GuardedLargeEvenLabel lab)
    (hM : MarkedModel lab X) {m f : ℕ} (hmodel : LieModel X .PSL m 2 f)
    (hm : m ≤ 5) : False := by
  obtain ⟨-, hA, hmr⟩ := guarded_lieModel_PSL hg hM hmodel
  have h5 : 5 ≤ lab.rank ∧ lab.n = 1 := by
    simpa [GuardedLargeEvenLabel, hA] using hg
  omega

theorem eight_le_card_of_guarded_component_of_statedOmega
    {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Finite K] [CharP K 2]
    (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    {C : Subgroup (GL ι K)} (hC : CFSG.Assembly.IsComponentOf C (StatedOmega ⇑Φ))
    (hmark : LargeEvenMarking C (fun lab _ _ _ _ _ => GuardedLargeEvenLabel lab)) :
    8 ≤ Fintype.card ι := by
  classical
  by_contra h8
  by_cases h2 : Fintype.card ι ≤ 2
  · have hCsub : CFSG.Assembly.IsComponentOf (C.subgroupOf (StatedOmega ⇑Φ)) ⊤ := by
      rw [← CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff
        (StatedOmega ⇑Φ).subtype_injective]
      simpa [Subgroup.subgroupOf_map_subtype, Subgroup.map_top, Subgroup.range_subtype,
        inf_of_le_left hC.1] using hC
    exact RCKRP.not_isComponentOf_statedOmega_of_card_le_two Φ hΦ h2 _
      ((CFSG.Assembly.isComponentOf_iff_open).1 hCsub)
  obtain ⟨n, hn⟩ := CFSG.ComponentClassification.UnbalancedCatalog.even_finrank_of_charTwo Φ hΦ
  rw [Module.finrank_fintype_fun_eq_card] at hn
  have h46 : Fintype.card ι = 4 ∨ Fintype.card ι = 6 := by omega
  obtain ⟨lab, -, R, _, I, F0, theta, -, -, hguard, hmarked⟩ :=
    largeEvenMarking_exists_markedModel hmark
  have hmarkedC : MarkedModel lab (C ⧸ Subgroup.center C) :=
    MarkedModel.of_mulEquiv theta.symm hmarked
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, -, hcardK⟩ := FiniteField.card K 2
  have hf : 1 ≤ (f : ℕ) := f.pos
  have hcard : Nat.card K = 2 ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card, hcardK]
  rcases h46 with h4 | h6
  · by_cases hplus : ∃ T : Submodule K (ι → K), Module.finrank K T = 2 ∧ ∀ x ∈ T, Φ x = 0
    · obtain ⟨g, hmodel⟩ := statedClassicalModel_of_isComponentOf_statedOmega_four
        Φ hΦ h4 hplus hC
      exact false_of_guarded_small_linear_model hguard hmarkedC
        (Or.inl ⟨by decide, hmodel⟩) (by norm_num)
    · have hq : CFSG.Assembly.IsQuasisimple (StatedOmega ⇑Φ) :=
        isQuasisimple_statedOmega Φ hΦ (Or.inr ⟨h4, hplus⟩)
      have hEq : C = StatedOmega ⇑Φ := GGHalf.eq_of_isComponentOf_isQuasisimple hq hC
      subst C
      have hdim : Module.finrank K (ι → K) = 2 * 2 := by
        rw [Module.finrank_fintype_fun_eq_card, h4]
      rcases CFSG.GroupTheory.WeirSylow.exists_isometry_quadPlus_or_quadMinus Φ hΦ
          (n := 2) (by norm_num) hdim with he | ⟨b, c, hirr, he⟩
      · obtain ⟨e⟩ := he
        have hp : CFSG.GroupTheory.WeirSylow.IsPlusType Φ :=
          (CFSG.GroupTheory.WeirSylow.isPlusType_congr e).2
            (CFSG.GroupTheory.WeirSylow.isPlusType_quadPlus K 2)
        obtain ⟨T, hT, hzero⟩ := hp
        exact hplus ⟨T, by rw [hdim] at hT; omega, hzero⟩
      · obtain ⟨e⟩ := he
        have hmodel := exists_statedClassicalModel_statedOmega_of_isometry_quadMinus_two
          (κ := Fin 1 ⊕ Fin 1 ⊕ Fin 2) hirr e hf hcard
        exact false_of_guarded_small_linear_model hguard hmarkedC
          (Or.inl ⟨by decide, hmodel⟩) (by norm_num)
  · have hq : CFSG.Assembly.IsQuasisimple (StatedOmega ⇑Φ) :=
      isQuasisimple_statedOmega Φ hΦ (Or.inl (by omega))
    have hEq : C = StatedOmega ⇑Φ := GGHalf.eq_of_isComponentOf_isQuasisimple hq hC
    subst C
    have hdim : Module.finrank K (ι → K) = 2 * 3 := by
      rw [Module.finrank_fintype_fun_eq_card, h6]
    rcases CFSG.GroupTheory.WeirSylow.exists_isometry_quadPlus_or_quadMinus Φ hΦ
        (n := 3) (by norm_num) hdim with he | ⟨b, c, hirr, he⟩
    · obtain ⟨e⟩ := he
      have hmodel := exists_statedClassicalModel_statedOmega_of_isometry_quadPlus_three
        (κ := Fin 3 ⊕ Fin 3) e hf hcard
      exact false_of_guarded_small_linear_model hguard hmarkedC
        (Or.inl ⟨by decide, hmodel⟩) (by norm_num)
    · obtain ⟨e⟩ := he
      have hmodel := exists_statedClassicalModel_statedOmega_of_isometry_quadMinus_three
        (κ := Fin 2 ⊕ Fin 2 ⊕ Fin 2) hirr e hf hcard
      exact false_of_guardedLabel_of_linear_unitary_model hguard hmarkedC (Or.inr rfl)
        (fun h => by cases h) (Or.inl ⟨by decide, hmodel⟩)

theorem eight_le_finrank_of_guarded_fixed_omega_block
    {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Fintype K] [CharP K 2]
    (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b))
    {ε : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε)
    (hfix : (b : Matrix ι ι K) * ε = ε)
    {C : Subgroup ↥(StatedOmega ⇑Φ)}
    (hC : CFSG.Assembly.IsComponentOf C
      ⁅glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε,
        glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε⁆)
    (hmark : LargeEvenMarking C (fun lab _ _ _ _ _ => GuardedLargeEvenLabel lab)) :
    8 ≤ Module.finrank K (LinearMap.range (Matrix.toLin' ε)) := by
  classical
  let H := glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε
  have hcomm : ⁅H, H⁆ ≤ H := Subgroup.commutator_le.2 fun a ha b hb =>
    H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)
  have hCH : C ≤ H := hC.1.trans hcomm
  have hCo : CFSG.Assembly.IsComponentOf (C.subgroupOf H) ⊤ :=
    RCKRP.rckIsComponentOf_top_of_commutator hC
  obtain ⟨ι₁, hfin, hdec, Q₁, hcard, ⟨Φ₁, heq, hnd⟩, hcases⟩ :=
    blockGroup_iso_Omega_one Φ hΦ h8 b hb hodd hε hfix
  letI : Fintype ι₁ := hfin
  letI : DecidableEq ι₁ := hdec
  rcases hcases with ⟨⟨eH⟩, -⟩ | ⟨-, -, hsol, -⟩
  · let eH' : H ≃* StatedOmega ⇑Φ₁ := heq.symm ▸ eH
    let g : H →* GL ι₁ K := (StatedOmega ⇑Φ₁).subtype.comp eH'.toMonoidHom
    have hg : Function.Injective g :=
      (StatedOmega ⇑Φ₁).subtype_injective.comp eH'.injective
    have hgrange : g.range = StatedOmega ⇑Φ₁ := by
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 eH'.surjective,
        Subgroup.map_top, Subgroup.range_subtype]
    have hCo' : CFSG.Assembly.IsComponentOf ((C.subgroupOf H).map g) (StatedOmega ⇑Φ₁) := by
      have hm := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff hg).2 hCo
      simpa [Subgroup.map_top, hgrange] using hm
    let eC : C ≃* (C.subgroupOf H).map g :=
      (Subgroup.subgroupOfEquivOfLe hCH).symm.trans
        (Subgroup.equivMapOfInjective (C.subgroupOf H) g hg)
    have hmark' : LargeEvenMarking ((C.subgroupOf H).map g)
        (fun lab _ _ _ _ _ => GuardedLargeEvenLabel lab) :=
      largeEvenMarking_of_mulEquiv eC.symm hmark
    have hd := eight_le_card_of_guarded_component_of_statedOmega Φ₁ hnd hCo' hmark'
    rwa [hcard] at hd
  · letI : Group.IsSolvable H := hsol
    exact (ResU3Three.not_isSolvable_of_isQuasisimple hCo.2.2
      (inferInstance : Group.IsSolvable (C.subgroupOf H))).elim

end Guard

end CFSG.StandardType.ClassicalBlocks
