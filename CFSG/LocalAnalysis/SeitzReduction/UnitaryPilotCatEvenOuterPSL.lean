module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatEvenOuter
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatEvenOuterPSUPSp
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatAlt

public noncomputable section

namespace CFSG.SeitzReduction.UnitaryPilot

open CFSG Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification
open CFSG.ComponentClassification.CatLeafProof (fixedSubgroupCongrEquiv)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.SeitzReduction.F4Pilot (FixedCentralizerTwoFree)
open CFSG.SeitzReduction.LinearPilot (psl_field_pComponents psl_graphField_pComponents
  SpFixedOrNoPComponent psu_outer_fixed_exact psp_outer_fixed_exact)

theorem even_of_graphField_involution {n : ℕ} (hn : 3 ≤ n) {K : Type} [Field K] [Finite K]
    {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (A : GL (Fin n) K) (σ : K ≃+* K)
    (hσ : σ ≠ 1) (hord : orderOf (CatalogueBGraphField.graphFieldAction n K A σ) = 2) :
    2 * (f / 2) = f := by
  have hsq : CatalogueBGraphField.graphFieldAction n K A σ ^ 2 = 1 :=
    hord ▸ pow_orderOf_eq_one _
  obtain ⟨hσ2, -⟩ := CatalogueBGraphField.graphField_involution_conjugacy n K hn A σ hσ hsq
  obtain ⟨heven, -⟩ := LocalAnalysis.ComponentInitial.LinearFlag.even_and_eq_pow_of_involution hf
    hK hσ (by rw [← sq]; exact hσ2)
  obtain ⟨j, hj⟩ := heven
  omega

@[expose] def PSLOuterFixedEven (X : Type) [Group X] (n e : ℕ) : Prop :=
  (∀ P : Subgroup X, IsPComponent 2 P →
      StatedLieAdmissible .PSL n 2 (e / 2) ∧ LieModel P .PSL n 2 (e / 2) ∧ 2 * (e / 2) = e) ∨
    (2 * (e / 2) = e ∧ ∀ P : Subgroup X, IsPComponent 2 P →
      StatedLieAdmissible .PSU n 2 (e / 2) ∧ LieModel P .PSU n 2 (e / 2)) ∨
    (∃ (k : Type) (_ : Field k) (_ : Finite k) (r : ℕ), Nat.card k = 2 ^ e ∧ 1 ≤ r ∧
      Nonempty (X ≃* StatedSp r k)) ∨
    (∀ P : Subgroup X, ¬ IsPComponent 2 P)

theorem pslOuterFixedEven_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {n e' : ℕ}
    (h : PSLOuterFixedEven Y n e') : PSLOuterFixedEven X n e' := by
  have hmap : ∀ P : Subgroup X, IsPComponent 2 P → IsPComponent 2 (P.map e.toMonoidHom) :=
    fun P hP => LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 e hP
  have heq : ∀ P : Subgroup X, P ≃* P.map e.toMonoidHom :=
    fun P => P.equivMapOfInjective e.toMonoidHom e.injective
  rcases h with h | ⟨he, h⟩ | ⟨k, _, _, r, hk, hr, ⟨Φ⟩⟩ | h
  · refine Or.inl fun P hP => ?_
    obtain ⟨hadm, hm, he⟩ := h _ (hmap P hP)
    exact ⟨hadm, LieType.CurtisTits.lieModel_of_mulEquiv (heq P).symm hm, he⟩
  · refine Or.inr (Or.inl ⟨he, fun P hP => ?_⟩)
    obtain ⟨hadm, hm⟩ := h _ (hmap P hP)
    exact ⟨hadm, LieType.CurtisTits.lieModel_of_mulEquiv (heq P).symm hm⟩
  · exact Or.inr (Or.inr (Or.inl ⟨k, inferInstance, inferInstance, r, hk, hr, ⟨e.trans Φ⟩⟩))
  · exact Or.inr (Or.inr (Or.inr fun P hP => h _ (hmap P hP)))

theorem psl_outer_fixed_even {J : Type} [Group J] {n e : ℕ}
    (hadm : StatedLieAdmissible .PSL n 2 e) (hm : LieModel J .PSL n 2 e) (α : MulAut J)
    (hα : orderOf α = 2) (hαo : α ∉ (MulAut.conj : J →* MulAut J).range) :
    PSLOuterFixedEven (fixedSubgroup α) n e := by
  obtain ⟨K, _, _, hK, ⟨eJ⟩⟩ := CatLeafProof.nonempty_mulEquiv_psl_of_lieModel hadm hm
  have hf : 1 ≤ e := hadm.2.1
  have hβ : orderOf (MulAut.congr eJ α) = 2 :=
    (orderOf_injective (MulAut.congr eJ).toMonoidHom (MulAut.congr eJ).injective α).trans hα
  have hβ2 : MulAut.congr eJ α ^ 2 = 1 := hβ ▸ pow_orderOf_eq_one _
  have hβo : MulAut.congr eJ α ∉ inner (ProjectiveSpecialLinearGroup (Fin n) K) := by
    rw [LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  have key : ∀ γ : MulAut (ProjectiveSpecialLinearGroup (Fin n) K), MulAut.congr eJ α = γ →
      PSLOuterFixedEven (fixedSubgroup γ) n e → PSLOuterFixedEven (fixedSubgroup α) n e :=
    fun γ hγ h => pslOuterFixedEven_of_mulEquiv ((fixedSubgroupCongrEquiv eJ α).trans
      (MulEquiv.subgroupCongr (congrArg fixedSubgroup hγ))) h
  have hn : 2 ≤ n := hadm.2.2.1
  have hsemi : ∀ (A : GL (Fin n) K) (σ : K ≃+* K),
      MulAut.congr eJ α = CatalogueBLinearSemilinear.semilinearAction n K A σ →
      PSLOuterFixedEven (fixedSubgroup α) n e := by
    intro A σ hAσ
    by_cases hσ : σ = 1
    · subst hσ
      rw [CatalogueBLinearSemilinear.semilinearAction_one_field] at hAσ
      exact absurd (CatLeafProof.innerDiagonalAction_mem_inner_of_sq hf hK A (hAσ ▸ hβ2))
        (hAσ ▸ hβo)
    · exact key _ hAσ (Or.inl (psl_field_pComponents hn hf hK A σ hσ (hAσ ▸ hβ2)))
  rcases (by omega : n = 2 ∨ 3 ≤ n) with rfl | hn3
  · obtain ⟨A, σ, hAσ⟩ := CatLeafProof.psl_two_normal_form (MulAut.congr eJ α)
    exact hsemi A σ hAσ
  · obtain ⟨-, hgen⟩ := LocalAnalysis.ComponentInitial.LinearFlag.automorphism_generation
      (K := K) hn3
    obtain ⟨A, σ, ε, hε, hAσε⟩ :=
      hgen (MulAut.congr (CatalogueBLinearHigherB.nativeEquiv n K).symm (MulAut.congr eJ α))
    have hβ' : MulAut.congr eJ α = MulAut.congr (CatalogueBLinearHigherB.nativeEquiv n K)
        (LocalAnalysis.ComponentInitial.LinearFlag.conjAut n K A *
          LocalAnalysis.ComponentInitial.LinearFlag.fieldAut n K σ *
            LocalAnalysis.ComponentInitial.LinearFlag.dualAut n K ^ ε) := by
      rw [← hAσε]
      ext x
      simp
    interval_cases ε
    · rw [pow_zero, mul_one, CatalogueBLinearHigherB.congr_semilinear] at hβ'
      exact hsemi A σ hβ'
    · rw [pow_one] at hβ'
      by_cases hσ : σ = 1
      · subst hσ
        rw [map_one, mul_one, CatalogueBLinearHigherB.congr_pureGraph] at hβ'
        refine key _ hβ' ?_
        rcases F4Pilot.psl_graph_cases hf hK hn3 A (hβ' ▸ hβ) with ⟨r, hr1, -, ⟨Φ⟩⟩ | hch
        · exact Or.inr (Or.inr (Or.inl ⟨K, inferInstance, inferInstance, r, hK, hr1, ⟨Φ⟩⟩))
        · exact Or.inr (Or.inr (Or.inr
            (ComponentClassification.CatLeafProof.not_isPComponent_of_isCharacteristicP hch)))
      · rw [CatalogueBLinearHigherB.congr_graphField] at hβ'
        exact key _ hβ' (Or.inr (Or.inl
          ⟨even_of_graphField_involution hn3 hf hK A σ hσ (hβ' ▸ hβ),
            psl_graphField_pComponents hn3 hf hK A σ hσ (hβ' ▸ hβ)⟩))

theorem no_sum_component_statedSp {m : ℕ} (hdet : SUmEvenTypeDetAt m) (hm : 4 ≤ m) {X : Type}
    [Group X] [Finite X] {k : Type} [Field k] [Finite k] {g r : ℕ} (hk : Nat.card k = 2 ^ g)
    (hr : 1 ≤ r) (Φ : X ≃* StatedSp r k) {D : Subgroup X} (hD : IsComponent D) {f : ℕ}
    (hDm : LieModel (D ⧸ center D) .PSU m 2 f) : False := by
  have hg : 1 ≤ g := by
    by_contra h0
    have hk1 : Nat.card k = 1 := by rw [hk, show g = 0 by omega, pow_zero]
    exact absurd hk1 (ne_of_gt Finite.one_lt_card)
  have : CharP k 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hg hk
  have hcardX : Nat.card X = Nat.card k ^ (r ^ 2) *
      ∏ j ∈ Finset.Icc 1 r, (Nat.card k ^ (2 * j) - 1) := by
    rw [Nat.card_congr Φ.toEquiv]
    exact LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp r
  have hdvdX : 2 ^ 6 ∣ Nat.card X :=
    ((two_pow_six_dvd_card_of_lieModel_PSU hm hDm).trans (card_quotient_dvd_card (center D))).trans
      (Subgroup.card_subgroup_dvd_card D)
  have hsmall : ¬ (g = 1 ∧ r ≤ 2) := by
    rintro ⟨rfl, hr2⟩
    rw [hcardX, hk, pow_one] at hdvdX
    rcases (by omega : r = 1 ∨ r = 2) with rfl | rfl
    · exact absurd (hdvdX.trans (dvd_of_eq (by decide) : _ ∣ 6)) (by decide)
    · exact absurd (hdvdX.trans (dvd_of_eq (by decide) : _ ∣ 720)) (by decide)
  obtain ⟨t, r', hX, hadm, hmX, ht⟩ : ∃ (t : StatedLieTag) (r' : ℕ),
      IsSimpleGroup X ∧ StatedLieAdmissible t r' 2 g ∧ LieModel X t r' 2 g ∧ t ≠ .PSU := by
    rcases (by omega : r = 1 ∨ 2 ≤ r) with rfl | hr2
    · have hg2 : 2 ≤ g := by omega
      obtain ⟨e₂⟩ := RankThree.PartOne.KFU.nonempty_SL2_mulEquiv_statedProj (F := k)
      have h4 : 4 ≤ 2 ^ g :=
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg2
      have hadm : StatedLieAdmissible .PSL 2 2 g := ⟨Nat.prime_two, hg, le_rfl,
        fun h => by rw [Prod.mk.injEq] at h; omega,
        fun h => by rw [Prod.mk.injEq] at h; omega⟩
      have hstated : StatedClassicalModel X .PSL 2 2 g :=
        ⟨hadm, k, inferInstance, inferInstance, hk,
          ⟨(Φ.trans (ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne k).symm).trans
            e₂⟩⟩
      exact ⟨.PSL, 2, (LieType.Simplicity.fam_PSL_simplicity X 2 2 g hstated).2, hadm,
        Or.inl ⟨by decide, hstated⟩, by decide⟩
    · have hcond : (Infinite k ∨ 4 ≤ Nat.card k) ∨ (Nat.card k = 3 ∧ 2 ≤ r) ∨
          (Nat.card k = 2 ∧ 3 ≤ r) := by
        rcases (by omega : g = 1 ∨ 2 ≤ g) with rfl | hg2
        · exact Or.inr (Or.inr ⟨by rw [hk, pow_one], by omega⟩)
        · refine Or.inl (Or.inr ?_)
          rw [hk]
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg2
      have hS := ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp k r (by omega) hcond
      obtain ⟨-, -, -, -, ⟨eProj⟩⟩ :=
        SymmetricLocal.small_standard_source_even_simple_symplectic_parameters_stated
          (X := StatedSp r k) hk (by omega) ⟨MulEquiv.refl _⟩
      have hadm : StatedLieAdmissible .PSp r 2 g := ⟨Nat.prime_two, hg, hr2, fun h => by
        rw [Prod.mk.injEq] at h
        obtain ⟨rfl, h2⟩ := h
        exact hsmall ⟨Nat.pow_right_injective le_rfl (h2.trans (pow_one 2).symm), le_rfl⟩⟩
      exact ⟨.PSp, r, (Φ.trans eProj.symm).isSimpleGroup, hadm,
        Or.inl ⟨by decide, hadm, k, inferInstance, inferInstance, hk, ⟨Φ.trans eProj.symm⟩⟩,
        by decide⟩
  have hDtop := F4Pilot.eq_top_of_isComponent_of_isSimpleGroup hD
  let eD : D ≃* X := (MulEquiv.subgroupCongr hDtop).trans Subgroup.topEquiv
  have hDs : IsSimpleGroup D := eD.isSimpleGroup
  obtain ⟨htt, -, -⟩ := sumTypeDet_of_simple hdet hD.1 hDs hDm hadm
    (LieType.CurtisTits.lieModel_of_mulEquiv eD.symm hmX)
  exact ht htt

theorem false_of_spFixedOrNoPComponent_su {m : ℕ} (hdet : SUmEvenTypeDetAt m) (hm : 4 ≤ m)
    {X : Type} [Group X] [Finite X] {g : ℕ} (h : SpFixedOrNoPComponent X g) {D : Subgroup X}
    (hD : IsComponent D) {f : ℕ} (hDm : LieModel (D ⧸ center D) .PSU m 2 f) : False := by
  rcases h with ⟨k, _, _, r, hk, hr, ⟨Φ⟩⟩ | h
  · exact no_sum_component_statedSp hdet hm hk hr Φ hD hDm
  · exact h D (LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hD)

theorem catSUmEvenOuterFamilyAt_PSL {m : ℕ} (hm : 4 ≤ m) (hdet : SUmEvenTypeDetAt m) :
    CatSUmEvenOuterFamilyAt .PSL m := by
  intro S _ _ _ _ n e hadm hmS σ hσ hout f D hD hDm _
  have hDp : IsPComponent 2 D := LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hD
  rcases psl_outer_fixed_even hadm hmS σ hσ hout with h | ⟨he, h⟩ | ⟨k, _, _, r, hk, hr, ⟨Φ⟩⟩ | h
  · obtain ⟨hadm', hmD, -⟩ := h D hDp
    obtain ⟨htt, -, -⟩ := sumTypeDet_of_simple hdet hD.1
      (LinearPilot.isSimpleGroup_of_lieModel_PSL hmD) hDm hadm' hmD
    exact absurd htt (by decide)
  · obtain ⟨hadm', hmD⟩ := h D hDp
    obtain ⟨-, hnm, hef⟩ := sumTypeDet_of_simple hdet hD.1
      (LinearPilot.isSimpleGroup_of_lieModel_PSU hmD) hDm hadm' hmD
    subst hnm
    rw [← hef, he]
    exact hmS
  · exact (no_sum_component_statedSp hdet hm hk hr Φ hD hDm).elim
  · exact (h D hDp).elim

theorem catSUmEvenOuterFamilyAt_PSU {m : ℕ} (hm : 4 ≤ m) (hdet : SUmEvenTypeDetAt m) :
    CatSUmEvenOuterFamilyAt .PSU m := by
  intro S _ _ _ _ n e hadm hmS σ hσ hout f D hD hDm _
  exact (false_of_spFixedOrNoPComponent_su hdet hm (psu_outer_fixed_exact hadm hmS σ hσ hout) hD
    hDm).elim

theorem catSUmEvenOuterFamilyAt_PSp {m : ℕ} (hm : 4 ≤ m)
    (hdet : SUmEvenTypeDetAt m) : CatSUmEvenOuterFamilyAt .PSp m := by
  intro S _ _ _ _ n e hadm hmS σ hσ hout f D hD hDm _
  rcases psp_outer_fixed_exact hadm hmS σ hσ hout with h | ⟨hS, hadmB, hLie⟩
  · exact (false_of_spFixedOrNoPComponent_su hdet hm h hD hDm).elim
  · have hDtop := F4Pilot.eq_top_of_isComponent_of_isSimpleGroup hD
    let eD : D ≃* fixedSubgroup σ := (MulEquiv.subgroupCongr hDtop).trans Subgroup.topEquiv
    have hDs : IsSimpleGroup D := eD.isSimpleGroup
    obtain ⟨htt, -, -⟩ := sumTypeDet_of_simple hdet hD.1 hDs hDm hadmB
      (LieType.CurtisTits.lieModel_of_mulEquiv eD.symm hLie)
    exact absurd htt (by decide)

end CFSG.SeitzReduction.UnitaryPilot
