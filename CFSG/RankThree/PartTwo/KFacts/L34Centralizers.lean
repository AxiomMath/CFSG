module

public import CFSG.RankThree.PartTwo.KFacts.L34Automizer
public import CFSG.RankThree.PartTwo.KFacts.L34Aut
public import CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModelCases

public section

namespace CFSG.RankThree.PartTwo.KFacts.L34

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModel (autFixed mem_autFixed)
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.CatalogueBHigherLinearField

section General

variable {G : Type*} [Group G]

theorem map_conj_autFixed (hinj : Function.Injective (MulAut.conj : G →* MulAut G))
    (α : MulAut G) :
    (autFixed α).map (MulAut.conj : G →* MulAut G) =
      (MulAut.conj : G →* MulAut G).range ⊓ Subgroup.centralizer {α} := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨⟨x, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h := CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv α x
    rw [(mem_autFixed).mp hx] at h
    calc MulAut.conj x * α = α * MulAut.conj x * α⁻¹ * α := by rw [h]
      _ = α * MulAut.conj x := by group
  · rintro _ ⟨⟨x, rfl⟩, hc⟩
    refine ⟨x, ?_, rfl⟩
    change α x = x
    apply hinj
    rw [← CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv,
      ← (Subgroup.mem_centralizer_singleton_iff.mp hc)]
    group

theorem card_autFixed_eq (hinj : Function.Injective (MulAut.conj : G →* MulAut G))
    (α : MulAut G) :
    Nat.card (autFixed α) =
      Nat.card ((MulAut.conj : G →* MulAut G).range ⊓ Subgroup.centralizer {α} :
        Subgroup (MulAut G)) := by
  rw [← map_conj_autFixed hinj, Subgroup.card_map_of_injective hinj]

theorem autFixed_conj (g α : MulAut G) :
    autFixed (g * α * g⁻¹) = (autFixed α).map g.toMonoidHom := by
  ext x
  rw [mem_autFixed]
  constructor
  · intro hx
    refine ⟨g⁻¹ x, ?_, by simp⟩
    change α (g⁻¹ x) = g⁻¹ x
    calc α (g⁻¹ x) = g⁻¹ (g (α (g⁻¹ x))) := by simp
      _ = g⁻¹ ((g * α * g⁻¹) x) := rfl
      _ = g⁻¹ x := by rw [hx]
  · rintro ⟨y, hy, rfl⟩
    change α y = y at hy
    simp [MulAut.mul_apply, hy]

theorem card_autFixed_conj (g α : MulAut G) :
    Nat.card (autFixed (g * α * g⁻¹)) = Nat.card (autFixed α) := by
  rw [autFixed_conj, Subgroup.card_map_of_injective g.injective]

end General

section Inner

variable {k : Type} [Field k] {σ : k ≃+* k}

theorem eq_of_conjAut_mul_mem_range (hk : Nat.card k = 4) (hσ : ∀ a, σ a = a ^ 2)
    (B : GL (Fin 3) k) (φ : k ≃+* k) {ε : ℕ} (hε : ε ≤ 1)
    (h : conjAut 3 k B * fieldAut 3 k φ * dualAut 3 k ^ ε ∈
      (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range) :
    φ = 1 ∧ ε = 0 ∧ Matrix.GeneralLinearGroup.det B = 1 := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨g, rfl⟩ := proj_surjective 3 k x
  rw [CFSG.RankThree.PartTwo.KFacts.conj_proj_eq_conjAut] at hx
  have hε' : dualAut 3 k ^ ε = dualAut 3 k ^ ((ε : ZMod 2)).val := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have hg : Matrix.GeneralLinearGroup.det (Matrix.SpecialLinearGroup.toGL g) = 1 :=
    Units.ext (by rw [Matrix.GeneralLinearGroup.val_det_apply]; exact g.prop)
  rcases LinearThreeFourOuter.ringEquiv_eq_one_or hσ hk φ with h1 | h1
  · subst h1
    have hnf : LinearThreeFourOuter.nf σ (Matrix.SpecialLinearGroup.toGL g) 0 0 =
        LinearThreeFourOuter.nf σ B 0 (ε : ZMod 2) := by
      rw [LinearThreeFourOuter.nf_zero_zero, hx, LinearThreeFourOuter.nf, ← hε']
      simp
    obtain ⟨hdet, -, hb⟩ := LinearThreeFourOuter.nf_inj hσ hk hnf
    refine ⟨rfl, ?_, hdet ▸ hg⟩
    have : ((ε : ℕ) : ZMod 2) = 0 := hb.symm
    interval_cases ε
    · rfl
    · exact absurd this (by decide)
  · rw [h1] at hx
    have hnf : LinearThreeFourOuter.nf σ (Matrix.SpecialLinearGroup.toGL g) 0 0 =
        LinearThreeFourOuter.nf σ B 1 (ε : ZMod 2) := by
      rw [LinearThreeFourOuter.nf_zero_zero, hx, LinearThreeFourOuter.nf, ← hε']
      simp [LinearThreeFourOuter.val_one_two]
    obtain ⟨-, ha, -⟩ := LinearThreeFourOuter.nf_inj hσ hk hnf
    exact absurd ha (by decide)

end Inner

section Field

variable {k : Type} [Field k] {σ : k ≃+* k}

theorem card_fixedField_eq_two (hk : Nat.card k = 4) (hσ : ∀ a, σ a = a ^ 2) :
    Nat.card (fixedField k σ) = 2 := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  have hsq : σ ^ 2 = 1 := by rw [pow_two]; exact LinearThreeFourOuter.sigma_mul_self hσ hk
  have h := fixedField_card_square k σ hsq (LinearThreeFourOuter.sigma_ne_one hσ hk)
  rw [hk] at h
  have h1 : Nat.card (fixedField k σ) ≤ 2 := by nlinarith
  have h2 : 2 ≤ Nat.card (fixedField k σ) := by nlinarith
  omega

theorem card_projectiveSL_fixedField (hk : Nat.card k = 4) (hσ : ∀ a, σ a = a ^ 2) :
    Nat.card (projectiveSL 3 (fixedField k σ)) = 168 := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  have : CharP (fixedField k σ) (ringChar (fixedField k σ)) := ringChar.charP _
  obtain ⟨-, hSL, -, hZ, hP, -⟩ := linear_order (K := fixedField k σ)
    (ringChar (fixedField k σ)) 2 (card_fixedField_eq_two hk hσ) (n := 3) (by norm_num)
  have hZ1 : Nat.card (scalars 3 (fixedField k σ)) = 1 := Nat.eq_one_of_dvd_one hZ
  rw [hP, hSL, hZ1]
  decide

theorem inf_centralizer_fieldAut (hk : Nat.card k = 4) (hσ : ∀ a, σ a = a ^ 2) :
    (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range ⊓
        Subgroup.centralizer {fieldAut 3 k σ} = (subfieldConj 3 σ).range := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  obtain ⟨-, -, hNinn, hC, hNC, -, -⟩ :=
    linear_quadratic_field_full_centralizer_rigidity (n := 3) σ le_rfl
  apply le_antisymm
  · rintro α ⟨hαinn, hαC⟩
    have hα : α ∈ (Subgroup.centralizer {fieldAut 3 k σ} : Set (MulAut (projectiveSL 3 k))) :=
      hαC
    rw [hC] at hα
    obtain ⟨B, φ, ε, hε, rfl⟩ := hα
    obtain ⟨rfl, rfl, hdet⟩ := eq_of_conjAut_mul_mem_range hk hσ _ φ hε hαinn
    have hdetB : (B : Matrix (Fin 3) (Fin 3) (fixedField k σ)).det = 1 := by
      apply (fixedField k σ).subtype.injective
      have h1 := congrArg Units.val hdet
      rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at h1
      rw [map_one, ← h1, RingHom.map_det]
      rfl
    set B' : Matrix.SpecialLinearGroup (Fin 3) (fixedField k σ) :=
      ⟨(B : Matrix (Fin 3) (Fin 3) (fixedField k σ)), hdetB⟩
    refine ⟨B', ?_⟩
    change conjAut 3 k (subfieldSLIncl 3 σ B') = _
    rw [subfieldSLIncl_eq]
    simp only [map_one, mul_one, pow_zero]
    congr 2
    exact Units.ext rfl
  · exact le_inf hNinn hNC

theorem card_autFixed_fieldAut (hk : Nat.card k = 4) (hσ : ∀ a, σ a = a ^ 2) :
    Nat.card (autFixed (fieldAut 3 k σ)) = 168 := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  obtain ⟨-, ⟨e, -⟩, -⟩ := linear_quadratic_field_full_centralizer_rigidity (n := 3) σ le_rfl
  rw [card_autFixed_eq (conj_injective hk), inf_centralizer_fieldAut hk hσ,
    ← Nat.card_congr e.toEquiv, card_projectiveSL_fixedField hk hσ]

theorem nonempty_autFixed_fieldAut_equiv (hk : Nat.card k = 4) (hσ : ∀ a, σ a = a ^ 2) :
    Nonempty (autFixed (fieldAut 3 k σ) ≃* projectiveSL 3 (fixedField k σ)) := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  obtain ⟨-, ⟨e, -⟩, -⟩ := linear_quadratic_field_full_centralizer_rigidity (n := 3) σ le_rfl
  exact ⟨((Subgroup.equivMapOfInjective _ _ (conj_injective hk)).trans
    (MulEquiv.subgroupCongr ((map_conj_autFixed (conj_injective hk) _).trans
      (inf_centralizer_fieldAut hk hσ)))).trans e.symm⟩

end Field

section GraphField

variable {k : Type} [Field k] {σ : k ≃+* k}

theorem unitaryFieldData_of_card (hk : Nat.card k = 4) : UnitaryFieldData 2 1 k :=
  ⟨Nat.prime_two, le_rfl, by rw [hk]; norm_num⟩

theorem inf_centralizer_betaAut (hk : Nat.card k = 4) (hσ : ∀ a, σ a = a ^ 2) :
    (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range ⊓
        Subgroup.centralizer {betaAut σ} =
      (CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 k 3).map (conjAut 3 k) := by
  have h := unitaryFieldData_of_card hk
  have hσbar : ∀ x, σ x = h.bar x := fun x => by rw [hσ, UnitaryFieldData.bar_apply, pow_one]
  obtain ⟨-, -, hNinn, hC, hNC, -, -⟩ :=
    linear_graph_field_full_centralizer_rigidity h (n := 3) le_rfl σ hσbar
  apply le_antisymm
  · rintro α ⟨hαinn, hαC⟩
    have hα : α ∈ (Subgroup.centralizer {fieldAut 3 k σ * dualAut 3 k} :
        Set (MulAut (projectiveSL 3 k))) := hαC
    rw [hC] at hα
    obtain ⟨B, hB, φ, ε, hε, rfl⟩ := hα
    obtain ⟨rfl, rfl, hdet⟩ := eq_of_conjAut_mul_mem_range hk hσ B φ hε hαinn
    refine ⟨B, (CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff h).mpr ⟨?_, hB⟩, ?_⟩
    · have h1 := congrArg Units.val hdet
      rwa [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at h1
    · simp
  · exact le_inf hNinn hNC

theorem nonempty_autFixed_betaAut_equiv (hk : Nat.card k = 4) (hσ : ∀ a, σ a = a ^ 2) :
    Nonempty (autFixed (betaAut σ) ≃*
      CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (unitaryFieldData_of_card hk) 3) := by
  have h := unitaryFieldData_of_card hk
  have hσbar : ∀ x, σ x = h.bar x := fun x => by rw [hσ, UnitaryFieldData.bar_apply, pow_one]
  obtain ⟨-, ⟨ι, -⟩, -⟩ := linear_graph_field_full_centralizer_rigidity h (n := 3) le_rfl σ hσbar
  exact ⟨((Subgroup.equivMapOfInjective _ _ (conj_injective hk)).trans
    (MulEquiv.subgroupCongr ((map_conj_autFixed (conj_injective hk) _).trans
      (inf_centralizer_betaAut hk hσ)))).trans ι.symm⟩

theorem card_autFixed_betaAut (hk : Nat.card k = 4) (hσ : ∀ a, σ a = a ^ 2) :
    Nat.card (autFixed (betaAut σ)) = 72 := by
  obtain ⟨e⟩ := nonempty_autFixed_betaAut_equiv hk hσ
  rw [Nat.card_congr e.toEquiv, GL3TwoFixedModel.card_unitaryPSU_three]

end GraphField

section Graph

variable {k : Type} [Field k]

theorem inf_centralizer_dualAut (hk : Nat.card k = 4) :
    (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range ⊓
        Subgroup.centralizer {dualAut 3 k} =
      (FourGroupEvenCanonical.matrixIsometryGroup
        ((1 : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)).map (conjAut 3 k) := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  have hσ : ∀ a, frobeniusEquiv k 2 a = a ^ 2 := fun a => frobeniusEquiv_apply k 2 a
  obtain ⟨-, hNinn, -, hC, hNC, -, -⟩ := even_linear_canonical_graph_symplectic_centralizers
    (K := k) (n := 3) (f := 2) (by norm_num) (by rw [hk]; norm_num) le_rfl 1 (Or.inl rfl)
  have h1 : conjAut 3 k 1 * dualAut 3 k = dualAut 3 k := by rw [map_one, one_mul]
  rw [h1] at hC hNC
  apply le_antisymm
  · rintro α ⟨hαinn, hαC⟩
    have hα : α ∈ (Subgroup.centralizer {dualAut 3 k} : Set (MulAut (projectiveSL 3 k))) := hαC
    rw [hC] at hα
    obtain ⟨g, hg, φ, ε, hε, rfl⟩ := hα
    obtain ⟨rfl, rfl, -⟩ := eq_of_conjAut_mul_mem_range hk hσ g φ hε hαinn
    exact ⟨g, hg, by simp⟩
  · exact le_inf hNinn hNC

theorem nonempty_autFixed_dualAut_equiv (hk : Nat.card k = 4) :
    Nonempty (autFixed (dualAut 3 k) ≃* CFSG.Assembly.LowTwoRank.StatedSp 1 k) := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  obtain ⟨hinj, -⟩ := even_linear_canonical_graph_symplectic_centralizers
    (K := k) (n := 3) (f := 2) (by norm_num) (by rw [hk]; norm_num) le_rfl 1 (Or.inl rfl)
  have h2 : (3 : ℕ) = 2 * 1 + 1 := rfl
  obtain ⟨e₂⟩ := CFSG.ComponentClassification.OutcomeLocal.nonempty_altIsometry_mulEquiv_statedSp _
    (CFSG.ComponentClassification.OutcomeLocal.dotForm_restrict_isAlt (k := k) (n := 3))
    (CFSG.ComponentClassification.OutcomeLocal.dotForm_restrict_nondegenerate h2)
    (CFSG.ComponentClassification.OutcomeLocal.finrank_dotForm_ker h2)
  have eN : (FourGroupEvenCanonical.matrixIsometryGroup
      ((1 : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)).map (conjAut 3 k) ≃*
      FourGroupEvenCanonical.matrixIsometryGroup
        ((1 : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) :=
    (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, Subgroup.range_subtype])).trans
      (MonoidHom.ofInjective hinj).symm
  exact ⟨(((Subgroup.equivMapOfInjective _ _ (conj_injective hk)).trans
    (MulEquiv.subgroupCongr ((map_conj_autFixed (conj_injective hk) _).trans
      (inf_centralizer_dualAut hk)))).trans eN).trans
    ((CFSG.ComponentClassification.OutcomeLocal.oneRestrictEquiv h2).trans e₂)⟩

theorem card_autFixed_dualAut (hk : Nat.card k = 4) :
    Nat.card (autFixed (dualAut 3 k)) = 60 := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  obtain ⟨e⟩ := nonempty_autFixed_dualAut_equiv hk
  rw [Nat.card_congr e.toEquiv, SymplecticFlag.card_statedSp, hk]
  decide

end Graph

section Classes

variable {k : Type} [Field k] {σ : k ≃+* k}

theorem involution_cases_card (hk : Nat.card k = 4) (hσ : ∀ a, σ a = a ^ 2)
    {α : MulAut (projectiveSL 3 k)} (hα : α * α = 1) :
    α ∈ (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range ∨
      (∃ H : GL (Fin 3) k, α = conjAut 3 k H * fieldAut 3 k σ * (conjAut 3 k H)⁻¹) ∧
        Nat.card (autFixed α) = 168 ∨
      (∃ H : GL (Fin 3) k, α = conjAut 3 k H * dualAut 3 k * (conjAut 3 k H)⁻¹) ∧
        Nat.card (autFixed α) = 60 ∨
      (∃ H : GL (Fin 3) k, α = conjAut 3 k H * betaAut σ * (conjAut 3 k H)⁻¹) ∧
        Nat.card (autFixed α) = 72 := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  rcases involution_cases hk hσ hα with h | ⟨H, h | h | h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨⟨H, h⟩, by rw [h, card_autFixed_conj, card_autFixed_fieldAut hk hσ]⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨⟨H, h⟩,
      by rw [h, card_autFixed_conj, card_autFixed_dualAut hk]⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨⟨H, h⟩,
      by rw [h, card_autFixed_conj, card_autFixed_betaAut hk hσ]⟩))

theorem card_autFixed_of_isField (hk : Nat.card k = 4) {τ : MulAut (projectiveSL 3 k)}
    (h : (stdPinnedPSL 3 k).IsField τ) : Nat.card (autFixed τ) = 168 := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  have hσ : ∀ a, frobeniusEquiv k 2 a = a ^ 2 := fun a => frobeniusEquiv_apply k 2 a
  obtain ⟨φ, ⟨σ', rfl⟩, hφ1, d, -, rfl⟩ := h
  rcases LinearThreeFourOuter.ringEquiv_eq_one_or hσ hk σ' with h1 | h1
  · exact absurd (by rw [h1, map_one]) hφ1
  · rw [card_autFixed_conj, h1, card_autFixed_fieldAut hk hσ]

theorem card_autFixed_of_isGraph (hk : Nat.card k = 4) {τ : MulAut (projectiveSL 3 k)}
    (h : (stdPinnedPSL 3 k).IsGraph τ) : Nat.card (autFixed τ) = 60 := by
  obtain ⟨γ, hγ, -, d, -, rfl⟩ := h
  rw [stdPinnedPSL_graph, Set.mem_singleton_iff] at hγ
  rw [card_autFixed_conj, hγ, card_autFixed_dualAut hk]

theorem card_autFixed_of_isGraphField (hk : Nat.card k = 4) {τ : MulAut (projectiveSL 3 k)}
    (h : (stdPinnedPSL 3 k).IsGraphField τ) : Nat.card (autFixed τ) = 72 := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  have hσ : ∀ a, frobeniusEquiv k 2 a = a ^ 2 := fun a => frobeniusEquiv_apply k 2 a
  obtain ⟨γ, hγ, -, φ, ⟨σ', rfl⟩, hφ1, d, -, rfl⟩ := h
  rw [stdPinnedPSL_graph, Set.mem_singleton_iff] at hγ
  subst hγ
  rcases LinearThreeFourOuter.ringEquiv_eq_one_or hσ hk σ' with h1 | h1
  · exact absurd (by rw [h1, map_one]) hφ1
  · rw [card_autFixed_conj, h1, dualAut_mul_fieldAut]
    exact card_autFixed_betaAut hk hσ

end Classes

section Normalizer

variable {k : Type} [Field k] {σ : k ≃+* k}

theorem card_normalizer_of_card_eq_nine (hk : Nat.card k = 4) {E : Subgroup (projectiveSL 3 k)}
    (hE : Nat.card E = 9) : Nat.card (Subgroup.normalizer (E : Set (projectiveSL 3 k))) = 72 := by
  obtain ⟨g, rfl⟩ := exists_eq_map_conj_eZero hk hE
  rw [← Subgroup.map_equiv_normalizer_eq, Subgroup.card_map_of_injective (MulAut.conj g).injective,
    card_normalizer_eZero hk]

theorem eq_normalizer_of_card_eq (hk : Nat.card k = 4) {H E : Subgroup (projectiveSL 3 k)}
    (hH : Nat.card H = 72) (hE : Nat.card E = 9) (hEH : E ≤ H) :
    H = Subgroup.normalizer (E : Set (projectiveSL 3 k)) := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  have hle : H ≤ Subgroup.normalizer (E : Set (projectiveSL 3 k)) := by
    intro x hx
    set E' := E.map (MulAut.conj x).toMonoidHom with hE'def
    have hE' : Nat.card E' = 9 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj x).injective, hE]
    have hE'H : E' ≤ H := by
      rintro _ ⟨e, he, rfl⟩
      exact H.mul_mem (H.mul_mem hx (hEH he)) (H.inv_mem hx)
    have heq : E' = E := by
      by_contra hne
      have hinf : ∀ y ∈ E, y ∈ E' → y = 1 := by
        intro y hy hy'
        by_contra hy1
        apply hne
        rw [← centralizer_eq_of_card_eq_nine hk hE hy hy1,
          centralizer_eq_of_card_eq_nine hk hE' hy' hy1]
      have hinj : Function.Injective (fun p : E × E' =>
          (⟨p.1 * p.2, H.mul_mem (hEH p.1.2) (hE'H p.2.2)⟩ : H)) := by
        rintro ⟨a, b⟩ ⟨a', b'⟩ hab
        have h1 : (a : projectiveSL 3 k) * b = a' * b' := congrArg Subtype.val hab
        have h2 : (a' : projectiveSL 3 k)⁻¹ * a = b' * (b : projectiveSL 3 k)⁻¹ := by
          calc (a' : projectiveSL 3 k)⁻¹ * a =
                (a' : projectiveSL 3 k)⁻¹ * ((a : projectiveSL 3 k) * b) *
                  (b : projectiveSL 3 k)⁻¹ := by group
            _ = (a' : projectiveSL 3 k)⁻¹ * ((a' : projectiveSL 3 k) * b') *
                  (b : projectiveSL 3 k)⁻¹ := by rw [h1]
            _ = b' * (b : projectiveSL 3 k)⁻¹ := by group
        have h3 := hinf _ (E.mul_mem (E.inv_mem a'.2) a.2)
          (h2 ▸ E'.mul_mem b'.2 (E'.inv_mem b.2))
        have ha : a = a' := Subtype.ext (by
          calc (a : projectiveSL 3 k) = a' * ((a' : projectiveSL 3 k)⁻¹ * a) := by group
            _ = a' := by rw [h3, mul_one])
        subst ha
        have hb : b = b' := Subtype.ext (mul_left_cancel h1)
        rw [hb]
      have := Nat.card_le_card_of_injective _ hinj
      rw [Nat.card_prod, hE, hE', hH] at this
      norm_num at this
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have : x * y * x⁻¹ ∈ E' := ⟨y, hy, rfl⟩
      rwa [heq] at this
    · intro hy
      rw [← heq] at hy
      obtain ⟨z, hz, hzy⟩ := hy
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hzy
      have : z = y := by
        have h := congrArg (fun w => x⁻¹ * w * x) hzy
        simpa [mul_assoc] using h
      rw [← this]
      exact hz
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hH, card_normalizer_of_card_eq_nine hk hE]

theorem autFixed_betaAut (hk : Nat.card k = 4) (hσ : ∀ a, σ a = a ^ 2) :
    autFixed (betaAut σ) = Subgroup.normalizer (eZero k : Set (projectiveSL 3 k)) :=
  eq_normalizer_of_card_eq hk (card_autFixed_betaAut hk hσ) (card_eZero hk)
    fun _ hx => betaAut_fixed hk hσ hx

theorem autFixed_eq_normalizer_of_isGraphField (hk : Nat.card k = 4)
    {τ : MulAut (projectiveSL 3 k)} (h : (stdPinnedPSL 3 k).IsGraphField τ)
    {E : Subgroup (projectiveSL 3 k)} (hE : Nat.card E = 9) (hfix : ∀ e ∈ E, τ e = e) :
    autFixed τ = Subgroup.normalizer (E : Set (projectiveSL 3 k)) :=
  eq_normalizer_of_card_eq hk (card_autFixed_of_isGraphField hk h) hE hfix

end Normalizer

section Kinds

variable {k : Type} [Field k]

theorem isInnerAut_of_conj {G : Type*} [Group G] {d α : MulAut G}
    (h : IsInnerAut (d * α * d⁻¹)) : IsInnerAut α := by
  have := (LinearThreeFourOuter.innerAut_normal G).conj_mem _ h d⁻¹
  rwa [inv_inv, show d⁻¹ * (d * α * d⁻¹) * d = α by group] at this

theorem not_isInnerAut_of_isField (hk : Nat.card k = 4) {τ : MulAut (projectiveSL 3 k)}
    (h : (stdPinnedPSL 3 k).IsField τ) : ¬ IsInnerAut τ := by
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  have := LinearFieldFour.finite_of_card_eq_four hk
  have hσ : ∀ a, frobeniusEquiv k 2 a = a ^ 2 := fun a => frobeniusEquiv_apply k 2 a
  intro hinn
  obtain ⟨φ, ⟨σ', rfl⟩, hφ1, d, -, rfl⟩ := h
  have h0 := isInnerAut_of_conj hinn
  have he : conjAut 3 k 1 * fieldAut 3 k σ' * dualAut 3 k ^ 0 = fieldAut 3 k σ' := by
    rw [map_one, one_mul, pow_zero, mul_one]
  rw [← he] at h0
  obtain ⟨h1, -⟩ := eq_of_conjAut_mul_mem_range hk hσ 1 σ' (by norm_num) h0
  exact hφ1 (by rw [h1, map_one])

theorem not_isInnerAut_of_isGraph (hk : Nat.card k = 4) {τ : MulAut (projectiveSL 3 k)}
    (h : (stdPinnedPSL 3 k).IsGraph τ) : ¬ IsInnerAut τ := by
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  have := LinearFieldFour.finite_of_card_eq_four hk
  have hσ : ∀ a, frobeniusEquiv k 2 a = a ^ 2 := fun a => frobeniusEquiv_apply k 2 a
  intro hinn
  obtain ⟨γ, hγ, -, d, -, rfl⟩ := h
  rw [stdPinnedPSL_graph, Set.mem_singleton_iff] at hγ
  subst hγ
  have h0 := isInnerAut_of_conj hinn
  have he : conjAut 3 k 1 * fieldAut 3 k 1 * dualAut 3 k ^ 1 = dualAut 3 k := by
    rw [map_one, map_one, one_mul, one_mul, pow_one]
  rw [← he] at h0
  obtain ⟨-, h1, -⟩ := eq_of_conjAut_mul_mem_range hk hσ 1 1 le_rfl h0
  exact absurd h1 one_ne_zero

theorem not_isInnerAut_of_isGraphField (hk : Nat.card k = 4) {τ : MulAut (projectiveSL 3 k)}
    (h : (stdPinnedPSL 3 k).IsGraphField τ) : ¬ IsInnerAut τ := by
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  have := LinearFieldFour.finite_of_card_eq_four hk
  have hσ : ∀ a, frobeniusEquiv k 2 a = a ^ 2 := fun a => frobeniusEquiv_apply k 2 a
  intro hinn
  obtain ⟨γ, hγ, -, φ, ⟨σ', rfl⟩, hφ1, d, -, rfl⟩ := h
  rw [stdPinnedPSL_graph, Set.mem_singleton_iff] at hγ
  subst hγ
  have h0 := isInnerAut_of_conj hinn
  have he : conjAut 3 k 1 * fieldAut 3 k σ' * dualAut 3 k ^ 1 =
      dualAut 3 k * fieldAut 3 k σ' := by
    rw [map_one, one_mul, pow_one, dualAut_mul_fieldAut]
  rw [← he] at h0
  obtain ⟨h1, -⟩ := eq_of_conjAut_mul_mem_range hk hσ 1 σ' le_rfl h0
  exact hφ1 (by rw [h1, map_one])

theorem not_isField_and_isGraph (hk : Nat.card k = 4) {τ : MulAut (projectiveSL 3 k)} :
    ¬ ((stdPinnedPSL 3 k).IsField τ ∧ (stdPinnedPSL 3 k).IsGraph τ) := fun h => by
  have := (card_autFixed_of_isField hk h.1).symm.trans (card_autFixed_of_isGraph hk h.2)
  norm_num at this

theorem not_isField_and_isGraphField (hk : Nat.card k = 4) {τ : MulAut (projectiveSL 3 k)} :
    ¬ ((stdPinnedPSL 3 k).IsField τ ∧ (stdPinnedPSL 3 k).IsGraphField τ) := fun h => by
  have := (card_autFixed_of_isField hk h.1).symm.trans (card_autFixed_of_isGraphField hk h.2)
  norm_num at this

theorem not_isGraph_and_isGraphField (hk : Nat.card k = 4) {τ : MulAut (projectiveSL 3 k)} :
    ¬ ((stdPinnedPSL 3 k).IsGraph τ ∧ (stdPinnedPSL 3 k).IsGraphField τ) := fun h => by
  have := (card_autFixed_of_isGraph hk h.1).symm.trans (card_autFixed_of_isGraphField hk h.2)
  norm_num at this

end Kinds

end CFSG.RankThree.PartTwo.KFacts.L34
