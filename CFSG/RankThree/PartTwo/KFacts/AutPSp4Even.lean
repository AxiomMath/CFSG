module

public import CFSG.RankThree.PartTwo.KFacts.AutPSpFaithful
public import CFSG.RankThree.PartTwo.KFacts.AutKindsSep
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveTauGrp
import CFSG.LocalAnalysis.ComponentInitial.SymplecticPerfectCoverOuterPrime
import CFSG.LocalAnalysis.ComponentInitial.ScalarSemilinearNormalizer
public import CFSG.RankThree.PartTwo.KFacts.AutPSp

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.QuasithinUnique.Lin2.Five (tauSp coe_tauSp tauAut tauAut_proj tauAut_not_mem_E)

variable {F : Type} [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
theorem tauSp_fieldSp (σ : F ≃+* F) (g : StatedSp 2 F) :
    tauSp (fieldSp 2 F σ g) = fieldSp 2 F σ (tauSp g) := by
  apply CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.statedSp_ext
  rw [coe_tauSp, coe_fieldSp, coe_fieldSp, coe_tauSp]
  ext r c
  simp only [CFSG.QuasithinUnique.Lin2.Five.tauMat_apply, Matrix.map_apply, map_sub, map_mul]

theorem tauAut_mul_fieldAut (σ : F ≃+* F) :
    tauAut * fieldAut 2 F σ = fieldAut 2 F σ * tauAut := by
  ext x
  obtain ⟨g, rfl⟩ := proj_surjective x
  rw [MulAut.mul_apply, fieldAut_proj, tauAut_proj, MulAut.mul_apply, tauAut_proj, fieldAut_proj,
    tauSp_fieldSp]

theorem conjAut_mem_inner_of_charTwo (A : gsp 2 F) :
    IsInnerAut (conjAut 2 F A) := by
  have : Fintype F := Fintype.ofFinite F
  exact conjAut_mem_inner_of_isSquare
    (FiniteField.isSquare_of_char_two (ringChar.eq F 2) (multiplier 2 F A : F))

theorem exists_eq_conjAut_mul_fieldAut_mul_tauAut_pow
    (α : MulAut (StatedProj (StatedSp 2 F))) :
    ∃ (A : gsp 2 F) (σ : F ≃+* F) (ε : ℕ), ε ≤ 1 ∧
      α = conjAut 2 F A * fieldAut 2 F σ * tauAut ^ ε := by
  obtain ⟨-, -, -, hindex⟩ :=
    CFSG.ComponentClassification.CatalogueBSymplecticTwo.kernel_generation (K := F)
  have hτ : (tauAut : MulAut (StatedProj (StatedSp 2 F))) ∉ spSemilinearAutGroup 2 F :=
    tauAut_not_mem_E
  have hidx : (spSemilinearAutGroup 2 F).index = 2 := by
    have h1 : (spSemilinearAutGroup 2 F).index ≠ 1 := by
      rw [Ne, Subgroup.index_eq_one]
      intro htop
      exact hτ (htop ▸ Subgroup.mem_top _)
    have h0 : (spSemilinearAutGroup 2 F).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  by_cases hα : α ∈ spSemilinearAutGroup 2 F
  · obtain ⟨A, σ, rfl⟩ := mem_spSemilinearAutGroup_iff.mp hα
    exact ⟨A, σ, 0, zero_le_one, by rw [pow_zero, mul_one]⟩
  · have h2 : α * tauAut⁻¹ ∈ spSemilinearAutGroup 2 F := by
      rw [Subgroup.mul_mem_iff_of_index_two hidx]
      exact iff_of_false hα fun h => hτ (by simpa using inv_mem h)
    obtain ⟨A, σ, hAσ⟩ := mem_spSemilinearAutGroup_iff.mp h2
    exact ⟨A, σ, 1, le_rfl, by rw [pow_one, ← hAσ, inv_mul_cancel_right]⟩

variable (F) in
@[expose] noncomputable def stdPinnedPSp4Even : PinnedAut (StatedProj (StatedSp 2 F)) where
  inndiag := (conjAut 2 F).range
  inn_le := innAut_le_range_spConjAut 2 F
  field := (fieldAut 2 F).range
  graph := {tauAut}

theorem stdPinnedPSp4Even_graph : (stdPinnedPSp4Even F).graph = {tauAut} :=
  rfl

theorem conj_eq_of_mem_fieldGraph (A : gsp 2 F) (ρ : F ≃+* F) (ε : ℕ)
    {X : MulAut (StatedProj (StatedSp 2 F))}
    (hX : X ∈ Subgroup.closure (Set.range (fieldAut 2 F) ∪ {tauAut})) :
    conjAut 2 F A * fieldAut 2 F ρ * tauAut ^ ε * X * (conjAut 2 F A * fieldAut 2 F ρ *
      tauAut ^ ε)⁻¹ = conjAut 2 F A * X * (conjAut 2 F A)⁻¹ := by
  have hgen : (Set.range (fieldAut 2 F) ∪ {tauAut}).Pairwise Commute := by
    rintro a (⟨σ, rfl⟩ | rfl) b (⟨τ, rfl⟩ | rfl) -
    · change fieldAut 2 F σ * fieldAut 2 F τ = fieldAut 2 F τ * fieldAut 2 F σ
      rw [← map_mul, ← map_mul, CFSG.LocalAnalysis.ComponentInitial.ringAut_mul_comm F σ τ]
    · exact (tauAut_mul_fieldAut σ).symm
    · exact tauAut_mul_fieldAut τ
    · exact Commute.refl _
  have hcomm := Subgroup.isMulCommutative_closure hgen
  have hρmem : fieldAut 2 F ρ ∈ Subgroup.closure (Set.range (fieldAut 2 F) ∪ {tauAut}) :=
    Subgroup.subset_closure (Set.mem_union_left _ ⟨ρ, rfl⟩)
  have hτmem : (tauAut : MulAut (StatedProj (StatedSp 2 F))) ∈
      Subgroup.closure (Set.range (fieldAut 2 F) ∪ {tauAut}) :=
    Subgroup.subset_closure (Set.mem_union_right _ rfl)
  have hr : fieldAut 2 F ρ * tauAut ^ ε ∈
      Subgroup.closure (Set.range (fieldAut 2 F) ∪ {tauAut}) :=
    mul_mem hρmem (pow_mem hτmem ε)
  have h := congrArg Subtype.val (hcomm.is_comm.comm (⟨_, hr⟩ :
    Subgroup.closure (Set.range (fieldAut 2 F) ∪ {tauAut})) ⟨X, hX⟩)
  change fieldAut 2 F ρ * tauAut ^ ε * X = X * (fieldAut 2 F ρ * tauAut ^ ε) at h
  calc conjAut 2 F A * fieldAut 2 F ρ * tauAut ^ ε * X *
        (conjAut 2 F A * fieldAut 2 F ρ * tauAut ^ ε)⁻¹ =
      conjAut 2 F A * (fieldAut 2 F ρ * tauAut ^ ε * X) * (fieldAut 2 F ρ * tauAut ^ ε)⁻¹ *
        (conjAut 2 F A)⁻¹ := by group
    _ = conjAut 2 F A * X * (conjAut 2 F A)⁻¹ := by rw [h]; group

theorem range_conjAut_normal_of_charTwo :
    ((conjAut 2 F).range : Subgroup (MulAut (StatedProj (StatedSp 2 F)))).Normal := by
  refine ⟨fun d hd α => ?_⟩
  obtain ⟨B, rfl⟩ := hd
  obtain ⟨y, hy⟩ := conjAut_mem_inner_of_charTwo B
  rw [← hy, mul_mulAutConj_mul_inv]
  exact innAut_le_range_spConjAut 2 F ⟨α y, rfl⟩

theorem stdPinnedPSp4Even_stable : (stdPinnedPSp4Even F).Stable := by
  have hmemσ : ∀ σ : F ≃+* F, fieldAut 2 F σ ∈
      Subgroup.closure (Set.range (fieldAut 2 F) ∪ {tauAut}) := fun σ =>
    Subgroup.subset_closure (Or.inl ⟨σ, rfl⟩)
  have hmemτ : (tauAut : MulAut (StatedProj (StatedSp 2 F))) ∈
      Subgroup.closure (Set.range (fieldAut 2 F) ∪ {tauAut}) :=
    Subgroup.subset_closure (Or.inr rfl)
  refine ⟨range_conjAut_normal_of_charTwo, ?_, ?_, ?_⟩
  · rintro α _ ⟨σ, rfl⟩ h1
    obtain ⟨A, ρ, ε, -, rfl⟩ := exists_eq_conjAut_mul_fieldAut_mul_tauAut_pow α
    exact ⟨fieldAut 2 F σ, ⟨σ, rfl⟩, h1, conjAut 2 F A, ⟨A, rfl⟩,
      conj_eq_of_mem_fieldGraph A ρ ε (hmemσ σ)⟩
  · rintro α γ hγ h1
    rw [stdPinnedPSp4Even_graph, Set.mem_singleton_iff] at hγ
    subst hγ
    obtain ⟨A, ρ, ε, -, rfl⟩ := exists_eq_conjAut_mul_fieldAut_mul_tauAut_pow α
    exact ⟨tauAut, rfl, h1, conjAut 2 F A, ⟨A, rfl⟩, conj_eq_of_mem_fieldGraph A ρ ε hmemτ⟩
  · rintro α γ _ hγ hγ1 ⟨σ, rfl⟩ hφ1
    rw [stdPinnedPSp4Even_graph, Set.mem_singleton_iff] at hγ
    subst hγ
    obtain ⟨A, ρ, ε, -, rfl⟩ := exists_eq_conjAut_mul_fieldAut_mul_tauAut_pow α
    exact ⟨tauAut, rfl, hγ1, fieldAut 2 F σ, ⟨σ, rfl⟩, hφ1, conjAut 2 F A, ⟨A, rfl⟩,
      conj_eq_of_mem_fieldGraph A ρ ε (mul_mem hmemτ (hmemσ σ))⟩

theorem stdPinnedPSp4Even_separated : (stdPinnedPSp4Even F).Separated := by
  have hnorm := (range_conjAut_normal_of_charTwo (F := F)).conj_mem
  have hinter : ∀ φ ∈ (stdPinnedPSp4Even F).field, φ ∈ (stdPinnedPSp4Even F).inndiag →
      φ = 1 := by
    rintro _ ⟨σ, rfl⟩ hmem
    rw [(fieldAut_mem_range_conjAut_iff (by norm_num)).mp hmem, map_one]
  refine ⟨?_, ?_, hinter, ?_, ?_⟩
  · rintro _ ⟨σ, rfl⟩ _ ⟨B, rfl⟩
    exact ⟨_, (fieldAut_mul_conjAut_mul_inv σ B).symm⟩
  · intro γ _ d hd
    exact hnorm d hd γ
  · intro γ hγ _ d hd _ ⟨σ, hσ⟩ heq
    rw [stdPinnedPSp4Even_graph, Set.mem_singleton_iff] at hγ
    subst hγ
    apply tauAut_not_mem_E (F := F)
    rw [heq, ← hσ]
    obtain ⟨A, rfl⟩ := hd
    exact mul_mem (spLinearAutGroup_le_spSemilinearAutGroup (conjAut_mem_spLinearAutGroup A))
      (fieldAut_mem_spSemilinearAutGroup σ)
  · intro γ hγ γ' hγ' φ hφ hφ1 d hd heq
    rw [stdPinnedPSp4Even_graph, Set.mem_singleton_iff] at hγ hγ'
    subst hγ
    subst hγ'
    refine hφ1 (hinter φ hφ ?_)
    have hφ' : φ = tauAut⁻¹ * d⁻¹ * tauAut⁻¹⁻¹ := by
      calc φ = (d * tauAut)⁻¹ * (d * (tauAut * φ)) := by group
        _ = (d * tauAut)⁻¹ * tauAut := by rw [← heq]
        _ = tauAut⁻¹ * d⁻¹ * tauAut⁻¹⁻¹ := by group
    rw [hφ']
    exact hnorm _ (inv_mem hd) _

section Induced

variable {G : Type*} [Group G] [Finite G] (L : Subgroup G)

variable (F) in
@[expose] def InducesKindPSp4Even (x : G) (k : AutKind) : Prop :=
  ∃ e : L ⧸ aschbacherSolvableCore 3 L ≃* StatedProj (StatedSp 2 F),
    InducesKind L (stdPinnedPSp4Even F) e x k

theorem inducesKindPSp4Even_iff (e : L ⧸ aschbacherSolvableCore 3 L ≃* StatedProj (StatedSp 2 F))
    (x : G) (k : AutKind) :
    InducesKindPSp4Even F L x k ↔ InducesKind L (stdPinnedPSp4Even F) e x k := by
  constructor
  · rintro ⟨e', h⟩
    exact (inducesKind_iff_of_stable L stdPinnedPSp4Even_stable e' e x k).1 h
  · intro h
    exact ⟨e, h⟩

theorem inducesKindPSp4Even_unique {x : G} {k₁ k₂ : AutKind}
    (h₁ : InducesKindPSp4Even F L x k₁) (h₂ : InducesKindPSp4Even F L x k₂) : k₁ = k₂ := by
  obtain ⟨e, h₁⟩ := h₁
  exact InducesKind.unique L stdPinnedPSp4Even_separated h₁
    ((inducesKindPSp4Even_iff L e x k₂).mp h₂)

end Induced

end CFSG.RankThree.PartTwo.KFacts
