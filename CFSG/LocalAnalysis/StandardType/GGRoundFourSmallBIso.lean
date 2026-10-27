module

import CFSG.LocalAnalysis.StandardType.GGTableBF4Basic

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45ConfigIso
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcOut
public import CFSG.LocalAnalysis.ComponentClassification.InnAutDerived

public section

namespace CFSG.StandardType

open CFSG.Assembly

open scoped commutatorElement

section Intrinsic

variable (R : Type) [Group R]

@[expose] def ggInndiagComm : Subgroup (MulAut R) :=
  (MulAut.conj : R →* MulAut R).range ⊔ ⁅(⊤ : Subgroup (MulAut R)), ⊤⁆

variable {R} {R' : Type} [Group R']

theorem range_conj_le_ggInndiagComm : (MulAut.conj : R →* MulAut R).range ≤ ggInndiagComm R :=
  le_sup_left

theorem commutator_mem_ggInndiagComm (α β : MulAut R) : ⁅α, β⁆ ∈ ggInndiagComm R :=
  Subgroup.mem_sup_right (Subgroup.commutator_mem_commutator (Subgroup.mem_top α)
    (Subgroup.mem_top β))

theorem ggCongr_conj_eq (σ : R ≃* R') (r : R) :
    MulAut.congr σ (MulAut.conj r) = MulAut.conj (σ r) := by
  ext s
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem ggInndiagComm_eq_innAutDerived :
    ggInndiagComm R = CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived R :=
  rfl

theorem map_congr_range_conj (σ : R ≃* R') :
    (MulAut.conj : R →* MulAut R).range.map (MulAut.congr σ).toMonoidHom =
      (MulAut.conj : R' →* MulAut R').range :=
  CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr σ

theorem map_congr_ggInndiagComm (σ : R ≃* R') :
    (ggInndiagComm R).map (MulAut.congr σ).toMonoidHom = ggInndiagComm R' :=
  CFSG.ComponentClassification.OuterAutomorphisms.map_innAutDerived_congr σ

theorem mem_ggInndiagComm_congr_iff (σ : R ≃* R') (φ : MulAut R) :
    φ ∈ ggInndiagComm R ↔ MulAut.congr σ φ ∈ ggInndiagComm R' :=
  (CFSG.ComponentClassification.OuterAutomorphisms.mem_innAutDerived_congr σ).symm

theorem ggInndiag_eq_comm_of_subset_inn {I : Set (MulAut R)} (hI : I ⊆ LargeEvenInnSet R)
    (h : ∀ α β : MulAut R, α * β * α⁻¹ * β⁻¹ ∈ (MulAut.conj : R →* MulAut R).range) :
    ggInndiag R I = ggInndiagComm R := by
  rw [ggInndiag_eq_range_of_subset hI]
  refine le_antisymm le_sup_left (sup_le le_rfl ?_)
  rw [Subgroup.commutator_le]
  intro α _ β _
  rw [commutatorElement_def]
  exact h α β

end Intrinsic

@[expose] def GGInndiagCommEq : LargeEvenRawCont :=
  fun R _ I _ => ggInndiag R I = ggInndiagComm R

theorem ggRawInndiagIsoOn_of_comm {S : LargeEvenLabel → Prop}
    (h : ∀ lab, LargeEvenInLambda2 lab → S lab →
      LargeEvenLabelAll lab (LargeEvenSimpleGuard GGInndiagCommEq)) :
    GGRawInndiagIsoOn fun lab lab' => S lab ∧ S lab' := by
  intro lab hlab Q hQ
  by_cases hS : S lab
  · refine largeEvenRawDatum_mono ?_ (h lab hlab hS Q hQ)
    rintro R _ I F ⟨hQ, hEq⟩
    refine ⟨hQ, fun hs hna lab' hlab' hl Q' hQ' => ?_⟩
    refine largeEvenRawDatum_mono ?_ (h lab' hlab' hl.2 Q' hQ')
    rintro R' _ I' F' ⟨hQ', hEq'⟩
    refine ⟨hQ', fun hs' hna' σ φ => ?_⟩
    have e : ggInndiag R I = ggInndiagComm R := hEq hs hna
    have e' : ggInndiag R' I' = ggInndiagComm R' := hEq' hs' hna'
    rw [e, e']
    exact mem_ggInndiagComm_congr_iff σ φ
  · refine largeEvenRawDatum_mono ?_ hQ
    intro R _ I F hQ
    exact ⟨hQ, fun _ _ lab' _ hl => absurd hl.1 hS⟩

theorem ggRawInndiagIsoOn_of_or {S S₁ S₂ : LargeEvenLabel → LargeEvenLabel → Prop}
    (h₁ : GGRawInndiagIsoOn S₁) (h₂ : GGRawInndiagIsoOn S₂)
    (hS : ∀ lab lab', S lab lab' → S₁ lab lab' ∨ S₂ lab lab') : GGRawInndiagIsoOn S := by
  intro lab hlab Q hQ
  have h2 := h₂ lab hlab _ (h₁ lab hlab Q hQ)
  refine largeEvenRawDatum_mono ?_ h2
  rintro R _ I F ⟨⟨hQ, hS₁⟩, hS₂⟩
  refine ⟨hQ, fun hs hna lab' hlab' hl => ?_⟩
  rcases hS lab lab' hl with hl | hl
  · exact hS₁ hs hna lab' hlab' hl
  · exact hS₂ hs hna lab' hlab' hl

section ExcOut

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem ggInndiagCommEq_chev (τ : Tag) {K : Type} [Field K] [Finite K]
    (hI : LargeEvenChevIDImage τ.cartan K (LargeEvenChevH τ.cartan K false) ⊆
      LargeEvenInnSet (LargeEvenCenterQuot (LargeEvenChevH τ.cartan K false)))
    (h : ∀ α β : MulAut (adjointGroup τ K),
      α * β * α⁻¹ * β⁻¹ ∈ (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range) :
    GGInndiagCommEq (LargeEvenCenterQuot (LargeEvenChevH τ.cartan K false))
      (LargeEvenChevIDImage τ.cartan K _) (LargeEvenChevFieldImage τ.cartan K _) :=
  ggInndiag_eq_comm_of_subset_inn hI (commutator_mem_inn_of_mulEquiv (recipeChevEquiv τ K) h)

theorem largeEvenLabelAll_inndiagComm_excOut {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGRecipeExcOutLabel lab) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard GGInndiagCommEq) := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, hl⟩ := hlab
  intro Q hQ
  rcases h with ht | ht | ht | ht <;> dsimp only at ht <;> subst ht
  · obtain ⟨-, hn2⟩ := hl
    exact recipeChevalley_and (P := LargeEvenSimpleGuard GGInndiagCommEq)
      (fun K _ _ hK _ _ => ggInndiagCommEq_chev .G2
        (chevIDImage_subset_inn_of_top (τ := .G2) (TableB.torusSubgroup_eq_top_of_mul_eq_smul _ K
          TableB.cartanG2_inv fun s => ⟨s, pow_one s⟩))
        (commutator_mem_inn_G2 hn2 K hK)) hQ
  · exact recipeChevalley_and (P := LargeEvenSimpleGuard GGInndiagCommEq)
      (fun K _ _ hK _ _ => ggInndiagCommEq_chev .F4
        (chevIDImage_subset_inn_of_top (τ := .F4) (TableB.torusSubgroup_eq_top_of_mul_eq_smul _ K
          TableB.cartanF4_inv fun s => ⟨s, pow_one s⟩))
        (commutator_mem_inn_F4 hn K hK)) hQ
  · exact recipeChevalley_and (P := LargeEvenSimpleGuard GGInndiagCommEq)
      (fun K _ _ hK _ _ => by
        have := charP_two_of_card hK
        exact ggInndiagCommEq_chev .E7
          (chevIDImage_subset_inn_of_top (τ := .E7) (TableB.torusSubgroup_eq_top_of_mul_eq_smul _ K
            TableB.cartanE7_adj (TableB.exists_sq_eq_of_charTwo K)))
          (commutator_mem_inn_E7_E8 hn K hK .E7 (Or.inl rfl))) hQ
  · exact recipeChevalley_and (P := LargeEvenSimpleGuard GGInndiagCommEq)
      (fun K _ _ hK _ _ => ggInndiagCommEq_chev .E8
        (chevIDImage_subset_inn_of_top (τ := .E8) (TableB.torusSubgroup_eq_top_of_mul_eq_smul _ K
          TableB.cartanE8_inv fun s => ⟨s, pow_one s⟩))
        (commutator_mem_inn_E7_E8 hn K hK .E8 (Or.inr rfl))) hQ

end ExcOut

section F4WeakRawFive


theorem ggRawFiveInnerDiagOn_F4
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (hF4 : lab.tag = .F4) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ =>
      ∀ a ∈ I, orderOf a = 5 → a ∈ ggInndiagComm R) := by
  obtain ⟨t, l, n⟩ := lab
  subst hF4
  intro Q hQ
  exact recipeChevalley_and (fun K _ _ _ _ _ a ha _ =>
    range_conj_le_ggInndiagComm (TableBF4.idImage_subset_inn K ha)) hQ

end F4WeakRawFive


end CFSG.StandardType

end
