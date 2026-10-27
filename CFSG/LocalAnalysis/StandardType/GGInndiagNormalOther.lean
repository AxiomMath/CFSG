module

public import CFSG.LocalAnalysis.StandardType.GGSixStepOneOutdiagLinear
public import CFSG.LocalAnalysis.StandardType.MarkingSmall
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open scoped commutatorElement

section OuterComm

variable {R : Type} [Group R]

theorem ggInndiagNormal_of_commutator_mem
    (h : ∀ α β : MulAut R, ⁅α, β⁆ ∈ (MulAut.conj : R →* MulAut R).range) (I : Set (MulAut R)) :
    GGInndiagNormal R I := by
  intro α φ hφ
  have e : α * φ * α⁻¹ = ⁅α, φ⁆ * φ := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact Subgroup.mul_mem _ (inn_le_ggInndiag (h α φ)) (subset_ggInndiag hφ)

theorem GGOutCyclic.ggInndiagNormal (h : GGOutCyclic R) (I : Set (MulAut R)) :
    GGInndiagNormal R I :=
  ggInndiagNormal_of_commutator_mem (fun α β =>
    (h.ggOutdiagCyclic Set.univ).commutator_mem (subset_ggInndiag (Set.mem_univ α))
      (subset_ggInndiag (Set.mem_univ β))) I

theorem ggInndiagNormal_of_outer_comm (h : ∀ x y : Outer R, x * y = y * x)
    (I : Set (MulAut R)) : GGInndiagNormal R I := by
  refine ggInndiagNormal_of_commutator_mem (fun α β => ?_) I
  change ⁅α, β⁆ ∈ inner R
  rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
    commutatorElement_eq_one_iff_mul_comm]
  exact h _ _

theorem ggInndiagNormal_of_mulEquiv_alternatingSix (e : R ≃* alternatingGroup (Fin 6))
    (I : Set (MulAut R)) : GGInndiagNormal R I := by
  refine ggInndiagNormal_of_outer_comm (fun x y => ?_) I
  apply (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).injective
  rw [map_mul, map_mul]
  exact (CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.outer_commutative
    ).is_comm.comm _ _

end OuterComm

section ChevInner

variable {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ} {K : Type} [Field K]

theorem chevIDImage_subset_inn {H : Subgroup (LargeEvenChevGL A K)}
    (hH : ∀ a : Fin r → Kˣ, (∀ h ∈ H, TableB.diagHom A K a * h * (TableB.diagHom A K a)⁻¹ ∈ H) →
      TableB.diagHom A K a ∈ H) :
    LargeEvenChevIDImage A K H ⊆
      (MulAut.conj : LargeEvenCenterQuot H →* MulAut (LargeEvenCenterQuot H)).range := by
  intro φ hφ
  have hle : Subgroup.closure (LargeEvenInnSet _ ∪ LargeEvenChevDiagImage A K H) ≤
      (MulAut.conj : LargeEvenCenterQuot H →* MulAut (LargeEvenCenterQuot H)).range := by
    rw [Subgroup.closure_le]
    refine Set.union_subset ?_ ?_
    · rintro _ ⟨x, rfl⟩
      exact ⟨x, rfl⟩
    · intro ψ hψ
      obtain ⟨a, ha⟩ := TableB.exists_isDiagOf hψ
      rw [TableB.isDiagOf_eq_conj ha (hH a ha.1)]
      exact ⟨_, rfl⟩
  exact hle hφ

theorem chevIDImage_subset_inn_of_subsingleton [Subsingleton Kˣ]
    (H : Subgroup (LargeEvenChevGL A K)) :
    LargeEvenChevIDImage A K H ⊆
      (MulAut.conj : LargeEvenCenterQuot H →* MulAut (LargeEvenCenterQuot H)).range :=
  chevIDImage_subset_inn fun a _ => by
    rw [Subsingleton.elim a 1, map_one]
    exact H.one_mem

theorem chevIDImage_subset_inn_of_top
    {τ : CFSG.Blueprint.Chevalley.Tag} (hT : TableB.torusSubgroup τ.cartan K = ⊤) :
    LargeEvenChevIDImage τ.cartan K (LargeEvenChevH τ.cartan K false) ⊆
      (MulAut.conj : LargeEvenCenterQuot (LargeEvenChevH τ.cartan K false) →*
        MulAut (LargeEvenCenterQuot (LargeEvenChevH τ.cartan K false))).range :=
  chevIDImage_subset_inn fun a _ =>
    TableB.diagHom_mem_of_mem_torusSubgroup τ K (by rw [hT]; exact Subgroup.mem_top a)

end ChevInner

section Labels

theorem recipeChevalley_inndiag {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ} {q : ℕ} {derived : Bool}
    {Q : LargeEvenRawCont}
    (hA : ∀ (K : Type) [Field K] [Finite K], Nat.card K = q →
      GGInndiagNormal (LargeEvenCenterQuot (LargeEvenChevH A K derived))
        (LargeEvenChevIDImage A K (LargeEvenChevH A K derived)))
    (h : LargeEvenRecipeChevalley A q derived Q) :
    LargeEvenRecipeChevalley A q derived fun R _ I F =>
      Q R I F ∧ LargeEvenSimpleGuard (fun R _ I _ => GGInndiagNormal R I) R I F := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, hQ, fun _ _ => hA K hK⟩

theorem recipeB2der_inndiag {Q : LargeEvenRawCont} (h : LargeEvenRecipeSymplectic 2 2 true Q) :
    LargeEvenRecipeSymplectic 2 2 true fun R _ I F =>
      Q R I F ∧ LargeEvenSimpleGuard (fun R _ I _ => GGInndiagNormal R I) R I F := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  obtain ⟨e⟩ := nonempty_b2der_equiv_alternatingGroup hK
  exact ⟨K, inferInstance, inferInstance, hK, hQ,
    fun _ _ => ggInndiagNormal_of_mulEquiv_alternatingSix e _⟩

@[expose] def GGInndiagExcLabel (lab : LargeEvenLabel) : Prop :=
  lab.tag = .G2 ∨ lab.tag = .F4 ∨ lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .triD4 ∨
    lab.tag = .twF4 ∨ lab.tag = .G2der ∨ lab.tag = .twF4der ∨ lab.tag = .B2der


theorem largeEvenLabelAll_inndiag_exc {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : GGInndiagExcLabel lab) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => GGInndiagNormal R I) := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, hl⟩ := hlab
  intro Q hQ
  rcases h with h | h | h | h | h | h | h | h | h <;> dsimp only at h <;> subst h
  · exact recipeChevalley_inndiag (fun K _ _ _ => ggInndiagNormal_of_subset_inn
      (chevIDImage_subset_inn_of_top (τ := .G2) (TableB.torusSubgroup_eq_top_of_mul_eq_smul _ K
        TableB.cartanG2_inv fun s => ⟨s, pow_one s⟩))) hQ
  · exact recipeChevalley_inndiag (fun K _ _ _ => ggInndiagNormal_of_subset_inn
      (chevIDImage_subset_inn_of_top (τ := .F4) (TableB.torusSubgroup_eq_top_of_mul_eq_smul _ K
        TableB.cartanF4_inv fun s => ⟨s, pow_one s⟩))) hQ
  · exact recipeChevalley_inndiag (fun K _ _ hK => by
      have := charP_two_of_card hK
      exact ggInndiagNormal_of_subset_inn
        (chevIDImage_subset_inn_of_top (τ := .E7) (TableB.torusSubgroup_eq_top_of_mul_eq_smul _ K
          TableB.cartanE7_adj (TableB.exists_sq_eq_of_charTwo K)))) hQ
  · exact recipeChevalley_inndiag (fun K _ _ _ => ggInndiagNormal_of_subset_inn
      (chevIDImage_subset_inn_of_top (τ := .E8) (TableB.torusSubgroup_eq_top_of_mul_eq_smul _ K
        TableB.cartanE8_inv fun s => ⟨s, pow_one s⟩))) hQ
  · exact recipeTwisted_and (P := LargeEvenSimpleGuard fun R _ I _ => GGInndiagNormal R I)
      (fun K _ _ hK _ _ => (ggOutCyclic_triD4 hn K hK).ggInndiagNormal _) hQ
  · obtain ⟨-, -, h3⟩ := hl
    exact recipeTwF4_and (P := LargeEvenSimpleGuard fun R _ I _ => GGInndiagNormal R I)
      (fun K _ _ hK _ _ => (ggOutCyclic_twF4 (by omega) K hK).ggInndiagNormal _) hQ
  · exact recipeChevalley_inndiag (fun K _ _ hK => by
      have := CFSG.Monster.Existence.Compat.subsingleton_units_of_card_two hK
      exact ggInndiagNormal_of_subset_inn (chevIDImage_subset_inn_of_subsingleton _)) hQ
  · obtain ⟨-, hn1⟩ := hl
    subst hn1
    exact recipeTwF4_and (P := LargeEvenSimpleGuard fun R _ I _ => GGInndiagNormal R I)
      (fun K _ _ hK _ _ => by
        have := CFSG.Monster.Existence.Compat.subsingleton_units_of_card_two
          (K := K) (by simpa using hK)
        exact ggInndiagNormal_of_subset_inn (chevIDImage_subset_inn_of_subsingleton _)) hQ
  · exact recipeB2der_inndiag hQ

end Labels

end CFSG.StandardType
