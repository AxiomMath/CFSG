module

public import CFSG.LocalAnalysis.StandardType.GGRoundFourSmallBIsoAssembly
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExc
public import CFSG.LocalAnalysis.StandardType.GGTableB

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

open scoped commutatorElement

@[expose] def GGOutComm (R : Type) [Group R] : Prop :=
  ∀ α β : MulAut R, α * β * α⁻¹ * β⁻¹ ∈ (MulAut.conj : R →* MulAut R).range

theorem GGOutComm.of_mulEquiv {R C : Type} [Group R] [Group C] (e : R ≃* C) (h : GGOutComm C) :
    GGOutComm R :=
  commutator_mem_inn_of_mulEquiv e h

theorem GGOutCyclic.ggOutComm {R : Type} [Group R] (h : GGOutCyclic R) : GGOutComm R :=
  commutator_mem_inn_of_outCyclic h

theorem ggOutComm_of_outer_comm {R : Type} [Group R] (h : ∀ x y : Outer R, x * y = y * x) :
    GGOutComm R := by
  intro α β
  change ⁅α, β⁆ ∈ inner R
  rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
    commutatorElement_eq_one_iff_mul_comm]
  exact h _ _

theorem ggOutComm_of_card_outer_prime {R : Type} [Group R] {p : ℕ} (hp : p.Prime)
    (h : Nat.card (Outer R) = p) : GGOutComm R := by
  have : Fact p.Prime := ⟨hp⟩
  have : IsCyclic (Outer R) := isCyclic_of_prime_card h
  exact ggOutComm_of_outer_comm fun x y => (IsCyclic.commGroup.mul_comm x y)

theorem ggOutComm_of_forall_inner_mul {R : Type} [Group R] (C : Set (MulAut R))
    (hC : ∀ c ∈ C, ∀ d ∈ C, c * d = d * c)
    (h : ∀ α : MulAut R, ∃ ι ∈ inner R, ∃ c ∈ C, α = ι * c) : GGOutComm R := by
  have hmk : ∀ α : MulAut R, ∃ c ∈ C,
      (QuotientGroup.mk' (inner R) α) = QuotientGroup.mk' (inner R) c := by
    intro α
    obtain ⟨ι, hι, c, hc, rfl⟩ := h α
    refine ⟨c, hc, ?_⟩
    have h1 : QuotientGroup.mk' (inner R) ι = 1 := (QuotientGroup.eq_one_iff ι).mpr hι
    rw [map_mul, h1, one_mul]
  refine ggOutComm_of_outer_comm fun x y => ?_
  obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective (inner R) x
  obtain ⟨β, rfl⟩ := QuotientGroup.mk'_surjective (inner R) y
  obtain ⟨c, hc, e1⟩ := hmk α
  obtain ⟨d, hd, e2⟩ := hmk β
  rw [e1, e2, ← map_mul, ← map_mul, hC c hc d hd]

theorem ggInndiagCommEq_of_subset_inn {R : Type} [Group R] {I F : Set (MulAut R)}
    (hI : I ⊆ LargeEvenInnSet R) (h : GGOutComm R) : GGInndiagCommEq R I F :=
  ggInndiag_eq_comm_of_subset_inn hI h

theorem largeEvenLabelAll_inndiagComm_of_inn {lab : LargeEvenLabel}
    (hI : LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => I ⊆ LargeEvenInnSet R))
    (hO : LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ _ _ => GGOutComm R)) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard GGInndiagCommEq) :=
  (largeEvenLabelAll_and hI hO).mono fun _ _ _ _ h hs hna =>
    ggInndiagCommEq_of_subset_inn (h.1 hs hna) (h.2 hs hna)

end CFSG.StandardType

end
