module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45KGForms
public import CFSG.LocalAnalysis.StandardType.MarkingChevalley
public import CFSG.LieType.Steinberg.Adjoint.Perfect

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley

section Mark

theorem gff_isQuasisimple_adjoint {τ : Tag} (hτ : τ = .F4 ∨ τ = .E8) (k : Type) [Field k] :
    CFSG.IsQuasisimple ↥(adjointGroup τ k) := by
  rcases hτ with rfl | rfl
  · exact CFSG.LieType.Steinberg.Adjoint.isQuasisimple_f4 k
  · exact CFSG.LieType.Steinberg.Adjoint.isQuasisimple_e8 k

private theorem gff_nonabelian_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : ∃ a b : A, a * b ≠ b * a) : ∃ a b : B, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := h
  exact ⟨e a, e b, fun h' => hab (e.injective (by rw [map_mul, map_mul, h']))⟩

theorem gff_marking_adjoint {τ : Tag} (hτ : τ = .F4 ∨ τ = .E8) {k : Type} [Field k] [Finite k]
    {m : ℕ} (hm : 1 ≤ m) (hk : Nat.card k = 2 ^ m) :
    LargeEvenMarking ↥(adjointGroup τ k) fun lab _ _ _ _ _ => GGL45TorsionTag lab := by
  have hq := gff_isQuasisimple_adjoint hτ k
  obtain ⟨eR⟩ := centerQuot_chevGroup_equiv k τ
  have hsimple : IsSimpleGroup (LargeEvenCenterQuot (LargeEvenChevH τ.cartan k false)) := by
    have := hq.2.1
    exact eR.isSimpleGroup
  have hnab : ∃ a b : LargeEvenCenterQuot (LargeEvenChevH τ.cartan k false),
      a * b ≠ b * a := gff_nonabelian_of_mulEquiv eR.symm hq.2.2
  have hcomm : commutator ↥(adjointGroup τ k) = ⊤ := hq.1.commutator_eq_top
  rcases hτ with rfl | rfl
  · have hraw : LargeEvenRecipeChevalley LargeEvenCartanF4 (2 ^ m) false
        fun R _ I F => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
          ∃ θ : ↥(adjointGroup .F4 k) ⧸ Subgroup.center ↥(adjointGroup .F4 k) ≃* R,
            GGL45TorsionTag (⟨.F4, 0, m⟩ : LargeEvenLabel) :=
      ⟨k, inferInstance, inferInstance, hk, hsimple, hnab, eR.symm, Or.inr (Or.inl rfl)⟩
    exact ⟨hcomm, ⟨.F4, 0, m⟩, ⟨hm, rfl⟩, hraw⟩
  · have hraw : LargeEvenRecipeChevalley (LargeEvenCartanE 8) (2 ^ m) false
        fun R _ I F => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
          ∃ θ : ↥(adjointGroup .E8 k) ⧸ Subgroup.center ↥(adjointGroup .E8 k) ≃* R,
            GGL45TorsionTag (⟨.E8, 0, m⟩ : LargeEvenLabel) :=
      ⟨k, inferInstance, inferInstance, hk, hsimple, hnab, eR.symm, Or.inl rfl⟩
    exact ⟨hcomm, ⟨.E8, 0, m⟩, ⟨hm, rfl⟩, hraw⟩

end Mark

end CFSG.StandardType
