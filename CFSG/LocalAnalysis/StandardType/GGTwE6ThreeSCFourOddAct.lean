module

public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeSCFourOddGroup


public section

namespace CFSG.StandardType.SCFourOdd

theorem exists_quotient_action {L' : Type} [Group L'] {K₂ : Subgroup L'} [K₂.Normal]
    (A : Subgroup (MulAut L')) (hA : ∀ a ∈ A, ∀ z ∈ K₂, a z ∈ K₂) :
    ∃ Φ : A →* MulAut (L' ⧸ K₂),
      ∀ (a : A) (l : L'), Φ a (l : L' ⧸ K₂) = (((a : MulAut L') l : L') : L' ⧸ K₂) := by
  have hEq : ∀ a : A, Subgroup.map ((a : MulAut L') : L' →* L') K₂ = K₂ := by
    intro a
    refine le_antisymm ?_ ?_
    · intro z hz
      rw [Subgroup.mem_map] at hz
      obtain ⟨y, hy, hyz⟩ := hz
      rw [← hyz]
      exact hA a a.2 y hy
    · intro z hz
      rw [Subgroup.mem_map]
      refine ⟨(a : MulAut L')⁻¹ z, ?_, ?_⟩
      · simpa using hA a⁻¹ a⁻¹.2 z hz
      · simp
  let Φ : A →* MulAut (L' ⧸ K₂) :=
    { toFun := fun a => QuotientGroup.congr K₂ K₂ (a : L' ≃* L') (hEq a)
      map_one' := by
        ext x
        obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
        rw [QuotientGroup.congr_mk]
        rfl
      map_mul' := fun a b => by
        ext x
        obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
        simp only [QuotientGroup.congr_mk, MulAut.mul_apply, Subgroup.coe_mul] }
  exact ⟨Φ, fun a l => QuotientGroup.congr_mk K₂ K₂ (a : L' ≃* L') (hEq a) l⟩

theorem injective_of_quotient_action {L' : Type} [Group L'] (hL : commutator L' = ⊤)
    {K₂ : Subgroup L'} [K₂.Normal] (hK : K₂ ≤ Subgroup.center L') (A : Subgroup (MulAut L'))
    (Φ : A →* MulAut (L' ⧸ K₂))
    (hΦ : ∀ (a : A) (l : L'), Φ a (l : L' ⧸ K₂) = (((a : MulAut L') l : L') : L' ⧸ K₂)) :
    Function.Injective Φ := by
  rw [injective_iff_map_eq_one]
  intro a ha
  refine Subtype.ext (aut_eq_one_of_central hL hK (a : MulAut L') ?_)
  intro l
  rw [← QuotientGroup.eq]
  have h1 : (((a : MulAut L') l : L') : L' ⧸ K₂) = (l : L' ⧸ K₂) := by
    rw [← hΦ a l, ha]
    rfl
  exact h1.symm

end CFSG.StandardType.SCFourOdd
