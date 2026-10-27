module

public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.Quasithin.Background.E2Three

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B2F

namespace R3c21

open E2

variable {G : Type} [Group G] [Finite G]

section Stage1aAux

omit [Finite G] in
theorem autI_le_normalizer_autI_of_le_normalizer {V A B : Subgroup G} (hV : IsElemAbelian 2 V)
    (hAB : A ≤ Subgroup.normalizer (B : Set G)) :
    autI hV A ≤ Subgroup.normalizer (autI hV B : Set (MulAut (IntMod V hV))) := by
  have key : ∀ a : Subgroup.normalizer (V : Set G), (a : G) ∈ A → ∀ ψ ∈ autI hV B,
      convI hV a * ψ * (convI hV a)⁻¹ ∈ autI hV B := by
    intro a ha ψ hψ
    obtain ⟨b, hb, rfl⟩ := (mem_autI hV).1 hψ
    refine (mem_autI hV).2 ⟨a * b * a⁻¹, ?_, by simp only [map_mul, map_inv]⟩
    have h := (Subgroup.mem_normalizer_iff.1 (hAB ha) (b : G)).1 hb
    simpa using h
  intro φ hφ
  obtain ⟨a, ha, rfl⟩ := (mem_autI hV).1 hφ
  refine B6.mem_normalizer_of_forall_mem (fun ψ hψ => key a ha ψ hψ) fun ψ hψ => ?_
  have h := key a⁻¹ (by simpa using ha) ψ hψ
  simpa using h

theorem twoResidual_autI_le_autI_twoResidual {V P : Subgroup G} (hV : IsElemAbelian 2 V) :
    twoResidual (autI hV P) ≤ autI hV (twoResidual P) := by
  refine twoResidual_le_of_isTwoQuotient (autI_mono hV (twoResidual_le P))
    (autI_le_normalizer_autI_of_le_normalizer hV (le_normalizer_twoResidual P)) ?_
  intro y hy
  obtain ⟨g, hgP, rfl⟩ := (mem_autI hV).1 hy
  obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient P (g : G) hgP
  exact ⟨k, (mem_autI hV).2 ⟨g ^ 2 ^ k, by simpa using hk, map_pow _ _ _⟩⟩

theorem isPerfect_of_isL2Natural {W : Type*} [CommGroup W] {L : Subgroup (MulAut W)}
    {C : Subgroup W} {n : ℕ} (h : IsL2Natural L C n) (hn : 2 ≤ n) : Group.IsPerfect ↥L := by
  obtain ⟨-, F, _, _, hF, e, -⟩ := h
  have h4 : 4 ≤ (Finset.univ : Finset F).card := by
    rw [Finset.card_univ, hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq h4
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) :=
    CFSG.LinearGroups.special_linear_dimension_two_perfect ⟨s, hs⟩
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

end Stage1aAux

end R3c21

end CFSG.Quasithin
