module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.RankThree.PartOne.K133H

theorem exists_conj_le_of_sylow {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Y H A : Subgroup G} (hHY : H ≤ Y) (hAY : A ≤ Y) (hApow : ∀ x ∈ A, x ^ p = 1)
    (hord : (Nat.card Y).factorization p = (Nat.card H).factorization p) :
    ∃ g ∈ Y, A.map (MulAut.conj g).toMonoidHom ≤ H := by
  classical
  obtain ⟨S₁⟩ : Nonempty (Sylow p ↥H) := inferInstance
  let P₀ : Subgroup ↥Y := (S₁ : Subgroup ↥H).map (Subgroup.inclusion hHY)
  have hP₀ : Nat.card ↥P₀ = p ^ (Nat.card ↥Y).factorization p := by
    rw [Subgroup.card_map_of_injective (Subgroup.inclusion_injective hHY),
      Sylow.card_eq_multiplicity, hord]
  let S₀ : Sylow p ↥Y := Sylow.ofCard P₀ hP₀
  have hA'p : IsPGroup p ↥(A.subgroupOf Y) := fun x => ⟨1, by
    apply Subtype.ext
    apply Subtype.ext
    simpa using hApow x.1.1 (Subgroup.mem_subgroupOf.1 x.2)⟩
  obtain ⟨P, hP⟩ := IsPGroup.exists_le_sylow hA'p
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥Y P S₀
  refine ⟨(g : G), g.2, ?_⟩
  rintro _ ⟨x, hxA, rfl⟩
  have hxP : (⟨x, hAY hxA⟩ : ↥Y) ∈ P := hP (Subgroup.mem_subgroupOf.2 hxA)
  have h1 : (MulAut.conj g) • (⟨x, hAY hxA⟩ : ↥Y) ∈ (g • P : Sylow p _) :=
    Subgroup.smul_mem_pointwise_smul _ _ _ hxP
  rw [hg] at h1
  obtain ⟨s, -, hs⟩ := Subgroup.mem_map.1 (show _ ∈ P₀ from h1)
  have := congrArg (fun z : ↥Y => (z : G)) hs
  simp only [Subgroup.coe_inclusion] at this
  show (g : G) * x * (g : G)⁻¹ ∈ H
  rw [show (g : G) * x * (g : G)⁻¹ = (s : G) from this.symm.trans (by rfl)]
  exact s.2

end CFSG.RankThree.PartOne.K133H
