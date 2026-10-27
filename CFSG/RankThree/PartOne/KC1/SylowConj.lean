module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.RankThree.PartOne.KC1

open scoped Pointwise

theorem exists_conj_mem_of_factorization_eq {G : Type*} [Group G] [Finite G] (p : ℕ)
    [Fact p.Prime] (H : Subgroup G)
    (hcard : (Nat.card H).factorization p = (Nat.card G).factorization p) {x : G}
    (hx : IsPGroup p (Subgroup.zpowers x)) : ∃ c : G, c * x * c⁻¹ ∈ H := by
  obtain ⟨P⟩ : Nonempty (Sylow p H) := inferInstance
  set P₁ : Subgroup G := (P : Subgroup H).map H.subtype with hP₁
  have hP₁card : Nat.card P₁ = p ^ (Nat.card G).factorization p := by
    rw [hP₁, Subgroup.card_map_of_injective (Subtype.val_injective), P.card_eq_multiplicity, hcard]
  set S₁ : Sylow p G := Sylow.ofCard P₁ hP₁card with hS₁
  obtain ⟨S, hxS⟩ := hx.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G S S₁
  refine ⟨c, ?_⟩
  have h1 : MulAut.conj c • x ∈ MulAut.conj c • (S : Subgroup G) :=
    Subgroup.smul_mem_pointwise_smul _ _ _ (hxS (Subgroup.mem_zpowers x))
  rw [← Sylow.coe_subgroup_smul, hc, Sylow.coe_ofCard] at h1
  have h2 : c * x * c⁻¹ ∈ P₁ := by simpa [MulAut.smul_def] using h1
  obtain ⟨h, -, hh⟩ := Subgroup.mem_map.1 h2
  rw [← hh]
  exact h.2

end CFSG.RankThree.PartOne.KC1
