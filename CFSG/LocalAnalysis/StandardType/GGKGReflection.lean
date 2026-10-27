module

public import CFSG.LocalAnalysis.StandardType.GGKGForkTransfer

public section

namespace CFSG.StandardType

theorem GGKGIsReflAt.isReflection {p : ℕ} {G : Type} [Group G] {E : Subgroup G}
    {w : G} (h : GGKGIsReflAt p E w) : GGIsReflection p (ggConjAut E h.1) := by
  refine ⟨?_, ?_⟩
  · apply MulEquiv.ext
    intro e
    apply Subtype.ext
    simpa only [pow_two, MulAut.mul_apply, ggConjAut_apply, MulAut.one_apply] using h.2.1 e e.2
  · have hfix : {e : E // ggConjAut E h.1 e = e} ≃
        {e : E // w * (e : G) * w⁻¹ = e} :=
      Equiv.subtypeEquivRight fun e => Subtype.ext_iff
    rw [Nat.card_congr hfix]
    exact h.2.2

theorem GGKGIsReflAt.map {p : ℕ} {G H : Type} [Group G] [Group H]
    (f : G →* H) (hf : Function.Injective f) {E : Subgroup G} {w : G}
    (h : GGKGIsReflAt p E w) : GGKGIsReflAt p (E.map f) (f w) := by
  refine ⟨Subgroup.le_normalizer_map f (Subgroup.mem_map_of_mem f h.1), ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    simpa only [map_mul, map_inv] using congrArg f (h.2.1 x hx)
  · have hfix : Nat.card {x : E // w * (x : G) * w⁻¹ = x} =
        Nat.card {y : E.map f // f w * (y : H) * (f w)⁻¹ = y} := by
      refine Nat.card_congr (Equiv.subtypeEquiv (E.equivMapOfInjective f hf) ?_)
      intro x
      change w * (x : G) * w⁻¹ = x ↔ f w * f (x : G) * (f w)⁻¹ = f (x : G)
      rw [← map_inv, ← map_mul, ← map_mul]
      exact ⟨congrArg f, fun h => hf h⟩
    rw [← hfix, h.2.2, Subgroup.card_map_of_injective hf]

theorem GGKGIsReflAt.of_map {p : ℕ} {G H : Type} [Group G] [Group H]
    (f : G →* H) (hf : Function.Injective f) {E : Subgroup G} {w : G}
    (h : GGKGIsReflAt p (E.map f) (f w)) : GGKGIsReflAt p E w := by
  have hmem : ∀ x : G, f x ∈ E.map f ↔ x ∈ E := fun _ => Subgroup.mem_map_iff_mem hf
  refine ⟨?_, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [← hmem, ← hmem]
    simpa only [map_mul, map_inv] using (Subgroup.mem_normalizer_iff.mp h.1) (f x)
  · intro x hx
    apply hf
    simpa only [map_mul, map_inv] using h.2.1 (f x) ((hmem x).mpr hx)
  · have hfix : Nat.card {x : E // w * (x : G) * w⁻¹ = x} =
        Nat.card {y : E.map f // f w * (y : H) * (f w)⁻¹ = y} := by
      refine Nat.card_congr (Equiv.subtypeEquiv (E.equivMapOfInjective f hf) ?_)
      intro x
      change w * (x : G) * w⁻¹ = x ↔ f w * f (x : G) * (f w)⁻¹ = f (x : G)
      rw [← map_inv, ← map_mul, ← map_mul]
      exact ⟨congrArg f, fun h => hf h⟩
    rw [hfix, h.2.2, Subgroup.card_map_of_injective hf]

theorem GGKGIsReflAt.exists_fixed_ne_one {p : ℕ} {G : Type} [Group G]
    {E : Subgroup G} [Finite E] {w : G} (hp : p.Prime) (hcard : p ^ 3 ≤ Nat.card E)
    (h : GGKGIsReflAt p E w) : ∃ x ∈ E, x ≠ 1 ∧ w * x * w⁻¹ = x := by
  classical
  let F := {x : E // w * (x : G) * w⁻¹ = x}
  have hlarge : 1 < Nat.card F := by
    have hpow : p < p ^ 3 := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    by_contra hsmall
    have hle : Nat.card F ≤ 1 := Nat.le_of_not_gt hsmall
    have h : Nat.card E ≤ p := by
      rw [← h.2.2]
      simpa using Nat.mul_le_mul_right p hle
    omega
  let oneF : F := ⟨1, by simp⟩
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨x, hx⟩ := Fintype.exists_ne_of_one_lt_card
    (by rwa [← Nat.card_eq_fintype_card]) oneF
  refine ⟨(x.1 : G), x.1.2, ?_, x.2⟩
  intro h1
  apply hx
  apply Subtype.ext
  exact Subtype.ext h1

end CFSG.StandardType

end
