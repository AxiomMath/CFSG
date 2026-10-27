module

public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12MovesPlan

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanStep131b

open scoped Pointwise

theorem s4_holds : S4 := by
  intro G _ _ B N S₁ S₂ hΩ hNB h1 h2 hp1 hp2 _ hc2 he1 he2
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp1' : IsPGroup 3 (S₁.comap N.subtype) := hp1.comap_subtype (K := N)
  have hp2' : IsPGroup 3 (S₂.comap N.subtype) := hp2.comap_subtype (K := N)
  obtain ⟨R₁, hR₁⟩ := hp1'.exists_le_sylow
  obtain ⟨R₂, hR₂⟩ := hp2'.exists_le_sylow
  haveI : Finite (Sylow 3 N) := Sylow.finite_of_finiteIndex R₁
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq N R₁ R₂
  have hgS : MulAut.conj g • (R₁ : Subgroup N) = (R₂ : Subgroup N) := by
    rw [← Sylow.coe_subgroup_smul, hg]
  have hconj : ∀ x ∈ (R₁ : Subgroup N), g * x * g⁻¹ ∈ (R₂ : Subgroup N) := by
    intro x hx
    rw [← hgS]
    exact Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) _ hx
  set R₂G : Subgroup G := (R₂ : Subgroup N).map N.subtype with hR₂G
  have hR₂p : IsPGroup 3 R₂G := R₂.isPGroup'.map _
  have hR₂B : R₂G ≤ B := by
    rintro _ ⟨y, -, rfl⟩
    exact hNB y.2
  have hbound := hΩ R₂G hR₂p hR₂B
  have hS₂R : ∀ x ∈ S₂, x ∈ R₂G := by
    intro x hx
    exact ⟨⟨x, h2 hx⟩, hR₂ (Subgroup.mem_comap.mpr hx), rfl⟩
  let φ : S₂ → {x : G // x ∈ R₂G ∧ x ^ 3 = 1} := fun x => ⟨x, hS₂R x x.2, he2 x x.2⟩
  have hφinj : Function.Injective φ := by
    intro x y h
    have h' := congrArg (fun z : {x : G // x ∈ R₂G ∧ x ^ 3 = 1} => (z : G)) h
    exact Subtype.ext h'
  have hbij : Function.Bijective φ :=
    hφinj.bijective_of_nat_card_le (by rw [hc2]; exact hbound)
  refine ⟨(g : G), g.2, fun x hx => ?_⟩
  have hxN : x ∈ N := h1 hx
  have hx1 : (⟨x, hxN⟩ : N) ∈ (R₁ : Subgroup N) := hR₁ (Subgroup.mem_comap.mpr hx)
  have h3 := hconj _ hx1
  have hmem : (g : G) * x * (g : G)⁻¹ ∈ R₂G := ⟨g * ⟨x, hxN⟩ * g⁻¹, h3, rfl⟩
  have hexp : ((g : G) * x * (g : G)⁻¹) ^ 3 = 1 := by
    rw [conj_pow, he1 x hx]
    simp
  obtain ⟨y, hy⟩ := hbij.2 ⟨(g : G) * x * (g : G)⁻¹, hmem, hexp⟩
  have hy2 : (y : G) = (g : G) * x * (g : G)⁻¹ := by
    have h' := congrArg (fun z : {x : G // x ∈ R₂G ∧ x ^ 3 = 1} => (z : G)) hy
    exact h'
  rw [← hy2]
  exact y.2

end CFSG.RankThree.PartTwo.Sec13.RonanStep131b
