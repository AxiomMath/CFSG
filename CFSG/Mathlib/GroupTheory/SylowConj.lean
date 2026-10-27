module

public import Mathlib.GroupTheory.Sylow

public section

theorem IsPGroup.exists_mem_conj_mem_of_card_eq {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    {P Q R : Subgroup G} [Finite P] (hQP : Q ≤ P)
    (hQ : Nat.card Q = p ^ (Nat.card P).factorization p) (hRP : R ≤ P) (hR : IsPGroup p R) :
    ∃ g ∈ P, ∀ r ∈ R, g⁻¹ * r * g ∈ Q := by
  let S0 : Sylow p P := Sylow.ofCard (Q.subgroupOf P)
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQP).toEquiv, hQ])
  have hpg : IsPGroup p (R.subgroupOf P) := hR.of_equiv (Subgroup.subgroupOfEquivOfLe hRP).symm
  obtain ⟨S, hS⟩ := hpg.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq P S0 S
  refine ⟨g, g.2, fun r hr => ?_⟩
  have hmem : (⟨r, hRP hr⟩ : P) ∈ ((g • S0 : Sylow p P) : Subgroup P) := by
    rw [hg]
    exact hS (Subgroup.mem_subgroupOf.2 hr)
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
    MulAut.smul_def, MulAut.conj_apply, inv_inv] at hmem
  have : ((g⁻¹ * ⟨r, hRP hr⟩ * g : P) : G) ∈ Q := hmem
  simpa using this
