module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieL3OConjCard

public section

namespace CFSG.Quasithin.H13.NQCore.L3Odd

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

theorem exists_conj_torusP {K : Type} [Field K] [Finite K] {p : ℕ} [hp : Fact p.Prime]
    (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K - 1) {P : Subgroup (projectiveSL 3 K)}
    (hexp : ∀ x ∈ P, x ^ p = 1) (hcard : p ^ 2 ≤ Nat.card P) :
    ∃ g : projectiveSL 3 K, P.map (MulAut.conj g).toMonoidHom = torusP K p := by
  have hP : IsPGroup p P := fun x => ⟨1, Subtype.ext (by simpa using hexp x x.2)⟩
  obtain ⟨Q, hQp, hQP, hQZ⟩ := exists_lift_projectiveSL (by omega : p ≠ 3) hP
  obtain ⟨S, hS⟩ := exists_sylow_le_range_diagHom hp5 hpq
  obtain ⟨S', hQS'⟩ := hQp.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq SL(3, K) S' S
  have hQexp : ∀ z ∈ Q, z ^ p = 1 := by
    intro z hz
    have h1 : proj 3 K (z ^ p) = 1 := by
      rw [map_pow]
      exact hexp _ (hQP ▸ Subgroup.mem_map_of_mem _ hz)
    rw [proj_eq_one_iff] at h1
    exact Subgroup.disjoint_def.1 hQZ (Q.pow_mem hz p) h1
  have hconj : ∀ z ∈ Q, h * z * h⁻¹ ∈ torusSL K p := by
    intro z hz
    have h1 : h * z * h⁻¹ ∈ ((h • S' : Sylow p SL(3, K)) : Subgroup SL(3, K)) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
      exact ⟨z, hQS' hz, by simp [MulAut.smul_def]⟩
    rw [hh] at h1
    obtain ⟨y, hy⟩ := hS h1
    rw [← hy]
    refine mem_torusSL_of_pow_eq_one ?_
    rw [hy, conj_pow, hQexp z hz]
    group
  have hle : P.map (MulAut.conj (proj 3 K h)).toMonoidHom ≤ torusP K p := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← hQP] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    refine ⟨h * z * h⁻¹, hconj z hz, ?_⟩
    simp [MulAut.conj_apply, map_mul, map_inv]
  refine ⟨proj 3 K h, Subgroup.eq_of_le_of_card_ge hle ?_⟩
  rw [card_torusP hp5 hpq, Subgroup.card_map_of_injective (MulAut.conj _).injective]
  exact hcard

end CFSG.Quasithin.H13.NQCore.L3Odd
