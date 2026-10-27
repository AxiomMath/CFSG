module

public import CFSG.Quasithin.AppendixH.Common.OctadStabBound

public section

open scoped Pointwise

namespace CFSG.ASVolI.AppH

open CFSG.ASVolI.ChH CFSG.Monster.Code

private theorem eq_of_le_of_le_of_mul_eq {a b : ℕ} (ha : a ≤ 759) (hb : b ≤ 322560)
    (h : a * b = 759 * 322560) : a = 759 ∧ b = 322560 := by
  have hle1 : a * b ≤ a * 322560 := Nat.mul_le_mul_left a hb
  have hle2 : a * 322560 ≤ 759 * 322560 := Nat.mul_le_mul_right 322560 ha
  have ha' : a = 759 := by
    refine Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 322560) ?_
    exact le_antisymm hle2 (by rw [← h]; exact hle1)
  have hb' : b = 322560 := by
    rw [ha'] at h
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 759) h
  exact ⟨ha', hb'⟩

private theorem orbit_subset_octads :
    MulAction.orbit (↥M24g) octadB0 ⊆ (octads : Set (Finset (Fin 24))) := by
  intro O hO
  obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hO
  exact (isOctad_iff_mem_octads).1 (by
    rw [Subgroup.smul_def]
    exact isOctad_smul (σ := (g : S24)) g.2 isOctad_octadB0)

theorem card_orbit_octadB0_le :
    Nat.card (MulAction.orbit M24g octadB0) ≤ 759 := by
  have hle := Set.ncard_le_ncard orbit_subset_octads octads.finite_toSet
  rw [Nat.card_coe_set_eq, ← card_octads, ← Set.ncard_coe_finset]
  exact hle

private theorem card_orbit_mul_card_stab :
    Nat.card (MulAction.orbit (↥M24g) octadB0) *
      Nat.card (MulAction.stabilizer (↥M24g) octadB0) = Nat.card (↥M24g) := by
  have h := (MulAction.stabilizer (↥M24g) octadB0).card_mul_index
  rw [MulAction.index_stabilizer] at h
  rw [← Nat.card_coe_set_eq] at h
  rw [mul_comm] at h
  exact h

private noncomputable def stabEquiv :
    ↥(MulAction.stabilizer (↥M24g) octadB0) ≃ ↥(octStab octadB0) where
  toFun k := ⟨(k.1 : S24),
    show (k.1 : S24) ∈ M24g ⊓ MulAction.stabilizer S24 octadB0 from
      Subgroup.mem_inf.mpr ⟨k.1.2, MulAction.mem_stabilizer_iff.mpr (by
        have h : k.1 • octadB0 = octadB0 := MulAction.mem_stabilizer_iff.mp k.2
        rw [Subgroup.smul_def] at h
        exact h)⟩⟩
  invFun s := ⟨⟨s.1, (Subgroup.mem_inf.mp s.2).1⟩,
    MulAction.mem_stabilizer_iff.mpr (by
      rw [Subgroup.smul_def]
      exact MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp s.2).2)⟩
  left_inv k := rfl
  right_inv s := rfl

private theorem card_stab_eq :
    Nat.card (MulAction.stabilizer (↥M24g) octadB0) = Nat.card (octStab octadB0) :=
  Nat.card_congr stabEquiv

private theorem card_orbit_and_card_octStab_octadB0 :
    Nat.card (MulAction.orbit (↥M24g) octadB0) = 759 ∧
      Nat.card (octStab octadB0) = 322560 := by
  have hmul := card_orbit_mul_card_stab
  rw [card_stab_eq] at hmul
  have hG244 : Nat.card (↥M24g) = 244823040 := by
    change Nat.card (↥AutPerm) = 244823040
    exact card_AutPerm
  have hG : Nat.card (↥M24g) = 759 * 322560 := by rw [hG244]
  have hprod : Nat.card (MulAction.orbit (↥M24g) octadB0) * Nat.card (octStab octadB0) =
      759 * 322560 := by rw [hmul, hG]
  exact eq_of_le_of_le_of_mul_eq card_orbit_octadB0_le card_octStab_octadB0_le hprod

private theorem orbit_eq_octads :
    MulAction.orbit (↥M24g) octadB0 = (octads : Set (Finset (Fin 24))) := by
  have h1 : (MulAction.orbit (↥M24g) octadB0).ncard = 759 := by
    rw [← Nat.card_coe_set_eq]
    exact (card_orbit_and_card_octStab_octadB0).1
  have h2 : (octads : Set (Finset (Fin 24))).ncard = 759 := by
    rw [Set.ncard_coe_finset, card_octads]
  refine Set.eq_of_subset_of_ncard_le orbit_subset_octads ?_ octads.finite_toSet
  rw [h2, h1]

theorem exists_smul_octad_eq {O₁ O₂ : Finset (Fin 24)}
    (h₁ : IsOctad O₁) (h₂ : IsOctad O₂) : ∃ σ ∈ M24g, σ • O₁ = O₂ := by
  have hO₁ : O₁ ∈ MulAction.orbit (↥M24g) octadB0 := by
    rw [orbit_eq_octads]
    exact (isOctad_iff_mem_octads).1 h₁
  have hO₂ : O₂ ∈ MulAction.orbit (↥M24g) octadB0 := by
    rw [orbit_eq_octads]
    exact (isOctad_iff_mem_octads).1 h₂
  obtain ⟨g₁, hg₁⟩ := MulAction.mem_orbit_iff.mp hO₁
  obtain ⟨g₂, hg₂⟩ := MulAction.mem_orbit_iff.mp hO₂
  refine ⟨((g₂ * g₁⁻¹ : ↥M24g) : S24), (g₂ * g₁⁻¹).2, ?_⟩
  have h₁' : g₁⁻¹ • O₁ = octadB0 := by
    have h := congrArg (fun x => g₁⁻¹ • x) hg₁
    rw [← mul_smul, inv_mul_cancel, one_smul] at h
    exact h.symm
  have hsub : (g₂ * g₁⁻¹ : ↥M24g) • O₁ = O₂ := by
    rw [mul_smul, h₁', hg₂]
  rw [← Subgroup.smul_def]
  exact hsub

theorem card_octStab {O : Finset (Fin 24)} (hO : IsOctad O) :
    Nat.card (octStab O) = 322560 := by
  obtain ⟨σ, hσ, hσO⟩ := exists_smul_octad_eq isOctad_octadB0 hO
  rw [← hσO, octStab_smul hσ octadB0]
  rw [Subgroup.card_map_of_injective (MulAut.conj σ).injective]
  exact (card_orbit_and_card_octStab_octadB0).2

end CFSG.ASVolI.AppH
