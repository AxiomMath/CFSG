module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieSylO

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.L5

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.U5K.Hyp
  CFSG.LocalAnalysis.EvenBN.U5 CFSG.LocalAnalysis.ComponentInitial CFSG.QuasithinUnique
open CFSG.LieType.Universal.Spin (upperSL2)

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem syl_sY_le_U : sylSY h ≤ hypProjUnitriangular h 2 1 := Subgroup.map_mono Ssub_le_Usub

theorem syl_inf_cent_eq_sup
    (H2 : ∀ x ∈ hypProjUnitriangular h 2 1,
      x ∈ Subgroup.centralizer ({t5Y h} : Set (hypPSU h 2 1)) →
        ∃ a : h.fixedField, ∃ s ∈ Ssub h,
          x = hypProj h 2 1 (levHom h (upperSL2 a) * s)) :
    hypProjUnitriangular h 2 1 ⊓ Subgroup.centralizer ({t5Y h} : Set (hypPSU h 2 1)) =
      sylSY h ⊔ sylBY h := by
  refine le_antisymm (fun x ⟨hxU, hxC⟩ => ?_)
    (sup_le (le_inf syl_sY_le_U syl_sY_le_cent) (le_inf syl_bY_le_U syl_bY_le_cent))
  obtain ⟨a, s, hs, rfl⟩ := H2 x hxU hxC
  rw [map_mul]
  exact mul_mem (Subgroup.mem_sup_right (syl_mem_bY.2 ⟨a, rfl⟩))
    (Subgroup.mem_sup_left ⟨s, hs, rfl⟩)

theorem syl_isSylowTwoOf_gen
    (H1 : ∀ x ∈ Subgroup.centralizer ({t5Y h} : Set (hypPSU h 2 1)),
      ∃ B : SpecialLinearGroup (Fin 2) h.fixedField, ∃ s ∈ Ssub h,
        x = hypProj h 2 1 (levHom h B * s))
    (H2 : ∀ x ∈ hypProjUnitriangular h 2 1,
      x ∈ Subgroup.centralizer ({t5Y h} : Set (hypPSU h 2 1)) →
        ∃ a : h.fixedField, ∃ s ∈ Ssub h,
          x = hypProj h 2 1 (levHom h (upperSL2 a) * s)) :
    IsSylowTwoOf
      (hypProjUnitriangular h 2 1 ⊓ Subgroup.centralizer ({t5Y h} : Set (hypPSU h 2 1)))
      (Subgroup.centralizer ({t5Y h} : Set (hypPSU h 2 1))) := by
  have hS : Nat.card (hypProjUnitriangular h 2 1 ⊓
      Subgroup.centralizer ({t5Y h} : Set (hypPSU h 2 1)) : Subgroup (hypPSU h 2 1)) =
        (2 ^ f) ^ 8 * 2 ^ f := by
    rw [syl_inf_cent_eq_sup H2, syl_card_sup_bY]
  have hC := syl_card_cent H1
  have hle : hypProjUnitriangular h 2 1 ⊓
      Subgroup.centralizer ({t5Y h} : Set (hypPSU h 2 1)) ≤
      Subgroup.centralizer ({t5Y h} : Set (hypPSU h 2 1)) := inf_le_right
  refine ⟨hle, ?_, ?_⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact IsPGroup.of_card (n := f * 9) (by rw [hS, ← pow_succ, ← pow_mul])
  · have e := Subgroup.card_mul_index ((hypProjUnitriangular h 2 1 ⊓
      Subgroup.centralizer ({t5Y h} : Set (hypPSU h 2 1))).subgroupOf
        (Subgroup.centralizer ({t5Y h} : Set (hypPSU h 2 1))))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hS, hC] at e
    have hidx : ((hypProjUnitriangular h 2 1 ⊓
        Subgroup.centralizer ({t5Y h} : Set (hypPSU h 2 1))).subgroupOf
          (Subgroup.centralizer ({t5Y h} : Set (hypPSU h 2 1)))).index = (2 ^ f) ^ 2 - 1 := by
      refine Nat.eq_of_mul_eq_mul_left (by positivity : 0 < (2 ^ f) ^ 8 * 2 ^ f) ?_
      rw [e]
      ring
    rw [hidx]
    have h1 : 2 ∣ (2 ^ f) ^ 2 := dvd_pow (dvd_pow_self 2 (by have := h.one_le; omega)) two_ne_zero
    have h2 : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    omega

theorem syl_isSylowTwoOf {K : Type} [Field K] (h : UnitaryFieldData 2 2 K)
    (H1 : ∀ x ∈ Subgroup.centralizer ({t5Y h} : Set (hypPSU h 2 1)),
      ∃ B : SpecialLinearGroup (Fin 2) h.fixedField, ∃ s ∈ Ssub h,
        x = hypProj h 2 1 (levHom h B * s))
    (H2 : ∀ x ∈ hypProjUnitriangular h 2 1,
      x ∈ Subgroup.centralizer ({t5Y h} : Set (hypPSU h 2 1)) →
        ∃ a : h.fixedField, ∃ s ∈ Ssub h,
          x = hypProj h 2 1 (levHom h (CFSG.LieType.Universal.Spin.upperSL2 a) * s)) :
    CFSG.QuasithinUnique.IsSylowTwoOf
      (hypProjUnitriangular h 2 1 ⊓ Subgroup.centralizer ({t5Y h} : Set (hypPSU h 2 1)))
      (Subgroup.centralizer ({t5Y h} : Set (hypPSU h 2 1))) :=
  syl_isSylowTwoOf_gen H1 H2

end CFSG.Quasithin.H13.F431.Un.L5
