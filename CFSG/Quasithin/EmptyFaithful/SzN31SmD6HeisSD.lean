module

public import CFSG.CharacterTheory.Semidihedral.NormalForm

public section

namespace CFSG.Quasithin.SzN31

namespace SmD6Heis

open CFSG.Open

variable {G : Type*} [Group G]

theorem closure_semidihedral_four {a b : G} (ha8 : a ^ 8 = 1) (ha4 : a ^ 4 ≠ 1) (hb2 : b ^ 2 = 1)
    (hab : b * a * b⁻¹ = a ^ 3) :
    Nat.card (Subgroup.closure ({a, b} : Set G)) = 16 ∧
      Nonempty (↥(Subgroup.closure ({a, b} : Set G)) ≃* SemidihedralGroup 4) := by
  have hab' : b * a * b⁻¹ = a ^ (2 ^ (4 - 2) - 1) := by
    rw [show (2 ^ (4 - 2) - 1 : ℕ) = 3 by norm_num]
    exact hab
  have hrels : ∀ r ∈ semidihedralRels 4, FreeGroup.lift ![a, b] r = 1 := by
    rintro r (rfl | rfl | rfl)
    · simpa using ha8
    · simpa using hb2
    · simp only [map_mul, map_inv, map_pow, FreeGroup.lift_apply_of, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [hab', mul_inv_cancel]
  let φ : SemidihedralGroup 4 →* G := PresentedGroup.toGroup hrels
  have hφ0 : φ (PresentedGroup.of 0) = a := (PresentedGroup.toGroup.of hrels).trans (by simp)
  have hφ1 : φ (PresentedGroup.of 1) = b := (PresentedGroup.toGroup.of hrels).trans (by simp)
  have hrange : φ.range = Subgroup.closure ({a, b} : Set G) := by
    rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of (semidihedralRels 4),
      MonoidHom.map_closure, ← Set.range_comp]
    congr 1
    ext g
    simp only [Set.mem_range, Function.comp_apply, Set.mem_insert_iff, Set.mem_singleton_iff,
      Fin.exists_fin_two]
    rw [hφ0, hφ1]
    exact ⟨fun h => h.imp Eq.symm Eq.symm, fun h => h.imp Eq.symm Eq.symm⟩
  have haP : a ∈ φ.range := ⟨_, hφ0⟩
  have hbP : b ∈ φ.range := ⟨_, hφ1⟩
  have hfin : Finite (SemidihedralGroup 4) := CFSG.Semidihedral.presentation_finite 4 (by norm_num)
  have hfinR : Finite φ.range := Finite.of_surjective _ φ.rangeRestrict_surjective
  have hcardSD : Nat.card (SemidihedralGroup 4) = 16 := by
    rw [CFSG.Semidihedral.card 4 (by norm_num)]
    norm_num
  have hle16 : Nat.card φ.range ≤ 16 := by
    rw [← hcardSD]
    exact Nat.card_le_card_of_surjective _ φ.rangeRestrict_surjective
  have hord : orderOf a = 8 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := orderOf_eq_prime_pow (p := 2) (n := 2) (x := a) (by norm_num; exact ha4)
      (by norm_num; exact ha8)
    simpa using this
  have hzA : Subgroup.zpowers a ≤ φ.range := (Subgroup.zpowers_le).2 haP
  have h8 : 8 ∣ Nat.card φ.range := by
    have := Subgroup.card_dvd_of_le hzA
    rwa [Nat.card_zpowers, hord] at this
  have hbnot : b ∉ Subgroup.zpowers a := by
    intro hb
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hb
    have hc : b * a = a * b := by
      rw [← hk]
      exact ((Commute.refl a).zpow_left k).eq
    have h1 : b * a * b⁻¹ = a := by rw [hc]; group
    have h3 : a ^ 3 = a := hab.symm.trans h1
    have h2 : a ^ 2 = 1 := by
      have : a * a ^ 2 = a * 1 := by rw [mul_one, ← pow_succ']; exact h3
      exact mul_left_cancel this
    apply ha4
    calc a ^ 4 = (a ^ 2) ^ 2 := by rw [← pow_mul]
      _ = 1 := by rw [h2, one_pow]
  have h16 : Nat.card φ.range = 16 := by
    have hne : Nat.card φ.range ≠ 8 := by
      intro h8'
      apply hbnot
      have heq : Subgroup.zpowers a = φ.range :=
        Subgroup.eq_of_le_of_card_ge hzA (by rw [h8', Nat.card_zpowers, hord])
      rw [heq]
      exact hbP
    have hpos : 0 < Nat.card φ.range := Nat.card_pos
    omega
  have hbij : Function.Bijective φ.rangeRestrict :=
    φ.rangeRestrict_surjective.bijective_of_nat_card_le (by rw [h16, hcardSD])
  refine ⟨by rw [← hrange]; exact h16, ⟨?_⟩⟩
  exact (MulEquiv.subgroupCongr hrange.symm).trans (MulEquiv.ofBijective _ hbij).symm

end SmD6Heis

end CFSG.Quasithin.SzN31
