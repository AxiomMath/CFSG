module

public import CFSG.RankThree.SubgroupLists.SL3Involutions

public section

namespace CFSG.Quasithin.H13.NQCore.S5

open Matrix

variable {K : Type*} [Field K]

theorem card_le_two_of_sq_eq_one_gl1 (E : Subgroup (GL (Fin 1) K))
    (hsq : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 2 := by
  classical
  have hfin : ∀ x ∈ E, x ∈ ({1, -1} : Finset (GL (Fin 1) K)) := by
    intro x hx
    have h := congrArg (fun m : GL (Fin 1) K => (m : Matrix (Fin 1) (Fin 1) K) 0 0) (hsq x hx)
    simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_one, Units.val_one,
      Matrix.one_apply_eq] at h
    rcases mul_self_eq_one_iff.1 h with h1 | h1
    · have : x = 1 := Units.ext (by ext i j; fin_cases i; fin_cases j; simpa using h1)
      simp [this]
    · have : x = -1 := Units.ext (by ext i j; fin_cases i; fin_cases j; simpa using h1)
      simp [this]
  calc Nat.card E = Nat.card (E : Set (GL (Fin 1) K)) := rfl
    _ ≤ Nat.card ((({1, -1} : Finset (GL (Fin 1) K)) : Set (GL (Fin 1) K))) :=
        Nat.card_mono (Set.toFinite _) fun x hx => hfin x hx
    _ ≤ 2 := by rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]; exact Finset.card_le_two

theorem card_le_eight_of_sq_eq_one_gl3 (h2 : (2 : K) ≠ 0) (E : Subgroup (GL (Fin 3) K))
    (hsq : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 8 := by
  classical
  let D : E →* Kˣ := Matrix.GeneralLinearGroup.det.comp E.subtype
  have hD : ∀ x : E, (D x : K) = (x : GL (Fin 3) K).val.det := fun x =>
    Matrix.GeneralLinearGroup.val_det_apply _
  have hrange : Nat.card D.range ≤ 2 := by
    have hfin : ∀ u ∈ D.range, u ∈ ({1, -1} : Finset Kˣ) := by
      rintro _ ⟨x, rfl⟩
      have h : (D x : K) * (D x : K) = 1 := by
        rw [← Units.val_mul, ← map_mul]
        have : x * x = 1 := Subtype.ext (hsq x x.2)
        rw [this, map_one, Units.val_one]
      rcases mul_self_eq_one_iff.1 h with h1 | h1
      · have : D x = 1 := Units.ext (by simpa using h1)
        simp [this]
      · have : D x = -1 := Units.ext (by simpa using h1)
        simp [this]
    calc Nat.card D.range = Nat.card (D.range : Set Kˣ) := rfl
      _ ≤ Nat.card ((({1, -1} : Finset Kˣ) : Set Kˣ)) :=
          Nat.card_mono (Set.toFinite _) fun x hx => hfin x hx
      _ ≤ 2 := by rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]; exact Finset.card_le_two
  have hker : Nat.card D.ker ≤ 4 := by
    have h4 := CFSG.RankThree.SubgroupLists.card_le_four_of_sq_eq_one_sl3 h2
      (D.ker.map E.subtype) (by
      rintro _ ⟨x, -, rfl⟩
      rw [← map_mul]
      have : x * x = 1 := Subtype.ext (hsq x x.2)
      rw [this, map_one]) (by
      rintro _ ⟨x, hx, rfl⟩
      have := hD x
      rw [MonoidHom.mem_ker.1 hx, Units.val_one] at this
      exact this.symm)
    rwa [Subgroup.card_map_of_injective E.subtype_injective] at h4
  calc Nat.card E = Nat.card D.ker * Nat.card D.range :=
        (Subgroup.card_ker_mul_card_range D).symm
    _ ≤ 4 * 2 := Nat.mul_le_mul hker hrange

theorem card_le_eight_of_sq_eq_one (h2 : (2 : K) ≠ 0) {d : ℕ} (hd : d ≤ 3)
    (E : Subgroup (GL (Fin d) K)) (hsq : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 8 := by
  interval_cases d
  · have hbot : E = ⊥ := (Subgroup.eq_bot_iff_forall E).2 fun x _ =>
      Units.ext (Subsingleton.elim _ _)
    rw [hbot, Subgroup.card_bot]
    norm_num
  · have := card_le_two_of_sq_eq_one_gl1 E hsq
    omega
  · have := CFSG.RankThree.SubgroupLists.card_le_four_of_sq_eq_one_gl2 h2 E hsq
    omega
  · exact card_le_eight_of_sq_eq_one_gl3 h2 E hsq

end CFSG.Quasithin.H13.NQCore.S5
