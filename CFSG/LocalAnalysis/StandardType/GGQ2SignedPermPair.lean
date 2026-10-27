module

public import CFSG.LocalAnalysis.StandardType.GGQ2ClassicalNormalizers
import CFSG.LocalAnalysis.StandardType.GGQ2PlaneChainGroups

public section

namespace CFSG.StandardType.GGQ2Frame.PlaneRaw

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem swapEquiv_mul_self (t : ℕ) (i j : Fin t) :
    swapEquiv t i j * swapEquiv t i j = 1 := by
  ext u k
  simp only [LinearEquiv.mul_apply, LinearEquiv.coe_one, id_eq, swapEquiv_apply]
  have h : ∀ x : Fin t, Equiv.swap i j (Equiv.swap i j x) = x := by
    intro x
    simp
  rw [h]

private theorem swapEquiv_comm (t : ℕ) (i j : Fin t) :
    swapEquiv t j i = swapEquiv t i j := by
  ext u k
  rw [swapEquiv_apply, swapEquiv_apply, Equiv.swap_comm j i]

private theorem conj_swap_negEquiv (t : ℕ) (i j : Fin t) :
    swapEquiv t i j * negEquiv t i * swapEquiv t i j = negEquiv t j := by
  ext u k
  have hss : ∀ x : Fin t, Equiv.swap i j (Equiv.swap i j x) = x := by
    intro x
    simp
  simp only [LinearEquiv.mul_apply, swapEquiv_apply, negEquiv_apply, hss]
  by_cases h : k = j
  · rw [h, Equiv.swap_apply_right]
    simp
  · have hk : Equiv.swap i j k ≠ i := by
      intro h'
      exact h (by simpa using congrArg (Equiv.swap i j) h')
    simp [hk, h]

private theorem negEquiv_mul_swapEquiv (t : ℕ) (i j : Fin t) :
    negEquiv t j * swapEquiv t i j = swapEquiv t i j * negEquiv t i := by
  calc negEquiv t j * swapEquiv t i j
      = (swapEquiv t i j * negEquiv t i * swapEquiv t i j) * swapEquiv t i j := by
        simp only [conj_swap_negEquiv]
    _ = swapEquiv t i j * negEquiv t i := by
        rw [mul_assoc (swapEquiv t i j * negEquiv t i) (swapEquiv t i j) (swapEquiv t i j),
          swapEquiv_mul_self, mul_one]

theorem swapEquiv_eq_rotEquiv_mul_negEquiv (t : ℕ) (i j : Fin t) :
    swapEquiv t i j = rotEquiv t i j * negEquiv t j := by
  ext u k
  simp only [rotEquiv, LinearEquiv.mul_apply, swapEquiv_apply, negEquiv_apply]
  by_cases h : Equiv.swap i j k = j <;> simp [h]

theorem rotEquiv_sq (t : ℕ) (i j : Fin t) :
    rotEquiv t i j ^ 2 = negEquiv t i * negEquiv t j := by
  have hss : swapEquiv t i j * swapEquiv t i j = 1 := swapEquiv_mul_self t i j
  rw [pow_two, rotEquiv]
  calc swapEquiv t i j * negEquiv t j * (swapEquiv t i j * negEquiv t j)
      = (swapEquiv t i j * negEquiv t j * swapEquiv t i j) * negEquiv t j := by
        rw [← mul_assoc (swapEquiv t i j * negEquiv t j) (swapEquiv t i j) (negEquiv t j)]
    _ = (swapEquiv t i j * (negEquiv t j * swapEquiv t i j)) * negEquiv t j := by
        rw [mul_assoc (swapEquiv t i j) (negEquiv t j) (swapEquiv t i j)]
    _ = (swapEquiv t i j * (swapEquiv t i j * negEquiv t i)) * negEquiv t j := by
        rw [negEquiv_mul_swapEquiv]
    _ = ((swapEquiv t i j * swapEquiv t i j) * negEquiv t i) * negEquiv t j := by
        rw [← mul_assoc (swapEquiv t i j) (swapEquiv t i j) (negEquiv t i)]
    _ = negEquiv t i * negEquiv t j := by rw [hss, one_mul]

theorem negEquiv_mul_rotEquiv_mul_negEquiv (t : ℕ) (i j : Fin t) :
    negEquiv t j * rotEquiv t i j * negEquiv t j = (rotEquiv t i j)⁻¹ := by
  have hnn : negEquiv t j * negEquiv t j = 1 := negEquiv_mul_self t j
  have hss : swapEquiv t i j * swapEquiv t i j = 1 := swapEquiv_mul_self t i j
  have hs : (swapEquiv t i j)⁻¹ = swapEquiv t i j := inv_eq_of_mul_eq_one_right hss
  have hn : (negEquiv t j)⁻¹ = negEquiv t j := inv_eq_of_mul_eq_one_right hnn
  rw [rotEquiv, mul_inv_rev, hs, hn]
  rw [← mul_assoc (negEquiv t j) (swapEquiv t i j) (negEquiv t j),
    mul_assoc (negEquiv t j * swapEquiv t i j) (negEquiv t j) (negEquiv t j), hnn, mul_one]

theorem rotEquiv_comm (t : ℕ) (i j : Fin t) :
    rotEquiv t j i = (rotEquiv t i j)⁻¹ := by
  have hprod : rotEquiv t j i * rotEquiv t i j = 1 := by
    rw [rotEquiv, rotEquiv, swapEquiv_comm]
    calc (swapEquiv t i j * negEquiv t i) * (swapEquiv t i j * negEquiv t j)
        = ((swapEquiv t i j * negEquiv t i) * swapEquiv t i j) * negEquiv t j := by
          rw [← mul_assoc (swapEquiv t i j * negEquiv t i) (swapEquiv t i j) (negEquiv t j)]
      _ = negEquiv t j * negEquiv t j := by simp only [conj_swap_negEquiv]
      _ = 1 := negEquiv_mul_self t j
  exact eq_inv_of_mul_eq_one_left hprod

theorem mem_zpowers_rotEquiv_or_of_mem (t : ℕ) {i j : Fin t}
    {φ : V t ≃ₗ[F] V t} (hφ : φ ∈ signedPermGroupOn t {i, j}) :
    φ ∈ Subgroup.zpowers (rotEquiv t i j) ∨
      φ * negEquiv t j ∈ Subgroup.zpowers (rotEquiv t i j) := by
  have hnn : negEquiv t j * negEquiv t j = 1 := negEquiv_mul_self t j
  have hninj : (negEquiv t j)⁻¹ = negEquiv t j := inv_eq_of_mul_eq_one_right hnn
  have hconj : negEquiv t j * rotEquiv t i j * (negEquiv t j)⁻¹ = (rotEquiv t i j)⁻¹ := by
    rw [hninj]
    exact negEquiv_mul_rotEquiv_mul_negEquiv t i j
  have hmap : (Subgroup.zpowers (rotEquiv t i j)).map
      (MulAut.conj (negEquiv t j)).toMonoidHom = Subgroup.zpowers (rotEquiv t i j) := by
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers (negEquiv t j * rotEquiv t i j * (negEquiv t j)⁻¹) =
      Subgroup.zpowers (rotEquiv t i j)
    rw [hconj, Subgroup.zpowers_inv]
  have hmemconj : ∀ z ∈ Subgroup.zpowers (rotEquiv t i j),
      negEquiv t j * z * negEquiv t j ∈ Subgroup.zpowers (rotEquiv t i j) := by
    intro z hz
    have h := Subgroup.mem_map_of_mem (MulAut.conj (negEquiv t j)).toMonoidHom hz
    rw [hmap] at h
    simpa [MulAut.conj_apply, hninj] using h
  let K : Subgroup (V t ≃ₗ[F] V t) :=
    { carrier := {a | a ∈ Subgroup.zpowers (rotEquiv t i j) ∨
          a * negEquiv t j ∈ Subgroup.zpowers (rotEquiv t i j)}
      one_mem' := Or.inl (Subgroup.one_mem _)
      mul_mem' := by
        intro a b ha hb
        rcases ha with ha | ha
        · rcases hb with hb | hb
          · exact Or.inl (Subgroup.mul_mem _ ha hb)
          · exact Or.inr (by rw [mul_assoc]; exact Subgroup.mul_mem _ ha hb)
        · rcases hb with hb | hb
          · refine Or.inr ?_
            have hc : negEquiv t j * b * negEquiv t j ∈
                Subgroup.zpowers (rotEquiv t i j) := hmemconj b hb
            have ha' : a = (a * negEquiv t j) * negEquiv t j := by
              rw [mul_assoc, hnn, mul_one]
            rw [ha']
            have heq : ((a * negEquiv t j) * negEquiv t j) * b * negEquiv t j =
                (a * negEquiv t j) * (negEquiv t j * b * negEquiv t j) := by
              rw [mul_assoc (a * negEquiv t j) (negEquiv t j) b,
                mul_assoc (a * negEquiv t j) (negEquiv t j * b) (negEquiv t j)]
            rw [heq]
            exact Subgroup.mul_mem _ ha hc
          · refine Or.inl ?_
            have hc : negEquiv t j * (b * negEquiv t j) * negEquiv t j ∈
                Subgroup.zpowers (rotEquiv t i j) := hmemconj (b * negEquiv t j) hb
            have ha' : a = (a * negEquiv t j) * negEquiv t j := by
              rw [mul_assoc, hnn, mul_one]
            have hb' : b = (b * negEquiv t j) * negEquiv t j := by
              rw [mul_assoc, hnn, mul_one]
            rw [ha', hb']
            have heq : (a * negEquiv t j) * negEquiv t j *
                  ((b * negEquiv t j) * negEquiv t j) =
                (a * negEquiv t j) *
                  (negEquiv t j * (b * negEquiv t j) * negEquiv t j) := by
              rw [mul_assoc (a * negEquiv t j) (negEquiv t j)
                ((b * negEquiv t j) * negEquiv t j)]
              rw [← mul_assoc (negEquiv t j) (b * negEquiv t j) (negEquiv t j)]
            rw [heq]
            exact Subgroup.mul_mem _ ha hc
      inv_mem' := by
        intro a ha
        rcases ha with ha | ha
        · exact Or.inl (Subgroup.inv_mem _ ha)
        · refine Or.inr ?_
          have hc : negEquiv t j * (a * negEquiv t j)⁻¹ * negEquiv t j ∈
              Subgroup.zpowers (rotEquiv t i j) :=
            hmemconj (a * negEquiv t j)⁻¹ (Subgroup.inv_mem _ ha)
          have ha' : a = (a * negEquiv t j) * negEquiv t j := by
            rw [mul_assoc, hnn, mul_one]
          rw [ha', mul_inv_rev]
          simpa [hninj] using hc }
  have hle : signedPermGroupOn t {i, j} ≤ K := by
    rw [signedPermGroupOn]
    refine (Subgroup.closure_le K).mpr ?_
    intro x hx
    rcases hx with ⟨a, ha, b, hb, rfl⟩ | ⟨a, ha, rfl⟩
    · change swapEquiv t a b ∈ Subgroup.zpowers (rotEquiv t i j) ∨
        swapEquiv t a b * negEquiv t j ∈ Subgroup.zpowers (rotEquiv t i j)
      have ha' : a = i ∨ a = j := by simpa using ha
      have hb' : b = i ∨ b = j := by simpa using hb
      rcases ha' with hai | haj <;> rcases hb' with hbi | hbj
      · rw [hai, hbi]
        exact Or.inl (by rw [swapEquiv_self t i]; exact Subgroup.one_mem _)
      · rw [hai, hbj]
        exact Or.inr (by
          rw [swapEquiv_eq_rotEquiv_mul_negEquiv t i j, mul_assoc, negEquiv_mul_self, mul_one]
          exact Subgroup.mem_zpowers _)
      · rw [haj, hbi]
        exact Or.inr (by
          rw [swapEquiv_comm t i j, swapEquiv_eq_rotEquiv_mul_negEquiv t i j, mul_assoc,
            negEquiv_mul_self, mul_one]
          exact Subgroup.mem_zpowers _)
      · rw [haj, hbj]
        exact Or.inl (by rw [swapEquiv_self t j]; exact Subgroup.one_mem _)
    · change negEquiv t a ∈ Subgroup.zpowers (rotEquiv t i j) ∨
        negEquiv t a * negEquiv t j ∈ Subgroup.zpowers (rotEquiv t i j)
      have ha' : a = i ∨ a = j := by simpa using ha
      rcases ha' with hai | haj
      · rw [hai]
        exact Or.inr (by
          rw [← rotEquiv_sq, pow_two]
          exact Subgroup.mul_mem _ (Subgroup.mem_zpowers _) (Subgroup.mem_zpowers _))
      · rw [haj]
        exact Or.inr (by rw [negEquiv_mul_self]; exact Subgroup.one_mem _)
  exact hle hφ

private theorem zpowers_rotEquiv_of_mem_pair {t : ℕ} {i j a b : Fin t}
    (ha : a ∈ ({i, j} : Finset (Fin t))) (hb : b ∈ ({i, j} : Finset (Fin t)))
    (hab : a ≠ b) :
    Subgroup.zpowers (rotEquiv t a b) = Subgroup.zpowers (rotEquiv t i j) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with hai | haj <;> rcases hb with hbi | hbj
  · rw [hai, hbi] at hab
    exact absurd rfl hab
  · rw [hai, hbj]
  · rw [haj, hbi, rotEquiv_comm, Subgroup.zpowers_inv]
  · rw [haj, hbj] at hab
    exact absurd rfl hab

theorem normalizerOf_symplectic_pair (t : ℕ) {i j : Fin t} (hij : i ≠ j) :
    normalizerOf .symplectic t (.zero {i, j}) = Subgroup.zpowers (rotEquiv t i j) := by
  have hcard : ({i, j} : Finset (Fin t)).card = 2 := Finset.card_pair hij
  have hstep : normalizerOf .symplectic t (.zero {i, j}) =
      (if ({i, j} : Finset (Fin t)).card = 2 then
        Subgroup.zpowers (if h : ∃ a b : Fin t, a ∈ ({i, j} : Finset (Fin t)) ∧
          b ∈ ({i, j} : Finset (Fin t)) ∧ a ≠ b then
          rotEquiv t h.choose h.choose_spec.choose else 1)
      else signedPermGroupOn t {i, j}) := rfl
  rw [hstep, if_pos hcard]
  split_ifs with hex
  · obtain ⟨ha, hb, hab⟩ := hex.choose_spec.choose_spec
    exact zpowers_rotEquiv_of_mem_pair ha hb hab
  · exact absurd ⟨i, j, by simp, by simp, hij⟩ hex

end CFSG.StandardType.GGQ2Frame.PlaneRaw
