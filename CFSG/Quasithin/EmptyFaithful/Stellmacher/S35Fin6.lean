module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Fin2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Fin3

public section

namespace CFSG.Quasithin.F53.Stellmacher.S35.Fin

open Equiv CFSG.Quasithin CFSG.Quasithin.F53Mod

@[expose] def ZstdF : Finset (Perm (Fin 5)) := {1, zStd}

@[expose] def C4F : Finset (Perm (Fin 5)) := {1, S5g, S5g ^ 2, S5g ^ 3}

theorem mem_zpowers_zStd (x : Perm (Fin 5)) : x ∈ Subgroup.zpowers zStd ↔ x ∈ ZstdF := by
  have h : zStd * zStd = 1 := by unfold zStd; decide +kernel
  rw [mem_zpowers_iff_of_mul_self h]
  simp [ZstdF]

theorem mem_zpowers_S5g (x : Perm (Fin 5)) : x ∈ Subgroup.zpowers S5g ↔ x ∈ C4F := by
  have h : S5g ^ 4 = 1 := by unfold S5g; decide +kernel
  rw [mem_zpowers_iff_of_pow_eq_one h (by norm_num)]
  constructor
  · rintro ⟨k, hk, rfl⟩
    interval_cases k <;> simp [C4F]
  · intro hx
    simp only [C4F, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨0, by norm_num, rfl⟩
    · exact ⟨1, by norm_num, pow_one _⟩
    · exact ⟨2, by norm_num, rfl⟩
    · exact ⟨3, by norm_num, rfl⟩

theorem cj_cj_inv (g : Perm (Fin 5)) (B : Subgroup (Perm (Fin 5))) : cj g (cj g⁻¹ B) = B := by
  ext x
  rw [mem_cj, mem_cj]
  simp [mul_assoc]

theorem le_cj_iff {g : Perm (Fin 5)} {B C : Subgroup (Perm (Fin 5))} :
    B ≤ cj g C ↔ cj g⁻¹ B ≤ C := by
  constructor
  · intro h x hx
    rw [mem_cj] at hx
    have := h hx
    rw [mem_cj] at this
    simpa [mul_assoc] using this
  · intro h x hx
    rw [mem_cj]
    apply h
    rw [mem_cj]
    simpa [mul_assoc] using hx

@[expose] def stdE : Fin 8 → Perm (Fin 5) :=
  ![1, S5g, S5g ^ 2, S5g ^ 3, swap 0 2, S5g * swap 0 2, S5g ^ 2 * swap 0 2,
    S5g ^ 3 * swap 0 2]

@[expose] def stdMul : Fin 8 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![1, 2, 3, 0, 5, 6, 7, 4], ![2, 3, 0, 1, 6, 7, 4, 5],
    ![3, 0, 1, 2, 7, 4, 5, 6], ![4, 7, 6, 5, 0, 3, 2, 1], ![5, 4, 7, 6, 1, 0, 3, 2],
    ![6, 5, 4, 7, 2, 1, 0, 3], ![7, 6, 5, 4, 3, 2, 1, 0]]

@[expose] def stdConj : Fin 8 → Fin 8 → Fin 8 :=
  ![![0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 3, 3, 3, 3], ![2, 2, 2, 2, 2, 2, 2, 2],
    ![3, 3, 3, 3, 1, 1, 1, 1], ![4, 6, 4, 6, 4, 6, 4, 6], ![5, 7, 5, 7, 7, 5, 7, 5],
    ![6, 4, 6, 4, 6, 4, 6, 4], ![7, 5, 7, 5, 5, 7, 5, 7]]

theorem stdE_mul : ∀ i j, stdE i * stdE j = stdE (stdMul i j) := by
  unfold stdE stdMul; decide +kernel

theorem stdE_conj : ∀ i j, stdE j * stdE i * (stdE j)⁻¹ = stdE (stdConj i j) := by
  unfold stdE stdConj; decide +kernel

theorem stdE_mem : ∀ i, stdE i ∈ S5SylF := by unfold stdE; decide +kernel

theorem stdE_surj : ∀ x ∈ S5SylF, ∃ i, stdE i = x := by unfold stdE; decide +kernel

theorem normal_idx : ∀ f : Fin 8 → Bool, f 0 = true →
    (∀ i j, f i = true → f j = true → f (stdMul i j) = true) →
    (∀ i j, f i = true → f (stdConj i j) = true) →
    (∀ i, f i = true ↔ i ∈ ({0} : Finset (Fin 8))) ∨
    (∀ i, f i = true ↔ i ∈ ({0, 2} : Finset (Fin 8))) ∨
    (∀ i, f i = true ↔ i ∈ ({0, 2, 5, 7} : Finset (Fin 8))) ∨
    (∀ i, f i = true ↔ i ∈ ({0, 2, 4, 6} : Finset (Fin 8))) ∨
    (∀ i, f i = true ↔ i ∈ ({0, 1, 2, 3} : Finset (Fin 8))) ∨
    (∀ i, f i = true ↔ i ∈ (Finset.univ : Finset (Fin 8))) := by
  unfold stdMul stdConj; decide +kernel

theorem mem_of_idx (X : Finset (Perm (Fin 5))) (I : Finset (Fin 8))
    (h1 : ∀ i ∈ I, stdE i ∈ X) (h2 : ∀ x ∈ X, ∃ i ∈ I, stdE i = x) :
    ∀ x, x ∈ X ↔ ∃ i ∈ I, stdE i = x := fun x =>
  ⟨h2 x, fun ⟨i, hi, hx⟩ => hx ▸ h1 i hi⟩

theorem idx_bot : ∀ x, x ∈ ({1} : Finset (Perm (Fin 5))) ↔
    ∃ i ∈ ({0} : Finset (Fin 8)), stdE i = x :=
  mem_of_idx _ _ (by unfold stdE; decide +kernel) (by unfold stdE; decide +kernel)

theorem idx_Z : ∀ x, x ∈ ZstdF ↔ ∃ i ∈ ({0, 2} : Finset (Fin 8)), stdE i = x :=
  mem_of_idx _ _ (by unfold ZstdF stdE zStd; decide +kernel)
    (by unfold ZstdF stdE zStd; decide +kernel)

theorem idx_T : ∀ x, x ∈ S5TF ↔ ∃ i ∈ ({0, 2, 5, 7} : Finset (Fin 8)), stdE i = x :=
  mem_of_idx _ _ (by unfold stdE; decide +kernel) (by unfold stdE; decide +kernel)

theorem idx_That : ∀ x, x ∈ S5ThatF ↔ ∃ i ∈ ({0, 2, 4, 6} : Finset (Fin 8)), stdE i = x :=
  mem_of_idx _ _ (by unfold stdE; decide +kernel) (by unfold stdE; decide +kernel)

theorem idx_C4 : ∀ x, x ∈ C4F ↔ ∃ i ∈ ({0, 1, 2, 3} : Finset (Fin 8)), stdE i = x :=
  mem_of_idx _ _ (by unfold C4F stdE; decide +kernel) (by unfold C4F stdE; decide +kernel)

theorem idx_Syl : ∀ x, x ∈ S5SylF ↔ ∃ i ∈ (Finset.univ : Finset (Fin 8)), stdE i = x :=
  mem_of_idx _ _ (fun i _ => stdE_mem i)
    (fun x hx => (stdE_surj x hx).imp fun i hi => ⟨Finset.mem_univ i, hi⟩)

theorem normal_cases_std {B : Subgroup (Perm (Fin 5))} (hle : B ≤ S5Syl)
    (hn : ∀ d ∈ S5Syl, ∀ b ∈ B, d * b * d⁻¹ ∈ B) :
    B = ⊥ ∨ B = Subgroup.zpowers zStd ∨ B = S5T ∨ B = S5That ∨ B = Subgroup.zpowers S5g ∨
      B = S5Syl := by
  classical
  set f : Fin 8 → Bool := fun i => decide (stdE i ∈ B) with hf
  have hfB : ∀ i, f i = true ↔ stdE i ∈ B := fun i => by simp [hf]
  have key := normal_idx f
    ((hfB 0).mpr (by
      have : stdE 0 = 1 := rfl
      rw [this]; exact B.one_mem))
    (fun i j hi hj => (hfB _).mpr (by
      rw [← stdE_mul]; exact B.mul_mem ((hfB i).mp hi) ((hfB j).mp hj)))
    (fun i j hi => (hfB _).mpr (by
      rw [← stdE_conj]
      exact hn _ ((mem_S5Syl_iff _).mpr (stdE_mem j)) _ ((hfB i).mp hi)))
  have eqI : ∀ (X : Subgroup (Perm (Fin 5))) (I : Finset (Fin 8)) (Y : Finset (Perm (Fin 5))),
      (∀ x, x ∈ X ↔ x ∈ Y) → (∀ x, x ∈ Y ↔ ∃ i ∈ I, stdE i = x) →
      (∀ i, f i = true ↔ i ∈ I) → B = X := by
    intro X I Y hX hY hI
    ext x
    rw [hX, hY]
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := stdE_surj x ((mem_S5Syl_iff x).mp (hle hx))
      exact ⟨i, (hI i).mp ((hfB i).mpr (hi ▸ hx)), hi⟩
    · rintro ⟨i, hi, rfl⟩
      exact (hfB i).mp ((hI i).mpr hi)
  rcases key with h | h | h | h | h | h
  · left
    exact eqI ⊥ _ {1} (fun x => by rw [Subgroup.mem_bot, Finset.mem_singleton]) idx_bot h
  · right; left
    exact eqI _ _ ZstdF mem_zpowers_zStd idx_Z h
  · right; right; left
    exact eqI _ _ S5TF mem_S5T_iff idx_T h
  · right; right; right; left
    exact eqI _ _ S5ThatF mem_S5That_iff idx_That h
  · right; right; right; right; left
    exact eqI _ _ C4F mem_zpowers_S5g idx_C4 h
  · right; right; right; right; right
    exact eqI _ _ S5SylF mem_S5Syl_iff idx_Syl h

theorem normal_cases {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) {z : Perm (Fin 5)}
    (hz : IsCentInv D z) {B : Subgroup (Perm (Fin 5))} (hle : B ≤ D)
    (hn : ∀ d ∈ D, ∀ b ∈ B, d * b * d⁻¹ ∈ B) :
    B = ⊥ ∨ B = Subgroup.zpowers z ∨ B = Tsub D ∨ B = That D ∨ B = Cfour D ∨ B = D := by
  obtain ⟨g, rfl⟩ := exists_cj hD
  have hz' := isCentInv_cj_std_iff.mp hz
  have hB' : cj g⁻¹ B ≤ S5Syl := le_cj_iff.mp hle
  have hn' : ∀ d ∈ S5Syl, ∀ b ∈ cj g⁻¹ B, d * b * d⁻¹ ∈ cj g⁻¹ B := by
    intro d hd b hb
    rw [mem_cj] at hb ⊢
    have h1 := hn (g * d * g⁻¹) (mem_cj_conj.mpr hd) _ hb
    simpa [mul_assoc] using h1
  have hB : B = cj g (cj g⁻¹ B) := (cj_cj_inv g B).symm
  rcases normal_cases_std hB' hn' with h | h | h | h | h | h
  · left; rw [hB, h]; exact Subgroup.map_bot _
  · right; left; rw [hB, h, hz', cj_zpowers]
  · right; right; left; rw [hB, h, ← Tsub_std, cj_Tsub]
  · right; right; right; left; rw [hB, h, ← That_std, cj_That]
  · right; right; right; right; left; rw [hB, h, ← Cfour_std, cj_Cfour]
  · right; right; right; right; right; rw [hB, h]

end CFSG.Quasithin.F53.Stellmacher.S35.Fin
