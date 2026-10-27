module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIBPair
public import CFSG.LinearAlgebra.RootGroupSL.TransvecSL

public section

namespace CFSG.StandardType.RCKK1II

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.Open
open scoped Matrix commutatorElement

theorem rckPSL_toStd_one {m : ℕ} (hm : 0 < m) :
    SpecialLinear.toStd m (fun _ : Fin m => (1 : ℤ)) =
      Pi.single 0 1 - Pi.single (Fin.last m) 1 := by
  funext a
  simp only [SpecialLinear.toStd, Pi.sub_apply, Pi.single_apply]
  by_cases h0 : a = 0
  · subst h0
    have h0last : (0 : Fin (m + 1)) ≠ Fin.last m := by
      intro h; have := congrArg Fin.val h; simp at this; omega
    simp [h0last, hm]
  · by_cases hl : a = Fin.last m
    · subst hl
      have h0last : (0 : Fin (m + 1)) ≠ Fin.last m := by
        intro h; have := congrArg Fin.val h; simp at this; omega
      simp [h0last, hm.ne']
    · have ha0 : 0 < a.val := by
        by_contra h
        have : a.val = 0 := by omega
        exact h0 (Fin.ext this)
      have ham : a.val < m := by
        by_contra h
        have : a.val = m := by have := a.isLt; omega
        exact hl (Fin.ext this)
      simp [h0, hl, ha0, ham]

theorem rckPSL_one_mem_roots {m : ℕ} (hm : 0 < m) :
    (fun _ : Fin m => (1 : ℤ)) ∈ roots (SpecialLinear.isFiniteType_A m) ∅ := by
  rw [SpecialLinear.roots_eq]
  exact ⟨0, Fin.last m, by
    intro h; have := congrArg Fin.val h; simp at this; omega, rckPSL_toStd_one hm⟩

theorem rckPSL_ht_root_le {m : ℕ} {δ : Fin m → ℤ}
    (hδ : δ ∈ roots (SpecialLinear.isFiniteType_A m) ∅) :
    CFSG.LieType.Steinberg.ht δ ≤ (m : ℤ) := by
  rw [SpecialLinear.roots_eq] at hδ
  obtain ⟨i, j, hij, hstd⟩ := hδ
  rw [SpecialLinear.ht_eq m hstd]
  have := i.isLt; have := j.isLt
  omega

theorem rckPSL_eq_zero_or_one (c : GaloisField 2 1) : c = 0 ∨ c = 1 := by
  by_cases h : c = 0
  · exact Or.inl h
  · refine Or.inr ?_
    have hcard : Nat.card (GaloisField 2 1) = 2 := by
      rw [GaloisField.card 2 1 (by norm_num)]; norm_num
    have hunits : Nat.card (GaloisField 2 1)ˣ = 1 := by
      rw [Nat.card_units, hcard]
    haveI : Subsingleton (GaloisField 2 1)ˣ := (Nat.card_eq_one_iff_unique.mp hunits).1
    have : (Units.mk0 c h : (GaloisField 2 1)ˣ) = 1 := Subsingleton.elim _ _
    exact congrArg Units.val this

private lemma rckPSL_four_aux {G : Type*} [Group G] {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) :
    a * (a * b) = b ∧ b * (a * b) = a ∧ (a * b) * a = b ∧ (a * b) * b = a ∧
      (a * b) * (a * b) = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · calc a * (a * b) = (a * a) * b := by group
      _ = 1 * b := by rw [ha]
      _ = b := one_mul b
  · calc b * (a * b) = (b * a) * b := by group
      _ = (a * b) * b := by rw [hab.symm]
      _ = a * (b * b) := by group
      _ = a * 1 := by rw [hb]
      _ = a := mul_one a
  · calc (a * b) * a = a * (b * a) := by group
      _ = a * (a * b) := by rw [hab.symm]
      _ = (a * a) * b := by group
      _ = 1 * b := by rw [ha]
      _ = b := one_mul b
  · calc (a * b) * b = a * (b * b) := by group
      _ = a * 1 := by rw [hb]
      _ = a := mul_one a
  · calc (a * b) * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hab.symm]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha, hb, one_mul]

abbrev rckPSL_four {G : Type*} [Group G] (a b : G) (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) : Subgroup G :=
  { carrier := {1, a, b, a * b}
    one_mem' := by simp
    mul_mem' := by
      obtain ⟨habb, hbab, haba, habb', habab⟩ := rckPSL_four_aux ha hb hab
      intro u v hu hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv ⊢
      rcases hu with rfl | rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl | rfl <;>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, ha, hb, hab.symm, habb, hbab,
          haba, habb', habab, one_mul, mul_one] <;>
        tauto
    inv_mem' := by
      obtain ⟨-, -, -, -, habab⟩ := rckPSL_four_aux ha hb hab
      intro u hu
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu ⊢
      rcases hu with rfl | rfl | rfl | rfl
      · exact Or.inl inv_one
      · exact Or.inr (Or.inl (inv_eq_of_mul_eq_one_right ha))
      · exact Or.inr (Or.inr (Or.inl (inv_eq_of_mul_eq_one_right hb)))
      · exact Or.inr (Or.inr (Or.inr (inv_eq_of_mul_eq_one_right habab))) }

theorem rckPSL_four_isElemAbelian {G : Type*} [Group G] {a b : G}
    (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) :
    IsElemAbelian 2 (rckPSL_four a b ha hb hab) := by
  obtain ⟨habb, hbab, haba, habb', habab⟩ := rckPSL_four_aux ha hb hab
  refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
  · intro u v
    apply Subtype.ext
    have hu : (u : G) = 1 ∨ (u : G) = a ∨ (u : G) = b ∨ (u : G) = a * b := by
      have h : (u : G) ∈ ({1, a, b, a * b} : Set G) := u.2
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h
    have hv : (v : G) = 1 ∨ (v : G) = a ∨ (v : G) = b ∨ (v : G) = a * b := by
      have h : (v : G) ∈ ({1, a, b, a * b} : Set G) := v.2
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h
    show (u : G) * (v : G) = (v : G) * (u : G)
    rcases hu with h1 | h1 | h1 | h1 <;> rcases hv with h2 | h2 | h2 | h2 <;>
      rw [h1, h2] <;>
      simp only [ha, hb, hab.symm, habb, hbab, haba, habb', habab, one_mul, mul_one]
  · intro v hv
    have hv' : (v : G) = 1 ∨ (v : G) = a ∨ (v : G) = b ∨ (v : G) = a * b := by
      have h : (v : G) ∈ ({1, a, b, a * b} : Set G) := hv
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h
    change (v : G) ^ 2 = 1
    rcases hv' with h | h | h | h
    · rw [h]; simp
    · rw [h]; simpa only [pow_two] using ha
    · rw [h]; simpa only [pow_two] using hb
    · rw [h]; simpa only [pow_two] using habab

@[expose] def rckPSL_row {F : Type} [Zero F] {m : ℕ} (a : Fin (m + 1) → F) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) F :=
  Matrix.of (fun i j => if i = 0 then a j else 0)

private lemma rckPSL_row_apply {F : Type} [Zero F] {m : ℕ} (a : Fin (m + 1) → F)
    (i j : Fin (m + 1)) : rckPSL_row a i j = if i = 0 then a j else 0 := rfl

private lemma rckPSL_row_mul {F : Type} [Field F] {m : ℕ} {a b : Fin (m + 1) → F}
    (ha : a 0 = 0) : rckPSL_row a * rckPSL_row b = 0 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  by_cases hi : i = 0
  · subst hi
    rw [Finset.sum_eq_single 0]
    · simp [rckPSL_row_apply, ha]
    · intro k _ hk
      simp [rckPSL_row_apply, hk]
    · intro h; exact absurd (Finset.mem_univ 0) h
  · refine Finset.sum_eq_zero fun k _ => ?_
    simp [rckPSL_row_apply, hi]

private lemma rckPSL_row_add {F : Type} [Field F] {m : ℕ} (a b : Fin (m + 1) → F) :
    rckPSL_row a + rckPSL_row b = rckPSL_row (a + b) := by
  ext i j
  by_cases hi : i = 0 <;> simp [rckPSL_row_apply, hi, Pi.add_apply]

lemma rckPSL_row_sq {F : Type} [Field F] [CharP F 2] {m : ℕ} {a : Fin (m + 1) → F}
    (ha : a 0 = 0) : (1 + rckPSL_row a) * (1 + rckPSL_row a) = 1 := by
  calc (1 + rckPSL_row a) * (1 + rckPSL_row a)
      = 1 + rckPSL_row a + rckPSL_row a + rckPSL_row a * rckPSL_row a := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one]
        abel
    _ = 1 + (rckPSL_row a + rckPSL_row a) + rckPSL_row a * rckPSL_row a := by abel
    _ = 1 + 0 + 0 := by rw [rckPSL_row_mul ha, CharTwo.add_self_eq_zero]
    _ = 1 := by simp

@[expose] def rckPSL_rad {F : Type} [Field F] [CharP F 2] {m : ℕ} :
    Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) F) where
  carrier := {g | ∃ a : Fin (m + 1) → F, a 0 = 0 ∧
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = 1 + rckPSL_row a}
  one_mem' := ⟨0, rfl, by
    rw [Matrix.SpecialLinearGroup.coe_one]
    ext i j
    simp [rckPSL_row_apply]⟩
  mul_mem' := by
    rintro g h ⟨a, ha, hga⟩ ⟨b, hb, hgb⟩
    refine ⟨a + b, by simp [ha, hb], ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_mul, hga, hgb]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one,
      rckPSL_row_mul ha, add_zero, ← rckPSL_row_add]
    abel
  inv_mem' := by
    rintro g ⟨a, ha, hga⟩
    refine ⟨a, ha, ?_⟩
    have hgg : g * g = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, hga, rckPSL_row_sq ha,
        Matrix.SpecialLinearGroup.coe_one]
    rw [show g⁻¹ = g from inv_eq_of_mul_eq_one_left hgg, hga]

lemma rckPSL_rad_comm {F : Type} [Field F] [CharP F 2] {m : ℕ}
    {g h : Matrix.SpecialLinearGroup (Fin (m + 1)) F}
    (hg : g ∈ rckPSL_rad (F := F) (m := m)) (hh : h ∈ rckPSL_rad (F := F) (m := m)) :
    g * h = h * g := by
  obtain ⟨a, ha, hga⟩ := hg
  obtain ⟨b, hb, hgb⟩ := hh
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hga, hgb]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one,
    rckPSL_row_mul ha, rckPSL_row_mul hb, add_zero]
  abel

private lemma rckPSL_row_single {F : Type} [Zero F] [One F] {m : ℕ}
    (j : Fin (m + 1)) :
    rckPSL_row (Pi.single j (1 : F)) = Matrix.single (0 : Fin (m + 1)) j 1 := by
  ext i' j'
  by_cases h : i' = 0
  · subst h
    by_cases h2 : j' = j
    · subst h2; simp [rckPSL_row_apply, Matrix.single_apply, Pi.single_apply]
    · simp [rckPSL_row_apply, Matrix.single_apply, Pi.single_apply, h2, Ne.symm h2]
  · simp [rckPSL_row_apply, Matrix.single_apply, Pi.single_apply, h, Ne.symm h]

lemma rckPSL_row_mulVec {F : Type} [Field F] {m : ℕ} (a : Fin (m + 1) → F)
    (v : Fin (m + 1) → F) :
    rckPSL_row a *ᵥ v = (∑ k, a k * v k) • Pi.single (0 : Fin (m + 1)) (1 : F) := by
  funext i
  show (∑ j, rckPSL_row a i j * v j) = ((∑ k, a k * v k) • Pi.single (0 : Fin (m + 1)) 1) i
  rw [Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  by_cases hi : i = 0
  · subst hi
    simp [rckPSL_row_apply]
  · simp [rckPSL_row_apply, hi]

lemma rckPSL_single_mulVec {F : Type} [Field F] {m : ℕ} (v : Fin (m + 1) → F) :
    Matrix.single (0 : Fin (m + 1)) (Fin.last m) (1 : F) *ᵥ v =
      (v (Fin.last m)) • Pi.single (0 : Fin (m + 1)) (1 : F) := by
  rw [Matrix.single_mulVec]
  funext i
  rw [Function.update_apply, Pi.smul_apply, Pi.single_apply]
  by_cases hi : i = 0 <;> simp [hi]

lemma rckPSL_transvection_mem_rad {m : ℕ} {i j : Fin (m + 1)}
    (hij : i ≠ j) (hi : i = 0) (hj : j ≠ 0) :
    Matrix.SpecialLinearGroup.transvection hij (1 : GaloisField 2 1) ∈
      rckPSL_rad (F := GaloisField 2 1) (m := m) := by
  subst hi
  refine ⟨Pi.single j 1, by simp [Pi.single_apply, hj, eq_comm], ?_⟩
  rw [Matrix.SpecialLinearGroup.transvection_coe, rckPSL_row_single j]

end CFSG.StandardType.RCKK1II
