module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral

public section

namespace CFSG.Quasithin.Fan86

namespace P71

variable {G : Type*} [Group G]

theorem conj_zpow_invol {s t : G} (hs : s * s = 1) (ht : t * t = 1) (k : ℤ) :
    s * (s * t) ^ k * s = (s * t) ^ (-k) := by
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hsy : s * (s * t) * s⁻¹ = (s * t)⁻¹ := by
    rw [mul_inv_rev, hsi, hti, ← mul_assoc, hs, one_mul]
  have := conj_zpow (a := s) (b := s * t) (i := k)
  rw [hsy, inv_zpow', hsi] at this
  exact this.symm


theorem mem_closure_two_invol {s t : G} (hs : s * s = 1) (ht : t * t = 1) {n : G}
    (hn : n ∈ Subgroup.closure ({s, t} : Set G)) :
    (∃ k : ℤ, n = (s * t) ^ k) ∨ ∃ k : ℤ, n = s * (s * t) ^ k := by
  have key := conj_zpow_invol hs ht
  have hc : ∀ k : ℤ, s * (s * t) ^ k = (s * t) ^ (-k) * s := by
    intro k
    calc s * (s * t) ^ k = s * (s * t) ^ k * s * s := by rw [mul_assoc _ s s, hs, mul_one]
      _ = (s * t) ^ (-k) * s := by rw [key]
  have hc' : ∀ k : ℤ, (s * t) ^ k * s = s * (s * t) ^ (-k) := by
    intro k
    rw [hc (-k), neg_neg]
  refine Subgroup.closure_induction (p := fun n _ =>
    (∃ k : ℤ, n = (s * t) ^ k) ∨ ∃ k : ℤ, n = s * (s * t) ^ k) ?_ ?_ ?_ ?_ hn
  · intro x hx
    rcases hx with rfl | rfl
    · exact Or.inr ⟨0, by simp⟩
    · exact Or.inr ⟨1, by rw [zpow_one, ← mul_assoc, hs, one_mul]⟩
  · exact Or.inl ⟨0, by simp⟩
  · rintro x y - - (⟨a, rfl⟩ | ⟨a, rfl⟩) (⟨b, rfl⟩ | ⟨b, rfl⟩)
    · exact Or.inl ⟨a + b, by rw [zpow_add]⟩
    · exact Or.inr ⟨-a + b, by rw [← mul_assoc, hc' a, mul_assoc, ← zpow_add]⟩
    · exact Or.inr ⟨a + b, by rw [mul_assoc, ← zpow_add]⟩
    · exact Or.inl ⟨-a + b, by
        rw [mul_assoc, ← mul_assoc ((s * t) ^ a), hc' a, ← mul_assoc, ← mul_assoc, hs, one_mul,
          ← zpow_add]⟩
  · rintro x - (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · exact Or.inl ⟨-a, by rw [zpow_neg]⟩
    · refine Or.inr ⟨a, ?_⟩
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hs, ← zpow_neg, hc' (-a), neg_neg]

theorem inv_of_mem_closure {s t x : G} (hs : s * s = 1) (ht : t * t = 1)
    (hx : x ∈ Subgroup.closure ({s, t} : Set G)) (hx2 : x * x ≠ 1) : s * x * s = x⁻¹ := by
  have key := conj_zpow_invol hs ht
  rcases mem_closure_two_invol hs ht hx with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [key, zpow_neg]
  · exfalso
    apply hx2
    calc s * (s * t) ^ k * (s * (s * t) ^ k) = (s * (s * t) ^ k * s) * (s * t) ^ k := by
          simp only [mul_assoc]
      _ = 1 := by rw [key, ← zpow_add, neg_add_cancel, zpow_zero]

theorem exists_hom_dihedral_five {s x : G} (hs : s * s = 1) (hx5 : x ^ 5 = 1)
    (hinv : s * x * s = x⁻¹) : ∃ φ : DihedralGroup 5 →* G,
      (∀ i : ZMod 5, φ (DihedralGroup.r i) = x ^ i.val) ∧
        ∀ i : ZMod 5, φ (DihedralGroup.sr i) = s * x ^ i.val := by
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have s_pw : ∀ n : ℕ, s * x ^ n * s = (x ^ n)⁻¹ := by
    intro n
    have := conj_pow (a := s) (b := x) (i := n)
    rw [hsi, hinv, inv_pow] at this
    exact this.symm
  have pw_s : ∀ n : ℕ, x ^ n * s = s * (x ^ n)⁻¹ := by
    intro n
    calc x ^ n * s = s * s * (x ^ n * s) := by rw [hs, one_mul]
      _ = s * (s * x ^ n * s) := by simp only [mul_assoc]
      _ = s * (x ^ n)⁻¹ := by rw [s_pw]
  have pw_add : ∀ i j : ZMod 5, x ^ (i + j).val = x ^ i.val * x ^ j.val := by
    intro i j
    rw [ZMod.val_add, ← pow_eq_pow_mod _ hx5, pow_add]
  have pw_sub : ∀ i j : ZMod 5, x ^ (j - i).val = (x ^ i.val)⁻¹ * x ^ j.val := by
    intro i j
    have := pw_add (j - i) i
    rw [sub_add_cancel] at this
    rw [this, (Commute.pow_pow_self x _ _).eq, inv_mul_cancel_left]
  let f : DihedralGroup 5 → G := fun a =>
    match a with
    | DihedralGroup.r i => x ^ i.val
    | DihedralGroup.sr i => s * x ^ i.val
  have hf : ∀ a b, f (a * b) = f a * f b := by
    intro a b
    rcases a with i | i <;> rcases b with j | j
    · show f (DihedralGroup.r i * DihedralGroup.r j) = _
      rw [DihedralGroup.r_mul_r]
      exact pw_add i j
    · show f (DihedralGroup.r i * DihedralGroup.sr j) = x ^ i.val * (s * x ^ j.val)
      rw [DihedralGroup.r_mul_sr]
      show s * x ^ (j - i).val = _
      rw [pw_sub, ← mul_assoc (x ^ i.val), pw_s, mul_assoc]
    · show f (DihedralGroup.sr i * DihedralGroup.r j) = s * x ^ i.val * x ^ j.val
      rw [DihedralGroup.sr_mul_r]
      show s * x ^ (i + j).val = _
      rw [pw_add, mul_assoc]
    · show f (DihedralGroup.sr i * DihedralGroup.sr j) = s * x ^ i.val * (s * x ^ j.val)
      rw [DihedralGroup.sr_mul_sr]
      show x ^ (j - i).val = _
      calc x ^ (j - i).val = (x ^ i.val)⁻¹ * x ^ j.val := pw_sub i j
        _ = (s * x ^ i.val * s) * x ^ j.val := by rw [s_pw]
        _ = s * x ^ i.val * (s * x ^ j.val) := by simp only [mul_assoc]
  exact ⟨MonoidHom.mk' f hf, fun i => rfl, fun i => rfl⟩

theorem dihedral_five {s x : G} (hs : s * s = 1) (hs1 : s ≠ 1) (hx : orderOf x = 5)
    (hinv : s * x * s = x⁻¹) :
    Nonempty (↥(Subgroup.closure ({s, x} : Set G)) ≃* DihedralGroup 5) := by
  have hx5 : x ^ 5 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  obtain ⟨φ, hr, hsr⟩ := exists_hom_dihedral_five hs hx5 hinv
  have hlt : ∀ i : ZMod 5, i.val < 5 := fun i => ZMod.val_lt i
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    rcases a with i | i
    · rw [hr] at ha
      have h1 : 5 ∣ i.val := by
        have := orderOf_dvd_of_pow_eq_one ha
        rwa [hx] at this
      have h2 : i.val = 0 := Nat.eq_zero_of_dvd_of_lt h1 (hlt i)
      rw [ZMod.val_eq_zero] at h2
      rw [h2, DihedralGroup.one_def]
    · exfalso
      rw [hsr] at ha
      have h1 : x ^ i.val = s := by
        rw [eq_inv_of_mul_eq_one_right ha, inv_eq_of_mul_eq_one_right hs]
      have h2 : x ^ (2 * i.val) = 1 := by rw [pow_mul', h1, pow_two, hs]
      have h3 : 5 ∣ 2 * i.val := by
        have := orderOf_dvd_of_pow_eq_one h2
        rwa [hx] at this
      have h4 : 5 ∣ i.val := (Nat.Coprime.dvd_mul_left (by decide : Nat.Coprime 5 2)).1 h3
      have h5 : i.val = 0 := Nat.eq_zero_of_dvd_of_lt h4 (hlt i)
      rw [h5, pow_zero] at h1
      exact hs1 h1.symm
  have hrange : φ.range = Subgroup.closure ({s, x} : Set G) := by
    apply le_antisymm
    · rintro _ ⟨a, rfl⟩
      rcases a with i | i
      · rw [hr]
        exact pow_mem (Subgroup.subset_closure (by simp)) _
      · rw [hsr]
        exact mul_mem (Subgroup.subset_closure (by simp))
          (pow_mem (Subgroup.subset_closure (by simp)) _)
    · rw [Subgroup.closure_le]
      rintro g (rfl | rfl)
      · exact ⟨DihedralGroup.sr 0, by rw [hsr]; simp⟩
      · refine ⟨DihedralGroup.r 1, ?_⟩
        have h1 : (1 : ZMod 5).val = 1 := rfl
        rw [hr, h1, pow_one]
  exact ⟨(MulEquiv.subgroupCongr hrange.symm).trans (MonoidHom.ofInjective hinj).symm⟩

theorem closure_conj_eq {s x : G} (hs : s * s = 1) (hx5 : x ^ 5 = 1) (hinv : s * x * s = x⁻¹) :
    Subgroup.closure ({s, x * s * x⁻¹} : Set G) = Subgroup.closure ({s, x} : Set G) := by
  have hxs : x * s = s * x⁻¹ := by
    calc x * s = s * s * (x * s) := by rw [hs, one_mul]
      _ = s * (s * x * s) := by simp only [mul_assoc]
      _ = s * x⁻¹ := by rw [hinv]
  have h1 : x * s * x⁻¹ = s * (x⁻¹ * x⁻¹) := by rw [hxs, mul_assoc]
  have h4 : (x⁻¹ * x⁻¹) * (x⁻¹ * x⁻¹) = x := by
    have : x ^ 4 * x = 1 := by rw [← pow_succ]; exact hx5
    calc (x⁻¹ * x⁻¹) * (x⁻¹ * x⁻¹) = (x ^ 4)⁻¹ := by group
      _ = x := inv_eq_of_mul_eq_one_right this
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro g (hg | hg)
    · rw [hg]
      exact Subgroup.subset_closure (by simp)
    · rw [hg]
      exact mul_mem (mul_mem (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))) (inv_mem (Subgroup.subset_closure (by simp)))
  · rw [Subgroup.closure_le]
    rintro g (hg | hg)
    · rw [hg]
      exact Subgroup.subset_closure (by simp)
    · rw [hg]
      have hs' : s ∈ Subgroup.closure ({s, x * s * x⁻¹} : Set G) :=
        Subgroup.subset_closure (by simp)
      have hz : x * s * x⁻¹ ∈ Subgroup.closure ({s, x * s * x⁻¹} : Set G) :=
        Subgroup.subset_closure (by simp)
      have hw : x⁻¹ * x⁻¹ ∈ Subgroup.closure ({s, x * s * x⁻¹} : Set G) := by
        have : x⁻¹ * x⁻¹ = s * (x * s * x⁻¹) := by rw [h1, ← mul_assoc, hs, one_mul]
        rw [this]
        exact mul_mem hs' hz
      have := mul_mem hw hw
      rwa [h4] at this

theorem dihedral_conj {s t x : G} (hs : s * s = 1) (hs1 : s ≠ 1) (ht : t * t = 1)
    (hx : x ∈ Subgroup.closure ({s, t} : Set G)) (hx5 : orderOf x = 5) :
    Nonempty (↥(Subgroup.closure ({s, x * s * x⁻¹} : Set G)) ≃* DihedralGroup 5) := by
  have hxx : x * x ≠ 1 := by
    intro h
    have h2 : x ^ 2 = 1 := by rw [pow_two]; exact h
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hx5] at this
    omega
  have hinv := inv_of_mem_closure hs ht hx hxx
  have hx5' : x ^ 5 = 1 := by rw [← hx5]; exact pow_orderOf_eq_one x
  obtain ⟨e⟩ := dihedral_five hs hs1 hx5 hinv
  exact ⟨(MulEquiv.subgroupCongr (closure_conj_eq hs hx5' hinv)).trans e⟩

end P71

end CFSG.Quasithin.Fan86
