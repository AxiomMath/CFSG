module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral

public section

namespace CFSG.Quasithin.Fan86

open DihedralGroup

variable {G : Type*} [Group G]

theorem orderOf_r_five (c : ZMod 5) (hc : c ≠ 0) :
    orderOf (DihedralGroup.r c : DihedralGroup 5) = 5 := by
  rw [DihedralGroup.orderOf_r]
  have key : ∀ c : ZMod 5, c ≠ 0 → 5 / Nat.gcd 5 c.val = 5 := by decide
  exact key c hc

theorem exists_sr_of_sq_eq_one (g : DihedralGroup 5) (h : g * g = 1) (hg : g ≠ 1) :
    ∃ a : ZMod 5, g = DihedralGroup.sr a := by
  revert g
  decide

theorem dihedral_orderOf_rot {s e : G} (hs : s * s = 1) (he : e * e = 1) (hs1 : s ≠ 1)
    (he1 : e ≠ 1) (hne : s ≠ e)
    (φ : ↥(Subgroup.closure ({e, s} : Set G)) ≃* DihedralGroup 5) : orderOf (s * e) = 5 := by
  have hsm : s ∈ Subgroup.closure ({e, s} : Set G) := Subgroup.subset_closure (by simp)
  have hem : e ∈ Subgroup.closure ({e, s} : Set G) := Subgroup.subset_closure (by simp)
  let S : ↥(Subgroup.closure ({e, s} : Set G)) := ⟨s, hsm⟩
  let E : ↥(Subgroup.closure ({e, s} : Set G)) := ⟨e, hem⟩
  have hS2 : φ S * φ S = 1 := by
    rw [← map_mul, show S * S = 1 from Subtype.ext hs, map_one]
  have hE2 : φ E * φ E = 1 := by
    rw [← map_mul, show E * E = 1 from Subtype.ext he, map_one]
  have hS1 : φ S ≠ 1 := fun h => by
    have : S = 1 := φ.injective (h.trans (map_one φ).symm)
    exact hs1 (congrArg Subtype.val this)
  have hE1 : φ E ≠ 1 := fun h => by
    have : E = 1 := φ.injective (h.trans (map_one φ).symm)
    exact he1 (congrArg Subtype.val this)
  obtain ⟨a, ha⟩ := exists_sr_of_sq_eq_one _ hS2 hS1
  obtain ⟨b, hb⟩ := exists_sr_of_sq_eq_one _ hE2 hE1
  have hab : a ≠ b := fun h => by
    have h' : φ S = φ E := by rw [ha, hb, h]
    exact hne (congrArg Subtype.val (φ.injective h'))
  have hrot : φ (S * E) = DihedralGroup.r (b - a) := by
    rw [map_mul, ha, hb, DihedralGroup.sr_mul_sr]
  have h1 : orderOf (S * E) = 5 := by
    rw [← MulEquiv.orderOf_eq φ, hrot]
    exact orderOf_r_five _ (sub_ne_zero.2 (Ne.symm hab))
  rw [← h1, ← Subgroup.orderOf_coe]
  rfl

@[expose] def dihConj (s r : G) (i : Fin 5) : G := (r ^ (i : ℕ))⁻¹ * s * r ^ (i : ℕ)

theorem dihedral_conj_eq {s r : G} (hs : s * s = 1) (hr5 : r ^ 5 = 1) (hsr : s * r * s = r⁻¹)
    (n : ℕ) : (r ^ n)⁻¹ * s * r ^ n = r ^ (8 * n) * s := by
  have h1 : s * r = r⁻¹ * s := by
    calc s * r = s * r * (s * s) := by rw [hs, mul_one]
      _ = (s * r * s) * s := by rw [mul_assoc (s * r) s s]
      _ = r⁻¹ * s := by rw [hsr]
  have h2 : ∀ k : ℕ, s * r ^ k = (r⁻¹) ^ k * s := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc s * r ^ (k + 1) = (s * r ^ k) * r := by rw [pow_succ, mul_assoc]
        _ = (r⁻¹) ^ k * (s * r) := by rw [ih, mul_assoc]
        _ = (r⁻¹) ^ (k + 1) * s := by rw [h1, ← mul_assoc, ← pow_succ]
  have hr4 : r⁻¹ = r ^ 4 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hr5)
  calc (r ^ n)⁻¹ * s * r ^ n = (r ^ n)⁻¹ * (s * r ^ n) := by rw [mul_assoc]
    _ = (r⁻¹) ^ n * ((r⁻¹) ^ n * s) := by rw [h2, inv_pow]
    _ = (r⁻¹) ^ (n + n) * s := by rw [← mul_assoc, ← pow_add]
    _ = r ^ (8 * n) * s := by rw [hr4, ← pow_mul]; congr 2; omega

theorem dihConj_injective {s e : G} (hs : s * s = 1) (he : e * e = 1) (hr : orderOf (s * e) = 5) :
    Function.Injective (dihConj s (s * e)) := by
  have hr5 : (s * e) ^ 5 = 1 := by rw [← hr]; exact pow_orderOf_eq_one _
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have he' : e⁻¹ = e := inv_eq_of_mul_eq_one_right he
  have hsr : s * (s * e) * s = (s * e)⁻¹ := by
    rw [mul_inv_rev, hs', he', ← mul_assoc, hs, one_mul]
  intro i j hij
  have h := hij
  simp only [dihConj] at h
  rw [dihedral_conj_eq hs hr5 hsr, dihedral_conj_eq hs hr5 hsr] at h
  have h2 := mul_right_cancel h
  have h3 := pow_inj_mod.1 h2
  rw [hr] at h3
  apply Fin.ext
  omega

theorem dihedral_setup {s e : G} (hs : s * s = 1) (he : e * e = 1) (hr : orderOf (s * e) = 5) :
    (s * e) ^ 5 = 1 ∧ s * (s * e) * s = (s * e)⁻¹ := by
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have he' : e⁻¹ = e := inv_eq_of_mul_eq_one_right he
  refine ⟨by rw [← hr]; exact pow_orderOf_eq_one _, ?_⟩
  rw [mul_inv_rev, hs', he', ← mul_assoc, hs, one_mul]

theorem dihConj_eq {s e : G} (hs : s * s = 1) (he : e * e = 1) (hr : orderOf (s * e) = 5)
    (i : Fin 5) : dihConj s (s * e) i = (s * e) ^ (8 * (i : ℕ)) * s := by
  obtain ⟨hr5, hsr⟩ := dihedral_setup hs he hr
  exact dihedral_conj_eq hs hr5 hsr i

theorem dihConj_two_mul_zero {s e : G} (hs : s * s = 1) (he : e * e = 1)
    (hr : orderOf (s * e) = 5) : dihConj s (s * e) 2 * dihConj s (s * e) 0 = s * e := by
  have h16 : (s * e) ^ 16 = s * e := by
    have : (s * e) ^ 16 = (s * e) ^ 1 := by rw [pow_inj_mod, hr]
    rwa [pow_one] at this
  rw [dihConj_eq hs he hr, dihConj_eq hs he hr]
  have h2 : ((2 : Fin 5) : ℕ) = 2 := rfl
  have h0 : ((0 : Fin 5) : ℕ) = 0 := rfl
  rw [h2, h0, mul_zero, pow_zero, one_mul, mul_assoc, hs, mul_one]
  exact h16

theorem dihConj_closure {s e : G} (hs : s * s = 1) (he : e * e = 1) (hr : orderOf (s * e) = 5) :
    Subgroup.closure (Set.range (dihConj s (s * e))) = Subgroup.closure ({e, s} : Set G) := by
  have hsm : s ∈ Subgroup.closure ({e, s} : Set G) := Subgroup.subset_closure (by simp)
  have hem : e ∈ Subgroup.closure ({e, s} : Set G) := Subgroup.subset_closure (by simp)
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    have hrm : s * e ∈ Subgroup.closure ({e, s} : Set G) := Subgroup.mul_mem _ hsm hem
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ hrm _))
      hsm) (Subgroup.pow_mem _ hrm _)
  · rw [Subgroup.closure_le]
    have hs0 : s ∈ Subgroup.closure (Set.range (dihConj s (s * e))) := by
      have h1 : dihConj s (s * e) 0 ∈ Subgroup.closure (Set.range (dihConj s (s * e))) :=
        Subgroup.subset_closure ⟨0, rfl⟩
      have h2 : dihConj s (s * e) 0 = s := by simp [dihConj]
      rwa [h2] at h1
    have hr0 : s * e ∈ Subgroup.closure (Set.range (dihConj s (s * e))) := by
      have h1 : dihConj s (s * e) 2 * dihConj s (s * e) 0 ∈
          Subgroup.closure (Set.range (dihConj s (s * e))) :=
        Subgroup.mul_mem _ (Subgroup.subset_closure ⟨2, rfl⟩) (Subgroup.subset_closure ⟨0, rfl⟩)
      rwa [dihConj_two_mul_zero hs he hr] at h1
    have he0 : e ∈ Subgroup.closure (Set.range (dihConj s (s * e))) := by
      have h1 : s * (s * e) ∈ Subgroup.closure (Set.range (dihConj s (s * e))) :=
        Subgroup.mul_mem _ hs0 hr0
      rwa [← mul_assoc, hs, one_mul] at h1
    intro g hg
    rcases hg with h | h
    · rw [h]; exact he0
    · rw [h]; exact hs0

theorem dihConj_shift {s e : G} (hs : s * s = 1) (he : e * e = 1) (hr : orderOf (s * e) = 5)
    (i : Fin 5) :
    (dihConj s (s * e) 2 * dihConj s (s * e) 0)⁻¹ * dihConj s (s * e) i *
        (dihConj s (s * e) 2 * dihConj s (s * e) 0) = dihConj s (s * e) (i + 1) := by
  obtain ⟨hr5, hsr⟩ := dihedral_setup hs he hr
  rw [dihConj_two_mul_zero hs he hr, dihConj_eq hs he hr, dihConj_eq hs he hr]
  set r := s * e with hrdef
  have h1 : s * r = r⁻¹ * s := by
    calc s * r = s * r * (s * s) := by rw [hs, mul_one]
      _ = (s * r * s) * s := by rw [mul_assoc (s * r) s s]
      _ = r⁻¹ * s := by rw [hsr]
  have hr4 : r⁻¹ = r ^ 4 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hr5)
  calc r⁻¹ * (r ^ (8 * (i : ℕ)) * s) * r = r⁻¹ * (r ^ (8 * (i : ℕ)) * (s * r)) := by
        simp only [mul_assoc]
    _ = r ^ 4 * (r ^ (8 * (i : ℕ)) * (r ^ 4 * s)) := by rw [h1, hr4]
    _ = r ^ (4 + 8 * (i : ℕ) + 4) * s := by
        rw [pow_add, pow_add]
        simp only [mul_assoc]
    _ = r ^ (8 * ((i + 1 : Fin 5) : ℕ)) * s := by
        congr 1
        rw [pow_inj_mod, hr, Fin.val_add]
        simp
        omega

end CFSG.Quasithin.Fan86
