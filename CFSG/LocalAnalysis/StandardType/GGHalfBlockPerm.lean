module

public import CFSG.LocalAnalysis.StandardType.GGHalfBlockTorus

public section

namespace CFSG.StandardType.GGHalf

open CFSG.LieType.Universal.SpecialLinear Matrix

private theorem fin_ofNat_ne {n : ℕ} [NeZero n] {a b : ℕ} (ha : a < n) (hb : b < n)
    (hab : a ≠ b) : Fin.ofNat n a ≠ Fin.ofNat n b := by
  intro h
  have h' := congrArg Fin.val h
  rw [Fin.val_ofNat, Fin.val_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h'
  exact hab h'

private theorem transvection_one_mul_self {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    SpecialLinearGroup.transvection hij (1 : F2) * SpecialLinearGroup.transvection hij 1 = 1 := by
  have hneg : (-1 : F2) = 1 := by
    rw [neg_eq_iff_add_eq_zero, one_add_one_eq_two, gf2_two]
  have ht := Matrix.SpecialLinearGroup.transvection_mul_neg hij (1 : F2)
  rwa [hneg] at ht

private theorem transvection_one_inv {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    (SpecialLinearGroup.transvection hij (1 : F2))⁻¹ = SpecialLinearGroup.transvection hij 1 :=
  inv_eq_of_mul_eq_one_right (transvection_one_mul_self hij)

private theorem transvection_congr {n : ℕ} {i j i' j' : Fin n} (hi : i = i') (hj : j = j')
    (hij : i ≠ j) (hij' : i' ≠ j') (c : F2) :
    SpecialLinearGroup.transvection hij c = SpecialLinearGroup.transvection hij' c := by
  apply Subtype.ext
  rw [SpecialLinearGroup.transvection_coe, SpecialLinearGroup.transvection_coe, hi, hj]

private theorem mul_inv_mul_mul_self {G : Type*} [Group G] {x y : G} (hx : x * x = 1) :
    (x * y * x) * x = x * y := by
  rw [mul_assoc (x * y) x x, hx, mul_one]

private theorem commute_inv_of_commute {G : Type*} [Group G] {a b : G} (h : a * b = b * a) :
    a * b⁻¹ = b⁻¹ * a := by
  have h1 : b⁻¹ * a * b = a := by
    rw [mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]
  have h2 : b⁻¹ * a = a * b⁻¹ := by
    have := congrArg (· * b⁻¹) h1
    simpa [mul_assoc] using this
  exact h2.symm

private theorem omegaBlock_eq_mul (n : ℕ) (k : Fin n) :
    omegaBlock n k =
      SpecialLinearGroup.transvection (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne
          (1 : F2) *
        SpecialLinearGroup.transvection
          (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne.symm 1 := by
  have hx2 : SpecialLinearGroup.transvection
        (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne (1 : F2) *
      SpecialLinearGroup.transvection
        (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne 1 = 1 :=
    transvection_one_mul_self _
  have hneg : (-1 : F2) = 1 := by
    rw [neg_eq_iff_add_eq_zero, one_add_one_eq_two, gf2_two]
  rw [omegaBlock, weylRep, hneg]
  exact mul_inv_mul_mul_self hx2

private theorem slPerm_conj_transvection {n : ℕ} (π : Equiv.Perm (Fin (n + 1)))
    {i j : Fin (n + 1)} (hij : i ≠ j) (c : F2) :
    slPerm gf2_two π * SpecialLinearGroup.transvection hij c * (slPerm gf2_two π)⁻¹ =
      SpecialLinearGroup.transvection (π.injective.ne hij) c := by
  have h := conj_transvection_of_coe_eq_signedPerm (g := slPerm gf2_two π)
    (coe_slPerm gf2_two π) (fun s => by simp) hij c
  simpa using h

private theorem mem_conj_closure_of_mem_conj_gens {G : Type*} [Group G] (s : Set G)
    (H : Subgroup G) (c : G) (hH : H = Subgroup.closure s)
    (hgen : ∀ x ∈ s, c * x * c⁻¹ ∈ H) : ∀ t ∈ H, c * t * c⁻¹ ∈ H := by
  intro t ht
  rw [hH] at ht
  induction ht using Subgroup.closure_induction with
  | mem y hy => exact hgen y hy
  | one => simp
  | mul y z _ _ ihy ihz =>
      rw [show c * (y * z) * c⁻¹ = (c * y * c⁻¹) * (c * z * c⁻¹) by group]
      exact mul_mem ihy ihz
  | inv y _ ihy =>
      rw [show c * y⁻¹ * c⁻¹ = (c * y * c⁻¹)⁻¹ by group]
      exact inv_mem ihy

theorem commute_omegaBlock_slOn {n : ℕ} {S : Set (Fin (n + 1))} {k : Fin n}
    (hk : k.castSucc ∉ S ∧ k.succ ∉ S) {g : SpecialLinearGroup (Fin (n + 1)) F2}
    (hg : g ∈ slOn (n + 1) S) : omegaBlock n k * g = g * omegaBlock n k := by
  rw [slOn] at hg
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
      obtain ⟨a, b, hab, c, ha, hb, rfl⟩ := hy
      have hai : a ≠ k.castSucc := fun h => hk.1 (h ▸ ha)
      have haj : a ≠ k.succ := fun h => hk.2 (h ▸ ha)
      have hbi : b ≠ k.castSucc := fun h => hk.1 (h ▸ hb)
      have hbj : b ≠ k.succ := fun h => hk.2 (h ▸ hb)
      have h : k.castSucc ≠ k.succ :=
        (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne
      rw [omegaBlock_eq_mul]
      have hzx : Commute (SpecialLinearGroup.transvection hab c)
          (SpecialLinearGroup.transvection h 1) :=
        Matrix.SpecialLinearGroup.commute_transvection hab h hbi haj.symm c 1
      have hzy : Commute (SpecialLinearGroup.transvection hab c)
          (SpecialLinearGroup.transvection h.symm 1) :=
        Matrix.SpecialLinearGroup.commute_transvection hab h.symm hbj hai.symm c 1
      exact (hzx.mul_right hzy).eq.symm
  | one => simp
  | mul y z _ _ ihy ihz =>
      calc omegaBlock n k * (y * z)
          = (omegaBlock n k * y) * z := (mul_assoc _ _ _).symm
        _ = (y * omegaBlock n k) * z := by rw [ihy]
        _ = y * (omegaBlock n k * z) := mul_assoc _ _ _
        _ = y * (z * omegaBlock n k) := by rw [ihz]
        _ = (y * z) * omegaBlock n k := (mul_assoc _ _ _).symm
  | inv y _ ihy => exact commute_inv_of_commute ihy

theorem slPerm_conj_omegaBlock {n : ℕ} (π : Equiv.Perm (Fin (n + 1))) {k k' : Fin n}
    (h0 : π k.castSucc = k'.castSucc) (h1 : π k.succ = k'.succ) :
    slPerm gf2_two π * omegaBlock n k * (slPerm gf2_two π)⁻¹ = omegaBlock n k' := by
  have h : k.castSucc ≠ k.succ := (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne
  have h' : k'.castSucc ≠ k'.succ := (show k'.castSucc < k'.succ from Fin.castSucc_lt_succ).ne
  rw [omegaBlock_eq_mul (n := n) (k := k), omegaBlock_eq_mul (n := n) (k := k')]
  rw [show slPerm gf2_two π *
        (SpecialLinearGroup.transvection h (1 : F2) *
          SpecialLinearGroup.transvection h.symm 1) * (slPerm gf2_two π)⁻¹ =
      (slPerm gf2_two π * SpecialLinearGroup.transvection h 1 * (slPerm gf2_two π)⁻¹) *
        (slPerm gf2_two π * SpecialLinearGroup.transvection h.symm 1 *
          (slPerm gf2_two π)⁻¹) by group]
  rw [slPerm_conj_transvection π h 1,
      transvection_congr h0 h1 (π.injective.ne h) h' 1,
      slPerm_conj_transvection π h.symm 1,
      transvection_congr h1 h0 (π.injective.ne h.symm) h'.symm 1]

theorem slPerm_conj_omegaBlock_inv {n : ℕ} (π : Equiv.Perm (Fin (n + 1))) {k k' : Fin n}
    (h0 : π k.castSucc = k'.succ) (h1 : π k.succ = k'.castSucc) :
    slPerm gf2_two π * omegaBlock n k * (slPerm gf2_two π)⁻¹ = (omegaBlock n k')⁻¹ := by
  have h : k.castSucc ≠ k.succ := (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne
  have h' : k'.castSucc ≠ k'.succ := (show k'.castSucc < k'.succ from Fin.castSucc_lt_succ).ne
  rw [omegaBlock_eq_mul (n := n) (k := k), omegaBlock_eq_mul (n := n) (k := k')]
  rw [show slPerm gf2_two π *
        (SpecialLinearGroup.transvection h (1 : F2) *
          SpecialLinearGroup.transvection h.symm 1) * (slPerm gf2_two π)⁻¹ =
      (slPerm gf2_two π * SpecialLinearGroup.transvection h 1 * (slPerm gf2_two π)⁻¹) *
        (slPerm gf2_two π * SpecialLinearGroup.transvection h.symm 1 *
          (slPerm gf2_two π)⁻¹) by group]
  rw [slPerm_conj_transvection π h 1,
      transvection_congr h0 h1 (π.injective.ne h) h'.symm 1,
      slPerm_conj_transvection π h.symm 1,
      transvection_congr h1 h0 (π.injective.ne h.symm) h' 1,
      _root_.mul_inv_rev, transvection_one_inv h'.symm, transvection_one_inv h']

private theorem slPerm_swap_zero_one_conj_halfTorus (n : ℕ) (hn : 0 < n) :
    ∀ t ∈ halfTorus n,
      slPerm gf2_two (Equiv.swap (0 : Fin (n + 1)) 1) * t *
        (slPerm gf2_two (Equiv.swap (0 : Fin (n + 1)) 1))⁻¹ ∈ halfTorus n := by
  haveI : NeZero n := ⟨hn.ne'⟩
  refine mem_conj_closure_of_mem_conj_gens
    {x | ∃ k : Fin n, k.val % 2 = 0 ∧ x = omegaBlock n k} (halfTorus n)
    (slPerm gf2_two (Equiv.swap (0 : Fin (n + 1)) 1)) rfl ?_
  rintro x ⟨k, hk2, rfl⟩
  rcases eq_or_ne k (0 : Fin n) with hk | hk
  · rw [hk]
    have hc : (0 : Fin n).castSucc = (0 : Fin (n + 1)) := Fin.castSucc_zero
    have hs : (0 : Fin n).succ = (1 : Fin (n + 1)) := by
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_zero, Fin.coe_ofNat_eq_mod,
        Nat.mod_eq_of_lt (show (1:ℕ) < n + 1 by omega), Nat.zero_mod]
    have h0 : Equiv.swap (0 : Fin (n + 1)) 1 (0 : Fin n).castSucc = (0 : Fin n).succ := by
      rw [hc, hs, Equiv.swap_apply_left]
    have h1 : Equiv.swap (0 : Fin (n + 1)) 1 (0 : Fin n).succ = (0 : Fin n).castSucc := by
      rw [hs, hc, Equiv.swap_apply_right]
    rw [slPerm_conj_omegaBlock_inv (Equiv.swap (0 : Fin (n + 1)) 1) h0 h1]
    exact inv_mem (Subgroup.subset_closure ⟨0, by norm_num, rfl⟩)
  · have hk0 : k.val ≠ 0 := by
      intro hv
      exact hk (Fin.ext (by simpa using hv))
    have hkval2 : 2 ≤ k.val :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) (Nat.dvd_of_mod_eq_zero hk2)
    have hkc0 : k.castSucc ≠ (0 : Fin (n + 1)) := by
      intro h; have := congrArg Fin.val h
      rw [Fin.val_castSucc, Fin.val_zero] at this
      exact hk0 this
    have hkc1 : k.castSucc ≠ 1 := by
      intro h; have := congrArg Fin.val h
      rw [Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
        Nat.mod_eq_of_lt (show (1:ℕ) < n + 1 by omega)] at this
      omega
    have hks0 : k.succ ≠ (0 : Fin (n + 1)) := by
      intro h; have := congrArg Fin.val h
      rw [Fin.val_succ, Fin.val_zero] at this; omega
    have hks1 : k.succ ≠ 1 := by
      intro h; have := congrArg Fin.val h
      rw [Fin.val_succ, Fin.coe_ofNat_eq_mod,
        Nat.mod_eq_of_lt (show (1:ℕ) < n + 1 by omega)] at this
      omega
    have h0 : Equiv.swap (0 : Fin (n + 1)) 1 k.castSucc = k.castSucc :=
      Equiv.swap_apply_of_ne_of_ne hkc0 hkc1
    have h1 : Equiv.swap (0 : Fin (n + 1)) 1 k.succ = k.succ :=
      Equiv.swap_apply_of_ne_of_ne hks0 hks1
    rw [slPerm_conj_omegaBlock (Equiv.swap (0 : Fin (n + 1)) 1) h0 h1]
    exact Subgroup.subset_closure ⟨k, hk2, rfl⟩

theorem weylRep_zero_conj_halfTorus (m : ℕ) {t : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2}
    (ht : t ∈ halfTorus (m + 1 + 1)) :
    weylRep (m + 1 + 1) F2 ⟨0, by omega⟩ * t * (weylRep (m + 1 + 1) F2 ⟨0, by omega⟩)⁻¹ ∈
      halfTorus (m + 1 + 1) := by
  have hc : weylRep (m + 1 + 1) F2 (⟨0, by omega⟩ : Fin (m + 1 + 1)) =
      slPerm gf2_two (Equiv.swap (0 : Fin (m + 1 + 1 + 1)) 1) := by
    rw [← slPerm_swap_castSucc_succ (F := F2) gf2_two (⟨0, by omega⟩ : Fin (m + 1 + 1)),
      show (⟨0, by omega⟩ : Fin (m + 1 + 1)) = (0 : Fin (m + 1 + 1)) from Fin.ext rfl,
      Fin.castSucc_zero, Fin.succ_zero_eq_one]
  rw [hc]
  exact slPerm_swap_zero_one_conj_halfTorus (m + 1 + 1) (by omega) t ht

theorem sigmaPerm_apply_zero (m : ℕ) (hm : 1 ≤ m) :
    sigmaPerm m (0 : Fin (m + 1 + 1 + 1)) = 2 := by
  rw [sigmaPerm, Equiv.Perm.mul_apply]
  have h : (Equiv.swap (1 : Fin (m + 1 + 1 + 1)) 3) 0 = 0 :=
    Equiv.swap_apply_of_ne_of_ne
      (fin_ofNat_ne (n := m + 1 + 1 + 1) (a := 0) (b := 1) (by omega) (by omega) (by norm_num))
      (fin_ofNat_ne (n := m + 1 + 1 + 1) (a := 0) (b := 3) (by omega) (by omega) (by norm_num))
  rw [h, Equiv.swap_apply_left]

theorem sigmaPerm_apply_one (m : ℕ) (hm : 1 ≤ m) :
    sigmaPerm m (1 : Fin (m + 1 + 1 + 1)) = 3 := by
  rw [sigmaPerm, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
  have h : (Equiv.swap (0 : Fin (m + 1 + 1 + 1)) 2) 3 = 3 :=
    Equiv.swap_apply_of_ne_of_ne
      (fin_ofNat_ne (n := m + 1 + 1 + 1) (a := 3) (b := 0) (by omega) (by omega) (by norm_num))
      (fin_ofNat_ne (n := m + 1 + 1 + 1) (a := 3) (b := 2) (by omega) (by omega) (by norm_num))
  rw [h]

theorem sigmaPerm_apply_two (m : ℕ) (hm : 1 ≤ m) :
    sigmaPerm m (2 : Fin (m + 1 + 1 + 1)) = 0 := by
  rw [sigmaPerm, Equiv.Perm.mul_apply]
  have h : (Equiv.swap (1 : Fin (m + 1 + 1 + 1)) 3) 2 = 2 :=
    Equiv.swap_apply_of_ne_of_ne
      (fin_ofNat_ne (n := m + 1 + 1 + 1) (a := 2) (b := 1) (by omega) (by omega) (by norm_num))
      (fin_ofNat_ne (n := m + 1 + 1 + 1) (a := 2) (b := 3) (by omega) (by omega) (by norm_num))
  rw [h, Equiv.swap_apply_right]

theorem sigmaPerm_apply_three (m : ℕ) (hm : 1 ≤ m) :
    sigmaPerm m (3 : Fin (m + 1 + 1 + 1)) = 1 := by
  rw [sigmaPerm, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
  have h : (Equiv.swap (0 : Fin (m + 1 + 1 + 1)) 2) 1 = 1 :=
    Equiv.swap_apply_of_ne_of_ne
      (fin_ofNat_ne (n := m + 1 + 1 + 1) (a := 1) (b := 0) (by omega) (by omega) (by norm_num))
      (fin_ofNat_ne (n := m + 1 + 1 + 1) (a := 1) (b := 2) (by omega) (by omega) (by norm_num))
  rw [h]

theorem sigmaPerm_apply_of_fixed (m : ℕ) {i : Fin (m + 1 + 1 + 1)}
    (hi0 : i ≠ 0) (hi1 : i ≠ 1) (hi2 : i ≠ 2) (hi3 : i ≠ 3) :
    sigmaPerm m i = i := by
  rw [sigmaPerm, Equiv.Perm.mul_apply]
  rw [Equiv.swap_apply_of_ne_of_ne hi1 hi3, Equiv.swap_apply_of_ne_of_ne hi0 hi2]

theorem tauPerm_apply_zero (m : ℕ) :
    tauPerm m (0 : Fin (m + 1 + 1 + 1)) = (Fin.last (m + 1)).castSucc := by
  rw [tauPerm, Equiv.Perm.mul_apply]
  have h : (Equiv.swap (Fin.last (m + 1 + 1)) 1) 0 = 0 :=
    Equiv.swap_apply_of_ne_of_ne
      (by
        intro h; have := congrArg Fin.val h
        rw [Fin.val_zero, Fin.val_last] at this; omega)
      (fin_ofNat_ne (n := m + 1 + 1 + 1) (a := 0) (b := 1) (by omega) (by omega) (by norm_num))
  rw [h, Equiv.swap_apply_right]

theorem tauPerm_apply_one (m : ℕ) :
    tauPerm m (1 : Fin (m + 1 + 1 + 1)) = Fin.last (m + 1 + 1) := by
  rw [tauPerm, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
  have h : (Equiv.swap ((Fin.last (m + 1)).castSucc) 0) (Fin.last (m + 1 + 1)) =
      Fin.last (m + 1 + 1) :=
    Equiv.swap_apply_of_ne_of_ne
      (by
        intro h; have := congrArg Fin.val h
        rw [Fin.val_last, Fin.val_castSucc, Fin.val_last] at this; omega)
      (by
        intro h; have := congrArg Fin.val h
        rw [Fin.val_last, Fin.val_zero] at this; omega)
  rw [h]

theorem tauPerm_apply_lastCast (m : ℕ) (hm : 1 ≤ m) :
    tauPerm m ((Fin.last (m + 1)).castSucc : Fin (m + 1 + 1 + 1)) = 0 := by
  rw [tauPerm, Equiv.Perm.mul_apply]
  have h : (Equiv.swap (Fin.last (m + 1 + 1)) 1) ((Fin.last (m + 1)).castSucc) =
      (Fin.last (m + 1)).castSucc :=
    Equiv.swap_apply_of_ne_of_ne
      (by
        intro h; have := congrArg Fin.val h
        rw [Fin.val_castSucc, Fin.val_last, Fin.val_last] at this; omega)
      (by
        intro h; have := congrArg Fin.val h
        rw [Fin.val_castSucc, Fin.val_last, Fin.coe_ofNat_eq_mod,
          Nat.mod_eq_of_lt (show (1:ℕ) < m + 1 + 1 + 1 by omega)] at this; omega)
  rw [h, Equiv.swap_apply_left]

theorem tauPerm_apply_lastSucc (m : ℕ) (hm : 1 ≤ m) :
    tauPerm m (Fin.last (m + 1 + 1)) = 1 := by
  rw [tauPerm, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
  have h : (Equiv.swap ((Fin.last (m + 1)).castSucc) 0) (1 : Fin (m + 1 + 1 + 1)) =
      (1 : Fin (m + 1 + 1 + 1)) :=
    Equiv.swap_apply_of_ne_of_ne
      (by
        intro h; have := congrArg Fin.val h
        rw [Fin.coe_ofNat_eq_mod,
          Nat.mod_eq_of_lt (show (1:ℕ) < m + 1 + 1 + 1 by omega),
          Fin.val_castSucc, Fin.val_last] at this; omega)
      (by
        intro h; have := congrArg Fin.val h
        rw [Fin.coe_ofNat_eq_mod,
          Nat.mod_eq_of_lt (show (1:ℕ) < m + 1 + 1 + 1 by omega), Fin.val_zero] at this; omega)
  rw [h]

theorem tauPerm_apply_of_fixed (m : ℕ) {i : Fin (m + 1 + 1 + 1)}
    (hi0 : i ≠ 0) (hi1 : i ≠ 1) (hiA : i ≠ (Fin.last (m + 1)).castSucc)
    (hiB : i ≠ Fin.last (m + 1 + 1)) : tauPerm m i = i := by
  rw [tauPerm, Equiv.Perm.mul_apply]
  rw [Equiv.swap_apply_of_ne_of_ne hiB hi1, Equiv.swap_apply_of_ne_of_ne hiA hi0]

theorem slPerm_sigma_conj_halfTorus (m : ℕ) (hm : 1 ≤ m)
    {t : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2} (ht : t ∈ halfTorus (m + 1 + 1)) :
    slPerm gf2_two (sigmaPerm m) * t * (slPerm gf2_two (sigmaPerm m))⁻¹ ∈
      halfTorus (m + 1 + 1) := by
  refine mem_conj_closure_of_mem_conj_gens
    {x | ∃ k : Fin (m + 1 + 1), k.val % 2 = 0 ∧ x = omegaBlock (m + 1 + 1) k}
    (halfTorus (m + 1 + 1)) (slPerm gf2_two (sigmaPerm m)) rfl ?_ t ht
  rintro x ⟨k, hk2, rfl⟩
  rcases eq_or_ne k (0 : Fin (m + 1 + 1)) with hk | hk
  · rw [hk]
    have h0 : sigmaPerm m (0 : Fin (m + 1 + 1)).castSucc =
        (⟨2, by omega⟩ : Fin (m + 1 + 1)).castSucc := by
      rw [Fin.castSucc_zero, sigmaPerm_apply_zero m hm]
      apply Fin.ext
      rw [Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
        Nat.mod_eq_of_lt (show (2:ℕ) < m + 1 + 1 + 1 by omega)]
    have h1 : sigmaPerm m (0 : Fin (m + 1 + 1)).succ =
        (⟨2, by omega⟩ : Fin (m + 1 + 1)).succ := by
      rw [show (0 : Fin (m + 1 + 1)).succ = (1 : Fin (m + 1 + 1 + 1)) from
          Fin.succ_zero_eq_one,
        sigmaPerm_apply_one m hm]
      apply Fin.ext
      rw [Fin.val_succ, Fin.coe_ofNat_eq_mod,
        Nat.mod_eq_of_lt (show (3:ℕ) < m + 1 + 1 + 1 by omega)]
    rw [slPerm_conj_omegaBlock (sigmaPerm m) h0 h1]
    exact Subgroup.subset_closure ⟨⟨2, by omega⟩, by norm_num, rfl⟩
  · rcases eq_or_ne k (⟨2, by omega⟩ : Fin (m + 1 + 1)) with hk2' | hk2'
    · rw [hk2']
      have h0 : sigmaPerm m (⟨2, by omega⟩ : Fin (m + 1 + 1)).castSucc =
          (0 : Fin (m + 1 + 1)).castSucc := by
        rw [show ((⟨2, by omega⟩ : Fin (m + 1 + 1)).castSucc : Fin (m + 1 + 1 + 1)) =
            2 from by
              apply Fin.ext
              rw [Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
                Nat.mod_eq_of_lt (show (2:ℕ) < m + 1 + 1 + 1 by omega)],
            sigmaPerm_apply_two m hm]
        exact Fin.castSucc_zero.symm
      have h1 : sigmaPerm m (⟨2, by omega⟩ : Fin (m + 1 + 1)).succ =
          (0 : Fin (m + 1 + 1)).succ := by
        rw [show ((⟨2, by omega⟩ : Fin (m + 1 + 1)).succ : Fin (m + 1 + 1 + 1)) =
            3 from by
              apply Fin.ext
              rw [Fin.val_succ, Fin.coe_ofNat_eq_mod,
                Nat.mod_eq_of_lt (show (3:ℕ) < m + 1 + 1 + 1 by omega)],
            sigmaPerm_apply_three m hm]
        exact Fin.succ_zero_eq_one.symm
      rw [slPerm_conj_omegaBlock (sigmaPerm m) h0 h1]
      exact Subgroup.subset_closure ⟨0, by norm_num, rfl⟩
    · have hk0 : k.val ≠ 0 := by
        intro hv; exact hk (Fin.ext (by simpa using hv))
      have hk2n : k.val ≠ 2 := by
        intro hv; exact hk2' (Fin.ext (by simpa using hv))
      have hkval4 : 4 ≤ k.val := by
        rcases Nat.dvd_of_mod_eq_zero hk2 with ⟨t, ht2⟩
        have ht0 : t ≠ 0 := by rintro rfl; exact hk0 (by omega)
        have ht1 : t ≠ 1 := by rintro rfl; exact hk2n (by omega)
        omega
      have hkc0 : k.castSucc ≠ (0 : Fin (m + 1 + 1 + 1)) := by
        intro h; have := congrArg Fin.val h
        rw [Fin.val_castSucc, Fin.val_zero] at this; omega
      have hkc1 : k.castSucc ≠ 1 := by
        intro h; have := congrArg Fin.val h
        rw [Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
          Nat.mod_eq_of_lt (show (1:ℕ) < m + 1 + 1 + 1 by omega)] at this; omega
      have hkc2 : k.castSucc ≠ 2 := by
        intro h; have := congrArg Fin.val h
        rw [Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
          Nat.mod_eq_of_lt (show (2:ℕ) < m + 1 + 1 + 1 by omega)] at this; omega
      have hkc3 : k.castSucc ≠ 3 := by
        intro h; have := congrArg Fin.val h
        rw [Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
          Nat.mod_eq_of_lt (show (3:ℕ) < m + 1 + 1 + 1 by omega)] at this; omega
      have hks0 : k.succ ≠ (0 : Fin (m + 1 + 1 + 1)) := by
        intro h; have := congrArg Fin.val h
        rw [Fin.val_succ, Fin.val_zero] at this; omega
      have hks1 : k.succ ≠ 1 := by
        intro h; have := congrArg Fin.val h
        rw [Fin.val_succ, Fin.coe_ofNat_eq_mod,
          Nat.mod_eq_of_lt (show (1:ℕ) < m + 1 + 1 + 1 by omega)] at this; omega
      have hks2 : k.succ ≠ 2 := by
        intro h; have := congrArg Fin.val h
        rw [Fin.val_succ, Fin.coe_ofNat_eq_mod,
          Nat.mod_eq_of_lt (show (2:ℕ) < m + 1 + 1 + 1 by omega)] at this; omega
      have hks3 : k.succ ≠ 3 := by
        intro h; have := congrArg Fin.val h
        rw [Fin.val_succ, Fin.coe_ofNat_eq_mod,
          Nat.mod_eq_of_lt (show (3:ℕ) < m + 1 + 1 + 1 by omega)] at this; omega
      have h0 : sigmaPerm m k.castSucc = k.castSucc :=
        sigmaPerm_apply_of_fixed m hkc0 hkc1 hkc2 hkc3
      have h1 : sigmaPerm m k.succ = k.succ :=
        sigmaPerm_apply_of_fixed m hks0 hks1 hks2 hks3
      rw [slPerm_conj_omegaBlock (sigmaPerm m) h0 h1]
      exact Subgroup.subset_closure ⟨k, hk2, rfl⟩

theorem weylRep_last_conj_halfTorusK (m : ℕ)
    {t : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2} (ht : t ∈ halfTorusK (m + 1 + 1)) :
    weylRep (m + 1 + 1) F2 ⟨m + 1, by omega⟩ * t *
        (weylRep (m + 1 + 1) F2 ⟨m + 1, by omega⟩)⁻¹ ∈ halfTorusK (m + 1 + 1) := by
  let kL : Fin (m + 1 + 1) := ⟨m + 1, by omega⟩
  have hc : weylRep (m + 1 + 1) F2 (⟨m + 1, by omega⟩ : Fin (m + 1 + 1)) =
      slPerm gf2_two (Equiv.swap kL.castSucc kL.succ) := by
    rw [slPerm_swap_castSucc_succ (F := F2) gf2_two kL]
  rw [hc]
  refine mem_conj_closure_of_mem_conj_gens
    {x | ∃ k : Fin (m + 1 + 1),
      (k.val + 1 = m + 1 + 1 ∨ (k.val % 2 = 0 ∧ k.val + 2 < m + 1 + 1)) ∧
        x = omegaBlock (m + 1 + 1) k}
    (halfTorusK (m + 1 + 1)) (slPerm gf2_two (Equiv.swap kL.castSucc kL.succ)) rfl ?_ t ht
  rintro x ⟨k, hk, rfl⟩
  rcases hk with hkA | ⟨hk2, hkB⟩
  · have hk_eq : k = kL := by
      apply Fin.ext; simp only [kL, Fin.val_mk]; omega
    rw [hk_eq]
    have h0 : Equiv.swap kL.castSucc kL.succ kL.castSucc = kL.succ :=
      Equiv.swap_apply_left _ _
    have h1 : Equiv.swap kL.castSucc kL.succ kL.succ = kL.castSucc :=
      Equiv.swap_apply_right _ _
    rw [slPerm_conj_omegaBlock_inv (Equiv.swap kL.castSucc kL.succ) h0 h1]
    exact inv_mem (Subgroup.subset_closure ⟨kL, Or.inl (by simp [kL]), rfl⟩)
  · have hklt : k.val < m := by omega
    have h0 : Equiv.swap kL.castSucc kL.succ k.castSucc = k.castSucc := by
      apply Equiv.swap_apply_of_ne_of_ne
      · intro h; have := congrArg Fin.val h
        rw [Fin.val_castSucc, Fin.val_castSucc] at this
        dsimp only [kL] at this; omega
      · intro h; have := congrArg Fin.val h
        rw [Fin.val_castSucc, Fin.val_succ] at this
        dsimp only [kL] at this; omega
    have h1 : Equiv.swap kL.castSucc kL.succ k.succ = k.succ := by
      apply Equiv.swap_apply_of_ne_of_ne
      · intro h; have := congrArg Fin.val h
        rw [Fin.val_succ, Fin.val_castSucc] at this
        dsimp only [kL] at this; omega
      · intro h; have := congrArg Fin.val h
        rw [Fin.val_succ, Fin.val_succ] at this
        dsimp only [kL] at this; omega
    rw [slPerm_conj_omegaBlock (Equiv.swap kL.castSucc kL.succ) h0 h1]
    exact Subgroup.subset_closure ⟨k, Or.inr ⟨hk2, hkB⟩, rfl⟩

theorem slPerm_tau_conj_halfTorusK (m : ℕ) (hm : 1 ≤ m)
    {t : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2} (ht : t ∈ halfTorusK (m + 1 + 1)) :
    slPerm gf2_two (tauPerm m) * t * (slPerm gf2_two (tauPerm m))⁻¹ ∈
      halfTorusK (m + 1 + 1) := by
  let kL : Fin (m + 1 + 1) := ⟨m + 1, by omega⟩
  refine mem_conj_closure_of_mem_conj_gens
    {x | ∃ k : Fin (m + 1 + 1),
      (k.val + 1 = m + 1 + 1 ∨ (k.val % 2 = 0 ∧ k.val + 2 < m + 1 + 1)) ∧
        x = omegaBlock (m + 1 + 1) k}
    (halfTorusK (m + 1 + 1)) (slPerm gf2_two (tauPerm m)) rfl ?_ t ht
  rintro x ⟨k, hk, rfl⟩
  rcases hk with hkA | ⟨hk2, hkB⟩
  · have hk_eq : k = kL := by
      apply Fin.ext; simp only [kL, Fin.val_mk]; omega
    rw [hk_eq]
    have h0 : tauPerm m kL.castSucc = (0 : Fin (m + 1 + 1)).castSucc := by
      rw [show kL.castSucc = (Fin.last (m + 1)).castSucc from by apply Fin.ext; rfl,
        tauPerm_apply_lastCast m hm, Fin.castSucc_zero]
    have h1 : tauPerm m kL.succ = (0 : Fin (m + 1 + 1)).succ := by
      rw [show kL.succ = Fin.last (m + 1 + 1) from by apply Fin.ext; rfl,
        tauPerm_apply_lastSucc m hm, Fin.succ_zero_eq_one]
    rw [slPerm_conj_omegaBlock (tauPerm m) h0 h1]
    refine Subgroup.subset_closure ⟨0, Or.inr ⟨?_, ?_⟩, rfl⟩
    · simp only [Fin.val_zero, Nat.zero_mod]
    · rw [Fin.val_zero]; omega
  · rcases eq_or_ne k (0 : Fin (m + 1 + 1)) with hk0' | hk0'
    · rw [hk0']
      have h0 : tauPerm m (0 : Fin (m + 1 + 1)).castSucc = kL.castSucc := by
        rw [Fin.castSucc_zero, tauPerm_apply_zero]
        apply Fin.ext
        rw [Fin.val_castSucc, Fin.val_last, Fin.val_castSucc]
      have h1 : tauPerm m (0 : Fin (m + 1 + 1)).succ = kL.succ := by
        rw [show (0 : Fin (m + 1 + 1)).succ = (1 : Fin (m + 1 + 1 + 1)) from
            Fin.succ_zero_eq_one,
          tauPerm_apply_one]
        apply Fin.ext
        rw [Fin.val_last, Fin.val_succ]
      rw [slPerm_conj_omegaBlock (tauPerm m) h0 h1]
      exact Subgroup.subset_closure ⟨kL, Or.inl (by simp [kL]), rfl⟩
    · have hk0 : k.val ≠ 0 := by
        intro hv; exact hk0' (Fin.ext (by simpa using hv))
      have hkval2 : 2 ≤ k.val :=
        Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) (Nat.dvd_of_mod_eq_zero hk2)
      have h0 : tauPerm m k.castSucc = k.castSucc := by
        refine tauPerm_apply_of_fixed m ?_ ?_ ?_ ?_
        · intro h; have := congrArg Fin.val h
          rw [Fin.val_castSucc, Fin.val_zero] at this; omega
        · intro h; have := congrArg Fin.val h
          rw [Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
            Nat.mod_eq_of_lt (show (1:ℕ) < m + 1 + 1 + 1 by omega)] at this; omega
        · intro h; have := congrArg Fin.val h
          rw [Fin.val_castSucc, Fin.val_castSucc, Fin.val_last] at this; omega
        · intro h; have := congrArg Fin.val h
          rw [Fin.val_castSucc, Fin.val_last] at this; omega
      have h1 : tauPerm m k.succ = k.succ := by
        refine tauPerm_apply_of_fixed m ?_ ?_ ?_ ?_
        · intro h; have := congrArg Fin.val h
          rw [Fin.val_succ, Fin.val_zero] at this; omega
        · intro h; have := congrArg Fin.val h
          rw [Fin.val_succ, Fin.coe_ofNat_eq_mod,
            Nat.mod_eq_of_lt (show (1:ℕ) < m + 1 + 1 + 1 by omega)] at this; omega
        · intro h; have := congrArg Fin.val h
          rw [Fin.val_succ, Fin.val_castSucc, Fin.val_last] at this; omega
        · intro h; have := congrArg Fin.val h
          rw [Fin.val_succ, Fin.val_last] at this; omega
      rw [slPerm_conj_omegaBlock (tauPerm m) h0 h1]
      exact Subgroup.subset_closure ⟨k, Or.inr ⟨hk2, hkB⟩, rfl⟩

theorem three_dvd_card_sl (m : ℕ) (hm : 1 ≤ m) :
    3 ∣ Nat.card (SpecialLinearGroup (Fin (m + 1)) F2) := by
  have hω3 : omegaBlock m ⟨0, by omega⟩ ^ 3 = 1 := omegaBlock_pow_three m ⟨0, by omega⟩
  have hω1 : omegaBlock m ⟨0, by omega⟩ ≠ 1 := omegaBlock_ne_one m ⟨0, by omega⟩
  have horder : orderOf (omegaBlock m ⟨0, by omega⟩) = 3 := orderOf_eq_prime hω3 hω1
  have hdvd := orderOf_dvd_natCard (omegaBlock m ⟨0, by omega⟩)
  rwa [horder] at hdvd

end CFSG.StandardType.GGHalf

end
