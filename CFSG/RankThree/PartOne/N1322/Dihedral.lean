module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral

public section

namespace CFSG.RankThree.PartOne.N1322

open DihedralGroup

@[expose] def IsNCInv {L : Type*} [Group L] (x : L) : Prop :=
  x * x = 1 ∧ x ≠ 1 ∧ ∃ y, x * y ≠ y * x

theorem isNCInv_iff_dih {n : ℕ} (hn : n = 4 ∨ n = 6 ∨ n = 8) (x : DihedralGroup n) :
    IsNCInv x ↔ ∃ i, x = sr i := by
  unfold IsNCInv
  rcases hn with rfl | rfl | rfl <;> revert x <;> decide

@[expose] def dihSignFun (n : ℕ) : DihedralGroup n → Multiplicative (ZMod 2)
  | r _ => 1
  | sr _ => Multiplicative.ofAdd 1

@[expose] def dihSign (n : ℕ) : DihedralGroup n →* Multiplicative (ZMod 2) where
  toFun := dihSignFun n
  map_one' := rfl
  map_mul' := by
    rintro (i | i) (j | j) <;> simp only [r_mul_r, r_mul_sr, sr_mul_r, sr_mul_sr, dihSignFun] <;>
      decide

@[expose] def dihParFun (n : ℕ) (h : 2 ∣ n) : DihedralGroup n → Multiplicative (ZMod 2)
  | r i => Multiplicative.ofAdd (ZMod.castHom h (ZMod 2) i)
  | sr i => Multiplicative.ofAdd (ZMod.castHom h (ZMod 2) i)

@[expose] def dihPar (n : ℕ) (h : 2 ∣ n) : DihedralGroup n →* Multiplicative (ZMod 2) where
  toFun := dihParFun n h
  map_one' := by
    show Multiplicative.ofAdd (ZMod.castHom h (ZMod 2) 0) = 1
    rw [map_zero]; rfl
  map_mul' := by
    have key : ∀ a b : ZMod 2, a - b = b + a := by decide
    rintro (i | i) (j | j)
    · rw [r_mul_r]
      show Multiplicative.ofAdd (ZMod.castHom h (ZMod 2) (i + j)) =
        Multiplicative.ofAdd (ZMod.castHom h (ZMod 2) i) *
          Multiplicative.ofAdd (ZMod.castHom h (ZMod 2) j)
      rw [map_add, ofAdd_add]
    · rw [r_mul_sr]
      show Multiplicative.ofAdd (ZMod.castHom h (ZMod 2) (j - i)) =
        Multiplicative.ofAdd (ZMod.castHom h (ZMod 2) i) *
          Multiplicative.ofAdd (ZMod.castHom h (ZMod 2) j)
      rw [map_sub, key, ofAdd_add]
    · rw [sr_mul_r]
      show Multiplicative.ofAdd (ZMod.castHom h (ZMod 2) (i + j)) =
        Multiplicative.ofAdd (ZMod.castHom h (ZMod 2) i) *
          Multiplicative.ofAdd (ZMod.castHom h (ZMod 2) j)
      rw [map_add, ofAdd_add]
    · rw [sr_mul_sr]
      show Multiplicative.ofAdd (ZMod.castHom h (ZMod 2) (j - i)) =
        Multiplicative.ofAdd (ZMod.castHom h (ZMod 2) i) *
          Multiplicative.ofAdd (ZMod.castHom h (ZMod 2) j)
      rw [map_sub, key, ofAdd_add]

theorem dih_par_div {n : ℕ} (hn : n = 4 ∨ n = 6 ∨ n = 8) (h : 2 ∣ n) :
    ∀ i k : ZMod n, ZMod.castHom h (ZMod 2) i = ZMod.castHom h (ZMod 2) k →
      ∃ m : ZMod n, k = i - 2 * m := by
  rcases hn with rfl | rfl | rfl
  · exact (by decide : ∀ i k : ZMod 4, ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2) i =
      ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2) k → ∃ m : ZMod 4, k = i - 2 * m)
  · exact (by decide : ∀ i k : ZMod 6, ZMod.castHom (by norm_num : 2 ∣ 6) (ZMod 2) i =
      ZMod.castHom (by norm_num : 2 ∣ 6) (ZMod 2) k → ∃ m : ZMod 6, k = i - 2 * m)
  · exact (by decide : ∀ i k : ZMod 8, ZMod.castHom (by norm_num : 2 ∣ 8) (ZMod 2) i =
      ZMod.castHom (by norm_num : 2 ∣ 8) (ZMod 2) k → ∃ m : ZMod 8, k = i - 2 * m)

theorem dih_cover {n : ℕ} (hn : n = 4 ∨ n = 6 ∨ n = 8) (S : Set (DihedralGroup n))
    (hS : ∀ x ∈ S, ∃ i, x = sr i) (hc : ∀ x ∈ S, ∀ g, g * x * g⁻¹ ∈ S)
    (hgen : Subgroup.closure S = ⊤) : ∀ i, sr i ∈ S := by
  have h2 : 2 ∣ n := by rcases hn with rfl | rfl | rfl <;> norm_num
  have : NeZero n := ⟨by rcases hn with rfl | rfl | rfl <;> norm_num⟩
  set c := ZMod.castHom h2 (ZMod 2) with hcdef
  have hr1 : c (1 : ZMod n) = 1 := map_one c
  have hkill : ∀ ψ : DihedralGroup n →* Multiplicative (ZMod 2), (∀ x ∈ S, ψ x = 1) →
      ψ (r 1) = 1 := by
    intro ψ hψ
    have hle : Subgroup.closure S ≤ ψ.ker := Subgroup.closure_le _ |>.mpr fun x hx => hψ x hx
    rw [hgen] at hle
    exact hle (Subgroup.mem_top _)
  have hboth : ∃ i j, sr i ∈ S ∧ sr j ∈ S ∧ c i ≠ c j := by
    by_contra hno
    push Not at hno
    by_cases hne : S.Nonempty
    · obtain ⟨x0, hx0⟩ := hne
      obtain ⟨i0, rfl⟩ := hS x0 hx0
      have hpar : ∀ x ∈ S, ∃ i, x = sr i ∧ c i = c i0 := by
        intro x hx
        obtain ⟨i, rfl⟩ := hS x hx
        exact ⟨i, rfl, hno i i0 hx hx0⟩
      have hc0 : c i0 = 0 ∨ c i0 = 1 := by
        generalize c i0 = a; revert a; decide
      rcases hc0 with h0 | h1
      · have := hkill (dihPar n h2) (by
          intro x hx
          obtain ⟨i, rfl, hi⟩ := hpar x hx
          show Multiplicative.ofAdd (c i) = 1
          rw [hi, h0]; rfl)
        have h3 : Multiplicative.ofAdd (c 1) = (1 : Multiplicative (ZMod 2)) := this
        rw [hr1] at h3
        revert h3; decide
      · have := hkill (dihPar n h2 * dihSign n) (by
          intro x hx
          obtain ⟨i, rfl, hi⟩ := hpar x hx
          show Multiplicative.ofAdd (c i) * Multiplicative.ofAdd 1 = 1
          rw [hi, h1]; decide)
        have h3 : Multiplicative.ofAdd (c 1) * (1 : Multiplicative (ZMod 2)) = 1 := this
        rw [hr1] at h3
        revert h3; decide
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne, Subgroup.closure_empty] at hgen
      have : (r 1 : DihedralGroup n) ∈ (⊤ : Subgroup (DihedralGroup n)) := Subgroup.mem_top _
      rw [← hgen, Subgroup.mem_bot] at this
      have h1 : (r 1 : DihedralGroup n) = r 0 := this
      have h2' : (1 : ZMod n) = 0 := r.inj h1
      have h3 : c 1 = c 0 := by rw [h2']
      rw [hr1] at h3
      simp at h3
  obtain ⟨i, j, hi, hj, hij⟩ := hboth
  have hconj : ∀ k m : ZMod n, sr k ∈ S → sr (k - 2 * m) ∈ S := by
    intro k m hk
    have := hc _ hk (r m)
    convert this using 1
    simp [r_mul_sr, sr_mul_r, inv_r]
    ring
  intro k
  have hcases : c k = c i ∨ c k = c j := by
    generalize c k = a at *
    generalize c i = b at *
    generalize c j = d at *
    revert a b d; decide
  rcases hcases with hk | hk
  · obtain ⟨m, hm⟩ := dih_par_div hn h2 i k hk.symm
    rw [hm]; exact hconj i m hi
  · obtain ⟨m, hm⟩ := dih_par_div hn h2 j k hk.symm
    rw [hm]; exact hconj j m hj

structure DihGens (L : Type*) [Group L] (n : ℕ) (ρ t₀ : L) : Prop where
  ord : orderOf ρ = n
  sq : t₀ * t₀ = 1
  inv : t₀ * ρ * t₀⁻¹ = ρ⁻¹
  all : ∀ l : L, ∃ k : ℤ, l = ρ ^ k ∨ l = t₀ * ρ ^ k
  four : 4 ≤ n
  ev : Even n

theorem exists_gens {L : Type*} [Group L] {n : ℕ} (hn : n = 4 ∨ n = 6 ∨ n = 8)
    (e : L ≃* DihedralGroup n) : ∃ ρ t₀ : L, DihGens L n ρ t₀ := by
  have : NeZero n := ⟨by rcases hn with rfl | rfl | rfl <;> norm_num⟩
  refine ⟨e.symm (r 1), e.symm (sr 0), ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [MulEquiv.orderOf_eq]; exact orderOf_r_one
  · apply e.injective
    simp
  · apply e.injective
    simp [sr_mul_r, sr_mul_sr, inv_r]
  · intro l
    obtain ⟨x, rfl⟩ := e.symm.surjective l
    rcases x with i | i
    · refine ⟨(i.val : ℤ), Or.inl ?_⟩
      apply e.injective
      simp [map_zpow]
    · refine ⟨(i.val : ℤ), Or.inr ?_⟩
      apply e.injective
      simp [map_zpow, sr_mul_r]
  · rcases hn with rfl | rfl | rfl <;> norm_num
  · rcases hn with rfl | rfl | rfl <;> decide

section Abstract

variable {L : Type*} [Group L] {n : ℕ} {ρ t₀ : L}

theorem DihGens.t0_inv (h : DihGens L n ρ t₀) : t₀⁻¹ = t₀ :=
  inv_eq_of_mul_eq_one_right h.sq

theorem DihGens.zpow_eq_one_iff (h : DihGens L n ρ t₀) (m : ℤ) : ρ ^ m = 1 ↔ (n : ℤ) ∣ m := by
  rw [← orderOf_dvd_iff_zpow_eq_one, h.ord]

theorem DihGens.conj_zpow (h : DihGens L n ρ t₀) (k : ℤ) : t₀ * ρ ^ k * t₀⁻¹ = ρ ^ (-k) := by
  have h1 := map_zpow (MulAut.conj t₀) ρ k
  rw [MulAut.conj_apply, MulAut.conj_apply, h.inv, inv_zpow'] at h1
  exact h1

theorem DihGens.tr (h : DihGens L n ρ t₀) (k : ℤ) : t₀ * ρ ^ k = ρ ^ (-k) * t₀ :=
  mul_inv_eq_iff_eq_mul.mp (h.conj_zpow k)

theorem DihGens.rt (h : DihGens L n ρ t₀) (k : ℤ) : ρ ^ k * t₀ = t₀ * ρ ^ (-k) := by
  have := h.tr (-k)
  rw [neg_neg] at this
  exact this.symm

theorem DihGens.refl_mul (h : DihGens L n ρ t₀) (a b : ℤ) :
    (t₀ * ρ ^ a) * (t₀ * ρ ^ b) = ρ ^ (b - a) := by
  calc (t₀ * ρ ^ a) * (t₀ * ρ ^ b) = t₀ * (ρ ^ a * t₀) * ρ ^ b := by group
    _ = t₀ * (t₀ * ρ ^ (-a)) * ρ ^ b := by rw [h.rt]
    _ = (t₀ * t₀) * (ρ ^ (-a) * ρ ^ b) := by group
    _ = ρ ^ (b - a) := by rw [h.sq, one_mul, ← zpow_add]; congr 1; ring

theorem DihGens.rho_sq_ne_one (h : DihGens L n ρ t₀) : ρ ^ (2 : ℤ) ≠ 1 := by
  intro h1
  rw [h.zpow_eq_one_iff] at h1
  have h2 : (n : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) h1
  have := h.four
  omega

theorem DihGens.not_comm (h : DihGens L n ρ t₀) : t₀ * ρ ≠ ρ * t₀ := by
  intro h1
  have h2 : t₀ * ρ = ρ⁻¹ * t₀ := by
    have := h.tr 1
    simpa [zpow_one, zpow_neg_one] using this
  rw [h1] at h2
  have h3 : ρ = ρ⁻¹ := mul_right_cancel h2
  apply h.rho_sq_ne_one
  rw [zpow_two]
  nth_rewrite 1 [h3]
  exact inv_mul_cancel ρ

theorem DihGens.nc_iff (h : DihGens L n ρ t₀) (x : L) :
    IsNCInv x ↔ ∃ k : ℤ, x = t₀ * ρ ^ k := by
  constructor
  · rintro ⟨hx2, hx1, y, hy⟩
    obtain ⟨k, hk | hk⟩ := h.all x
    · exfalso
      apply hy
      have h1 : ρ ^ (k + k) = 1 := by rw [zpow_add, ← hk]; exact hx2
      obtain ⟨m, hm | hm⟩ := h.all y
      · rw [hk, hm, ← zpow_add, ← zpow_add, add_comm]
      · have e1 : ρ ^ k * (t₀ * ρ ^ m) = t₀ * ρ ^ (m - k) := by
          calc ρ ^ k * (t₀ * ρ ^ m) = (ρ ^ k * t₀) * ρ ^ m := by group
            _ = (t₀ * ρ ^ (-k)) * ρ ^ m := by rw [h.rt]
            _ = t₀ * ρ ^ (m - k) := by group
        have e2 : t₀ * ρ ^ m * ρ ^ k = t₀ * ρ ^ (m + k) := by group
        have e3 : ρ ^ (m + k) = ρ ^ (m - k) := by
          have : m + k = (m - k) + (k + k) := by ring
          rw [this, zpow_add, h1, mul_one]
        rw [hk, hm, e1, e2, e3]
    · exact ⟨k, hk⟩
  · rintro ⟨k, rfl⟩
    refine ⟨?_, ?_, ρ, ?_⟩
    · rw [h.refl_mul k k]; simp
    · intro h1
      have h2 : t₀ = ρ ^ (-k) := by
        rw [zpow_neg]; exact eq_inv_of_mul_eq_one_left h1
      apply h.not_comm
      rw [h2]
      exact ((Commute.refl ρ).zpow_left (-k)).eq
    · intro h1
      have h2 : t₀ * ρ ^ k * ρ = t₀ * ρ ^ (k + 1) := by rw [mul_assoc, ← zpow_add_one]
      have h3 : ρ * (t₀ * ρ ^ k) = t₀ * ρ ^ (k - 1) := by
        calc ρ * (t₀ * ρ ^ k) = (ρ ^ (1 : ℤ) * t₀) * ρ ^ k := by rw [zpow_one, mul_assoc]
          _ = (t₀ * ρ ^ (-(1 : ℤ))) * ρ ^ k := by rw [h.rt]
          _ = t₀ * ρ ^ (k - 1) := by group
      rw [h2, h3] at h1
      have h4 := mul_left_cancel h1
      apply h.rho_sq_ne_one
      have : ρ ^ (2 : ℤ) = ρ ^ (k + 1) * (ρ ^ (k - 1))⁻¹ := by
        rw [← zpow_neg, ← zpow_add]; congr 1; ring
      rw [this, h4, mul_inv_cancel]

theorem DihGens.not_conj (h : DihGens L n ρ t₀) (a b : ℤ) (hab : Odd (b - a)) (l : L) :
    l * (t₀ * ρ ^ a) * l⁻¹ ≠ t₀ * ρ ^ b := by
  intro heq
  have h2n : (2 : ℤ) ∣ (n : ℤ) := by
    have := even_iff_two_dvd.mp h.ev
    exact_mod_cast this
  have hdvd : ∀ m : ℤ, ρ ^ m = 1 → 2 ∣ m := by
    intro m hm
    rw [h.zpow_eq_one_iff] at hm
    exact dvd_trans h2n hm
  obtain ⟨q, hq⟩ := hab
  obtain ⟨k, hk | hk⟩ := h.all l
  · have h1 : l * (t₀ * ρ ^ a) * l⁻¹ = t₀ * ρ ^ (a - k - k) := by
      rw [hk]
      calc ρ ^ k * (t₀ * ρ ^ a) * (ρ ^ k)⁻¹ = (ρ ^ k * t₀) * ρ ^ a * ρ ^ (-k) := by
            rw [zpow_neg]; group
        _ = (t₀ * ρ ^ (-k)) * ρ ^ a * ρ ^ (-k) := by rw [h.rt]
        _ = t₀ * ρ ^ (a - k - k) := by group
    rw [h1] at heq
    have h2 := mul_left_cancel heq
    have h3 : ρ ^ (a - k - k - b) = 1 := by
      rw [zpow_sub, h2, mul_inv_cancel]
    obtain ⟨s, hs⟩ := hdvd _ h3
    omega
  · have h1 : l * (t₀ * ρ ^ a) * l⁻¹ = t₀ * ρ ^ (k + k - a) := by
      rw [hk]
      have hinv : (t₀ * ρ ^ k)⁻¹ = ρ ^ (-k) * t₀ := by
        rw [mul_inv_rev, h.t0_inv, zpow_neg]
      rw [hinv]
      calc t₀ * ρ ^ k * (t₀ * ρ ^ a) * (ρ ^ (-k) * t₀)
          = t₀ * (ρ ^ k * t₀) * ρ ^ a * ρ ^ (-k) * t₀ := by group
        _ = t₀ * (t₀ * ρ ^ (-k)) * ρ ^ a * ρ ^ (-k) * t₀ := by rw [h.rt]
        _ = (t₀ * t₀) * ρ ^ (a - k - k) * t₀ := by group
        _ = ρ ^ (a - k - k) * t₀ := by rw [h.sq, one_mul]
        _ = t₀ * ρ ^ (-(a - k - k)) := by rw [h.rt]
        _ = t₀ * ρ ^ (k + k - a) := by congr 2; ring
    rw [h1] at heq
    have h2 := mul_left_cancel heq
    have h3 : ρ ^ (k + k - a - b) = 1 := by
      rw [zpow_sub, h2, mul_inv_cancel]
    obtain ⟨s, hs⟩ := hdvd _ h3
    omega

end Abstract

theorem IsNCInv.map {L M : Type*} [Group L] [Group M] (e : L ≃* M) {x : L} (h : IsNCInv x) :
    IsNCInv (e x) := by
  obtain ⟨h1, h2, y, hy⟩ := h
  refine ⟨by rw [← map_mul, h1, map_one], fun h => h2 (e.injective (by rw [h, map_one])),
    e y, fun h => hy (e.injective (by simpa [map_mul] using h))⟩

theorem refl_cover {L : Type*} [Group L] {n : ℕ} (hn : n = 4 ∨ n = 6 ∨ n = 8)
    (e : L ≃* DihedralGroup n) (S : Set L) (hS : ∀ x ∈ S, IsNCInv x)
    (hc : ∀ x ∈ S, ∀ g : L, g * x * g⁻¹ ∈ S) (hgen : Subgroup.closure S = ⊤) :
    ∀ x : L, IsNCInv x → x ∈ S := by
  have hcl : Subgroup.closure (e '' S) = ⊤ := by
    have h1 : Subgroup.closure (e '' S) = (Subgroup.closure S).map e.toMonoidHom := by
      rw [MonoidHom.map_closure]; rfl
    rw [h1, hgen, Subgroup.map_top, MonoidHom.range_eq_top]
    exact e.surjective
  have hcov := dih_cover hn (e '' S)
    (by
      rintro _ ⟨x, hx, rfl⟩
      exact (isNCInv_iff_dih hn _).mp ((hS x hx).map e))
    (by
      rintro _ ⟨x, hx, rfl⟩ g
      refine ⟨e.symm g * x * (e.symm g)⁻¹, hc x hx _, ?_⟩
      simp)
    hcl
  intro x hx
  obtain ⟨i, hi⟩ := (isNCInv_iff_dih hn _).mp (hx.map e)
  obtain ⟨s, hs, hse⟩ := hcov i
  have : e s = e x := by rw [hse, hi]
  rw [← e.injective this]
  exact hs

end CFSG.RankThree.PartOne.N1322
