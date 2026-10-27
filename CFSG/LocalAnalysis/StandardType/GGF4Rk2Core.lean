module

public import CFSG.LocalAnalysis.StandardType.GGF4B3CoreRep
public import Mathlib.GroupTheory.Coxeter.Matrix
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType.F4Model

@[expose] def posB (k : Fin 3) : Fin 4 := ⟨k.val, by omega⟩

@[expose] def posC (k : Fin 3) : Fin 4 := ⟨3 - k.val, by omega⟩

@[expose] def longL : List ℕ := [0, 3, 5, 6, 7, 9, 10, 16, 17, 18, 22, 23]

abbrev IsLongM (m : M4) : Prop := ∃ x ∈ longL, m = Rm x

abbrev FixB (m : M4) : Prop := m.m30 = 0 ∧ m.m31 = 0 ∧ m.m32 = 0 ∧ m.m33 = 1

abbrev FixC (m : M4) : Prop := m.m00 = 1 ∧ m.m01 = 0 ∧ m.m02 = 0 ∧ m.m03 = 0

@[expose] def reflB : List ℕ := [1, 3, 5, 6, 9, 14, 16, 17, 19]

@[expose] def tabB : List (ℕ × ℕ × List (Fin 3) × Fin 3 × Fin 3) :=
  [(1, 3, [0, 1, 0], 2, 1), (1, 5, [0, 1], 2, 1), (1, 6, [2, 0, 1], 2, 1),
   (1, 9, [0, 1, 2, 0], 2, 1), (1, 16, [0, 1], 2, 0), (1, 17, [2, 0, 1], 2, 0),
   (3, 1, [0, 1, 0], 1, 2), (3, 5, [0], 0, 1), (3, 6, [2, 0], 0, 1), (3, 14, [], 0, 2),
   (3, 16, [], 0, 1), (3, 17, [2], 0, 1), (3, 19, [1, 0], 1, 2), (5, 1, [0, 1], 1, 2),
   (5, 3, [1, 0], 0, 1), (5, 9, [1, 2, 0], 0, 1), (5, 14, [0], 1, 2), (5, 16, [1], 0, 1),
   (5, 17, [1, 2], 0, 1), (5, 19, [1], 0, 2), (6, 1, [2, 0, 1], 1, 2), (6, 3, [2, 1, 0], 0, 1),
   (6, 9, [2, 1, 2, 0], 0, 1), (6, 14, [2, 0], 1, 2), (6, 16, [2, 1, 2], 0, 1),
   (6, 17, [2, 1], 0, 1), (6, 19, [2, 1], 0, 2), (9, 1, [0, 1, 2, 0], 1, 2),
   (9, 5, [1, 2, 1, 0], 0, 1), (9, 6, [0, 1, 2, 1], 0, 1), (9, 14, [1, 2, 1], 0, 2),
   (9, 16, [2, 1, 2, 1], 0, 1), (9, 17, [1, 2, 1], 0, 1), (9, 19, [1, 2, 0], 1, 2),
   (14, 3, [], 2, 0), (14, 5, [0], 2, 1), (14, 6, [2, 0], 2, 1), (14, 9, [1, 2, 1], 2, 0),
   (14, 16, [], 2, 1), (14, 17, [2], 2, 1), (16, 1, [0, 1], 0, 2), (16, 3, [0, 1, 0], 0, 1),
   (16, 5, [0, 1], 0, 1), (16, 6, [0, 1, 2], 0, 1), (16, 9, [0, 1, 2, 0], 0, 1),
   (16, 14, [], 1, 2), (16, 19, [1], 1, 2), (17, 1, [2, 0, 1], 0, 2), (17, 3, [2, 0, 1, 0], 0, 1),
   (17, 5, [2, 0, 1, 2], 0, 1), (17, 6, [2, 0, 1], 0, 1), (17, 9, [1, 2, 0, 1], 0, 1),
   (17, 14, [2], 1, 2), (17, 19, [2, 1], 1, 2), (19, 3, [1, 0], 2, 1), (19, 5, [1], 2, 0),
   (19, 6, [2, 1], 2, 0), (19, 9, [1, 2, 0], 2, 1), (19, 16, [1], 2, 1), (19, 17, [2, 1], 2, 1)]

@[expose] def reflC : List ℕ := [13, 14, 15, 16, 17, 18, 19, 20, 21]

@[expose] def tabC : List (ℕ × ℕ × List (Fin 3) × Fin 3 × Fin 3) :=
  [(13, 14, [], 0, 1), (13, 15, [0], 0, 1), (13, 16, [], 0, 2), (13, 17, [1, 0], 1, 2),
   (13, 18, [0, 1, 0], 1, 2), (13, 19, [2], 0, 1), (13, 20, [2, 0], 0, 1),
   (14, 13, [0, 1, 0], 0, 1), (14, 15, [0, 1], 0, 1), (14, 16, [], 1, 2), (14, 17, [1], 1, 2),
   (14, 18, [0, 1], 0, 2), (14, 20, [0, 1, 2], 0, 1), (14, 21, [0, 1, 2, 0], 0, 1),
   (15, 13, [1, 0], 0, 1), (15, 14, [1], 0, 1), (15, 16, [0], 1, 2), (15, 17, [1], 0, 2),
   (15, 18, [0, 1], 1, 2), (15, 19, [1, 2], 0, 1), (15, 21, [1, 2, 0], 0, 1), (16, 13, [], 2, 0),
   (16, 14, [], 2, 1), (16, 15, [0], 2, 1), (16, 19, [2], 2, 1), (16, 20, [2, 0], 2, 1),
   (16, 21, [1, 2, 1], 2, 0), (17, 13, [1, 0], 2, 1), (17, 14, [1], 2, 1), (17, 15, [1], 2, 0),
   (17, 19, [2, 1], 2, 1), (17, 20, [2, 1], 2, 0), (17, 21, [1, 2, 0], 2, 1),
   (18, 13, [0, 1, 0], 2, 1), (18, 14, [0, 1], 2, 0), (18, 15, [0, 1], 2, 1),
   (18, 19, [2, 0, 1], 2, 0), (18, 20, [2, 0, 1], 2, 1), (18, 21, [0, 1, 2, 0], 2, 1),
   (19, 13, [2, 0, 1, 0], 0, 1), (19, 15, [2, 0, 1, 2], 0, 1), (19, 16, [2], 1, 2),
   (19, 17, [2, 1], 1, 2), (19, 18, [2, 0, 1], 0, 2), (19, 20, [2, 0, 1], 0, 1),
   (19, 21, [1, 2, 0, 1], 0, 1), (20, 13, [2, 1, 0], 0, 1), (20, 14, [2, 1, 2], 0, 1),
   (20, 16, [2, 0], 1, 2), (20, 17, [2, 1], 0, 2), (20, 18, [2, 0, 1], 1, 2),
   (20, 19, [2, 1], 0, 1), (20, 21, [2, 1, 2, 0], 0, 1), (21, 14, [2, 1, 2, 1], 0, 1),
   (21, 15, [1, 2, 1, 0], 0, 1), (21, 16, [1, 2, 1], 0, 2), (21, 17, [1, 2, 0], 1, 2),
   (21, 18, [0, 1, 2, 0], 1, 2), (21, 19, [1, 2, 1], 0, 1), (21, 20, [0, 1, 2, 1], 0, 1)]

abbrev EntryOK (σ : Fin 3 → Fin 4) (x y : ℕ) (e : ℕ × ℕ × List (Fin 3) × Fin 3 × Fin 3) : Prop :=
  e.1 = x ∧ e.2.1 = y ∧ conjW (e.2.2.1.map σ) (Sm (σ e.2.2.2.1)) = Rm x ∧
    conjW (e.2.2.1.map σ) (Sm (σ e.2.2.2.2)) = Rm y

abbrev TableOK (σ : Fin 3 → Fin 4) (refl : List ℕ)
    (tab : List (ℕ × ℕ × List (Fin 3) × Fin 3 × Fin 3)) : Prop :=
  ∀ x ∈ refl, ∀ y ∈ refl, x ≠ y →
    (pw2 ((Rm x).mul (Rm y)) = M4.one → (IsLongM (Rm x) ↔ ¬ IsLongM (Rm y)) →
      ∃ e ∈ tab, EntryOK σ x y e ∧
        (e.2.2.2.1 = 0 ∧ e.2.2.2.2 = 2 ∨ e.2.2.2.1 = 2 ∧ e.2.2.2.2 = 0)) ∧
    (pw3 ((Rm x).mul (Rm y)) = M4.one →
      ∃ e ∈ tab, EntryOK σ x y e ∧ e.2.2.2.1 = 0 ∧ e.2.2.2.2 = 1) ∧
    (pw4 ((Rm x).mul (Rm y)) = M4.one → pw2 ((Rm x).mul (Rm y)) ≠ M4.one →
      ∃ e ∈ tab, EntryOK σ x y e ∧
        (e.2.2.2.1 = 2 ∧ e.2.2.2.2 = 1 ∨ e.2.2.2.1 = 1 ∧ e.2.2.2.2 = 2))

set_option synthInstance.maxSize 4096 in
theorem tabB_spec : TableOK posB reflB tabB := by decide +kernel

set_option synthInstance.maxSize 4096 in
theorem tabC_spec : TableOK posC reflC tabC := by decide +kernel

theorem fixB_refl : ∀ x, x < 24 → FixB (Rm x) → x ∈ reflB := by decide +kernel

theorem fixC_refl : ∀ x, x < 24 → FixC (Rm x) → x ∈ reflC := by decide +kernel

theorem fixB_Sm : ∀ k : Fin 3, FixB (Sm (posB k)) := by decide +kernel

theorem fixC_Sm : ∀ k : Fin 3, FixC (Sm (posC k)) := by decide +kernel

theorem fixB_one : FixB M4.one := by decide +kernel

theorem fixC_one : FixC M4.one := by decide +kernel

theorem isLongM_conj :
    ∀ i : Fin 4, ∀ x, x < 24 → (IsLongM ((Sm i).mul ((Rm x).mul (Sm i))) ↔ IsLongM (Rm x)) := by
  decide +kernel

theorem isLongM_label_two (i j : Fin 4) (h : CoxeterMatrix.F₄ i j = 2) :
    IsLongM (Sm i) ↔ ¬ IsLongM (Sm j) := by
  fin_cases i <;> fin_cases j <;> first | decide | exact absurd h (by decide)

theorem label_of_ne (i j : Fin 4) (hij : i ≠ j) :
    CoxeterMatrix.F₄ i j = 2 ∨ CoxeterMatrix.F₄ i j = 3 ∨ CoxeterMatrix.F₄ i j = 4 := by
  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide

theorem Sm_eq_iff : ∀ i j : Fin 4, Sm i = Sm j → i = j := by decide +kernel

theorem FixB.mul {x y : M4} (hx : FixB x) (hy : FixB y) : FixB (x.mul y) := by
  obtain ⟨h0, h1, h2, h3⟩ := hx
  obtain ⟨h4, h5, h6, h7⟩ := hy
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [M4.mul, h0, h1, h2, h3, h4, h5, h6, h7]

theorem FixC.mul {x y : M4} (hx : FixC x) (hy : FixC y) : FixC (x.mul y) := by
  obtain ⟨h0, h1, h2, h3⟩ := hx
  obtain ⟨h4, h5, h6, h7⟩ := hy
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [M4.mul, h0, h1, h2, h3, h4, h5, h6, h7]

namespace F4Rep

variable {W : Type} [Group W] (R : F4Rep W)

theorem exists_word_of_mem_closure {ι : Type} (σ : ι → Fin 4) {u : W}
    (hu : u ∈ Subgroup.closure (Set.range fun k => R.s (σ k))) :
    ∃ l : List ι, u = R.wd (l.map σ) := by
  induction hu using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    exact ⟨[k], by simp [wd]⟩
  | one => exact ⟨[], by simp [wd]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨l₁, rfl⟩ := hx
    obtain ⟨l₂, rfl⟩ := hy
    exact ⟨l₁ ++ l₂, by simp [wd, List.map_append, List.prod_append]⟩
  | inv x _ hx =>
    obtain ⟨l, rfl⟩ := hx
    exact ⟨l.reverse, by rw [List.map_reverse, R.wd_reverse]⟩

theorem fix_of_mem_closure {σ : Fin 3 → Fin 4} {Fix : M4 → Prop}
    (hmul : ∀ x y, Fix x → Fix y → Fix (x.mul y)) (hone : Fix M4.one)
    (hgen : ∀ k, Fix (Sm (σ k))) {u : W}
    (hu : u ∈ Subgroup.closure (Set.range fun k => R.s (σ k))) :
    ∃ z, R.ρ u = z.toMat ∧ Fix z := by
  obtain ⟨l, rfl⟩ := R.exists_word_of_mem_closure σ hu
  refine ⟨evalW (l.map σ), R.rho_wd _, ?_⟩
  clear hu
  induction l with
  | nil => exact hone
  | cons k l ih => exact hmul _ _ (hgen k) ih

theorem isLongM_of_conj (h : W) (i : Fin 4) {x : ℕ} (hx : x < 24)
    (hρ : R.ρ (h * R.s i * h⁻¹) = (Rm x).toMat) : IsLongM (Rm x) ↔ IsLongM (Sm i) := by
  have hh : h ∈ Subgroup.closure (Set.range fun k => R.s (id k)) := by
    rw [show (Set.range fun k => R.s (id k)) = Set.range R.s from rfl, R.gen]
    exact Subgroup.mem_top h
  obtain ⟨l, rfl⟩ := R.exists_word_of_mem_closure id hh
  clear hh
  induction l generalizing x with
  | nil =>
    have e : Rm x = Sm i := by
      apply M4.toMat_injective
      rw [← hρ, ← R.hs i]
      simp [wd]
    rw [e]
  | cons k l ih =>
    obtain ⟨x', hx', hρ'⟩ := R.refl_rep ⟨R.wd (l.map id), i, rfl⟩
    have e1 : R.wd ((k :: l).map id) * R.s i * (R.wd ((k :: l).map id))⁻¹ =
        R.s k * (R.wd (l.map id) * R.s i * (R.wd (l.map id))⁻¹) * R.s k := by
      have hw : R.wd ((k :: l).map id) = R.s k * R.wd (l.map id) := by simp [wd]
      rw [hw, mul_inv_rev, R.s_inv]
      group
    have e2 : (Sm k).mul ((Rm x').mul (Sm k)) = Rm x := by
      apply M4.toMat_injective
      rw [← hρ, e1, R.rho_mul3 (R.hs k) hρ' (R.hs k)]
    rw [← e2, isLongM_conj k x' hx']
    exact ih hx' hρ'

theorem pair_core {a : Fin 3 → W} (ha : ∀ k, R.IsRefl (a k)) (ha01 : orderOf (a 0 * a 1) = 3)
    (ha12 : orderOf (a 1 * a 2) = 4) (ha02 : orderOf (a 0 * a 2) = 2) {w : W} {i j : Fin 4}
    (hij : i ≠ j) (hord : orderOf (R.s i * R.s j) = CoxeterMatrix.F₄ i j)
    (hi : w * R.s i * w⁻¹ ∈ Subgroup.closure (Set.range a))
    (hj : w * R.s j * w⁻¹ ∈ Subgroup.closure (Set.range a)) :
    ∃ (v : List (Fin 3)) (c d : Fin 3),
      w * R.s i * w⁻¹ = (v.map a).prod * a c * ((v.map a).prod)⁻¹ ∧
      w * R.s j * w⁻¹ = (v.map a).prod * a d * ((v.map a).prod)⁻¹ ∧
      (CoxeterMatrix.F₄ i j = 2 → c = 0 ∧ d = 2 ∨ c = 2 ∧ d = 0) ∧
      (CoxeterMatrix.F₄ i j = 3 → c = 0 ∧ d = 1) ∧
      (CoxeterMatrix.F₄ i j = 4 → c = 2 ∧ d = 1 ∨ c = 1 ∧ d = 2) := by
  obtain ⟨g, hg⟩ := R.classify (ha 0) (ha 1) (ha 2) ha01 ha12 ha02
  obtain ⟨σ, Fix, refl, tab, hσ, hFmul, hFone, hFgen, hFrefl, htab⟩ :
      ∃ (σ : Fin 3 → Fin 4) (Fix : M4 → Prop) (refl : List ℕ)
        (tab : List (ℕ × ℕ × List (Fin 3) × Fin 3 × Fin 3)),
        (∀ k, g * a k * g⁻¹ = R.s (σ k)) ∧ (∀ x y, Fix x → Fix y → Fix (x.mul y)) ∧
        Fix M4.one ∧ (∀ k, Fix (Sm (σ k))) ∧ (∀ x, x < 24 → Fix (Rm x) → x ∈ refl) ∧
        TableOK σ refl tab := by
    have hk : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
    rcases hg with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
    · refine ⟨posB, FixB, reflB, tabB, ?_, fun _ _ => FixB.mul, fixB_one, fixB_Sm, fixB_refl,
        tabB_spec⟩
      intro k
      rcases hk k with rfl | rfl | rfl
      exacts [h0, h1, h2]
    · refine ⟨posC, FixC, reflC, tabC, ?_, fun _ _ => FixC.mul, fixC_one, fixC_Sm, fixC_refl,
        tabC_spec⟩
      intro k
      rcases hk k with rfl | rfl | rfl
      exacts [h0, h1, h2]
  have hP : ∀ u ∈ Subgroup.closure (Set.range a),
      g * u * g⁻¹ ∈ Subgroup.closure (Set.range fun k => R.s (σ k)) := by
    intro u hu
    induction hu using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact Subgroup.subset_closure ⟨k, (hσ k).symm⟩
    | one => simp
    | mul x y _ _ hx hy =>
      have h := mul_mem hx hy
      rwa [show g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ by group] at h
    | inv x _ hx =>
      have h := inv_mem hx
      rwa [show (g * x * g⁻¹)⁻¹ = g * x⁻¹ * g⁻¹ by group] at h
  have hidx : ∀ k : Fin 4, w * R.s k * w⁻¹ ∈ Subgroup.closure (Set.range a) →
      ∃ x, x ∈ refl ∧ x < 24 ∧ R.ρ (g * (w * R.s k * w⁻¹) * g⁻¹) = (Rm x).toMat ∧
        (IsLongM (Rm x) ↔ IsLongM (Sm k)) := by
    intro k hk
    have hconj : g * (w * R.s k * w⁻¹) * g⁻¹ = g * w * R.s k * (g * w)⁻¹ := by group
    obtain ⟨x, hx, hρ⟩ := R.refl_rep ⟨g * w, k, hconj⟩
    obtain ⟨z, hz, hfz⟩ := R.fix_of_mem_closure hFmul hFone hFgen (hP _ hk)
    have hzx : z = Rm x := M4.toMat_injective (hz.symm.trans hρ)
    refine ⟨x, hFrefl x hx (hzx ▸ hfz), hx, hρ, ?_⟩
    rw [hconj] at hρ
    exact R.isLongM_of_conj (g * w) k hx hρ
  obtain ⟨x, hxr, hx24, hρx, hlx⟩ := hidx i hi
  obtain ⟨y, hyr, hy24, hρy, hly⟩ := hidx j hj
  have hxy : x ≠ y := by
    rintro rfl
    apply hij
    have h := R.inj (hρx.trans hρy.symm)
    have h' : R.s i = R.s j := by
      have h2 : (g * w)⁻¹ * (g * (w * R.s i * w⁻¹) * g⁻¹) * (g * w) =
          (g * w)⁻¹ * (g * (w * R.s j * w⁻¹) * g⁻¹) * (g * w) := by rw [h]
      rwa [show (g * w)⁻¹ * (g * (w * R.s i * w⁻¹) * g⁻¹) * (g * w) = R.s i by group,
        show (g * w)⁻¹ * (g * (w * R.s j * w⁻¹) * g⁻¹) * (g * w) = R.s j by group] at h2
    apply Sm_eq_iff
    apply M4.toMat_injective
    rw [← R.hs i, ← R.hs j, h']
  have hordM : orderOf ((Rm x).mul (Rm y)).toMat = CoxeterMatrix.F₄ i j := by
    rw [← R.rho_mul hρx hρy, orderOf_injective R.ρ R.inj,
      show g * (w * R.s i * w⁻¹) * g⁻¹ * (g * (w * R.s j * w⁻¹) * g⁻¹) =
        g * w * (R.s i * R.s j) * (g * w)⁻¹ by group, orderOf_conj_eq, hord]
  have hpow : ∀ n : ℕ, orderOf ((Rm x).mul (Rm y)).toMat = n →
      ((Rm x).mul (Rm y)).toMat ^ n = 1 := fun n hn => hn ▸ pow_orderOf_eq_one _
  have hword : ∀ v : List (Fin 3), R.wd (v.map σ) = g * (v.map a).prod * g⁻¹ := by
    intro v
    induction v with
    | nil => simp [wd]
    | cons k v ih =>
      have hw : R.wd ((k :: v).map σ) = R.s (σ k) * R.wd (v.map σ) := by simp [wd]
      rw [hw, ih, ← hσ k, List.map_cons, List.prod_cons]
      group
  have hback : ∀ e, EntryOK σ x y e →
      w * R.s i * w⁻¹ = (e.2.2.1.map a).prod * a e.2.2.2.1 * ((e.2.2.1.map a).prod)⁻¹ ∧
      w * R.s j * w⁻¹ = (e.2.2.1.map a).prod * a e.2.2.2.2 * ((e.2.2.1.map a).prod)⁻¹ := by
    rintro ⟨x', y', v, c, d⟩ ⟨-, -, hc, hd⟩
    have h1 := R.conj_wd_eq (R.hs (σ c)) hρx hc
    have h2 := R.conj_wd_eq (R.hs (σ d)) hρy hd
    rw [hword, ← hσ c] at h1
    rw [hword, ← hσ d] at h2
    constructor
    · have h : g⁻¹ * (g * (v.map a).prod * g⁻¹ * (g * a c * g⁻¹) *
          (g * (v.map a).prod * g⁻¹)⁻¹) * g = g⁻¹ * (g * (w * R.s i * w⁻¹) * g⁻¹) * g := by
        rw [h1]
      rw [show g⁻¹ * (g * (v.map a).prod * g⁻¹ * (g * a c * g⁻¹) *
          (g * (v.map a).prod * g⁻¹)⁻¹) * g = (v.map a).prod * a c * ((v.map a).prod)⁻¹ by group,
        show g⁻¹ * (g * (w * R.s i * w⁻¹) * g⁻¹) * g = w * R.s i * w⁻¹ by group] at h
      exact h.symm
    · have h : g⁻¹ * (g * (v.map a).prod * g⁻¹ * (g * a d * g⁻¹) *
          (g * (v.map a).prod * g⁻¹)⁻¹) * g = g⁻¹ * (g * (w * R.s j * w⁻¹) * g⁻¹) * g := by
        rw [h2]
      rw [show g⁻¹ * (g * (v.map a).prod * g⁻¹ * (g * a d * g⁻¹) *
          (g * (v.map a).prod * g⁻¹)⁻¹) * g = (v.map a).prod * a d * ((v.map a).prod)⁻¹ by group,
        show g⁻¹ * (g * (w * R.s j * w⁻¹) * g⁻¹) * g = w * R.s j * w⁻¹ by group] at h
      exact h.symm
  obtain ⟨hT2, hT3, hT4⟩ := htab x hxr y hyr hxy
  rcases label_of_ne i j hij with hl | hl | hl
  ·
    have hp2 : pw2 ((Rm x).mul (Rm y)) = M4.one := by
      apply M4.toMat_injective
      rw [M4.toMat_pw2, M4.toMat_one, ← pow_two]
      exact hpow 2 (hordM.trans hl)
    have hcl : IsLongM (Rm x) ↔ ¬ IsLongM (Rm y) := by
      rw [hlx, hly]
      exact isLongM_label_two i j hl
    obtain ⟨e, -, he, hcd⟩ := hT2 hp2 hcl
    obtain ⟨h1, h2⟩ := hback e he
    exact ⟨e.2.2.1, e.2.2.2.1, e.2.2.2.2, h1, h2, fun _ => hcd, fun h => by omega,
      fun h => by omega⟩
  ·
    have hp3 : pw3 ((Rm x).mul (Rm y)) = M4.one := by
      apply M4.toMat_injective
      rw [M4.toMat_pw3, M4.toMat_one, ← pow_three]
      exact hpow 3 (hordM.trans hl)
    obtain ⟨e, -, he, hcd⟩ := hT3 hp3
    obtain ⟨h1, h2⟩ := hback e he
    exact ⟨e.2.2.1, e.2.2.2.1, e.2.2.2.2, h1, h2, fun h => by omega, fun _ => hcd,
      fun h => by omega⟩
  ·
    have hp4 : pw4 ((Rm x).mul (Rm y)) = M4.one := by
      apply M4.toMat_injective
      rw [M4.toMat_pw4, M4.toMat_one, ← pow_four_eq]
      exact hpow 4 (hordM.trans hl)
    have hp2 : pw2 ((Rm x).mul (Rm y)) ≠ M4.one := by
      intro h
      have h' := congrArg M4.toMat h
      rw [M4.toMat_pw2, M4.toMat_one, ← pow_two] at h'
      exact pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hordM, hl]; norm_num) h'
    obtain ⟨e, -, he, hcd⟩ := hT4 hp4 hp2
    obtain ⟨h1, h2⟩ := hback e he
    exact ⟨e.2.2.1, e.2.2.2.1, e.2.2.2.2, h1, h2, fun h => by omega, fun h => by omega,
      fun _ => hcd⟩

end F4Rep

end CFSG.StandardType.F4Model

end
