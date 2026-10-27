module

public import CFSG.LieType.RootSystem.Basic
import CFSG.LieType.RootSystem.Cartan
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Prime.Int

public section

namespace CFSG.StandardType

open CFSG.LieType.RootSystem

section Generic

variable {I : Type} [Fintype I] [DecidableEq I] {A : Matrix I I ℤ}

@[expose] def rsForm (A : Matrix I I ℤ) (x y : I → ℤ) : ℤ := ∑ i, x i * ∑ j, A i j * y j

private theorem rsForm_single_left (i : I) (y : I → ℤ) :
    rsForm A (Pi.single i 1) y = ∑ j, A i j * y j := by
  simp only [rsForm, Pi.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ i) h

private theorem rsForm_comm (hS : A.IsSymm) (x y : I → ℤ) : rsForm A x y = rsForm A y x := by
  have h : rsForm A y x = ∑ i, ∑ j, x i * (A i j * y j) := by
    simp only [rsForm, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hS.apply j i]
    ring
  rw [h]
  simp only [rsForm, Finset.mul_sum]

private theorem rsForm_single_right (hS : A.IsSymm) (x : I → ℤ) (i : I) :
    rsForm A x (Pi.single i 1) = ∑ j, A i j * x j := by
  rw [rsForm_comm hS, rsForm_single_left]

private theorem rsForm_single_single (i : I) :
    rsForm A (Pi.single i 1) (Pi.single i 1) = A i i := by
  rw [rsForm_single_left]
  simp [Pi.single_apply]

private theorem rsForm_sub_left (x x' y : I → ℤ) :
    rsForm A (x - x') y = rsForm A x y - rsForm A x' y := by
  simp only [rsForm, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

private theorem rsForm_smul_left (a : ℤ) (x y : I → ℤ) :
    rsForm A (a • x) y = a * rsForm A x y := by
  simp only [rsForm, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

private theorem rsForm_sub_right (x y y' : I → ℤ) :
    rsForm A x (y - y') = rsForm A x y - rsForm A x y' := by
  simp only [rsForm, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

private theorem rsForm_smul_right (hS : A.IsSymm) (a : ℤ) (x y : I → ℤ) :
    rsForm A x (a • y) = a * rsForm A x y := by
  rw [rsForm_comm hS, rsForm_smul_left, rsForm_comm hS]

private theorem rsForm_reflection (hA : TauCeti.IsFiniteType A) (hS : A.IsSymm) (i : I)
    (x y : I → ℤ) : rsForm A (reflection A i x) (reflection A i y) = rsForm A x y := by
  set a : ℤ := ∑ j, A i j * x j with ha
  set b : ℤ := ∑ j, A i j * y j with hb
  have hx : reflection A i x = x - a • Pi.single i 1 := by
    rw [reflection_apply, ← ha]
  have hy : reflection A i y = y - b • Pi.single i 1 := by
    rw [reflection_apply, ← hb]
  rw [hx, hy]
  calc
    rsForm A (x - a • Pi.single i 1) (y - b • Pi.single i 1)
        = rsForm A x (y - b • Pi.single i 1) -
            a * rsForm A (Pi.single i 1) (y - b • Pi.single i 1) := by
          rw [rsForm_sub_left, rsForm_smul_left]
    _ = (rsForm A x y - b * rsForm A x (Pi.single i 1)) -
          a * (rsForm A (Pi.single i 1) y -
            b * rsForm A (Pi.single i 1) (Pi.single i 1)) := by
          rw [rsForm_sub_right, rsForm_smul_right hS, rsForm_sub_right,
            rsForm_smul_right hS]
    _ = (rsForm A x y - b * a) - a * (b - b * 2) := by
          rw [rsForm_single_right hS, rsForm_single_left, rsForm_single_single, ← ha, ← hb,
            hA.apply_self]
    _ = rsForm A x y := by ring

private theorem rsForm_weylAction (hA : TauCeti.IsFiniteType A) (hS : A.IsSymm)
    (w : (coxeterMatrix hA).Group) (x y : I → ℤ) :
    rsForm A (weylAction hA w x) (weylAction hA w y) = rsForm A x y := by
  induction w using (coxeterMatrix hA).toCoxeterSystem.simple_induction_left generalizing x y with
  | one => simp
  | mul_simple_left w i ih =>
    rw [weylAction_mul_apply, weylAction_mul_apply, weylAction_simple, rsForm_reflection hA hS, ih]

theorem rsForm_root (hA : TauCeti.IsFiniteType A) (hS : A.IsSymm) {γ : I → ℤ}
    (hγ : γ ∈ roots hA ∅) : rsForm A γ γ = 2 := by
  rcases hγ with ⟨w, i, rfl⟩ | ⟨w, i, hi, rfl⟩
  · rw [rsForm_weylAction hA hS, rsForm_single_left]
    simp [Pi.single_apply, hA.apply_self]
  · exact absurd hi (by simp)

private theorem rsForm_eq_sum_support {J : Finset I} {x y : I → ℤ}
    (hx : ∀ k ∉ J, x k = 0) (hy : ∀ k ∉ J, y k = 0) :
    rsForm A x y = ∑ i ∈ J, x i * ∑ j ∈ J, A i j * y j := by
  unfold rsForm
  rw [← Finset.sum_subset (Finset.subset_univ J)]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_subset (Finset.subset_univ J)]
    exact fun j _ hj => by rw [hy j hj, mul_zero]
  · exact fun i _ hi => by rw [hx i hi, zero_mul]

private theorem rsForm_eq_single {i : I} {x y : I → ℤ}
    (hx : ∀ k ∉ ({i} : Finset I), x k = 0) (hy : ∀ k ∉ ({i} : Finset I), y k = 0) :
    rsForm A x y = x i * (A i i * y i) := by
  rw [rsForm_eq_sum_support (J := {i}) hx hy]
  simp

private theorem rsForm_eq_pair {i j : I} (hij : i ≠ j) {x y : I → ℤ}
    (hx : ∀ k ∉ ({i, j} : Finset I), x k = 0)
    (hy : ∀ k ∉ ({i, j} : Finset I), y k = 0) :
    rsForm A x y = x i * (A i i * y i + A i j * y j) +
      x j * (A j i * y i + A j j * y j) := by
  rw [rsForm_eq_sum_support (J := {i, j}) hx hy]
  rw [Finset.sum_pair hij, Finset.sum_pair hij, Finset.sum_pair hij]

private theorem apply_eq_zero_or_neg_one_of_ne (hA : TauCeti.IsFiniteType A) (hS : A.IsSymm)
    {i j : I} (hij : i ≠ j) : A i j = 0 ∨ A i j = -1 := by
  rcases cartan_pair_cases hA hij with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ |
    ⟨h, h'⟩
  · exact Or.inl h
  · exact Or.inr h
  all_goals
    exfalso
    have := hS.apply i j
    rw [h, h'] at this
    omega

private theorem abs_le_one_of_support (hA : TauCeti.IsFiniteType A) (hS : A.IsSymm)
    {J : Finset I} (hJ : J.card ≤ 2) {γ : I → ℤ} (hγ : γ ∈ roots hA ∅)
    (hsupp : ∀ k ∉ J, γ k = 0) (k : I) : |γ k| ≤ 1 := by
  have hroot := rsForm_root hA hS hγ
  have hcases : J.card = 0 ∨ J.card = 1 ∨ J.card = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · have hJ0 : J = ∅ := Finset.card_eq_zero.mp h0
    rw [hsupp k (by rw [hJ0]; simp)]
    norm_num
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp h1
    have hsum : rsForm A γ γ = 2 * γ i ^ 2 := by
      rw [rsForm_eq_single (i := i) (x := γ) (y := γ) hsupp hsupp, hA.apply_self]
      ring
    rw [hsum] at hroot
    have hsq : γ i ^ 2 = 1 := by omega
    have hb : |γ i| ≤ 1 := (sq_le_one_iff_abs_le_one (γ i)).mp (le_of_eq hsq)
    rcases eq_or_ne k i with rfl | hki
    · exact hb
    · rw [hsupp k (by simp [hki])]
      norm_num
  · obtain ⟨i, j, hij, hJeq⟩ := Finset.card_eq_two.mp h2
    rw [hJeq] at hsupp
    have hsum : rsForm A γ γ = 2 * γ i ^ 2 + 2 * A i j * γ i * γ j + 2 * γ j ^ 2 := by
      rw [rsForm_eq_pair (i := i) (j := j) (x := γ) (y := γ) hij hsupp hsupp,
        hA.apply_self i, hA.apply_self j, hS.apply i j]
      ring
    rw [hsum] at hroot
    rcases apply_eq_zero_or_neg_one_of_ne hA hS hij with hAij | hAij
    · rw [hAij] at hroot
      have h' : 2 * γ i ^ 2 + 2 * γ j ^ 2 = 2 := by simpa using hroot
      have hkey : γ i ^ 2 + γ j ^ 2 = 1 := by nlinarith
      have hsq : γ i ^ 2 ≤ 1 := by
        have hb2 : 0 ≤ γ j ^ 2 := sq_nonneg _
        omega
      have hb : |γ i| ≤ 1 := (sq_le_one_iff_abs_le_one (γ i)).mp hsq
      have hsqj : γ j ^ 2 ≤ 1 := by
        have hb1 : 0 ≤ γ i ^ 2 := sq_nonneg _
        omega
      have hbj : |γ j| ≤ 1 := (sq_le_one_iff_abs_le_one (γ j)).mp hsqj
      rcases eq_or_ne k i with hki | hki
      · rw [hki]; exact hb
      · rcases eq_or_ne k j with hkj | hkj
        · rw [hkj]; exact hbj
        · rw [hsupp k (by simp [hki, hkj])]
          norm_num
    · rw [hAij] at hroot
      have hkey : γ i ^ 2 - γ i * γ j + γ j ^ 2 = 1 := by nlinarith
      have hsq : γ i ^ 2 ≤ 1 := by
        have h3 : 3 * (γ i ^ 2) ≤ 4 := by nlinarith [sq_nonneg (2 * γ j - γ i)]
        omega
      have hb : |γ i| ≤ 1 := (sq_le_one_iff_abs_le_one (γ i)).mp hsq
      have hsqj : γ j ^ 2 ≤ 1 := by
        have h3 : 3 * (γ j ^ 2) ≤ 4 := by nlinarith [sq_nonneg (2 * γ i - γ j)]
        omega
      have hbj : |γ j| ≤ 1 := (sq_le_one_iff_abs_le_one (γ j)).mp hsqj
      rcases eq_or_ne k i with hki | hki
      · rw [hki]; exact hb
      · rcases eq_or_ne k j with hkj | hkj
        · rw [hkj]; exact hbj
        · rw [hsupp k (by simp [hki, hkj])]
          norm_num

private theorem eq_zero_of_dvd_coroot (hA : TauCeti.IsFiniteType A) (hS : A.IsSymm)
    (hpend : ∀ i j, A i j = -1 → ∃ m, (A m i = -1 ∧ A m j = 0) ∨ (A m i = 0 ∧ A m j = -1))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {J : Finset I} (hJ : J.card ≤ 2) {v : I → ℤ}
    (hsupp : ∀ k ∉ J, v k = 0) (hv : ∀ k, |v k| ≤ 2)
    (hdvd : ∀ i, (p : ℤ) ∣ ∑ j, A i j * v j) : v = 0 := by
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hp3' : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp3
  have hpdvd2 : ¬ (p : ℤ) ∣ 2 := by
    intro h
    have hle : (p : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num : (0 : ℤ) < 2) h
    omega
  have hdvd2 : ∀ x : ℤ, (p : ℤ) ∣ 2 * x → (p : ℤ) ∣ x := by
    intro x hx
    have hpint : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    rcases hpint.dvd_or_dvd hx with h2 | hx'
    · exact absurd h2 hpdvd2
    · exact hx'
  have hzero : ∀ x : ℤ, (p : ℤ) ∣ x → |x| ≤ 2 → x = 0 := by
    intro x hx hx2
    refine Int.eq_zero_of_abs_lt_dvd hx ?_
    rw [abs_lt]
    have hb := abs_le.mp hx2
    omega
  have hcases : J.card = 0 ∨ J.card = 1 ∨ J.card = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · have hJ0 : J = ∅ := Finset.card_eq_zero.mp h0
    funext k
    exact hsupp k (by rw [hJ0]; simp)
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp h1
    have hrow : ∑ j, A i j * v j = 2 * v i := by
      rw [Finset.sum_eq_single i]
      · rw [hA.apply_self]
      · intro j _ hji
        rw [hsupp j (by simpa using hji), mul_zero]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    have hvi : v i = 0 :=
      hzero (v i) (hdvd2 (v i) (by rw [← hrow]; exact hdvd i)) (hv i)
    funext k
    rcases eq_or_ne k i with rfl | hki
    · exact hvi
    · exact hsupp k (by simp [hki])
  · obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp h2
    have hrow : ∀ k, ∑ m, A k m * v m = A k i * v i + A k j * v j := by
      intro k
      rw [← Finset.sum_subset (Finset.subset_univ ({i, j} : Finset I))
        (fun m _ hm => by rw [hsupp m hm, mul_zero]), Finset.sum_pair hij]
    rcases apply_eq_zero_or_neg_one_of_ne hA hS hij with hAij | hAij
    · have hai : v i = 0 := by
        refine hzero (v i) (hdvd2 (v i) ?_) (hv i)
        have hi := hdvd i
        rw [hrow i, hA.apply_self i, hAij] at hi
        simpa using hi
      have hbj : v j = 0 := by
        refine hzero (v j) (hdvd2 (v j) ?_) (hv j)
        have hj := hdvd j
        rw [hrow j, hS.apply i j, hAij, hA.apply_self j] at hj
        simpa using hj
      funext k
      rcases eq_or_ne k i with rfl | hki
      · exact hai
      · rcases eq_or_ne k j with rfl | hkj
        · exact hbj
        · exact hsupp k (by simp [hki, hkj])
    · obtain ⟨m, hm | hm⟩ := hpend i j hAij
      · obtain ⟨hmi, hmj⟩ := hm
        have ha : v i = 0 := by
          have hm' := hdvd m
          rw [hrow m, hmi, hmj] at hm'
          have hm0 : (p : ℤ) ∣ -v i := by
            simpa only [neg_one_mul, zero_mul, mul_zero, add_zero, zero_add] using hm'
          exact hzero (v i) (dvd_neg.mp hm0) (hv i)
        have hb : v j = 0 := by
          have hi := hdvd i
          rw [hrow i, hA.apply_self i, hAij, ha] at hi
          have hi0 : (p : ℤ) ∣ -v j := by
            simpa only [neg_one_mul, zero_mul, mul_zero, add_zero, zero_add] using hi
          exact hzero (v j) (dvd_neg.mp hi0) (hv j)
        funext k
        rcases eq_or_ne k i with rfl | hki
        · exact ha
        · rcases eq_or_ne k j with rfl | hkj
          · exact hb
          · exact hsupp k (by simp [hki, hkj])
      · obtain ⟨hmi, hmj⟩ := hm
        have hb : v j = 0 := by
          have hm' := hdvd m
          rw [hrow m, hmi, hmj] at hm'
          have hm0 : (p : ℤ) ∣ -v j := by
            simpa only [neg_one_mul, zero_mul, mul_zero, add_zero, zero_add] using hm'
          exact hzero (v j) (dvd_neg.mp hm0) (hv j)
        have ha : v i = 0 := by
          have hj := hdvd j
          rw [hrow j, hS.apply i j, hAij, hA.apply_self j, hb] at hj
          have hj0 : (p : ℤ) ∣ -v i := by
            simpa only [neg_one_mul, zero_mul, mul_zero, add_zero, zero_add] using hj
          exact hzero (v i) (dvd_neg.mp hj0) (hv i)
        funext k
        rcases eq_or_ne k i with rfl | hki
        · exact ha
        · rcases eq_or_ne k j with rfl | hkj
          · exact hb
          · exact hsupp k (by simp [hki, hkj])

private theorem rsForm_cast_eq {α β : I → ℤ} {p : ℕ} (c : ZMod p)
    (hprop : ∀ i, ((∑ j, A i j * β j : ℤ) : ZMod p) =
      c * ((∑ j, A i j * α j : ℤ) : ZMod p)) (y : I → ℤ) :
    ((rsForm A y β : ℤ) : ZMod p) = c * ((rsForm A y α : ℤ) : ZMod p) := by
  calc
    ((rsForm A y β : ℤ) : ZMod p)
        = ∑ i, (y i : ZMod p) * ((∑ j, A i j * β j : ℤ) : ZMod p) := by
          simp only [rsForm, Int.cast_sum, Int.cast_mul]
    _ = ∑ i, (y i : ZMod p) *
          (c * ((∑ j, A i j * α j : ℤ) : ZMod p)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hprop i]
    _ = c * ∑ i, (y i : ZMod p) *
          ((∑ j, A i j * α j : ℤ) : ZMod p) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
    _ = c * ((rsForm A y α : ℤ) : ZMod p) := by
          simp only [rsForm, Int.cast_sum, Int.cast_mul]

private theorem rsForm_c_eq_pm_one (hA : TauCeti.IsFiniteType A) (hS : A.IsSymm)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {α β : I → ℤ} (hα : α ∈ roots hA ∅)
    (hβ : β ∈ roots hA ∅) (c : ZMod p)
    (hprop : ∀ i, ((∑ j, A i j * β j : ℤ) : ZMod p) =
      c * ((∑ j, A i j * α j : ℤ) : ZMod p)) :
    c = 1 ∨ c = -1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcast := rsForm_cast_eq (α := α) (β := β) c hprop
  have hαβ : ((rsForm A α β : ℤ) : ZMod p) = c * (2 : ZMod p) := by
    have h := hcast α
    rw [rsForm_root hA hS hα] at h
    simpa using h
  have hβα : (2 : ZMod p) = c * ((rsForm A α β : ℤ) : ZMod p) := by
    have h := hcast β
    rw [rsForm_root hA hS hβ, rsForm_comm hS] at h
    simpa using h
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by norm_num] at h
    rw [ZMod.natCast_eq_zero_iff] at h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
  have h2c : c * (c * 2) = 2 := by
    rw [← hαβ, ← hβα]
  have hsq : (2 : ZMod p) * (c ^ 2 - 1) = 0 := by
    have h' : (2 : ZMod p) * c ^ 2 = 2 := by
      calc
        (2 : ZMod p) * c ^ 2 = c * (c * 2) := by ring
        _ = 2 := h2c
    rw [mul_sub, mul_one, h', sub_self]
  have hc2 : c ^ 2 = 1 := by
    exact sub_eq_zero.mp ((mul_eq_zero.mp hsq).resolve_left h2)
  have hfac : (c - 1) * (c + 1) = 0 := by
    rw [sub_mul, one_mul, mul_add, mul_one, ← pow_two, hc2]
    ring
  rcases mul_eq_zero.mp hfac with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

private theorem ggRootSeparation_aux (hA : TauCeti.IsFiniteType A) (hS : A.IsSymm)
    (hpend : ∀ i j, A i j = -1 → ∃ m, (A m i = -1 ∧ A m j = 0) ∨ (A m i = 0 ∧ A m j = -1))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {α β : I → ℤ} (hα : α ∈ roots hA ∅)
    (hβ : β ∈ roots hA ∅) (c : ZMod p)
    (hprop : ∀ i, ((∑ j, A i j * β j : ℤ) : ZMod p) =
      c * ((∑ j, A i j * α j : ℤ) : ZMod p))
    (ε : ℤ) (hε : ((ε : ℤ) : ZMod p) = c) (hεpm : ε = 1 ∨ ε = -1) :
    β = ε • α := by
  haveI : Fact p.Prime := ⟨hp⟩
  let v : I → ℤ := β - ε • α
  have hdiv : ∀ i, (p : ℤ) ∣ ∑ j, A i j * v j := by
    intro i
    have hv_eval : ∑ j, A i j * v j =
        (∑ j, A i j * β j) - ε * (∑ j, A i j * α j) := by
      calc
        ∑ j, A i j * v j = ∑ j, (A i j * β j - ε * (A i j * α j)) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [v, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          ring
        _ = (∑ j, A i j * β j) - ∑ j, ε * (A i j * α j) := by
          rw [Finset.sum_sub_distrib]
        _ = (∑ j, A i j * β j) - ε * (∑ j, A i j * α j) := by
          rw [Finset.mul_sum]
    have h0 : ((∑ j, A i j * v j : ℤ) : ZMod p) = 0 := by
      calc
        ((∑ j, A i j * v j : ℤ) : ZMod p)
            = ((∑ j, A i j * β j : ℤ) : ZMod p) -
                (ε : ZMod p) * ((∑ j, A i j * α j : ℤ) : ZMod p) := by
              rw [hv_eval]
              push_cast
              ring
        _ = c * ((∑ j, A i j * α j : ℤ) : ZMod p) -
                (ε : ZMod p) * ((∑ j, A i j * α j : ℤ) : ZMod p) := by
              rw [hprop i]
        _ = 0 := by
              rw [hε]
              ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 h0
  obtain ⟨u, J, hJ, hsupp⟩ := exists_weylAction_support_subset hA ∅ hα hβ
  let α' : I → ℤ := weylAction hA u α
  let β' : I → ℤ := weylAction hA u β
  let v' : I → ℤ := β' - ε • α'
  have hαsupp : ∀ k ∉ J, α' k = 0 := by
    intro k hk
    exact hsupp α hα ⟨1, 0, by intro m; simp⟩ k hk
  have hβsupp : ∀ k ∉ J, β' k = 0 := by
    intro k hk
    exact hsupp β hβ ⟨0, 1, by intro m; simp⟩ k hk
  have hαroot : α' ∈ roots hA ∅ := by
    simpa [α'] using weylAction_mem_roots hA u hα
  have hβroot : β' ∈ roots hA ∅ := by
    simpa [β'] using weylAction_mem_roots hA u hβ
  have hα1 : ∀ k, |α' k| ≤ 1 := fun k =>
    abs_le_one_of_support hA hS hJ hαroot hαsupp k
  have hβ1 : ∀ k, |β' k| ≤ 1 := fun k =>
    abs_le_one_of_support hA hS hJ hβroot hβsupp k
  have hεabs : |ε| = 1 := by
    rcases hεpm with h | h <;> simp [h]
  have hsuppv : ∀ k ∉ J, v' k = 0 := by
    intro k hk
    simp [v', hαsupp k hk, hβsupp k hk]
  have hv2 : ∀ k, |v' k| ≤ 2 := by
    intro k
    have hk : v' k = β' k - ε * α' k := by
      simp [v', Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [hk]
    calc
      |β' k - ε * α' k| ≤ |β' k| + |ε * α' k| := abs_sub _ _
      _ = |β' k| + |ε| * |α' k| := by rw [abs_mul]
      _ = |β' k| + |α' k| := by rw [hεabs, one_mul]
      _ ≤ 1 + 1 := by linarith [hβ1 k, hα1 k]
      _ = 2 := by norm_num
  have hv' : weylAction hA u v = v' := by
    simp only [v, v', α', β', map_sub, map_smul]
  have hdvd : ∀ i, (p : ℤ) ∣ ∑ j, A i j * v' j := by
    intro i
    rw [← rsForm_single_left]
    rw [← hv']
    rw [← weylAction_apply_inv_apply hA u (Pi.single i 1)]
    rw [rsForm_weylAction hA hS]
    rw [rsForm]
    exact Finset.dvd_sum fun k _ =>
      dvd_mul_of_dvd_right (hdiv k) ((weylAction hA u⁻¹ (Pi.single i 1)) k)
  have hv'0 : v' = 0 := eq_zero_of_dvd_coroot hA hS hpend hp hp2 hJ hsuppv hv2 hdvd
  have hwv : weylAction hA u v = 0 := by rw [hv', hv'0]
  have hv0 : v = 0 := (weylAction_apply_injective hA u) (by rw [hwv, map_zero])
  exact sub_eq_zero.mp (by simpa [v] using hv0)

theorem ggRootSeparation_of_pendant (hA : TauCeti.IsFiniteType A) (hS : A.IsSymm)
    (hpend : ∀ i j, A i j = -1 → ∃ m, (A m i = -1 ∧ A m j = 0) ∨ (A m i = 0 ∧ A m j = -1))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {α β : I → ℤ} (hα : α ∈ roots hA ∅)
    (hβ : β ∈ roots hA ∅) (c : ZMod p)
    (hprop : ∀ i, ((∑ j, A i j * β j : ℤ) : ZMod p) = c * ((∑ j, A i j * α j : ℤ) : ZMod p)) :
    β = α ∨ β = -α := by
  rcases rsForm_c_eq_pm_one hA hS hp hp2 hα hβ c hprop with hc | hc
  · have hε : ((1 : ℤ) : ZMod p) = c := by rw [hc]; norm_num
    have h := ggRootSeparation_aux hA hS hpend hp hp2 hα hβ c hprop 1 hε (Or.inl rfl)
    exact Or.inl (by simpa using h)
  · have hε : ((-1 : ℤ) : ZMod p) = c := by rw [hc]; norm_num
    have h := ggRootSeparation_aux hA hS hpend hp hp2 hα hβ c hprop (-1) hε (Or.inr rfl)
    exact Or.inr (by simpa using h)

end Generic

end CFSG.StandardType

end
