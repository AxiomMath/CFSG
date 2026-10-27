module

public import CFSG.Monster.SteinbergBQOddPrimeCongruenceTorsionFree
public import CFSG.Monster.Griess.Product

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Griess.ModFive

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin Matrix

instance fact_prime_five : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

abbrev R5 : Subring ℚ := ratLocal 5

theorem dyadic_le_R5 : dyadic ≤ R5 := by
  rintro q ⟨k, hk⟩ h5
  have h : 5 ∣ 2 ^ k := h5.trans hk
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_five h
  omega

theorem natCast_mem_R5 (n : ℕ) : (n : ℚ) ∈ R5 := natCast_mem _ n

theorem eight_mem_R5 : (8 : ℚ) ∈ R5 := natCast_mem_R5 8

theorem inv_two_mem_R5 : (2 : ℚ)⁻¹ ∈ R5 := dyadic_le_R5 inv_two_mem_dyadic'

theorem inv_four_mem_R5 : (4 : ℚ)⁻¹ ∈ R5 := dyadic_le_R5 inv_four_mem_dyadic

theorem inv_eight_mem_R5 : (8 : ℚ)⁻¹ ∈ R5 := dyadic_le_R5 inv_eight_mem_dyadic

theorem inv_mem_R5_of_int {n : ℤ} (hn : ¬ (5 : ℤ) ∣ n) : (n : ℚ)⁻¹ ∈ R5 := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn (dvd_zero _)
  refine (mem_ratLocal_iff 5).2 ⟨1, n, hn0, by exact_mod_cast hn, ?_⟩
  rw [Int.cast_one, one_div]

theorem inv_28_mem_R5 : (28 : ℚ)⁻¹ ∈ R5 := by
  have h := inv_mem_R5_of_int (n := 28) (by norm_num)
  rwa [Int.cast_ofNat] at h

theorem inv_32_mem_R5 : (32 : ℚ)⁻¹ ∈ R5 := by
  have h := inv_mem_R5_of_int (n := 32) (by norm_num)
  rwa [Int.cast_ofNat] at h

theorem div_eight_mem_R5 {x : ℚ} (hx : x ∈ R5) : x / 8 ∈ R5 := by
  rw [div_eq_mul_inv]
  exact mul_mem hx inv_eight_mem_R5

theorem div_four_mem_R5 {x : ℚ} (hx : x ∈ R5) : x / 4 ∈ R5 := by
  rw [div_eq_mul_inv]
  exact mul_mem hx inv_four_mem_R5

@[expose] def D5 : AddSubgroup ℚ where
  carrier := {x | x / 5 ∈ R5}
  add_mem' {x y} hx hy := by
    change (x + y) / 5 ∈ R5
    rw [add_div]
    exact add_mem hx hy
  zero_mem' := by
    change (0 : ℚ) / 5 ∈ R5
    rw [zero_div]
    exact zero_mem _
  neg_mem' {x} hx := by
    change -x / 5 ∈ R5
    rw [neg_div]
    exact neg_mem hx

theorem mem_D5 {x : ℚ} : x ∈ D5 ↔ x / 5 ∈ R5 := Iff.rfl

theorem mem_D5_iff_inv_mul {x : ℚ} : x ∈ D5 ↔ (5 : ℚ)⁻¹ * x ∈ R5 := by
  rw [mem_D5, div_eq_inv_mul]

theorem mem_R5_of_mem_D5 {x : ℚ} (hx : x ∈ D5) : x ∈ R5 := by
  have e : x = 5 * (x / 5) := by ring
  rw [e]
  exact mul_mem (natCast_mem_R5 5) hx

theorem mul_mem_D5 {r x : ℚ} (hr : r ∈ R5) (hx : x ∈ D5) : r * x ∈ D5 := by
  rw [mem_D5, mul_div_assoc]
  exact mul_mem hr hx

theorem mul_mem_D5' {r x : ℚ} (hx : x ∈ D5) (hr : r ∈ R5) : x * r ∈ D5 := by
  rw [mul_comm]
  exact mul_mem_D5 hr hx

theorem five_mul_mem_D5 {x : ℚ} (hx : x ∈ R5) : 5 * x ∈ D5 := by
  rw [mem_D5, mul_div_cancel_left₀ _ (by norm_num : (5 : ℚ) ≠ 0)]
  exact hx

theorem ratLocalRed_eq_zero_iff_mem_D5 (x : R5) : ratLocalRed 5 x = 0 ↔ (x : ℚ) ∈ D5 := by
  rw [ratLocalRed_eq_zero_iff]
  constructor
  · rintro ⟨y, hy⟩
    have h : (x : ℚ) = 5 * (y : ℚ) := by
      rw [hy]
      push_cast
      rfl
    rw [mem_D5, h, mul_div_cancel_left₀ _ (by norm_num : (5 : ℚ) ≠ 0)]
    exact y.2
  · intro h
    refine ⟨⟨(x : ℚ) / 5, h⟩, Subtype.ext ?_⟩
    change (x : ℚ) = ((5 : ℕ) : ℚ) * ((x : ℚ) / 5)
    push_cast
    ring

theorem inv_mem_R5 {x : ℚ} (hx : x ∈ R5) (hx5 : x ∉ D5) : x⁻¹ ∈ R5 := by
  have hred : ratLocalRed 5 ⟨x, hx⟩ ≠ 0 := fun h =>
    hx5 ((ratLocalRed_eq_zero_iff_mem_D5 ⟨x, hx⟩).1 h)
  obtain ⟨w, hw⟩ := (isUnit_of_ratLocalRed_ne_zero 5 hred).exists_right_inv
  have h1 : x * (w : ℚ) = 1 := congrArg Subtype.val hw
  rw [inv_eq_of_mul_eq_one_right h1]
  exact w.2

theorem ne_zero_of_not_mem_D5 {x : ℚ} (hx : x ∉ D5) : x ≠ 0 := by
  rintro rfl
  exact hx (zero_mem _)

theorem mem_D5_of_mul_mem {x y : ℚ} (hx : x ∈ R5) (hx5 : x ∉ D5) (hxy : x * y ∈ D5) :
    y ∈ D5 := by
  have e : y = x⁻¹ * (x * y) := by
    rw [← mul_assoc, inv_mul_cancel₀ (ne_zero_of_not_mem_D5 hx5), one_mul]
  rw [e]
  exact mul_mem_D5 (inv_mem_R5 hx hx5) hxy

theorem mul_not_mem_D5 {x y : ℚ} (hx : x ∈ R5) (hx5 : x ∉ D5) (hy5 : y ∉ D5) : x * y ∉ D5 :=
  fun h => hy5 (mem_D5_of_mul_mem hx hx5 h)

theorem intCast_mem_D5_iff (n : ℤ) : (n : ℚ) ∈ D5 ↔ (5 : ℤ) ∣ n := by
  rw [← ratLocalRed_eq_zero_iff_mem_D5 ⟨(n : ℚ), intCast_mem _ n⟩]
  have h : (⟨(n : ℚ), intCast_mem _ n⟩ : R5) = (n : R5) := Subtype.ext (by push_cast; rfl)
  rw [h, map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
  norm_cast

@[expose] def IsR5 {m n : Type*} (M : Matrix m n ℚ) : Prop := ∀ i j, M i j ∈ R5

@[expose] def IsD5 {m n : Type*} (M : Matrix m n ℚ) : Prop := ∀ i j, M i j ∈ D5

section Mat

variable {l m n ι : Type*}

theorem IsR5.add {M N : Matrix m n ℚ} (hM : IsR5 M) (hN : IsR5 N) : IsR5 (M + N) :=
  fun i j => add_mem (hM i j) (hN i j)

theorem IsR5.sub {M N : Matrix m n ℚ} (hM : IsR5 M) (hN : IsR5 N) : IsR5 (M - N) :=
  fun i j => sub_mem (hM i j) (hN i j)

theorem IsR5.smul {M : Matrix m n ℚ} (hM : IsR5 M) {c : ℚ} (hc : c ∈ R5) : IsR5 (c • M) :=
  fun i j => mul_mem hc (hM i j)

theorem IsR5.transpose {M : Matrix m n ℚ} (hM : IsR5 M) : IsR5 Mᵀ := fun i j => hM j i

theorem IsR5.mul [Fintype m] {M : Matrix l m ℚ} {N : Matrix m n ℚ} (hM : IsR5 M) (hN : IsR5 N) :
    IsR5 (M * N) :=
  fun i j => sum_mem fun k _ => mul_mem (hM i k) (hN k j)

theorem IsR5.trace_mem [Fintype n] {M : Matrix n n ℚ} (hM : IsR5 M) : trace M ∈ R5 :=
  sum_mem fun i _ => hM i i

theorem isR5_sum (s : Finset ι) {M : ι → Matrix m n ℚ} (h : ∀ k ∈ s, IsR5 (M k)) :
    IsR5 (∑ k ∈ s, M k) := fun i j => by
  rw [Matrix.sum_apply]
  exact sum_mem fun k hk => h k hk i j

theorem isR5_one [DecidableEq n] : IsR5 (1 : Matrix n n ℚ) := fun i j => by
  rw [Matrix.one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem isR5_single [DecidableEq m] [DecidableEq n] (i : m) (j : n) :
    IsR5 (Matrix.single i j (1 : ℚ)) := fun k l => by
  rw [Matrix.single_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem IsDyM.isR5 {M : Matrix m n ℚ} (hM : IsDyM M) : IsR5 M := fun i j => dyadic_le_R5 (hM i j)

theorem IsD5.add {M N : Matrix m n ℚ} (hM : IsD5 M) (hN : IsD5 N) : IsD5 (M + N) :=
  fun i j => add_mem (hM i j) (hN i j)

theorem IsD5.sub {M N : Matrix m n ℚ} (hM : IsD5 M) (hN : IsD5 N) : IsD5 (M - N) :=
  fun i j => sub_mem (hM i j) (hN i j)

theorem IsD5.neg {M : Matrix m n ℚ} (hM : IsD5 M) : IsD5 (-M) :=
  fun i j => neg_mem (hM i j)

theorem IsD5.smul {M : Matrix m n ℚ} (hM : IsD5 M) {c : ℚ} (hc : c ∈ R5) : IsD5 (c • M) :=
  fun i j => mul_mem_D5 hc (hM i j)

theorem IsD5.isR5 {M : Matrix m n ℚ} (hM : IsD5 M) : IsR5 M :=
  fun i j => mem_R5_of_mem_D5 (hM i j)

theorem isD5_zero : IsD5 (0 : Matrix m n ℚ) := fun _ _ => zero_mem _

theorem isD5_sum (s : Finset ι) {M : ι → Matrix m n ℚ} (h : ∀ k ∈ s, IsD5 (M k)) :
    IsD5 (∑ k ∈ s, M k) := fun i j => by
  rw [Matrix.sum_apply]
  exact sum_mem fun k hk => h k hk i j

theorem IsR5.mul_D5 [Fintype m] {M : Matrix l m ℚ} {N : Matrix m n ℚ} (hM : IsR5 M)
    (hN : IsD5 N) : IsD5 (M * N) :=
  fun i j => sum_mem fun k _ => mul_mem_D5 (hM i k) (hN k j)

theorem IsD5.mul_R5 [Fintype m] {M : Matrix l m ℚ} {N : Matrix m n ℚ} (hM : IsD5 M)
    (hN : IsR5 N) : IsD5 (M * N) :=
  fun i j => sum_mem fun k _ => mul_mem_D5' (hM i k) (hN k j)

theorem isD5_iff_smul {M : Matrix m n ℚ} : IsD5 M ↔ IsR5 ((5 : ℚ)⁻¹ • M) := by
  simp only [IsD5, IsR5, mem_D5_iff_inv_mul, Matrix.smul_apply, smul_eq_mul]

end Mat

theorem Umat_isR5 (c : ShortIdx) : IsR5 (Umat c) := IsDyM.isR5 (Umat_isDyM c)

theorem Rmat_isR5 (c : ShortIdx) : IsR5 (Rmat c) := IsDyM.isR5 (Rmat_isDyM c)

theorem uQ_mem_R5 (c : ShortIdx) (i : Fin 24) : uQ c i ∈ R5 := dyadic_le_R5 (uQ_mem_dyadic c i)

theorem qf_mem_R5 (c : ShortIdx) {M : Matrix (Fin 24) (Fin 24) ℚ} (hM : IsR5 M) :
    qf c M ∈ R5 := by
  unfold qf
  exact sum_mem fun i _ => mul_mem (uQ_mem_R5 c i)
    (sum_mem fun j _ => mul_mem (hM i j) (uQ_mem_R5 c j))

theorem tau_mem_R5 (d e c : ShortIdx) : tau d e c ∈ R5 := dyadic_le_R5 (tau_mem_dyadic d e c)

@[expose] def Int5 (v : SpaceB) : Prop :=
  (∀ i j, (v.1 : Matrix (Fin 24) (Fin 24) ℚ) i j ∈ ratLocal 5) ∧ (∀ c, v.2.1 c ∈ ratLocal 5) ∧
    ∀ j i, v.2.2 j i ∈ ratLocal 5

@[expose] def Cong5 (u v : SpaceB) : Prop := Int5 u ∧ Int5 v ∧ Int5 ((5 : ℚ)⁻¹ • (u - v))

@[expose] def Div5 (v : SpaceB) : Prop :=
  IsD5 (Am v) ∧ (∀ c, xs v c ∈ D5) ∧ IsD5 (Nm v)

theorem int5_iff (v : SpaceB) : Int5 v ↔ IsR5 (Am v) ∧ (∀ c, xs v c ∈ R5) ∧ IsR5 (Nm v) :=
  Iff.rfl

@[expose] def L5 : AddSubgroup SpaceB where
  carrier := {v | Int5 v}
  add_mem' {_ _} hu hv :=
    ⟨fun i j => add_mem (hu.1 i j) (hv.1 i j), fun c => add_mem (hu.2.1 c) (hv.2.1 c),
      fun j i => add_mem (hu.2.2 j i) (hv.2.2 j i)⟩
  zero_mem' := ⟨fun _ _ => zero_mem _, fun _ => zero_mem _, fun _ _ => zero_mem _⟩
  neg_mem' {_} hu :=
    ⟨fun i j => neg_mem (hu.1 i j), fun c => neg_mem (hu.2.1 c), fun j i => neg_mem (hu.2.2 j i)⟩

@[expose] def M5 : AddSubgroup SpaceB where
  carrier := {v | Div5 v}
  add_mem' {_ _} hu hv :=
    ⟨fun i j => add_mem (hu.1 i j) (hv.1 i j), fun c => add_mem (hu.2.1 c) (hv.2.1 c),
      fun j i => add_mem (hu.2.2 j i) (hv.2.2 j i)⟩
  zero_mem' := ⟨fun _ _ => zero_mem _, fun _ => zero_mem _, fun _ _ => zero_mem _⟩
  neg_mem' {_} hu :=
    ⟨fun i j => neg_mem (hu.1 i j), fun c => neg_mem (hu.2.1 c), fun j i => neg_mem (hu.2.2 j i)⟩

theorem mem_L5 {v : SpaceB} : v ∈ L5 ↔ Int5 v := Iff.rfl

theorem mem_M5 {v : SpaceB} : v ∈ M5 ↔ Div5 v := Iff.rfl

theorem mem_M5_iff_smul {v : SpaceB} : v ∈ M5 ↔ (5 : ℚ)⁻¹ • v ∈ L5 := by
  simp only [mem_M5, mem_L5, Div5, Int5, IsD5, mem_D5_iff_inv_mul]
  exact Iff.rfl

theorem cong5_iff {u v : SpaceB} : Cong5 u v ↔ u ∈ L5 ∧ v ∈ L5 ∧ u - v ∈ M5 := by
  rw [mem_M5_iff_smul]
  exact Iff.rfl

theorem M5_le_L5 : M5 ≤ L5 := fun _ hv =>
  ⟨fun i j => mem_R5_of_mem_D5 (hv.1 i j), fun c => mem_R5_of_mem_D5 (hv.2.1 c),
    fun j i => mem_R5_of_mem_D5 (hv.2.2 j i)⟩

theorem smul_mem_L5 {r : ℚ} (hr : r ∈ R5) {v : SpaceB} (hv : v ∈ L5) : r • v ∈ L5 :=
  ⟨fun i j => mul_mem hr (hv.1 i j), fun c => mul_mem hr (hv.2.1 c),
    fun j i => mul_mem hr (hv.2.2 j i)⟩

theorem smul_mem_M5 {r : ℚ} (hr : r ∈ R5) {v : SpaceB} (hv : v ∈ M5) : r • v ∈ M5 :=
  ⟨fun i j => mul_mem_D5 hr (hv.1 i j), fun c => mul_mem_D5 hr (hv.2.1 c),
    fun j i => mul_mem_D5 hr (hv.2.2 j i)⟩

theorem five_smul_mem_M5 {v : SpaceB} (hv : v ∈ L5) : (5 : ℚ) • v ∈ M5 := by
  rw [mem_M5_iff_smul, smul_smul, inv_mul_cancel₀ (by norm_num : (5 : ℚ) ≠ 0), one_smul]
  exact hv

theorem inA_mem_L5_iff {A : symMat} :
    inA A ∈ L5 ↔ IsR5 (A : Matrix (Fin 24) (Fin 24) ℚ) :=
  ⟨fun h => h.1, fun h => ⟨h, fun _ => zero_mem _, fun _ _ => zero_mem _⟩⟩

theorem inX_mem_L5_iff {x : SpaceX} : inX x ∈ L5 ↔ ∀ c, x c ∈ R5 :=
  ⟨fun h => h.2.1, fun h => ⟨fun _ _ => zero_mem _, h, fun _ _ => zero_mem _⟩⟩

theorem inW_mem_L5_iff {N : SpaceW} : inW N ∈ L5 ↔ IsR5 N :=
  ⟨fun h => h.2.2, fun h => ⟨fun _ _ => zero_mem _, fun _ => zero_mem _, h⟩⟩

theorem inW_mem_M5_iff {N : SpaceW} : inW N ∈ M5 ↔ IsD5 N :=
  ⟨fun h => h.2.2, fun h => ⟨fun _ _ => zero_mem _, fun _ => zero_mem _, h⟩⟩

theorem gmulA_isR5 {u v : SpaceB} (hu : Int5 u) (hv : Int5 v) : IsR5 (gmulA u v) := by
  have hAu : IsR5 (Am u) := hu.1
  have hAv : IsR5 (Am v) := hv.1
  have hNu : IsR5 (Nm u) := hu.2.2
  have hNv : IsR5 (Nm v) := hv.2.2
  unfold gmulA
  refine (((IsR5.smul ((hAu.mul hAv).add (hAv.mul hAu)) (natCast_mem_R5 2)).add
    (IsR5.smul (isR5_sum _ fun c _ => (Umat_isR5 c).smul
      (mul_mem (hu.2.1 c) (hv.2.1 c))) inv_eight_mem_R5)).add
    (isR5_one.smul (div_eight_mem_R5 (hNu.transpose.mul hNv).trace_mem))).add
    (IsR5.smul ((hNu.transpose.mul hNv).add (hNv.transpose.mul hNu)) inv_two_mem_R5)

theorem gmulX_mem_R5 {u v : SpaceB} (hu : Int5 u) (hv : Int5 v) (c : ShortIdx) :
    gmulX u v c ∈ R5 := by
  have hAu : IsR5 (Am u) := hu.1
  have hAv : IsR5 (Am v) := hv.1
  have hNu : IsR5 (Nm u) := hu.2.2
  have hNv : IsR5 (Nm v) := hv.2.2
  have hM : IsR5 ((Nm u)ᵀ * Rmat c * Nm v) := (hNu.transpose.mul (Rmat_isR5 c)).mul hNv
  unfold gmulX
  refine add_mem (add_mem (div_eight_mem_R5 (add_mem (mul_mem (hv.2.1 c)
    (qf_mem_R5 c hAu)) (mul_mem (hu.2.1 c) (qf_mem_R5 c hAv))))
    (sum_mem fun d _ => sum_mem fun e _ => mul_mem (mul_mem (hu.2.1 d) (hv.2.1 e))
      (tau_mem_R5 d e c)))
    (div_eight_mem_R5 (sub_mem hM.trace_mem (div_four_mem_R5 (qf_mem_R5 c hM))))

theorem gmulWHalf_isR5 {u v : SpaceB} (hu : Int5 u) (hv : Int5 v) : IsR5 (gmulWHalf u v) := by
  have hAu : IsR5 (Am u) := hu.1
  have hNv : IsR5 (Nm v) := hv.2.2
  unfold gmulWHalf
  refine ((hNv.smul (div_eight_mem_R5 hAu.trace_mem)).add (hNv.mul hAu)).add
    (IsR5.smul (isR5_sum _ fun c _ => IsR5.smul (((Rmat_isR5 c).mul hNv).sub
      ((((Rmat_isR5 c).mul hNv).mul (Umat_isR5 c)).smul inv_four_mem_R5)) (hu.2.1 c))
      inv_eight_mem_R5)

theorem gmul_mem_L5 {u v : SpaceB} (hu : u ∈ L5) (hv : v ∈ L5) : gmul u v ∈ L5 :=
  ⟨gmulA_isR5 hu hv, gmulX_mem_R5 hu hv,
    ((gmulWHalf_isR5 hu hv).add (gmulWHalf_isR5 hv hu) : IsR5 (gmulWHalf u v + gmulWHalf v u))⟩

theorem gmul_mem_M5_right {u v : SpaceB} (hu : u ∈ L5) (hv : v ∈ M5) : gmul u v ∈ M5 := by
  rw [mem_M5_iff_smul, ← map_smul]
  exact gmul_mem_L5 hu (mem_M5_iff_smul.1 hv)

theorem gmul_mem_M5_left {u v : SpaceB} (hu : u ∈ M5) (hv : v ∈ L5) : gmul u v ∈ M5 := by
  rw [gmul_comm]
  exact gmul_mem_M5_right hv hu

theorem gmul_sub_gmul_mem_M5 {u u' v v' : SpaceB} (hu' : u' ∈ L5) (hv : v ∈ L5)
    (hu : u - u' ∈ M5) (hv' : v - v' ∈ M5) : gmul u v - gmul u' v' ∈ M5 := by
  have e : gmul u v - gmul u' v' = gmul (u - u') v + gmul u' (v - v') := by
    rw [map_sub, map_sub, LinearMap.sub_apply]
    abel
  rw [e]
  exact add_mem (gmul_mem_M5_left hu hv) (gmul_mem_M5_right hu' hv')

theorem bform_mem_R5 {u v : SpaceB} (hu : u ∈ L5) (hv : v ∈ L5) : bform u v ∈ R5 := by
  rw [bform_apply]
  have hA : IsR5 (Am u) := hu.1
  have hA' : IsR5 (Am v) := hv.1
  exact add_mem (add_mem (hA.mul hA').trace_mem (sum_mem fun c _ => mul_mem (hu.2.1 c) (hv.2.1 c)))
    (sum_mem fun j _ => sum_mem fun i _ => mul_mem (hu.2.2 j i) (hv.2.2 j i))

theorem bform_mem_D5 {u v : SpaceB} (hu : u ∈ L5) (hv : v ∈ M5) : bform u v ∈ D5 := by
  rw [mem_D5_iff_inv_mul, ← smul_eq_mul, ← map_smul]
  exact bform_mem_R5 hu (mem_M5_iff_smul.1 hv)

end CFSG.Monster.Griess.ModFive
