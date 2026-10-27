module

public import CFSG.RankThree.PartOne.S12.Sec153Syl

public section

namespace CFSG.RankThree.PartOne.K159W

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne Sec153

section Module

theorem eq_one_of_fixed_cycle_of_eq_pair {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {M : Type*}
    [CommGroup M] (v : Fin 5 → M)
    (hrel : ∀ a : Fin 5 → ℤ, ∏ i, v i ^ a i = 1 ↔ ∃ m : ℤ, ∀ i, (p : ℤ) ∣ a i - m)
    (a : Fin 5 → ℤ) (π : Equiv.Perm (Fin 5))
    (hπ : ∀ i j : Fin 5, ∃ k : ℕ, k < 5 ∧ (π ^ k) i = j)
    (s : M ≃* M) (hs : ∀ k, s (v k) = v (π k)) (hsfx : s (∏ k, v k ^ a k) = ∏ k, v k ^ a k)
    {i j : Fin 5} (hij : i ≠ j) (hsw : (p : ℤ) ∣ a j - a i) : ∏ k, v k ^ a k = 1 := by
  classical
  obtain ⟨m, hm⟩ := exists_const_of_fixed_perm v hrel a π s hs hsfx
  have hstep : ∀ j, (p : ℤ) ∣ a (π j) - a j + m := by
    intro j
    have h1 := hm (π j)
    rw [Equiv.symm_apply_apply] at h1
    have h2 := dvd_neg.2 h1
    have : -(a j - a (π j) - m) = a (π j) - a j + m := by ring
    rwa [this] at h2
  have hall : ∀ n : ℕ, ∀ j, (p : ℤ) ∣ a ((π ^ n) j) - a j + n * m := by
    intro n
    induction n with
    | zero => intro j; simp
    | succ n ih =>
      intro j
      have h1 := hstep ((π ^ n) j)
      have h2 := ih j
      have h3 : (π ^ (n + 1)) j = π ((π ^ n) j) := by rw [pow_succ']; rfl
      rw [h3]
      have h4 := dvd_add h1 h2
      have e : a (π ((π ^ n) j)) - a ((π ^ n) j) + m + (a ((π ^ n) j) - a j + n * m)
          = a (π ((π ^ n) j)) - a j + ((n + 1 : ℕ) : ℤ) * m := by push_cast; ring
      rwa [e] at h4
  obtain ⟨ki, hki, hi⟩ := hπ 0 i
  obtain ⟨kj, hkj, hj⟩ := hπ 0 j
  have hi' := hall ki 0
  rw [hi] at hi'
  have hj' := hall kj 0
  rw [hj] at hj'
  have hmk : (p : ℤ) ∣ ((kj : ℤ) - ki) * m := by
    have h5 := dvd_sub (dvd_sub hj' hi') hsw
    have e : a j - a 0 + kj * m - (a i - a 0 + ki * m) - (a j - a i) = ((kj : ℤ) - ki) * m := by
      ring
    rwa [e] at h5
  have hpm : (p : ℤ) ∣ m := by
    have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    rcases hpr.dvd_or_dvd hmk with h | h
    · exfalso
      have h0 : (kj : ℤ) - ki = 0 :=
        Int.eq_zero_of_abs_lt_dvd h (by rw [abs_lt]; constructor <;> omega)
      have hkk : kj = ki := by omega
      apply hij
      rw [← hi, ← hj, hkk]
    · exact h
  refine (hrel a).2 ⟨a 0, fun l => ?_⟩
  obtain ⟨kl, hkl, hl⟩ := hπ 0 l
  have h1 := hall kl 0
  rw [hl] at h1
  have h2 : (p : ℤ) ∣ (kl : ℤ) * m := dvd_mul_of_dvd_right hpm _
  have h3 := dvd_sub h1 h2
  simpa using h3

theorem dvd_of_fixed_fix {p : ℕ} {M : Type*} [CommGroup M] (v : Fin 5 → M)
    (hrel : ∀ a : Fin 5 → ℤ, ∏ i, v i ^ a i = 1 ↔ ∃ m : ℤ, ∀ i, (p : ℤ) ∣ a i - m)
    (a : Fin 5 → ℤ) (τ : Equiv.Perm (Fin 5)) (t : M ≃* M) (ht : ∀ k, t (v k) = v (τ k))
    (hfx : t (∏ k, v k ^ a k) = ∏ k, v k ^ a k) {l : Fin 5} (hl : τ l = l) {i : Fin 5}
    (_hi : τ i ≠ i) : (p : ℤ) ∣ a (τ i) - a i := by
  obtain ⟨m, hm⟩ := exists_const_of_fixed_perm v hrel a τ t ht hfx
  have h1 := hm l
  have hl' : τ.symm l = l := (Equiv.symm_apply_eq τ).2 hl.symm
  rw [hl', sub_self, zero_sub] at h1
  have hpm : (p : ℤ) ∣ m := dvd_neg.1 h1
  have h2 := hm (τ i)
  rw [Equiv.symm_apply_apply] at h2
  have h3 := dvd_neg.2 (dvd_add h2 hpm)
  have e : -(a i - a (τ i) - m + m) = a (τ i) - a i := by ring
  rwa [e] at h3

theorem zmod5_cube_eq_one : ∀ x : ZMod 5, x ^ 3 = 1 → x = 1 := by decide

theorem perm5_order_three : ∀ τ : Equiv.Perm (Fin 5), τ ^ 3 = 1 → τ ≠ 1 →
    (∃ l, τ l = l) ∧ (∃ i, τ i ≠ i) := by decide +kernel

end Module

section Group

variable {G : Type} [Group G] [Finite G]

theorem mem_of_order_three {E : Subgroup G} (M : ModData 5 E) (hp : Nat.Prime 5)
    (hEc : ∀ a b : ↥E, a * b = b * a) (hE : ∀ e : ↥E, e ^ 5 = 1) {g : MulAut ↥E}
    (hg : g ∈ torusWeyl E) (hg3 : g ^ 3 = 1) : g ∈ reflectionGroup 5 E := by
  obtain ⟨s, hsI, k, hk⟩ := M.split hp hEc g hg
  set z : MulAut ↥E := s⁻¹ * g with hz
  have hgsz : g = s * z := by rw [hz]; group
  have hcomm : s * z = z * s := (central_of_pow z k hk s)
  have hz3 : z ^ 3 = 1 := by
    have h1 : g ^ 3 = s ^ 3 * z ^ 3 := by
      rw [hgsz]
      exact (Commute.mul_pow (hcomm : Commute s z) _)
    have h2 : z ^ 3 = (s ^ 3)⁻¹ := by
      rw [hg3] at h1
      exact eq_inv_of_mul_eq_one_right h1.symm
    have h3 : z ^ 3 ∈ reflectionGroup 5 E := by
      rw [h2]
      exact (reflectionGroup 5 E).inv_mem ((reflectionGroup 5 E).pow_mem hsI _)
    exact M.eq_one_of_pow_mem h3 (pow_of_pow z k hk 3)
  have hv0 : ∀ n : ℤ, M.v 0 ^ n = 1 → (5 : ℤ) ∣ n := by
    intro n hn
    have h1 := (M.rel (![n, 0, 0, 0, 0] : Fin 5 → ℤ)).1 (by simpa using hn)
    obtain ⟨m, hm⟩ := h1
    have h0 := hm 0
    have h1' := hm 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zero_sub] at h0 h1'
    have h5m : (5 : ℤ) ∣ m := by simpa using dvd_neg.1 h1'
    have := dvd_add h0 h5m
    simpa using this
  have hz1 : z = 1 := by
    have h1 := pow_of_pow z k hk 3 (M.v 0)
    rw [hz3] at h1
    have h2 : M.v 0 ^ (k ^ 3 - 1) = 1 := by
      rw [zpow_sub, zpow_one]
      have : (1 : MulAut ↥E) ↑(M.v 0) = M.v 0 := rfl
      rw [this] at h1
      rw [← h1]
      simp
    have h3 : (5 : ℤ) ∣ k ^ 3 - 1 := hv0 _ h2
    have h4 : ((k : ZMod 5)) ^ 3 = 1 := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd (k ^ 3 - 1) 5).2 h3
      push_cast at this
      exact sub_eq_zero.1 this
    have h5 : (k : ZMod 5) = 1 := zmod5_cube_eq_one _ h4
    have h6 : (5 : ℤ) ∣ k - 1 := by
      have : ((k - 1 : ℤ) : ZMod 5) = 0 := by push_cast; rw [h5]; ring
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).1 this
    obtain ⟨t, ht⟩ := h6
    have hkt : k = 5 * t + 1 := by omega
    refine MulEquiv.ext fun e => ?_
    rw [hk e, hkt, zpow_add, zpow_mul, zpow_one]
    have : e ^ (5 : ℤ) = 1 := by simpa using hE e
    rw [this, one_zpow, one_mul]
    rfl
  rw [hgsz, hz1, mul_one]
  exact hsI

theorem eq_one_of_fixed_order_three_five {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G 5 A c L E) (M : ModData 5 E) {α β : MulAut ↥E} (hα : α ∈ torusWeyl E)
    (hβ : β ∈ torusWeyl E) (hα3 : α ^ 3 = 1) (hα1 : α ≠ 1) (hβ5 : β ^ 5 = 1) (hβ1 : β ≠ 1)
    {u : ↥E} (huα : α u = u) (huβ : β u = u) : u = 1 := by
  classical
  have hp := h.prime
  have hEel : IsElementaryAbelian 5 ↥E := h.E_elem
  have hEc : ∀ a b : ↥E, a * b = b * a := fun a b => hEel.is_comm.comm a b
  have hE : ∀ e : ↥E, e ^ 5 = 1 := fun e =>
    Monoid.exponent_dvd_iff_forall_pow_eq_one.1 (IsElementaryAbelian.exponent_dvd_p 5 ↥E) e
  have hβI : β ∈ reflectionGroup 5 E := M.mem_of_pPower hp hEc hE hβ (a := 1) (by simpa using hβ5)
  have hαI : α ∈ reflectionGroup 5 E := mem_of_order_three M hp hEc hE hα hα3
  let _ : CommGroup ↥E := commE hEc
  have hrel' : ∀ a : Fin 5 → ℤ, ∏ i, M.v i ^ a i = 1 ↔ ∃ m : ℤ, ∀ i, ((5 : ℕ) : ℤ) ∣ a i - m :=
    fun a => by rw [Fin.prod_univ_five]; exact M.rel a
  have hgen' : ∀ x : ↥E, ∃ a : Fin 5 → ℤ, x = ∏ i, M.v i ^ a i := fun x => by
    obtain ⟨a, ha⟩ := M.gen x
    exact ⟨a, by rw [Fin.prod_univ_five]; exact ha⟩
  set π := M.θ ⟨β, hβI⟩ with hπdef
  set τ := M.θ ⟨α, hαI⟩ with hτdef
  have hπ5 : π ^ 5 = 1 := by
    rw [hπdef, ← map_pow]
    have : (⟨β, hβI⟩ : ↥(reflectionGroup 5 E)) ^ 5 = 1 := Subtype.ext (by simpa using hβ5)
    rw [this, map_one]
  have hπ1 : π ≠ 1 := by
    intro h1
    apply hβ1
    have := M.θ.injective (h1.trans (map_one M.θ).symm)
    exact congrArg Subtype.val this
  have hτ3 : τ ^ 3 = 1 := by
    rw [hτdef, ← map_pow]
    have : (⟨α, hαI⟩ : ↥(reflectionGroup 5 E)) ^ 3 = 1 := Subtype.ext (by simpa using hα3)
    rw [this, map_one]
  have hτ1 : τ ≠ 1 := by
    intro h1
    apply hα1
    have := M.θ.injective (h1.trans (map_one M.θ).symm)
    exact congrArg Subtype.val this
  obtain ⟨⟨l, hl⟩, ⟨i, hi⟩⟩ := perm5_order_three τ hτ3 hτ1
  have htrans : ∀ i j : Fin 5, ∃ k : ℕ, k < 5 ∧ (π ^ k) i = j := fun i j => by
    obtain ⟨k, hk⟩ := trans5 _ hπ5 hπ1 i j
    exact ⟨k, k.2, hk⟩
  obtain ⟨a₀, ha₀⟩ := hgen' u
  have hs : ∀ k, β (M.v k) = M.v (π k) := fun k => M.perm ⟨β, hβI⟩ k
  have ht : ∀ k, α (M.v k) = M.v (τ k) := fun k => M.perm ⟨α, hαI⟩ k
  have hdiv := dvd_of_fixed_fix M.v hrel' a₀ τ α ht (by rw [← ha₀]; exact huα) hl hi
  have key := eq_one_of_fixed_cycle_of_eq_pair hp (by omega) M.v hrel' a₀ π htrans β hs
    (by rw [← ha₀]; exact huβ) hi.symm hdiv
  rw [ha₀]
  exact key

end Group

end CFSG.RankThree.PartOne.K159W
