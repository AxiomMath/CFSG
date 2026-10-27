module

public import CFSG.RankThree.PartOne.S12.Sec153Syl
public import CFSG.RankThree.PartOne.S12.Sec1510FiveDefs

public section

namespace CFSG.RankThree.PartOne.K1510R

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne Sec153

theorem eq_one_of_fixed_cycle_swap {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {M : Type*} [CommGroup M]
    (v : Fin 5 → M)
    (hrel : ∀ a : Fin 5 → ℤ, ∏ i, v i ^ a i = 1 ↔ ∃ m : ℤ, ∀ i, (p : ℤ) ∣ a i - m)
    (a : Fin 5 → ℤ) (π : Equiv.Perm (Fin 5))
    (hπ : ∀ i j : Fin 5, ∃ k : ℕ, k < 5 ∧ (π ^ k) i = j)
    (s : M ≃* M) (hs : ∀ k, s (v k) = v (π k)) (hsfx : s (∏ k, v k ^ a k) = ∏ k, v k ^ a k)
    {i j : Fin 5} (hij : i ≠ j) (t : M ≃* M) (ht : ∀ k, t (v k) = v (Equiv.swap i j k))
    (htfx : t (∏ k, v k ^ a k) = ∏ k, v k ^ a k) : ∏ k, v k ^ a k = 1 := by
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
  have hsw := dvd_of_fixed_swap v hrel a t ht htfx
  have hmk : (p : ℤ) ∣ ((kj : ℤ) - ki) * m := by
    have h5 := dvd_sub (dvd_sub hj' hi') hsw
    have e : a j - a 0 + kj * m - (a i - a 0 + ki * m) - (a j - a i) = ((kj : ℤ) - ki) * m := by ring
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

variable {G : Type} [Group G] [Finite G]

theorem fixed_eq_one_of_cycle_swap {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G 5 A c L E) (M : ModData 5 E) {t : MulAut ↥E} (ht : t ∈ reflectionSet 5 E)
    {y : G} (hyN : y ∈ Subgroup.normalizer (E : Set G)) {a : ℕ}
    (hpow : conjAut E y hyN ^ (5 ^ a) = 1) (hne : conjAut E y hyN ≠ 1) {u : ↥E} (hut : t u = u)
    (huy : conjAut E y hyN u = u) : u = 1 := by
  classical
  have hp := h.prime
  have hEel : IsElementaryAbelian 5 ↥E := h.E_elem
  have hEc : ∀ a b : ↥E, a * b = b * a := fun a b => hEel.is_comm.comm a b
  have hE : ∀ e : ↥E, e ^ 5 = 1 := fun e =>
    Monoid.exponent_dvd_iff_forall_pow_eq_one.1 (IsElementaryAbelian.exponent_dvd_p 5 ↥E) e
  have hW : conjAut E y hyN ∈ torusWeyl E := ⟨⟨y, hyN⟩, rfl⟩
  have hI := M.mem_of_pPower hp hEc hE hW hpow
  let _ : CommGroup ↥E := commE hEc
  have hrel' : ∀ a : Fin 5 → ℤ, ∏ i, M.v i ^ a i = 1 ↔ ∃ m : ℤ, ∀ i, ((5 : ℕ) : ℤ) ∣ a i - m :=
    fun a => by rw [Fin.prod_univ_five]; exact M.rel a
  have hgen' : ∀ x : ↥E, ∃ a : Fin 5 → ℤ, x = ∏ i, M.v i ^ a i := fun x => by
    obtain ⟨a, ha⟩ := M.gen x
    exact ⟨a, by rw [Fin.prod_univ_five]; exact ha⟩
  set π := M.θ ⟨conjAut E y hyN, hI⟩ with hπdef
  have hπpow : π ^ (5 ^ a) = 1 := by
    rw [hπdef, ← map_pow]
    have : (⟨conjAut E y hyN, hI⟩ : ↥(reflectionGroup 5 E)) ^ (5 ^ a) = 1 :=
      Subtype.ext (by simpa using hpow)
    rw [this, map_one]
  have hπ5 : π ^ 5 = 1 := by
    have h1 : orderOf π ∣ 5 ^ a := orderOf_dvd_of_pow_eq_one hπpow
    have h2 : orderOf π ∣ 120 := by
      have := orderOf_dvd_natCard π
      rwa [card_perm5] at this
    obtain ⟨j, hj, hjo⟩ := (Nat.dvd_prime_pow hp).1 h1
    have hj1 : j ≤ 1 := by
      by_contra hcon
      push Not at hcon
      have h25 : 25 ∣ 120 := by
        have : 5 ^ 2 ∣ 5 ^ j := pow_dvd_pow 5 hcon
        rw [hjo] at h2
        exact (by norm_num : (25 : ℕ) = 5 ^ 2) ▸ this.trans h2
      omega
    have h3 : orderOf π ∣ 5 := by
      rw [hjo]
      exact (pow_dvd_pow 5 hj1).trans (by norm_num)
    exact orderOf_dvd_iff_pow_eq_one.1 h3
  have hπ1 : π ≠ 1 := by
    intro h1
    apply hne
    have := M.θ.injective (h1.trans (map_one M.θ).symm)
    exact congrArg Subtype.val this
  have htrans : ∀ i j : Fin 5, ∃ k : ℕ, k < 5 ∧ (π ^ k) i = j := fun i j => by
    obtain ⟨k, hk⟩ := trans5 _ hπ5 hπ1 i j
    exact ⟨k, k.2, hk⟩
  obtain ⟨a₀, ha₀⟩ := hgen' u
  obtain ⟨i, j, hij, hθt⟩ := M.refl t ht
  have hs : ∀ k, conjAut E y hyN (M.v k) = M.v (π k) := fun k => M.perm ⟨conjAut E y hyN, hI⟩ k
  have hts : ∀ k, t (M.v k) = M.v (Equiv.swap i j k) := fun k => by
    have := M.perm ⟨t, Subgroup.subset_closure ht⟩ k
    rw [hθt] at this
    exact this
  have key := eq_one_of_fixed_cycle_swap hp (by omega) M.v hrel' a₀ π htrans (conjAut E y hyN) hs
    (by rw [← ha₀]; exact huy) hij t hts (by rw [← ha₀]; exact hut)
  rw [ha₀]
  exact key

theorem centralizesE_of_mem_autFixedInG_five {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G 5 A c L E) (M : ModData 5 E) {t : MulAut ↥E} (ht : t ∈ reflectionSet 5 E)
    {b : G} (hb : b ∈ autFixedInG E t) (hb1 : b ≠ 1) : CentralizesE 5 E b := by
  classical
  intro x hxb hxN hk y hy
  obtain ⟨k, hk⟩ := hk
  by_cases h1 : conjAut E x hxN = 1
  · have h2 := Equivariance.coe_conjAut hxN ⟨y, hy⟩
    rw [h1] at h2
    have h3 : y = x * y * x⁻¹ := h2
    calc x * y = x * y * x⁻¹ * x := by group
      _ = y * x := by rw [← h3]
  · exfalso
    have hpow : conjAut E x hxN ^ (5 ^ k) = 1 := by
      unfold conjAut
      rw [← map_pow]
      have : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (E : Set G))) ^ (5 ^ k) = 1 :=
        Subtype.ext (by simpa using hk)
      rw [this, map_one]
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hb
    have hte : t e = e := he
    have hxbc : x * (e : G) = (e : G) * x := Subgroup.mem_centralizer_singleton_iff.1 hxb
    have hxe : conjAut E x hxN e = e := by
      apply Subtype.ext
      rw [Equivariance.coe_conjAut]
      calc x * (e : G) * x⁻¹ = (e : G) * x * x⁻¹ := by rw [hxbc]
        _ = (e : G) := by group
    have := fixed_eq_one_of_cycle_swap h M ht hxN hpow h1 hte hxe
    exact hb1 (by rw [this]; rfl)

end CFSG.RankThree.PartOne.K1510R
