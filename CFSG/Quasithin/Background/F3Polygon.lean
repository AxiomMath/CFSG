module

public import CFSG.Quasithin.Background.F3Geodesic
public import CFSG.Quasithin.Background.F3Dihedral
import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Algebra.Ring.Divisibility.Basic
public import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Quasithin

universe u

variable {V : Type u} {Γ : SimpleGraph V} {H : Type*} [Group H] [MulAction H V]

structure DihedralSeq (Γ : SimpleGraph V) (s t : H) (u : ℤ → V) (L : ℕ) (a : ℤ) : Prop where
  adj : ∀ k, Γ.Adj (u k) (u (k + 1))
  nb : ∀ k, u k ≠ u (k + 2)
  rot : ∀ k, (t * s) • u k = u (k + L)
  refl : ∀ k, s • u k = u (a - k)

namespace DihedralSeq

variable {s t : H} {u : ℤ → V} {L : ℕ} {a : ℤ} (D : DihedralSeq Γ s t u L a)

include D in
theorem zpow_smul (j k : ℤ) : (t * s) ^ j • u k = u (k + j * L) := by
  induction j using Int.induction_on generalizing k with
  | zero => simp
  | succ i ih =>
    rw [zpow_add_one, mul_smul, D.rot, ih]
    congr 1
    ring
  | pred i ih =>
    have h1 : (t * s)⁻¹ • u k = u (k - L) := by
      rw [inv_smul_eq_iff, D.rot]
      congr 1
      ring
    rw [zpow_sub_one, mul_smul, h1, ih]
    congr 1
    ring

include D in
theorem zpow_mul_s_smul (j k : ℤ) : ((t * s) ^ j * s) • u k = u (a + j * L - k) := by
  rw [mul_smul, D.refl, D.zpow_smul]
  congr 1
  ring

variable (hs : s * s = 1) (ht : t * t = 1)

include D hs ht in
theorem smul_of_mem_closure {w : H} (hw : w ∈ Subgroup.closure {s, t}) :
    (∃ j : ℤ, ∀ k, w • u k = u (k + j * L)) ∨ (∃ j : ℤ, ∀ k, w • u k = u (a + j * L - k)) := by
  obtain ⟨j, rfl | rfl⟩ := (mem_closure_iff hs ht w).mp hw
  · exact Or.inl ⟨j, fun k => D.zpow_smul j k⟩
  · exact Or.inr ⟨j, fun k => D.zpow_mul_s_smul j k⟩

include D hs ht in
theorem smul_mem_range {w : H} (hw : w ∈ Subgroup.closure {s, t}) (k : ℤ) :
    ∃ k', w • u k = u k' := by
  rcases D.smul_of_mem_closure hs ht hw with ⟨j, hj⟩ | ⟨j, hj⟩
  · exact ⟨_, hj k⟩
  · exact ⟨_, hj k⟩

section Periodic

variable {c : V → Bool}

include D in
theorem u_eq_iff (hΓ : Γ.Connected) (hc : ∀ a b, Γ.Adj a b → c a ≠ c b) {m : ℕ} (hm : 1 ≤ m)
    (hU : UniqueGeod Γ m) (hper : ∀ k, u (k + (2 * m : ℕ)) = u k) (i j : ℤ) :
    u i = u j ↔ ((2 * m : ℕ) : ℤ) ∣ i - j := by
  set z : ℕ → V := fun i => u (i : ℤ) with hz
  have hzadj : ∀ i, Γ.Adj (z i) (z (i + 1)) := fun i => by
    have := D.adj (i : ℤ)
    simpa [hz] using this
  have hznb : ∀ i, z i ≠ z (i + 2) := fun i => by
    have := D.nb (i : ℤ)
    simpa [hz] using this
  have hzper : ∀ i, z (i + 2 * m) = z i := fun i => by
    have := hper (i : ℤ)
    simpa [hz] using this
  have hpos : (0 : ℤ) < ((2 * m : ℕ) : ℤ) := by
    have : 0 < 2 * m := by omega
    exact_mod_cast this
  have hperZ : Function.Periodic u (((2 * m : ℕ) : ℤ)) := fun k => hper k
  have key : ∀ i : ℤ, u i = z (i % ((2 * m : ℕ) : ℤ)).toNat := by
    intro i
    have h1 : (((i % ((2 * m : ℕ) : ℤ)).toNat : ℕ) : ℤ) = i % ((2 * m : ℕ) : ℤ) :=
      Int.toNat_of_nonneg (Int.emod_nonneg _ hpos.ne')
    simp only [hz, h1]
    have h2 := hperZ.sub_int_mul_eq (x := i) (i / ((2 * m : ℕ) : ℤ))
    rw [Int.emod_def, ← h2]
    congr 1
    simp only [Int.cast_id]
    ring
  have hlt : ∀ i : ℤ, (i % ((2 * m : ℕ) : ℤ)).toNat < 2 * m := fun i => by
    have h1 := Int.emod_lt_of_pos i hpos
    have h2 := Int.emod_nonneg i hpos.ne'
    omega
  rw [key i, key j, GPath.periodic_eq_iff hΓ hc hm hU z hzadj hznb hzper,
    Nat.mod_eq_of_lt (hlt i), Nat.mod_eq_of_lt (hlt j)]
  have h3 : (i % ((2 * m : ℕ) : ℤ)).toNat = (j % ((2 * m : ℕ) : ℤ)).toNat ↔
      i % ((2 * m : ℕ) : ℤ) = j % ((2 * m : ℕ) : ℤ) := by
    have := Int.emod_nonneg i hpos.ne'
    have := Int.emod_nonneg j hpos.ne'
    omega
  rw [h3, Int.emod_eq_emod_iff_emod_sub_eq_zero, ← Int.dvd_iff_emod_eq_zero]

include D in
theorem adj_nat (i : ℕ) : Γ.Adj (u (i : ℤ)) (u ((i + 1 : ℕ) : ℤ)) := by
  simpa using D.adj (i : ℤ)

include D in
theorem nb_nat (i : ℕ) : u (i : ℤ) ≠ u ((i + 2 : ℕ) : ℤ) := by
  simpa using D.nb (i : ℤ)

theorem per_nat {N : ℕ} (hper : ∀ k, u (k + (N : ℤ)) = u k) (i : ℕ) :
    u ((i + N : ℕ) : ℤ) = u (i : ℤ) := by
  simpa using hper (i : ℤ)

theorem eq_nat_mod {N : ℕ} (hN : 0 < N) (hper : ∀ k, u (k + (N : ℤ)) = u k) (i : ℤ) :
    u i = u (((i % (N : ℤ)).toNat : ℕ) : ℤ) := by
  have hpos : (0 : ℤ) < (N : ℤ) := by exact_mod_cast hN
  have hperZ : Function.Periodic u (N : ℤ) := fun k => hper k
  have h1 : (((i % (N : ℤ)).toNat : ℕ) : ℤ) = i % (N : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ hpos.ne')
  rw [h1]
  have h2 := hperZ.sub_int_mul_eq (x := i) (i / (N : ℤ))
  rw [Int.emod_def, ← h2]
  congr 1
  simp only [Int.cast_id]
  ring

include D in
theorem isPolygon (hΓ : Γ.Connected) (hc : ∀ a b, Γ.Adj a b → c a ≠ c b) {m : ℕ} (hm : 2 ≤ m)
    (hU : UniqueGeod Γ m) (hper : ∀ k, u (k + (2 * m : ℕ)) = u k) :
    IsPolygon Γ (Set.range u) (2 * m) := by
  have hN : 0 < 2 * m := by omega
  have hrange : Set.range (fun i : ℕ => u (i : ℤ)) = Set.range u := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨(k % ((2 * m : ℕ) : ℤ)).toNat, (eq_nat_mod (u := u) hN hper k).symm⟩
  rw [← hrange]
  exact GPath.isPolygon_of_periodic hΓ hc hm hU (fun i : ℕ => u (i : ℤ)) D.adj_nat D.nb_nat
    (per_nat (u := u) hper)

end Periodic

section Kernel

variable (hs : s * s = 1) (ht : t * t = 1)

include D hs ht in
theorem fixes_iff_mem_zpowers {N n : ℕ} (hL : 0 < L) (hNnL : (N : ℤ) = n * L)
    (hN3 : 3 ≤ N) (hu : ∀ i j, u i = u j ↔ (N : ℤ) ∣ i - j) {w : H}
    (hw : w ∈ Subgroup.closure {s, t}) :
    (∀ k, w • u k = u k) ↔ w ∈ Subgroup.zpowers ((t * s) ^ (n : ℤ)) := by
  constructor
  · intro hfix
    obtain ⟨j, rfl | rfl⟩ := (mem_closure_iff hs ht w).mp hw
    · have h0 := hfix 0
      rw [D.zpow_smul] at h0
      have h1 := (hu _ _).mp h0
      rw [hNnL, zero_add, sub_zero] at h1
      have hLz : (L : ℤ) ≠ 0 := by exact_mod_cast hL.ne'
      have h2 : (n : ℤ) ∣ j := (Int.mul_dvd_mul_iff_right hLz).mp h1
      obtain ⟨q, rfl⟩ := h2
      exact ⟨q, (zpow_mul _ _ _).symm⟩
    · exfalso
      have h0 := hfix 0
      have h1 := hfix 1
      rw [D.zpow_mul_s_smul] at h0 h1
      have e0 := (hu _ _).mp h0
      have e1 := (hu _ _).mp h1
      have h2 : (N : ℤ) ∣ 2 := by
        have := dvd_sub e0 e1
        convert this using 1
        ring
      have := Int.le_of_dvd (by norm_num) h2
      omega
  · rintro ⟨q, rfl⟩ k
    show ((t * s) ^ (n : ℤ)) ^ q • u k = u k
    rw [← zpow_mul, D.zpow_smul]
    refine (hu _ _).mpr ⟨q, ?_⟩
    rw [hNnL]
    ring

include D hs ht in
theorem fixes_pair_iff_mem_zpowers {N n : ℕ} (hL : 0 < L) (hNnL : (N : ℤ) = n * L)
    (hN3 : 3 ≤ N) (hu : ∀ i j, u i = u j ↔ (N : ℤ) ∣ i - j) {w : H}
    (hw : w ∈ Subgroup.closure {s, t}) :
    (w • u 0 = u 0 ∧ w • u 1 = u 1) ↔ w ∈ Subgroup.zpowers ((t * s) ^ (n : ℤ)) := by
  have key := D.fixes_iff_mem_zpowers hs ht hL hNnL hN3 hu hw
  constructor
  · rintro ⟨h0, h1⟩
    obtain ⟨j, rfl | rfl⟩ := (mem_closure_iff hs ht w).mp hw
    · rw [D.zpow_smul] at h0
      have h1 := (hu _ _).mp h0
      rw [hNnL, zero_add, sub_zero] at h1
      have hLz : (L : ℤ) ≠ 0 := by exact_mod_cast hL.ne'
      have h2 : (n : ℤ) ∣ j := (Int.mul_dvd_mul_iff_right hLz).mp h1
      obtain ⟨q, rfl⟩ := h2
      exact ⟨q, (zpow_mul _ _ _).symm⟩
    · exfalso
      rw [D.zpow_mul_s_smul] at h0 h1
      have e0 := (hu _ _).mp h0
      have e1 := (hu _ _).mp h1
      have h2 : (N : ℤ) ∣ 2 := by
        have := dvd_sub e0 e1
        convert this using 1
        ring
      have := Int.le_of_dvd (by norm_num) h2
      omega
  · intro hw'
    exact ⟨key.mpr hw' 0, key.mpr hw' 1⟩

include D hs ht in
theorem relIndex_eq {N n : ℕ} (hn : 0 < n) (hL : 0 < L) (hNnL : (N : ℤ) = n * L) (hN3 : 3 ≤ N)
    (hu : ∀ i j, u i = u j ↔ (N : ℤ) ∣ i - j) :
    (Subgroup.zpowers ((t * s) ^ (n : ℤ))).relIndex (Subgroup.closure {s, t}) = 2 * n := by
  set W := Subgroup.closure {s, t} with hW
  set p₀ : V × V := (u 0, u 1) with hp₀
  have hstab : (Subgroup.zpowers ((t * s) ^ (n : ℤ))).subgroupOf W =
      MulAction.stabilizer W p₀ := by
    ext ⟨w, hw⟩
    rw [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff]
    rw [← D.fixes_pair_iff_mem_zpowers hs ht hL hNnL hN3 hu hw]
    constructor
    · rintro ⟨h0, h1⟩
      exact Prod.ext h0 h1
    · intro h
      exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  unfold Subgroup.relIndex
  rw [hstab, MulAction.index_stabilizer]
  have hs' : s ∈ W := Subgroup.subset_closure (by simp)
  have ht' : t ∈ W := Subgroup.subset_closure (by simp)
  have hr : t * s ∈ W := Subgroup.mul_mem _ ht' hs'
  have hLz : (L : ℤ) ≠ 0 := by exact_mod_cast hL.ne'
  have hnz : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  let Φ : Fin n × Bool → V × V := fun jb =>
    if jb.2 then (u (a + (jb.1 : ℕ) * L), u (a + (jb.1 : ℕ) * L - 1))
    else (u ((jb.1 : ℕ) * L), u ((jb.1 : ℕ) * L + 1))
  have hdvd : ∀ i j : ℤ, u (i * L) = u (j * L) → (n : ℤ) ∣ i - j := by
    intro i j h
    have h1 := (hu _ _).mp h
    rw [hNnL, ← sub_mul] at h1
    exact (Int.mul_dvd_mul_iff_right hLz).mp h1
  have hndvd2 : ∀ i j : ℤ, u (a + i * L) = u (a + j * L) → (n : ℤ) ∣ i - j := by
    intro i j h
    have h1 := (hu _ _).mp h
    rw [hNnL, show a + i * L - (a + j * L) = (i - j) * L by ring] at h1
    exact (Int.mul_dvd_mul_iff_right hLz).mp h1
  have hcross : ∀ i j : ℤ, u (i * L) = u (a + j * L) → u (i * L + 1) = u (a + j * L - 1) →
      False := by
    intro i j h1 h2
    have e1 := (hu _ _).mp h1
    have e2 := (hu _ _).mp h2
    have h3 : (N : ℤ) ∣ 2 := by
      have := dvd_sub e2 e1
      convert this using 1
      ring
    have := Int.le_of_dvd (by norm_num) h3
    omega
  have hinj : Function.Injective Φ := by
    rintro ⟨j, b⟩ ⟨j', b'⟩ h
    have hjj : ∀ i i' : Fin n, (n : ℤ) ∣ (i : ℤ) - i' → i = i' := by
      intro i i' hd
      have := Int.eq_zero_of_abs_lt_dvd hd (by
        have := i.2
        have := i'.2
        rw [abs_lt]
        constructor <;> omega)
      exact Fin.ext (by omega)
    cases b <;> cases b' <;> simp [Φ] at h
    · exact Prod.ext (hjj _ _ (hdvd _ _ h.1)) rfl
    · exact (hcross _ _ h.1 h.2).elim
    · exact (hcross _ _ h.1.symm h.2.symm).elim
    · exact Prod.ext (hjj _ _ (hndvd2 _ _ h.1)) rfl
  have hrange : Set.range Φ = MulAction.orbit W p₀ := by
    ext ⟨v1, v2⟩
    constructor
    · rintro ⟨⟨j, b⟩, h⟩
      cases b
      · simp only [Φ, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] at h
        refine ⟨⟨(t * s) ^ ((j : ℕ) : ℤ), Subgroup.zpow_mem _ hr _⟩, ?_⟩
        show ((t * s) ^ ((j : ℕ) : ℤ) • u 0, (t * s) ^ ((j : ℕ) : ℤ) • u 1) = (v1, v2)
        rw [D.zpow_smul, D.zpow_smul, ← h.1, ← h.2, zero_add, add_comm 1]
      · simp only [Φ, ↓reduceIte, Prod.mk.injEq] at h
        refine ⟨⟨(t * s) ^ ((j : ℕ) : ℤ) * s,
          Subgroup.mul_mem _ (Subgroup.zpow_mem _ hr _) hs'⟩, ?_⟩
        show (((t * s) ^ ((j : ℕ) : ℤ) * s) • u 0, ((t * s) ^ ((j : ℕ) : ℤ) * s) • u 1) = (v1, v2)
        rw [D.zpow_mul_s_smul, D.zpow_mul_s_smul, ← h.1, ← h.2, sub_zero]
    · rintro ⟨⟨w, hw⟩, h⟩
      have h' : (w • u 0, w • u 1) = (v1, v2) := h
      obtain ⟨j', rfl | rfl⟩ := (mem_closure_iff hs ht w).mp hw
      all_goals
        have hnn : (0 : ℤ) ≤ j' % n := Int.emod_nonneg _ hnz
        have hlt : j' % (n : ℤ) < n := Int.emod_lt_of_pos _ (by omega)
        have hdiv : (n : ℤ) ∣ j' - j' % n := ⟨j' / n, by rw [Int.emod_def]; ring⟩
        have hred : ∀ c₀ : ℤ, u (c₀ + ((j' % n).toNat : ℤ) * L) = u (c₀ + j' * L) := by
          intro c₀
          rw [hu, Int.toNat_of_nonneg hnn, hNnL, show c₀ + (j' % n) * L - (c₀ + j' * L) =
            -((j' - j' % n) * L) by ring, dvd_neg]
          exact mul_dvd_mul_right hdiv _
        have hjn : (j' % n).toNat < n := by omega
      · rw [D.zpow_smul, D.zpow_smul] at h'
        refine ⟨(⟨(j' % n).toNat, hjn⟩, false), ?_⟩
        simp only [Φ, Bool.false_eq_true, ↓reduceIte]
        rw [← h', Prod.mk.injEq]
        constructor
        · have := hred 0
          rw [zero_add, zero_add] at this
          rw [zero_add]
          exact this
        · have := hred 1
          rw [add_comm 1, add_comm 1] at this
          rw [add_comm 1 (j' * (L : ℤ))]
          exact this
      · rw [D.zpow_mul_s_smul, D.zpow_mul_s_smul] at h'
        refine ⟨(⟨(j' % n).toNat, hjn⟩, true), ?_⟩
        simp only [Φ, ↓reduceIte]
        rw [← h', Prod.mk.injEq]
        constructor
        · have := hred a
          rw [sub_zero]
          exact this
        · have := hred (a - 1)
          rw [show a - 1 + (↑(j' % ↑n).toNat : ℤ) * L = a + ↑(j' % ↑n).toNat * L - 1 by ring,
            show a - 1 + j' * L = a + j' * L - 1 by ring] at this
          exact this
  rw [← hrange, ← Nat.card_coe_set_eq, ← Nat.card_congr (Equiv.ofInjective Φ hinj)]
  simp
  ring

end Kernel

end DihedralSeq

end CFSG.Quasithin
