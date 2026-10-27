module

public import CFSG.RankThree.PartOne.A6N.Sylow3Defs
public import CFSG.RankThree.PartOne.A6N.Setup
public import CFSG.RankThree.PartOne.A6N.Heis
public import CFSG.RankThree.PartOne.A6N.Finite
public import Mathlib.GroupTheory.Sylow
public import Certificates.Certificate14979
public import CFSG.RankThree.PartOne.N1322.CaseBasic
public import CFSG.RankThree.PartOne.N1322.CoreHyp
public import CFSG.RankThree.PartOne.N1322.Mono
public import Mathlib.Algebra.Algebra.Subalgebra.Rank

public section

namespace CFSG.RankThree.PartOne.A6N

open Equiv CFSG.RankThree.PartOne.N1322

theorem y₀A_pow_three : y₀A ^ 3 = 1 := Subtype.ext (by simpa using y₀_pow_three)

theorem g₂A_pow_three : g₂A ^ 3 = 1 := Subtype.ext (by simpa using g₂_pow_three)

theorem y₀A_comm : y₀A * g₂A = g₂A * y₀A := Subtype.ext (by simpa using y₀_g₂_comm)

@[expose] def E0 : Subgroup (alternatingGroup (Fin 6)) where
  carrier := {x | ∃ i j : Fin 3, x = y₀A ^ (i : ℕ) * g₂A ^ (j : ℕ)}
  one_mem' := ⟨0, 0, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨i, j, rfl⟩ ⟨i', j', rfl⟩
    have h1 : ∀ n : ℕ, y₀A ^ n = y₀A ^ (n % 3) := fun n => pow_eq_pow_mod n y₀A_pow_three
    have h2 : ∀ n : ℕ, g₂A ^ n = g₂A ^ (n % 3) := fun n => pow_eq_pow_mod n g₂A_pow_three
    refine ⟨⟨(i + i' : ℕ) % 3, Nat.mod_lt _ (by norm_num)⟩,
      ⟨(j + j' : ℕ) % 3, Nat.mod_lt _ (by norm_num)⟩, ?_⟩
    simp only
    rw [← h1, ← h2, pow_add, pow_add]
    have hc : Commute (g₂A ^ (j : ℕ)) (y₀A ^ (i' : ℕ)) :=
      ((Commute.pow_pow y₀A_comm.symm) j i')
    calc y₀A ^ (i : ℕ) * g₂A ^ (j : ℕ) * (y₀A ^ (i' : ℕ) * g₂A ^ (j' : ℕ))
        = y₀A ^ (i : ℕ) * (g₂A ^ (j : ℕ) * y₀A ^ (i' : ℕ)) * g₂A ^ (j' : ℕ) := by
          simp only [mul_assoc]
      _ = y₀A ^ (i : ℕ) * (y₀A ^ (i' : ℕ) * g₂A ^ (j : ℕ)) * g₂A ^ (j' : ℕ) := by rw [hc.eq]
      _ = _ := by simp only [mul_assoc]
  inv_mem' := by
    rintro _ ⟨i, j, rfl⟩
    have h1 : ∀ n : ℕ, y₀A ^ n = y₀A ^ (n % 3) := fun n => pow_eq_pow_mod n y₀A_pow_three
    have h2 : ∀ n : ℕ, g₂A ^ n = g₂A ^ (n % 3) := fun n => pow_eq_pow_mod n g₂A_pow_three
    refine ⟨⟨(2 * i : ℕ) % 3, Nat.mod_lt _ (by norm_num)⟩,
      ⟨(2 * j : ℕ) % 3, Nat.mod_lt _ (by norm_num)⟩, ?_⟩
    simp only
    refine inv_eq_of_mul_eq_one_right ?_
    have hc : Commute (g₂A ^ (j : ℕ)) (y₀A ^ ((2 * i : ℕ) % 3)) :=
      ((Commute.pow_pow y₀A_comm.symm) j _)
    calc y₀A ^ (i : ℕ) * g₂A ^ (j : ℕ) * (y₀A ^ ((2 * i : ℕ) % 3) * g₂A ^ ((2 * j : ℕ) % 3))
        = y₀A ^ (i : ℕ) * (g₂A ^ (j : ℕ) * y₀A ^ ((2 * i : ℕ) % 3)) *
            g₂A ^ ((2 * j : ℕ) % 3) := by
          simp only [mul_assoc]
      _ = y₀A ^ (i : ℕ) * (y₀A ^ ((2 * i : ℕ) % 3) * g₂A ^ (j : ℕ)) *
            g₂A ^ ((2 * j : ℕ) % 3) := by
          rw [hc.eq]
      _ = y₀A ^ ((i : ℕ) + (2 * i : ℕ) % 3) * g₂A ^ ((j : ℕ) + (2 * j : ℕ) % 3) := by
          rw [pow_add, pow_add]; simp only [mul_assoc]
      _ = 1 := by
          rw [h1, h2]
          have hi : ((i : ℕ) + (2 * i : ℕ) % 3) % 3 = 0 := by omega
          have hj : ((j : ℕ) + (2 * j : ℕ) % 3) % 3 = 0 := by omega
          rw [hi, hj]; simp

theorem card_E0 : Nat.card E0 = 9 := by
  have hbij : Function.Bijective (fun p : Fin 3 × Fin 3 =>
      (⟨y₀A ^ (p.1 : ℕ) * g₂A ^ (p.2 : ℕ), p.1, p.2, rfl⟩ : E0)) := by
    refine ⟨fun p q h => y₀_g₂_inj p q ?_, fun x => ?_⟩
    · have := congrArg (fun z : E0 => (z : alternatingGroup (Fin 6)).1) h
      simpa using this
    · obtain ⟨x, i, j, hx⟩ := x
      exact ⟨(i, j), Subtype.ext hx.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij)]
  simp

theorem E0_cube {x : alternatingGroup (Fin 6)} (hx : x ∈ E0) : x ^ 3 = 1 := by
  obtain ⟨i, j, rfl⟩ := hx
  have hc : Commute (y₀A ^ (i : ℕ)) (g₂A ^ (j : ℕ)) := Commute.pow_pow y₀A_comm i j
  rw [hc.mul_pow, ← pow_mul, ← pow_mul, mul_comm (i : ℕ), mul_comm (j : ℕ), pow_mul, pow_mul,
    y₀A_pow_three, g₂A_pow_three]
  simp

theorem E0_inv {x : alternatingGroup (Fin 6)} (hx : x ∈ E0) : k₀A * x * k₀A⁻¹ = x⁻¹ := by
  obtain ⟨i, j, rfl⟩ := hx
  have h1 : k₀A * y₀A * k₀A⁻¹ = y₀A⁻¹ := Subtype.ext (by simpa using k₀_y₀)
  have h2 : k₀A * g₂A * k₀A⁻¹ = g₂A⁻¹ := Subtype.ext (by simpa using k₀_g₂)
  have hc : Commute (y₀A ^ (i : ℕ)) (g₂A ^ (j : ℕ)) := Commute.pow_pow y₀A_comm i j
  calc k₀A * (y₀A ^ (i : ℕ) * g₂A ^ (j : ℕ)) * k₀A⁻¹
      = (k₀A * y₀A * k₀A⁻¹) ^ (i : ℕ) * (k₀A * g₂A * k₀A⁻¹) ^ (j : ℕ) := by
        rw [conj_pow, conj_pow]; group
    _ = (y₀A ^ (i : ℕ) * g₂A ^ (j : ℕ))⁻¹ := by
        rw [h1, h2, inv_pow, inv_pow, mul_inv_rev]
        exact (hc.inv_inv.symm.eq ▸ rfl)

theorem card_A6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

theorem outer_det_check : ∀ (k : alternatingGroup (Fin 6)) (a b c d : Fin 3),
    k * y₁A * k⁻¹ = y₀A ^ (a : ℕ) * g₂A ^ (c : ℕ) →
    k * t₂A * k⁻¹ = y₀A ^ (b : ℕ) * g₂A ^ (d : ℕ) → ((a : ℕ) * d + 2 * b * c) % 3 = 2 :=
  Certificates.certificate14979

namespace Val

variable {p : ℕ} [Fact p.Prime] (V : Val p)

include V

local notation "G3" => GL (Fin 3) (ZMod p)

@[expose] def P3 : Subgroup V.H := E0.comap V.E

theorem mem_P3 {x : V.H} : x ∈ V.P3 ↔ V.E x ∈ E0 := Iff.rfl

theorem card_P3 : Nat.card V.P3 = 27 := by
  have hi : V.P3.index = E0.index := Subgroup.index_comap_of_surjective E0 V.E_surjective
  have h1 := Subgroup.card_mul_index V.P3
  have h2 := Subgroup.card_mul_index E0
  rw [card_E0, card_A6] at h2
  rw [V.card_H, hi] at h1
  have h3 : E0.index = 40 := by omega
  rw [h3] at h1
  omega

theorem frattini3 {g : G3} (hg : ∀ x ∈ V.H, g * x * g⁻¹ ∈ V.H) :
    ∃ h : V.H, ∀ x : V.H, x ∈ V.P3 → h * V.conjAut hg x * h⁻¹ ∈ V.P3 := by
  have : Finite V.H := V.finite_H
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1080 : (Nat.card V.H).factorization 3 = 3 := by
    rw [V.card_H]
    decide +kernel
  have hP : Nat.card V.P3 = 3 ^ (Nat.card V.H).factorization 3 := by
    rw [V.card_P3, h1080]; norm_num
  let α := V.conjAut hg
  let Q : Subgroup V.H := V.P3.map α.toMonoidHom
  have hQ : Nat.card Q = 3 ^ (Nat.card V.H).factorization 3 := by
    rw [← hP]
    exact Subgroup.card_map_of_injective α.injective
  let SP : Sylow 3 V.H := Sylow.ofCard V.P3 hP
  let SQ : Sylow 3 V.H := Sylow.ofCard Q hQ
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq V.H SQ SP
  refine ⟨h, fun x hx => ?_⟩
  have hxQ : α x ∈ (SQ : Subgroup V.H) := by
    rw [Sylow.coe_ofCard]
    exact ⟨x, hx, rfl⟩
  have hmem : h * α x * h⁻¹ ∈ (SP : Subgroup V.H) := by
    rw [← hh, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨α x, hxQ, by simp [MulAut.smul_def, MulAut.conj_apply]⟩
  rw [Sylow.coe_ofCard] at hmem
  exact hmem

theorem pow_three_of_mem_P3 {q : V.H} (hq : q ∈ V.P3) : q ^ 3 = 1 := by
  obtain ⟨κ, hκ⟩ := V.E_surjective k₀A
  have hqE : V.E q ∈ E0 := V.mem_P3.mp hq
  have hq3 : q ^ 3 ∈ Subgroup.center V.H := by
    rw [← V.E_eq_one_iff, map_pow]
    exact E0_cube hqE
  obtain ⟨z, hzdef⟩ : ∃ z, z = q * (κ * q * κ⁻¹) := ⟨_, rfl⟩
  have hz : z ∈ Subgroup.center V.H := by
    rw [hzdef, ← V.E_eq_one_iff, map_mul, map_mul, map_mul, map_inv, hκ, E0_inv hqE,
      mul_inv_cancel]
  have hκq : κ * q * κ⁻¹ = q⁻¹ * z := by rw [hzdef, inv_mul_cancel_left]
  have hc3 : z ^ 3 = 1 := V.center_pow_three _ hz
  have hconj : κ * q ^ 3 * κ⁻¹ = q ^ 3 := by
    rw [Subgroup.mem_center_iff.mp hq3 κ, mul_inv_cancel_right]
  have h1 : (κ * q * κ⁻¹) ^ 3 = q ^ 3 := by
    rw [conj_pow]; exact hconj
  have h2 : (κ * q * κ⁻¹) ^ 3 = (q ^ 3)⁻¹ := by
    have hcomm : Commute q⁻¹ z := Subgroup.mem_center_iff.mp hz q⁻¹
    rw [hκq, hcomm.mul_pow, hc3, mul_one, inv_pow]
  have hw2 : q ^ 3 * q ^ 3 = 1 := by
    have h3 : q ^ 3 = (q ^ 3)⁻¹ := h1.symm.trans h2
    calc q ^ 3 * q ^ 3 = q ^ 3 * (q ^ 3)⁻¹ := by rw [← h3]
      _ = 1 := mul_inv_cancel _
  have hw3 : q ^ 3 * q ^ 3 * q ^ 3 = 1 := by
    rw [← pow_three']
    exact V.center_pow_three _ hq3
  calc q ^ 3 = q ^ 3 * q ^ 3 * q ^ 3 := by rw [hw2, one_mul]
    _ = 1 := hw3

omit V in
theorem seven_le {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (h5 : p ≠ 5) : 7 ≤ p := by
  by_contra h
  have hpr : p.Prime := Fact.out
  interval_cases p
  · exact h5 rfl
  · exact absurd hpr (by decide)

theorem trace_zero_of_mem_P3 {q : V.H} (hq : q ∈ V.P3) (hq1 : V.E q ≠ 1) :
    (((q : G3)) : Matrix (Fin 3) (Fin 3) (ZMod p)).trace = 0 := by
  have := V.perf
  refine trace_zero_of_cube ?_ (det_eq_one_of_perfect q.2) ?_
  · have h3 := congrArg (fun w : V.H => ((w : G3) : Matrix (Fin 3) (Fin 3) (ZMod p)))
      (V.pow_three_of_mem_P3 hq)
    simpa [pow_three'] using h3
  · intro c hc
    apply hq1
    rw [V.E_eq_one_iff]
    refine Subgroup.mem_center_iff.mpr fun g => ?_
    apply Subtype.ext
    apply Units.ext
    have h1 : Commute (Matrix.scalar (Fin 3) c) ((g : G3) : Matrix (Fin 3) (Fin 3) (ZMod p)) :=
      Matrix.scalar_commute c (fun r' => Commute.all c r') _
    have h2 := h1.eq
    rw [← hc] at h2
    simpa using h2.symm

omit V in
theorem not_dvd_small {p : ℕ} (hpr : p.Prime) (hp7 : 7 ≤ p) {N : ℕ} (hN : N = 3 ∨ N = 6 ∨ N = 15 ∨ N = 24) :
    ¬ p ∣ N := by
  intro h
  have hle : p ≤ N := Nat.le_of_dvd (by omega) h
  have h24 : p ≤ 24 := by omega
  interval_cases p <;> rcases hN with rfl | rfl | rfl | rfl <;> simp_all (config := {decide := true})

theorem not_commute_lifts (hp5 : 5 ≤ p) {x y : V.H} (hx : V.E x = y₀A) (hy : V.E y = g₂A) :
    x * y ≠ y * x := by
  intro hxy
  have hp7 : 7 ≤ p := seven_le hp5 V.p_ne_five
  have hpr : p.Prime := Fact.out
  have hP : ∀ i j : ℕ, i < 3 → j < 3 → x ^ i * y ^ j ∈ V.P3 := by
    intro i j hi hj
    rw [V.mem_P3, map_mul, map_pow, map_pow, hx, hy]
    exact ⟨⟨i, hi⟩, ⟨j, hj⟩, rfl⟩
  have hne : ∀ i j : ℕ, i < 3 → j < 3 → (i ≠ 0 ∨ j ≠ 0) → V.E (x ^ i * y ^ j) ≠ 1 := by
    intro i j hi hj hij h1
    rw [map_mul, map_pow, map_pow, hx, hy] at h1
    have h2 : y₀ ^ i * g₂ ^ j = 1 := by simpa using congrArg Subtype.val h1
    have h3 := y₀_g₂_indep ⟨i, hi⟩ ⟨j, hj⟩ h2
    simp only [Fin.ext_iff, Fin.val_zero] at h3
    omega
  have htr : ∀ i j : ℕ, i < 3 → j < 3 → (i ≠ 0 ∨ j ≠ 0) →
      ((((x ^ i * y ^ j : V.H) : G3)) : Matrix (Fin 3) (Fin 3) (ZMod p)).trace = 0 :=
    fun i j hi hj hij => V.trace_zero_of_mem_P3 (hP i j hi hj) (hne i j hi hj hij)
  have hmat : ∀ i j : ℕ, ((((x ^ i * y ^ j : V.H) : G3)) : Matrix (Fin 3) (Fin 3) (ZMod p)) =
      ((x : G3) : Matrix (Fin 3) (Fin 3) (ZMod p)) ^ i *
        ((y : G3) : Matrix (Fin 3) (Fin 3) (ZMod p)) ^ j := by
    intro i j
    simp [Units.val_pow_eq_pow_val]
  have hX3 : ((x : G3) : Matrix (Fin 3) (Fin 3) (ZMod p)) * ((x : G3) : Matrix (Fin 3) (Fin 3) (ZMod p)) * ((x : G3) : Matrix (Fin 3) (Fin 3) (ZMod p)) = 1 := by
    have h := congrArg (fun w : V.H => ((w : G3) : Matrix (Fin 3) (Fin 3) (ZMod p)))
      (V.pow_three_of_mem_P3 (show x ∈ V.P3 by simpa using hP 1 0 (by norm_num) (by norm_num)))
    simpa [pow_three'] using h
  have hY3 : ((y : G3) : Matrix (Fin 3) (Fin 3) (ZMod p)) * ((y : G3) : Matrix (Fin 3) (Fin 3) (ZMod p)) * ((y : G3) : Matrix (Fin 3) (Fin 3) (ZMod p)) = 1 := by
    have h := congrArg (fun w : V.H => ((w : G3) : Matrix (Fin 3) (Fin 3) (ZMod p)))
      (V.pow_three_of_mem_P3 (show y ∈ V.P3 by simpa using hP 0 1 (by norm_num) (by norm_num)))
    simpa [pow_three'] using h
  have hXY : ((x : G3) : Matrix (Fin 3) (Fin 3) (ZMod p)) * ((y : G3) : Matrix (Fin 3) (Fin 3) (ZMod p)) =
      ((y : G3) : Matrix (Fin 3) (Fin 3) (ZMod p)) * ((x : G3) : Matrix (Fin 3) (Fin 3) (ZMod p)) := by
    have := congrArg (fun w : V.H => ((w : G3) : Matrix (Fin 3) (Fin 3) (ZMod p))) hxy
    simpa using this
  have h9 : (9 : ZMod p) ≠ 0 := by
    intro h
    have h1 : p ∣ 9 := (ZMod.natCast_eq_zero_iff 9 p).mp (by exact_mod_cast h)
    have h2 : p ∣ 3 := hpr.dvd_of_dvd_pow (show p ∣ 3 ^ 2 by simpa using h1)
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  obtain ⟨r, hr3, hr⟩ := commuting_cubes _ _ hXY hX3 hY3 h9
    (by simpa [hmat] using htr 1 0 (by norm_num) (by norm_num) (Or.inl (by norm_num)))
    (by simpa [hmat, pow_two] using htr 2 0 (by norm_num) (by norm_num) (Or.inl (by norm_num)))
    (by simpa [hmat] using htr 0 1 (by norm_num) (by norm_num) (Or.inr (by norm_num)))
    (by simpa [hmat, pow_two] using htr 0 2 (by norm_num) (by norm_num) (Or.inr (by norm_num)))
    (by simpa [hmat] using htr 1 1 (by norm_num) (by norm_num) (Or.inl (by norm_num)))
    (by simpa [hmat, pow_two] using htr 1 2 (by norm_num) (by norm_num) (Or.inl (by norm_num)))
    (by simpa [hmat, pow_two] using htr 2 1 (by norm_num) (by norm_num) (Or.inl (by norm_num)))
    (by simpa [hmat, pow_two] using htr 2 2 (by norm_num) (by norm_num) (Or.inl (by norm_num)))
  have hN : ∀ N : ℕ, (N = 3 ∨ N = 6 ∨ N = 15 ∨ N = 24) → (N : ZMod p) ≠ 0 := by
    intro N hN h
    exact not_dvd_small hpr hp7 hN ((ZMod.natCast_eq_zero_iff N p).mp h)
  interval_cases r
  · exact hN 3 (by simp) (by simpa using hr.symm)
  · refine hN 6 (by simp) ?_
    have : ((6 : ℕ) : ZMod p) = 9 * ((1 : ℕ) : ZMod p) - 3 := by push_cast; ring
    rw [this, hr]; ring
  · refine hN 15 (by simp) ?_
    have : ((15 : ℕ) : ZMod p) = 9 * ((2 : ℕ) : ZMod p) - 3 := by push_cast; ring
    rw [this, hr]; ring
  · refine hN 24 (by simp) ?_
    have : ((24 : ℕ) : ZMod p) = 9 * ((3 : ℕ) : ZMod p) - 3 := by push_cast; ring
    rw [this, hr]; ring

omit V in
theorem arith_fin3 : ∀ a b c d : Fin 3,
    ((3 : ℤ) ∣ (((a : ℕ) * d : ℕ) : ℤ) - (((b : ℕ) * c : ℕ) : ℤ) - 1) →
      ((a : ℕ) * d + 2 * b * c) % 3 = 1 := by decide

theorem det_identity (hp5 : 5 ≤ p) {x y : V.H} (hx : V.E x = y₀A) (hy : V.E y = g₂A)
    (β : V.H ≃* V.H) (hβ : ∀ z ∈ Subgroup.center V.H, β z = z) {a b c d : Fin 3}
    {z₁ z₂ : V.H} (hz₁ : z₁ ∈ Subgroup.center V.H) (hz₂ : z₂ ∈ Subgroup.center V.H)
    (hX : β x = x ^ (a : ℕ) * y ^ (c : ℕ) * z₁) (hY : β y = x ^ (b : ℕ) * y ^ (d : ℕ) * z₂) :
    ((a : ℕ) * d + 2 * b * c) % 3 = 1 := by
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : V.H, c₀ = x * y * x⁻¹ * y⁻¹ := ⟨_, rfl⟩
  have hc₀E : V.E c₀ = 1 := by
    rw [hc₀, map_mul, map_mul, map_mul, map_inv, map_inv, hx, hy, y₀A_comm]
    group
  have hc₀c : c₀ ∈ Subgroup.center V.H := (V.E_eq_one_iff c₀).mp hc₀E
  have hxy : x * y = c₀ * (y * x) := by rw [hc₀]; group
  have hc₀1 : c₀ ≠ 1 := by
    intro h
    refine V.not_commute_lifts hp5 hx hy ?_
    rw [hxy, h, one_mul]
  have hc₀3 : c₀ ^ 3 = 1 := V.center_pow_three _ hc₀c
  have hord : orderOf c₀ = 3 := orderOf_eq_prime hc₀3 hc₀1
  have hβc : β c₀ = c₀ := hβ _ hc₀c
  have h1 : β x * β y = c₀ * (β y * β x) := by
    rw [← map_mul, hxy, map_mul, hβc, map_mul]
  have hz₁c : ∀ g : V.H, g * z₁ = z₁ * g := Subgroup.mem_center_iff.mp hz₁
  have hz₂c : ∀ g : V.H, g * z₂ = z₂ * g := Subgroup.mem_center_iff.mp hz₂
  have hzz : z₂ * z₁ = z₁ * z₂ := (hz₂c z₁).symm
  have hpair := pair_mul_comm hc₀c hxy a c b d
  have h2 : β x * β y = c₀ ^ (((a * d : ℕ) : ℤ) - ((b * c : ℕ) : ℤ)) * (β y * β x) := by
    rw [hX, hY]
    have e1 : (x ^ (a : ℕ) * y ^ (c : ℕ) * z₁) * (x ^ (b : ℕ) * y ^ (d : ℕ) * z₂) =
        ((x ^ (a : ℕ) * y ^ (c : ℕ)) * (x ^ (b : ℕ) * y ^ (d : ℕ))) * (z₁ * z₂) := by
      calc (x ^ (a : ℕ) * y ^ (c : ℕ) * z₁) * (x ^ (b : ℕ) * y ^ (d : ℕ) * z₂)
          = x ^ (a : ℕ) * y ^ (c : ℕ) * (z₁ * (x ^ (b : ℕ) * y ^ (d : ℕ))) * z₂ := by
            simp only [mul_assoc]
        _ = x ^ (a : ℕ) * y ^ (c : ℕ) * ((x ^ (b : ℕ) * y ^ (d : ℕ)) * z₁) * z₂ := by
            rw [← hz₁c]
        _ = _ := by simp only [mul_assoc]
    have e2 : (x ^ (b : ℕ) * y ^ (d : ℕ) * z₂) * (x ^ (a : ℕ) * y ^ (c : ℕ) * z₁) =
        ((x ^ (b : ℕ) * y ^ (d : ℕ)) * (x ^ (a : ℕ) * y ^ (c : ℕ))) * (z₁ * z₂) := by
      calc (x ^ (b : ℕ) * y ^ (d : ℕ) * z₂) * (x ^ (a : ℕ) * y ^ (c : ℕ) * z₁)
          = x ^ (b : ℕ) * y ^ (d : ℕ) * (z₂ * (x ^ (a : ℕ) * y ^ (c : ℕ))) * z₁ := by
            simp only [mul_assoc]
        _ = x ^ (b : ℕ) * y ^ (d : ℕ) * ((x ^ (a : ℕ) * y ^ (c : ℕ)) * z₂) * z₁ := by
            rw [← hz₂c]
        _ = ((x ^ (b : ℕ) * y ^ (d : ℕ)) * (x ^ (a : ℕ) * y ^ (c : ℕ))) * (z₂ * z₁) := by
            simp only [mul_assoc]
        _ = _ := by rw [hzz]
    rw [e1, e2, hpair, mul_assoc]
  have h3 : c₀ = c₀ ^ (((a * d : ℕ) : ℤ) - ((b * c : ℕ) : ℤ)) :=
    mul_right_cancel (h1.symm.trans h2)
  have h4 : c₀ ^ ((((a * d : ℕ) : ℤ) - ((b * c : ℕ) : ℤ)) - 1) = 1 := by
    rw [zpow_sub_one, ← h3, mul_inv_cancel]
  have h5 := orderOf_dvd_iff_zpow_eq_one.mpr h4
  rw [hord] at h5
  exact arith_fin3 a b c d (by exact_mod_cast h5)

theorem conjAut_center {g : G3} (hg : ∀ x ∈ V.H, g * x * g⁻¹ ∈ V.H) {z : V.H}
    (hz : z ∈ Subgroup.center V.H) : V.conjAut hg z = z := by
  obtain ⟨c, hc⟩ := V.scalar_of_center z hz
  apply Subtype.ext
  rw [coe_conjAut, central_of_scalar hc g]
  group

section Tau

theorem tau_false (hp5 : 5 ≤ p) {g : G3} (hg : ∀ x ∈ V.H, g * x * g⁻¹ ∈ V.H)
    {ψ : alternatingGroup (Fin 6) ≃* alternatingGroup (Fin 6)}
    (hψ : ∀ x : V.H, V.E (V.conjAut hg x) = ψ (V.E x))
    (ha : ψ a₀A = a₀A) (hs : ψ s₀A = s₀A) (hy : ψ y₀A = y₁A) : False := by
  have hg₂ : ψ g₂A = t₂A := by
    have h1 : g₂A = a₀A * a₀A * y₀A * y₀A * s₀A * a₀A * y₀A * s₀A * a₀A :=
      Subtype.ext (by simpa using g₂_word)
    have h2 : t₂A = a₀A * a₀A * y₁A * y₁A * s₀A * a₀A * y₁A * s₀A * a₀A :=
      Subtype.ext (by simpa using t₂_word)
    rw [h1, h2]
    simp only [map_mul, ha, hs, hy]
  obtain ⟨h₃, hh₃⟩ := V.frattini3 hg
  obtain ⟨x, hx⟩ := V.E_surjective y₀A
  obtain ⟨y, hy'⟩ := V.E_surjective g₂A
  let β : V.H ≃* V.H := (V.conjAut hg).trans (MulAut.conj h₃)
  have hβ : ∀ u, β u = h₃ * V.conjAut hg u * h₃⁻¹ := fun u => rfl
  have hβz : ∀ z ∈ Subgroup.center V.H, β z = z := by
    intro z hz
    rw [hβ, V.conjAut_center hg hz, Subgroup.mem_center_iff.mp hz h₃, mul_inv_cancel_right]
  have hEβ : ∀ u, V.E (β u) = V.E h₃ * ψ (V.E u) * (V.E h₃)⁻¹ := by
    intro u
    rw [hβ, map_mul, map_mul, map_inv, hψ]
  have hxP : x ∈ V.P3 := by rw [V.mem_P3, hx]; exact ⟨1, 0, by simp⟩
  have hyP : y ∈ V.P3 := by rw [V.mem_P3, hy']; exact ⟨0, 1, by simp⟩
  obtain ⟨a, c, hac⟩ := V.mem_P3.mp (hh₃ x hxP)
  obtain ⟨b, d, hbd⟩ := V.mem_P3.mp (hh₃ y hyP)
  have hEx : V.E (β x) = V.E h₃ * y₁A * (V.E h₃)⁻¹ := by rw [hEβ, hx, hy]
  have hEy : V.E (β y) = V.E h₃ * t₂A * (V.E h₃)⁻¹ := by rw [hEβ, hy', hg₂]
  have h1 : V.E h₃ * y₁A * (V.E h₃)⁻¹ = y₀A ^ (a : ℕ) * g₂A ^ (c : ℕ) := by
    rw [← hEx, hβ]; exact hac
  have h2 : V.E h₃ * t₂A * (V.E h₃)⁻¹ = y₀A ^ (b : ℕ) * g₂A ^ (d : ℕ) := by
    rw [← hEy, hβ]; exact hbd
  have hcert := outer_det_check (V.E h₃) a b c d h1 h2
  have hz₁ : (x ^ (a : ℕ) * y ^ (c : ℕ))⁻¹ * β x ∈ Subgroup.center V.H := by
    rw [← V.E_eq_one_iff, map_mul, map_inv, map_mul, map_pow, map_pow, hx, hy', hEx, h1,
      inv_mul_cancel]
  have hz₂ : (x ^ (b : ℕ) * y ^ (d : ℕ))⁻¹ * β y ∈ Subgroup.center V.H := by
    rw [← V.E_eq_one_iff, map_mul, map_inv, map_mul, map_pow, map_pow, hx, hy', hEy, h2,
      inv_mul_cancel]
  have hdet := V.det_identity hp5 hx hy' β hβz hz₁ hz₂
    (by rw [mul_inv_cancel_left]) (by rw [mul_inv_cancel_left])
  omega

end Tau

end Val

end CFSG.RankThree.PartOne.A6N
