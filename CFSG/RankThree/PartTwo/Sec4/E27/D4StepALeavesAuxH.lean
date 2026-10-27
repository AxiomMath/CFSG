module

public import Mathlib.Tactic.Group
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.RankThree.PartTwo.Sec4.E27

section LemmaH

variable {K : Type*} [Group K]

theorem aut_mul_conj_eq (φ : MulAut K) (x : K) : φ * MulAut.conj x = MulAut.conj (φ x) * φ := by
  refine MulEquiv.ext fun y => ?_
  simp [MulAut.mul_apply, MulAut.conj_apply]

theorem conj_pow_mul_conj_pow (τ : MulAut K) (g₁ g₂ : K) (j₁ j₂ : ℕ) :
    (MulAut.conj g₁ * τ ^ j₁) * (MulAut.conj g₂ * τ ^ j₂) =
      MulAut.conj (g₁ * (τ ^ j₁) g₂) * τ ^ (j₁ + j₂) := by
  calc (MulAut.conj g₁ * τ ^ j₁) * (MulAut.conj g₂ * τ ^ j₂)
      = MulAut.conj g₁ * ((τ ^ j₁ * MulAut.conj g₂) * τ ^ j₂) := by group
    _ = MulAut.conj g₁ * ((MulAut.conj ((τ ^ j₁) g₂) * τ ^ j₁) * τ ^ j₂) := by
        rw [aut_mul_conj_eq]
    _ = MulAut.conj (g₁ * (τ ^ j₁) g₂) * τ ^ (j₁ + j₂) := by
        rw [map_mul, pow_add]
        group

theorem eq_of_comm_conj_pow (hinj : Function.Injective (MulAut.conj : K →* MulAut K))
    (τ : MulAut K) {g₁ g₂ : K} {j₁ j₂ : ℕ}
    (h : (MulAut.conj g₁ * τ ^ j₁) * (MulAut.conj g₂ * τ ^ j₂) =
      (MulAut.conj g₂ * τ ^ j₂) * (MulAut.conj g₁ * τ ^ j₁)) :
    g₁ * (τ ^ j₁) g₂ = g₂ * (τ ^ j₂) g₁ := by
  rw [conj_pow_mul_conj_pow, conj_pow_mul_conj_pow, add_comm j₂ j₁] at h
  exact hinj (mul_right_cancel h)

end LemmaH

section Prime3

variable {K : Type*} [Group K] [Finite K]

theorem three_part_coboundary (τ : MulAut K) (Z : Subgroup K)
    (hZab : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a)
    (hτZ : ∀ j : ℕ, ∀ z ∈ Z, (τ ^ j) z ∈ Z)
    (hfix3 : ∀ j : ℕ, ∀ z ∈ Z, (∃ k : ℕ, z ^ (3 ^ k) = 1) → (τ ^ j) z = z)
    {z : K} (hz : z ∈ Z) (j : ℕ) :
    ∃ m : ℕ, ¬ 3 ∣ m ∧ (z * ((τ ^ j) z)⁻¹) ^ m = 1 := by
  classical
  have hN : 0 < orderOf z := orderOf_pos z
  obtain ⟨a, m, hm3, hNm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' 3 (by norm_num)
  refine ⟨m, hm3, ?_⟩
  have hcop : Nat.Coprime (3 ^ a) m := Nat.Coprime.pow_left a
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hm3)
  obtain ⟨s, t, hst⟩ : ∃ s t : ℤ, s * ((3 : ℤ) ^ a) + t * (m : ℤ) = 1 := by
    refine ⟨Nat.gcdA (3 ^ a) m, Nat.gcdB (3 ^ a) m, ?_⟩
    have h := Nat.gcd_eq_gcd_ab (3 ^ a) m
    rw [hcop.gcd_eq_one] at h
    push_cast at h
    linarith
  set z₁ : K := z ^ (t * (m : ℤ)) with hz₁
  set z₂ : K := z ^ (s * (3 : ℤ) ^ a) with hz₂
  have hz12 : z = z₁ * z₂ := by
    rw [hz₁, hz₂, ← zpow_add]
    have : t * (m : ℤ) + s * (3 : ℤ) ^ a = 1 := by linarith
    rw [this, zpow_one]
  have hz₁Z : z₁ ∈ Z := Subgroup.zpow_mem _ hz _
  have hz₂Z : z₂ ∈ Z := Subgroup.zpow_mem _ hz _
  have hz₁3 : z₁ ^ (3 ^ a) = 1 := by
    rw [hz₁, ← zpow_natCast, ← zpow_mul]
    have : t * (m : ℤ) * ((3 ^ a : ℕ) : ℤ) = (orderOf z : ℤ) * t := by
      rw [hNm]; push_cast; ring
    rw [this, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
  have hz₂m : z₂ ^ m = 1 := by
    rw [hz₂, ← zpow_natCast, ← zpow_mul]
    have : s * (3 : ℤ) ^ a * (m : ℤ) = (orderOf z : ℤ) * s := by
      rw [hNm]; push_cast; ring
    rw [this, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
  have hτz₁ : (τ ^ j) z₁ = z₁ := hfix3 j z₁ hz₁Z ⟨a, hz₁3⟩
  have hτz₂Z : (τ ^ j) z₂ ∈ Z := hτZ j z₂ hz₂Z
  have hu : z * ((τ ^ j) z)⁻¹ = z₂ * ((τ ^ j) z₂)⁻¹ := by
    conv_lhs => rw [hz12]
    rw [map_mul, hτz₁, mul_inv_rev]
    have hc : z₁ * z₂ * (((τ ^ j) z₂)⁻¹ * z₁⁻¹) = z₂ * ((τ ^ j) z₂)⁻¹ := by
      have h1 : z₁ * (z₂ * ((τ ^ j) z₂)⁻¹) = (z₂ * ((τ ^ j) z₂)⁻¹) * z₁ :=
        hZab _ hz₁Z _ (Subgroup.mul_mem _ hz₂Z (Subgroup.inv_mem _ hτz₂Z))
      calc z₁ * z₂ * (((τ ^ j) z₂)⁻¹ * z₁⁻¹) = (z₁ * (z₂ * ((τ ^ j) z₂)⁻¹)) * z₁⁻¹ := by group
        _ = ((z₂ * ((τ ^ j) z₂)⁻¹) * z₁) * z₁⁻¹ := by rw [h1]
        _ = z₂ * ((τ ^ j) z₂)⁻¹ := by group
    exact hc
  rw [hu]
  have hcomm : z₂ * ((τ ^ j) z₂)⁻¹ = ((τ ^ j) z₂)⁻¹ * z₂ :=
    hZab _ hz₂Z _ (Subgroup.inv_mem _ hτz₂Z)
  have hcomm' : Commute z₂ (((τ ^ j) z₂)⁻¹) := hcomm
  rw [hcomm'.mul_pow, hz₂m, one_mul, inv_pow, ← map_pow, hz₂m, map_one, inv_one]

theorem commute_of_comm_autos (hinj : Function.Injective (MulAut.conj : K →* MulAut K))
    (τ : MulAut K) (x : K) (D : Subgroup K) (hx3 : x ^ 3 = 1)
    (hτD : ∀ d ∈ D, τ d = d) (hτx : τ x = x)
    (hZab : ∀ a ∈ Subgroup.centralizer (D : Set K), ∀ b ∈ Subgroup.centralizer (D : Set K),
      a * b = b * a)
    (hZ3 : ∀ z ∈ Subgroup.centralizer (D : Set K), (∃ k : ℕ, z ^ (3 ^ k) = 1) →
      z ∈ Subgroup.zpowers x)
    (hDZ : ∀ w ∈ D, (∀ d ∈ D, w * d = d * w) → w ∈ Subgroup.zpowers x)
    {g₁ g₂ d₁ d₂ : K} {j₁ j₂ : ℕ} (hd₁ : d₁ ∈ D) (hd₂ : d₂ ∈ D)
    (hz₁ : d₁⁻¹ * g₁ ∈ Subgroup.centralizer (D : Set K))
    (hz₂ : d₂⁻¹ * g₂ ∈ Subgroup.centralizer (D : Set K))
    (hcomm : (MulAut.conj g₁ * τ ^ j₁) * (MulAut.conj g₂ * τ ^ j₂) =
      (MulAut.conj g₂ * τ ^ j₂) * (MulAut.conj g₁ * τ ^ j₁)) :
    d₁ * d₂ = d₂ * d₁ := by
  classical
  set Z : Subgroup K := Subgroup.centralizer (D : Set K) with hZ
  have hτjD : ∀ (j : ℕ), ∀ d ∈ D, (τ ^ j) d = d := by
    intro j
    induction j with
    | zero => intro d _; simp
    | succ j ih => intro d hd; rw [pow_succ, MulAut.mul_apply, hτD d hd, ih d hd]
  have hτjx : ∀ j : ℕ, (τ ^ j) x = x := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, MulAut.mul_apply, hτx, ih]
  have hcz : ∀ z ∈ Z, ∀ d ∈ D, z * d = d * z := fun z hz d hd =>
    (Subgroup.mem_centralizer_iff.mp hz d hd).symm
  have hτjZ : ∀ j : ℕ, ∀ z ∈ Z, (τ ^ j) z ∈ Z := by
    intro j z hz
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have h2 := congrArg (τ ^ j) (Subgroup.mem_centralizer_iff.mp hz h hh)
    rw [map_mul, map_mul, hτjD j h hh] at h2
    exact h2
  have hfix3 : ∀ j : ℕ, ∀ z ∈ Z, (∃ k : ℕ, z ^ (3 ^ k) = 1) → (τ ^ j) z = z := by
    intro j z hz h3
    obtain ⟨c, hc⟩ := Subgroup.mem_zpowers_iff.mp (hZ3 z hz h3)
    rw [← hc, map_zpow, hτjx j]
  have hrel := eq_of_comm_conj_pow hinj τ hcomm
  obtain ⟨z₁, hz₁Z, rfl⟩ : ∃ z ∈ Z, g₁ = d₁ * z := ⟨d₁⁻¹ * g₁, hz₁, by group⟩
  obtain ⟨z₂, hz₂Z, rfl⟩ : ∃ z ∈ Z, g₂ = d₂ * z := ⟨d₂⁻¹ * g₂, hz₂, by group⟩
  rw [map_mul, map_mul, hτjD j₁ d₂ hd₂, hτjD j₂ d₁ hd₁] at hrel
  have hτ₁ : (τ ^ j₁) z₂ ∈ Z := hτjZ j₁ z₂ hz₂Z
  have hτ₂ : (τ ^ j₂) z₁ ∈ Z := hτjZ j₂ z₁ hz₁Z
  set ζ₁ : K := z₁ * (τ ^ j₁) z₂ with hζ₁
  set ζ₂ : K := z₂ * (τ ^ j₂) z₁ with hζ₂
  have hζ₁Z : ζ₁ ∈ Z := Subgroup.mul_mem _ hz₁Z hτ₁
  have hζ₂Z : ζ₂ ∈ Z := Subgroup.mul_mem _ hz₂Z hτ₂
  have h1 : d₁ * d₂ * ζ₁ = d₂ * d₁ * ζ₂ := by
    have e1 : z₁ * d₂ = d₂ * z₁ := hcz z₁ hz₁Z d₂ hd₂
    have e2 : z₂ * d₁ = d₁ * z₂ := hcz z₂ hz₂Z d₁ hd₁
    calc d₁ * d₂ * ζ₁ = d₁ * (d₂ * z₁) * (τ ^ j₁) z₂ := by rw [hζ₁]; group
      _ = d₁ * (z₁ * d₂) * (τ ^ j₁) z₂ := by rw [← e1]
      _ = d₁ * z₁ * (d₂ * (τ ^ j₁) z₂) := by group
      _ = d₂ * z₂ * (d₁ * (τ ^ j₂) z₁) := hrel
      _ = d₂ * (z₂ * d₁) * (τ ^ j₂) z₁ := by group
      _ = d₂ * (d₁ * z₂) * (τ ^ j₂) z₁ := by rw [e2]
      _ = d₂ * d₁ * ζ₂ := by rw [hζ₂]; group
  have hw : (d₂ * d₁)⁻¹ * (d₁ * d₂) = ζ₂ * ζ₁⁻¹ := by
    calc (d₂ * d₁)⁻¹ * (d₁ * d₂) = (d₂ * d₁)⁻¹ * (d₁ * d₂ * ζ₁) * ζ₁⁻¹ := by group
      _ = (d₂ * d₁)⁻¹ * (d₂ * d₁ * ζ₂) * ζ₁⁻¹ := by rw [h1]
      _ = ζ₂ * ζ₁⁻¹ := by group
  set w : K := (d₂ * d₁)⁻¹ * (d₁ * d₂) with hwdef
  have hwD : w ∈ D := Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mul_mem _ hd₂ hd₁))
    (Subgroup.mul_mem _ hd₁ hd₂)
  have hwZ : w ∈ Z := by rw [hw]; exact Subgroup.mul_mem _ hζ₂Z (Subgroup.inv_mem _ hζ₁Z)
  have hwx : w ∈ Subgroup.zpowers x := hDZ w hwD (fun d hd => hcz w hwZ d hd)
  have hw3 : w ^ 3 = 1 := by
    obtain ⟨c, hc⟩ := Subgroup.mem_zpowers_iff.mp hwx
    rw [← hc, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]
  obtain ⟨m₂, hm₂, hu₂⟩ := three_part_coboundary τ Z hZab hτjZ hfix3 hz₂Z j₁
  obtain ⟨m₁, hm₁, hv₁⟩ := three_part_coboundary τ Z hZab hτjZ hfix3 hz₁Z j₂
  set u₂ : K := z₂ * ((τ ^ j₁) z₂)⁻¹ with hu₂def
  set v₁ : K := z₁ * ((τ ^ j₂) z₁)⁻¹ with hv₁def
  have hwuv : w = u₂ * v₁⁻¹ := by
    rw [hw, hζ₁, hζ₂, hu₂def, hv₁def]
    have hab : (τ ^ j₂) z₁ * ((τ ^ j₁) z₂)⁻¹ = ((τ ^ j₁) z₂)⁻¹ * (τ ^ j₂) z₁ :=
      hZab _ hτ₂ _ (Subgroup.inv_mem _ hτ₁)
    calc z₂ * (τ ^ j₂) z₁ * (z₁ * (τ ^ j₁) z₂)⁻¹
        = z₂ * ((τ ^ j₂) z₁ * ((τ ^ j₁) z₂)⁻¹) * z₁⁻¹ := by group
      _ = z₂ * (((τ ^ j₁) z₂)⁻¹ * (τ ^ j₂) z₁) * z₁⁻¹ := by rw [hab]
      _ = z₂ * ((τ ^ j₁) z₂)⁻¹ * (z₁ * ((τ ^ j₂) z₁)⁻¹)⁻¹ := by group
  have hu₂Z : u₂ ∈ Z := Subgroup.mul_mem _ hz₂Z (Subgroup.inv_mem _ hτ₁)
  have hv₁Z : v₁⁻¹ ∈ Z := Subgroup.inv_mem _ (Subgroup.mul_mem _ hz₁Z (Subgroup.inv_mem _ hτ₂))
  have hcuv : Commute u₂ v₁⁻¹ := hZab _ hu₂Z _ hv₁Z
  have hwpow : w ^ (m₁ * m₂) = 1 := by
    rw [hwuv, hcuv.mul_pow, pow_mul' u₂, hu₂, one_pow, one_mul, inv_pow, pow_mul, hv₁, one_pow,
      inv_one]
  have hcop : Nat.Coprime 3 (m₁ * m₂) := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
    · exact hm₁ h
    · exact hm₂ h
  have hw1 : w = 1 := by
    have := pow_gcd_eq_one.2 ⟨hw3, hwpow⟩
    rwa [hcop.gcd_eq_one, pow_one] at this
  rw [hwdef, inv_mul_eq_one] at hw1
  exact hw1.symm

end Prime3

end CFSG.RankThree.PartTwo.Sec4.E27
