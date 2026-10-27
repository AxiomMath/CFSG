module

public import CFSG.Quasithin.Vol2.Ch11SecO6C
public import CFSG.Quasithin.Vol2.Ch11SecO6I

public section

namespace CFSG.Quasithin.Vol2.Ch11.O6

open CFSG.Quasithin

variable {X : Type} [Group X] [Finite X] (r : ℕ) [Fact r.Prime]

theorem zpow_eq_one_of_homocyclic (hP : IsHomocyclicRank2 r ↥(CFSG.pCore r X)) {u : X}
    (hu : u ∈ CFSG.pCore r X) (hu' : u ∉ frattiniIn (CFSG.pCore r X)) {b : ℤ}
    (hub : u ^ b = 1) : ∀ e ∈ CFSG.pCore r X, e ^ b = 1 := by
  obtain ⟨n, -, ⟨φ⟩⟩ := hP
  set P := CFSG.pCore r X
  have : NeZero (r ^ n) := ⟨pow_ne_zero n (Fact.out : r.Prime).ne_zero⟩
  set x₁ := Multiplicative.toAdd (φ ⟨u, hu⟩).1 with hx₁
  set x₂ := Multiplicative.toAdd (φ ⟨u, hu⟩).2 with hx₂
  have hub' : φ ⟨u, hu⟩ ^ b = 1 := by
    have h1 : (⟨u, hu⟩ : ↥P) ^ b = 1 := Subtype.ext (by rw [SubgroupClass.coe_zpow]; exact hub)
    rw [← map_zpow, h1, map_one]
  have h1 : (b : ZMod (r ^ n)) * x₁ = 0 := by
    have := congrArg (fun p => Multiplicative.toAdd p.1) hub'
    simpa only [Prod.pow_fst, toAdd_zpow, zsmul_eq_mul, Prod.fst_one, toAdd_one] using this
  have h2 : (b : ZMod (r ^ n)) * x₂ = 0 := by
    have := congrArg (fun p => Multiplicative.toAdd p.2) hub'
    simpa only [Prod.pow_snd, toAdd_zpow, zsmul_eq_mul, Prod.snd_one, toAdd_one] using this
  have hdvd : ∀ x : ZMod (r ^ n), ¬ IsUnit x → r ∣ x.val := by
    intro x hx
    by_contra hr
    apply hx
    rw [← ZMod.natCast_zmod_val x, ZMod.isUnit_iff_coprime]
    exact Nat.Coprime.pow_right n ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hr).symm
  have hunit : IsUnit x₁ ∨ IsUnit x₂ := by
    by_contra hnu
    push Not at hnu
    apply hu'
    obtain ⟨c₁, hc₁⟩ := hdvd x₁ hnu.1
    obtain ⟨c₂, hc₂⟩ := hdvd x₂ hnu.2
    have hc : ∀ (x : ZMod (r ^ n)) (c : ℕ), x.val = r * c → r • (c : ZMod (r ^ n)) = x :=
      fun x c hxc => by rw [nsmul_eq_mul, ← Nat.cast_mul, ← hxc, ZMod.natCast_zmod_val]
    set w : ↥P := φ.symm (Multiplicative.ofAdd (c₁ : ZMod (r ^ n)),
      Multiplicative.ofAdd (c₂ : ZMod (r ^ n)))
    have hw : w ^ r = ⟨u, hu⟩ := by
      apply φ.injective
      rw [map_pow, φ.apply_symm_apply]
      refine Prod.ext ?_ ?_
      · rw [Prod.pow_fst, ← ofAdd_nsmul, hc x₁ c₁ hc₁, hx₁, ofAdd_toAdd]
      · rw [Prod.pow_snd, ← ofAdd_nsmul, hc x₂ c₂ hc₂, hx₂, ofAdd_toAdd]
    have e : u = (w : X) ^ r := by rw [← SubgroupClass.coe_pow, hw]
    rw [e]
    exact pow_mem_frattiniIn w.2
  have hb0 : (b : ZMod (r ^ n)) = 0 := by
    rcases hunit with h | h
    · exact h.mul_left_eq_zero.mp h1
    · exact h.mul_left_eq_zero.mp h2
  intro e he
  have h3 : φ ⟨e, he⟩ ^ b = 1 := by
    refine Prod.ext ?_ ?_
    · apply Multiplicative.toAdd.injective
      rw [Prod.pow_fst, toAdd_zpow, zsmul_eq_mul, hb0, zero_mul, Prod.fst_one, toAdd_one]
    · apply Multiplicative.toAdd.injective
      rw [Prod.pow_snd, toAdd_zpow, zsmul_eq_mul, hb0, zero_mul, Prod.snd_one, toAdd_one]
  have h4 : (⟨e, he⟩ : ↥P) ^ b = 1 := by
    apply φ.injective
    rw [map_zpow, h3, map_one]
  simpa using congrArg Subtype.val h4

omit [Finite X] in
theorem zpow_eq_one_of_exponent (hexp : ∀ e ∈ CFSG.pCore r X, e ^ r = 1) {u : X}
    (hu : u ∈ CFSG.pCore r X) (hu' : u ∉ frattiniIn (CFSG.pCore r X)) {b : ℤ}
    (hub : u ^ b = 1) : ∀ e ∈ CFSG.pCore r X, e ^ b = 1 := by
  have hu1 : u ≠ 1 := fun h => hu' (h ▸ one_mem _)
  have hord : orderOf u = r := orderOf_eq_prime (hexp u hu) hu1
  have hdvd : (r : ℤ) ∣ b := by
    rw [← hord]
    exact orderOf_dvd_iff_zpow_eq_one.mpr hub
  obtain ⟨c, rfl⟩ := hdvd
  intro e he
  rw [zpow_mul, zpow_natCast, hexp e he, one_zpow]

omit [Finite X] in
theorem exists_zpow_of_mem_closure_pair {v w : X} (hvw : Commute v w) {g : X}
    (hg : g ∈ Subgroup.closure ({v, w} : Set X)) : ∃ a b : ℤ, g = v ^ a * w ^ b := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact ⟨1, 0, by simp⟩
    · rw [Set.mem_singleton_iff] at hx
      exact ⟨0, 1, by simp [hx]⟩
  | one => exact ⟨0, 0, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨c, d, rfl⟩ := hy
    refine ⟨a + c, b + d, ?_⟩
    have h1 : w ^ b * v ^ c = v ^ c * w ^ b := ((hvw.zpow_zpow c b).eq).symm
    rw [zpow_add, zpow_add]
    calc v ^ a * w ^ b * (v ^ c * w ^ d) = v ^ a * (w ^ b * v ^ c) * w ^ d := by group
      _ = v ^ a * (v ^ c * w ^ b) * w ^ d := by rw [h1]
      _ = v ^ a * v ^ c * (w ^ b * w ^ d) := by group
  | inv x _ hx =>
    obtain ⟨a, b, rfl⟩ := hx
    refine ⟨-a, -b, ?_⟩
    have h1 : (w ^ b)⁻¹ * (v ^ a)⁻¹ = (v ^ a)⁻¹ * (w ^ b)⁻¹ :=
      ((hvw.zpow_zpow a b).inv_inv.eq).symm
    rw [mul_inv_rev, h1, zpow_neg, zpow_neg]

theorem conj_comm_of_fitting (hab : ∀ d ∈ CFSG.pCore r X, ∀ e ∈ CFSG.pCore r X, d * e = e * d)
    {σ : MulAut X} (hσ : ∀ x : X, x⁻¹ * σ x ∈ CFSG.fittingSubgroup X) (x : X) {d : X}
    (hd : d ∈ CFSG.pCore r X) : σ (x * d * x⁻¹) = x * σ d * x⁻¹ := by
  have hFC : CFSG.fittingSubgroup X ≤ Subgroup.centralizer (CFSG.pCore r X : Set X) := by
    rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore]
    refine iSup_le fun p => ?_
    have : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
    intro f hf
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    by_cases hpr : (p : ℕ) = r
    · have hf' : f ∈ CFSG.pCore r X := hpr ▸ hf
      exact hab e he f hf'
    · exact commute_of_pCore_ne (Ne.symm hpr) he hf
  set f := x⁻¹ * σ x with hf
  have hσx : σ x = x * f := by rw [hf, mul_inv_cancel_left]
  have hfd : f * σ d = σ d * f :=
    (Subgroup.mem_centralizer_iff.mp (hFC (hσ x)) (σ d) (map_mem_pCore r σ hd)).symm
  rw [map_mul, map_mul, map_inv, hσx]
  calc x * f * σ d * (x * f)⁻¹ = x * (f * σ d) * f⁻¹ * x⁻¹ := by group
    _ = x * (σ d * f) * f⁻¹ * x⁻¹ := by rw [hfd]
    _ = x * σ d * x⁻¹ := by group

omit [Finite X] [Fact r.Prime] in
theorem comm_eq_of_zpow {a : ℤ} {σ : MulAut X} (hσ : ∀ d ∈ CFSG.pCore r X, σ d = d ^ a)
    (α : MulAut X) {d : X} (hd : d ∈ CFSG.pCore r X) : (σ * α * σ⁻¹ * α⁻¹) d = d := by
  have he : α⁻¹ d ∈ CFSG.pCore r X := map_mem_pCore r α⁻¹ hd
  have he' : σ⁻¹ (α⁻¹ d) ∈ CFSG.pCore r X := map_mem_pCore r σ⁻¹ he
  simp only [MulAut.mul_apply]
  rw [hσ _ (map_mem_pCore r α he'), ← map_zpow, ← hσ _ he', MulAut.apply_inv_self,
    MulAut.apply_inv_self]

end CFSG.Quasithin.Vol2.Ch11.O6
