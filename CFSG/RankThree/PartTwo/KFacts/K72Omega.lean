module

public import CFSG.RankThree.PartTwo.KFacts.AutKinds

public section

namespace CFSG.RankThree.PartTwo.KFacts

section Core

variable {P : Type*} [Group P]

theorem exists_zpow_conj_of_isCyclic {X₀ : Subgroup P} [X₀.Normal] [IsCyclic X₀] (σ : P) :
    ∃ m : ℤ, ∀ y ∈ X₀, σ * y * σ⁻¹ = y ^ m := by
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic (MulAut.conjNormal σ : MulAut X₀).toMonoidHom
  refine ⟨m, fun y hy => ?_⟩
  have h := congrArg Subtype.val (hm ⟨y, hy⟩)
  rw [MulEquiv.coe_toMonoidHom, MulAut.conjNormal_apply] at h
  rw [h, Subgroup.coe_zpow]

theorem conj_pow_eq_zpow {X₀ : Subgroup P} {σ : P} {m : ℤ}
    (hm : ∀ y ∈ X₀, σ * y * σ⁻¹ = y ^ m) (k : ℕ) :
    ∀ y ∈ X₀, σ ^ k * y * (σ ^ k)⁻¹ = y ^ (m ^ k) := by
  induction k with
  | zero => intro y _; simp
  | succ k ih =>
    intro y hy
    have h1 : σ ^ (k + 1) * y * (σ ^ (k + 1))⁻¹ = σ * (σ ^ k * y * (σ ^ k)⁻¹) * σ⁻¹ := by
      rw [pow_succ']
      group
    rw [h1, ih y hy, hm _ (X₀.zpow_mem hy _), ← zpow_mul, pow_succ]

theorem mul_pow_three_eq {X₀ : Subgroup P} {σ : P} {m : ℤ}
    (hm : ∀ y ∈ X₀, σ * y * σ⁻¹ = y ^ m) {y : P} (hy : y ∈ X₀) :
    (σ * y) ^ 3 = y ^ m * y ^ (m ^ 2) * y ^ (m ^ 3) * σ ^ 3 := by
  have h1 := conj_pow_eq_zpow hm 1 y hy
  have h2 := conj_pow_eq_zpow hm 2 y hy
  have h3 := conj_pow_eq_zpow hm 3 y hy
  simp only [pow_one] at h1
  rw [← h1, ← h2, ← h3, pow_three (σ * y)]
  group

theorem emod_three_eq_one_of_zpow {y : P} {m : ℤ} {k : ℕ} (hk : y ^ (3 ^ k) = 1)
    (hy1 : y ≠ 1) (hm : y ^ (m ^ 3) = y) : m % 3 = 1 := by
  have h1 : y ^ (m ^ 3 - 1) = 1 := by
    rw [zpow_sub, zpow_one, hm, mul_inv_cancel]
  have hdvd : (orderOf y : ℤ) ∣ m ^ 3 - 1 := orderOf_dvd_iff_zpow_eq_one.mpr h1
  have hord : orderOf y ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hord
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hy1 (orderOf_eq_one_iff.mp (by simpa using hj))
  have h3 : (3 : ℤ) ∣ m ^ 3 - 1 := by
    refine dvd_trans ?_ hdvd
    rw [hj]
    exact_mod_cast dvd_pow_self 3 hj0
  have h3' : ((m ^ 3 - 1 : ℤ) : ZMod 3) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr h3
  have hz : ∀ x : ZMod 3, x ^ 3 - 1 = 0 → x = 1 := by decide
  have h4 : ((m : ℤ) : ZMod 3) = ((1 : ℤ) : ZMod 3) := by
    rw [Int.cast_one]
    exact hz _ (by push_cast at h3'; exact h3')
  have h5 := (ZMod.intCast_eq_intCast_iff' m 1 3).mp h4
  omega

variable {X₀ : Subgroup P} [X₀.Normal] [IsCyclic X₀]

theorem pow_three_mul_eq_one_iff (hX₀ : IsPGroup 3 X₀) {σ : P} (hσ : σ ^ 3 = 1) {y : P}
    (hy : y ∈ X₀) : (σ * y) ^ 3 = 1 ↔ y ^ 3 = 1 := by
  obtain ⟨m, hm⟩ := exists_zpow_conj_of_isCyclic (X₀ := X₀) σ
  have hm3 : ∀ z ∈ X₀, z ^ (m ^ 3) = z := fun z hz => by
    rw [← conj_pow_eq_zpow hm 3 z hz, hσ, one_mul, inv_one, mul_one]
  rw [mul_pow_three_eq hm hy, hσ, mul_one, hm3 y hy]
  by_cases hy1 : y = 1
  · simp [hy1]
  obtain ⟨k, hk⟩ := hX₀ ⟨y, hy⟩
  have hk' : y ^ (3 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hm1 := emod_three_eq_one_of_zpow hk' hy1 (hm3 y hy)
  obtain ⟨s, hs⟩ : ∃ s, m = 1 + 3 * s := ⟨m / 3, by omega⟩
  have hsum : y ^ m * y ^ (m ^ 2) * y = (y ^ 3) ^ (1 + 3 * s + 3 * s ^ 2) := by
    rw [← zpow_add, ← zpow_add_one, ← zpow_natCast y 3, ← zpow_mul]
    congr 1
    rw [hs]
    push_cast
    ring
  rw [hsum]
  constructor
  · intro h
    have hord : orderOf (y ^ 3) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one (by
      rw [← pow_mul, mul_comm, pow_mul, hk', one_pow])
    have hdvd : (orderOf (y ^ 3) : ℤ) ∣ 1 + 3 * s + 3 * s ^ 2 :=
      orderOf_dvd_iff_zpow_eq_one.mpr h
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hord
    by_cases hj0 : j = 0
    · rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
      exact hj
    · exfalso
      have h3 : (3 : ℤ) ∣ 1 + 3 * s + 3 * s ^ 2 := by
        refine dvd_trans ?_ hdvd
        rw [hj]
        exact_mod_cast dvd_pow_self 3 hj0
      generalize s ^ 2 = t at h3
      omega
  · intro h
    rw [h, one_zpow]

theorem conj_eq_of_pow_three_eq_one {σ : P} (hσ : σ ^ 3 = 1) {y : P} (hy : y ∈ X₀)
    (hy3 : y ^ 3 = 1) : σ * y * σ⁻¹ = y := by
  obtain ⟨m, hm⟩ := exists_zpow_conj_of_isCyclic (X₀ := X₀) σ
  have hm3 : y ^ (m ^ 3) = y := by
    rw [← conj_pow_eq_zpow hm 3 y hy, hσ, one_mul, inv_one, mul_one]
  by_cases hy1 : y = 1
  · rw [hy1, mul_one, mul_inv_cancel]
  have hm1 := emod_three_eq_one_of_zpow (k := 1) (by rwa [pow_one]) hy1 hm3
  obtain ⟨s, hs⟩ : ∃ s, m = 1 + 3 * s := ⟨m / 3, by omega⟩
  rw [hm y hy, hs, zpow_add, zpow_one, zpow_mul]
  have : y ^ (3 : ℤ) = 1 := by rw [zpow_ofNat, hy3]
  rw [this, one_zpow, mul_one]

theorem commute_of_pow_three_eq_one (hX₀ : IsPGroup 3 X₀)
    (hb : ∀ σ τ : P, σ ^ 3 = 1 → τ ^ 3 = 1 → σ ∉ X₀ → ∃ i : ℕ, σ ^ i * τ ∈ X₀) {σ τ : P}
    (hσ : σ ^ 3 = 1) (hτ : τ ^ 3 = 1) : σ * τ = τ * σ := by
  have key : ∀ σ τ : P, σ ^ 3 = 1 → τ ^ 3 = 1 → σ ∉ X₀ → σ * τ = τ * σ := by
    intro σ τ hσ hτ hσX
    obtain ⟨i, hi⟩ := hb σ τ hσ hτ hσX
    obtain ⟨y, hyX, rfl⟩ : ∃ y ∈ X₀, τ = (σ⁻¹) ^ i * y :=
      ⟨σ ^ i * τ, hi, by rw [inv_pow, inv_mul_cancel_left]⟩
    have hσ' : ((σ⁻¹) ^ i) ^ 3 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, inv_pow, hσ, inv_one, one_pow]
    have hy3 : y ^ 3 = 1 := (pow_three_mul_eq_one_iff hX₀ hσ' hyX).mp hτ
    have hσy : σ * y = y * σ := by
      have h1 := conj_eq_of_pow_three_eq_one hσ hyX hy3
      calc σ * y = σ * y * σ⁻¹ * σ := by group
        _ = y * σ := by rw [h1]
    calc σ * ((σ⁻¹) ^ i * y) = (σ⁻¹) ^ i * (σ * y) := by group
      _ = (σ⁻¹) ^ i * (y * σ) := by rw [hσy]
      _ = (σ⁻¹) ^ i * y * σ := by rw [mul_assoc]
  by_cases hσX : σ ∈ X₀
  · by_cases hτX : τ ∈ X₀
    · have := (IsCyclic.commGroup (α := X₀)).mul_comm ⟨σ, hσX⟩ ⟨τ, hτX⟩
      exact congrArg Subtype.val this
    · exact (key τ σ hτ hσ hτX).symm
  · exact key σ τ hσ hτ hσX

end Core

section Aut

variable {X : Type*} [Group X]

theorem range_conj_normal : (MulAut.conj : X →* MulAut X).range.Normal := by
  constructor
  rintro _ ⟨x, rfl⟩ φ
  refine ⟨φ x, ?_⟩
  ext y
  simp [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]

theorem isCyclic_of_le_range_conj [Finite X] (hcyc : ∀ S : Sylow 3 X, IsCyclic S)
    {Q : Subgroup (MulAut X)} (hQ : IsPGroup 3 Q)
    (hQI : Q ≤ (MulAut.conj : X →* MulAut X).range) : IsCyclic Q := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set I := (MulAut.conj : X →* MulAut X).range with hI
  set f : X →* I := (MulAut.conj : X →* MulAut X).rangeRestrict with hf
  have hfs : Function.Surjective f := MonoidHom.rangeRestrict_surjective _
  set Q' : Subgroup I := Q.subgroupOf I with hQ'
  have hQ'p : IsPGroup 3 Q' := hQ.of_equiv (Subgroup.subgroupOfEquivOfLe hQI).symm
  obtain ⟨S', hS'⟩ := hQ'p.exists_le_sylow
  obtain ⟨S, rfl⟩ := Sylow.mapSurjective_surjective hfs 3 S'
  have : IsCyclic S := hcyc S
  have : IsCyclic (S.mapSurjective hfs : Subgroup I) := by
    rw [Sylow.coe_mapSurjective]
    exact isCyclic_of_surjective (f.subgroupMap (S : Subgroup X))
      (f.subgroupMap_surjective (S : Subgroup X))
  have : IsCyclic Q' :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hS').toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hS').surjective
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hQI).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hQI).surjective

theorem commute_of_pow_three_eq_one_of_isPGroup [Finite X] (hcyc : ∀ S : Sylow 3 X, IsCyclic S)
    {P : Subgroup (MulAut X)} (hP : IsPGroup 3 P)
    (hb : ∀ σ ∈ P, ∀ τ ∈ P, σ ^ 3 = 1 → τ ^ 3 = 1 → ¬ IsInnerAut σ →
      ∃ i : ℕ, IsInnerAut (σ ^ i * τ))
    {σ τ : MulAut X} (hσP : σ ∈ P) (hτP : τ ∈ P) (hσ : σ ^ 3 = 1) (hτ : τ ^ 3 = 1) :
    σ * τ = τ * σ := by
  set I := (MulAut.conj : X →* MulAut X).range with hI
  have hIn : I.Normal := range_conj_normal
  set X₀ : Subgroup P := I.subgroupOf P with hX₀
  have : X₀.Normal := hIn.subgroupOf P
  have hX₀p : IsPGroup 3 X₀ := hP.to_subgroup X₀
  have : IsCyclic X₀ := by
    have : IsCyclic (I ⊓ P : Subgroup (MulAut X)) :=
      isCyclic_of_le_range_conj hcyc (Q := I ⊓ P) hP.to_inf_right inf_le_left
    rw [hX₀, ← Subgroup.inf_subgroupOf_right]
    exact isCyclic_of_surjective
      (Subgroup.subgroupOfEquivOfLe (inf_le_right : I ⊓ P ≤ P)).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe (inf_le_right : I ⊓ P ≤ P)).symm.surjective
  have hb' : ∀ σ τ : P, σ ^ 3 = 1 → τ ^ 3 = 1 → σ ∉ X₀ → ∃ i : ℕ, σ ^ i * τ ∈ X₀ := by
    intro σ' τ' hσ' hτ' hσX
    have h1 : (σ' : MulAut X) ^ 3 = 1 := by rw [← Subgroup.coe_pow, hσ', Subgroup.coe_one]
    have h2 : (τ' : MulAut X) ^ 3 = 1 := by rw [← Subgroup.coe_pow, hτ', Subgroup.coe_one]
    have h3 : ¬ IsInnerAut (σ' : MulAut X) := fun h => hσX (Subgroup.mem_subgroupOf.mpr h)
    obtain ⟨i, hi⟩ := hb σ' σ'.2 τ' τ'.2 h1 h2 h3
    refine ⟨i, Subgroup.mem_subgroupOf.mpr ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_pow]
    exact hi
  have h := commute_of_pow_three_eq_one hX₀p hb' (σ := ⟨σ, hσP⟩) (τ := ⟨τ, hτP⟩)
    (Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hσ))
    (Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hτ))
  exact congrArg Subtype.val h

end Aut

end CFSG.RankThree.PartTwo.KFacts
