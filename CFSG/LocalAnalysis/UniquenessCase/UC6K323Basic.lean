module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K323Fr

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6.K323B

open Matrix

variable {p : ℕ} [Fact p.Prime]

theorem arith (hp2 : p ≠ 2) :
    ∃ m : ℕ, 0 < m ∧ (p ^ 2 - 1) / 2 = 4 * m ∧ ((p ^ 2 - 1) / 2) * 2 = p ^ 2 - 1 ∧
      p - 1 < (p ^ 2 - 1) / 2 ∧ ¬ p ∣ (p ^ 2 - 1) / 2 := by
  have hp : p.Prime := Fact.out
  obtain ⟨k, hk⟩ : ∃ k, p = 2 * k + 1 := by
    rcases hp.eq_two_or_odd' with h | h
    · exact absurd h hp2
    · exact h
  have hk1 : 1 ≤ k := by
    have := hp.two_le
    omega
  obtain ⟨m, hm⟩ := Nat.even_mul_succ_self k
  have hsq : p ^ 2 - 1 = 8 * m := by
    have h1 : p ^ 2 = 4 * (k * (k + 1)) + 1 := by rw [hk]; ring
    omega
  have hn : (p ^ 2 - 1) / 2 = 4 * m := by omega
  have hm0 : 0 < m := by
    have : 0 < k * (k + 1) := Nat.mul_pos (by omega) (by omega)
    omega
  refine ⟨m, hm0, hn, by omega, ?_, ?_⟩
  · have h2 : 2 * k < 4 * m := by nlinarith
    omega
  · intro h
    have h4 : p ∣ 4 * m := hn ▸ h
    have h1 : p ∣ p ^ 2 - 1 := by
      rw [hsq, show 8 * m = 2 * (4 * m) by ring]
      exact h4.mul_left 2
    have h2 : p ∣ p ^ 2 := dvd_pow_self p (by norm_num)
    have h3 : p ∣ p ^ 2 - (p ^ 2 - 1) := Nat.dvd_sub h2 h1
    rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hp.pos)] at h3
    exact hp.one_lt.ne' (Nat.dvd_one.1 h3)

theorem cyclic_data {X : Subgroup (GL (Fin 3) (ZMod p))} (hXcyc : IsCyclic X) :
    ∃ g : GL (Fin 3) (ZMod p), g ∈ X ∧ orderOf g = Nat.card X ∧ ∀ y ∈ X, ∃ k : ℕ, y = g ^ k := by
  obtain ⟨g, hg⟩ := hXcyc.exists_generator
  refine ⟨g, g.2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg]
  · intro y hy
    obtain ⟨k, hk⟩ := mem_powers_iff_mem_zpowers.2 (hg ⟨y, hy⟩)
    exact ⟨k, by simpa using congrArg Subtype.val hk.symm⟩

theorem exists_nonzero_of_finrank_one {Z : Submodule (ZMod p) (Fin 3 → ZMod p)}
    (hZ : Module.finrank (ZMod p) Z = 1) :
    ∃ z : Fin 3 → ZMod p, z ≠ 0 ∧ z ∈ Z ∧ ∀ w ∈ Z, ∃ c : ZMod p, w = c • z := by
  obtain ⟨⟨z, hzZ⟩, hz0, hall⟩ := finrank_eq_one_iff'.1 hZ
  refine ⟨z, fun h => hz0 (Subtype.ext h), hzZ, fun w hw => ?_⟩
  obtain ⟨c, hc⟩ := hall ⟨w, hw⟩
  exact ⟨c, (congrArg Subtype.val hc).symm⟩

theorem frobenius {X : Subgroup (GL (Fin 3) (ZMod p))} {g : GL (Fin 3) (ZMod p)} (hgX : g ∈ X)
    {n : ℕ} (horder : orderOf g = n) (hn : p - 1 < n) (hpn : ¬ p ∣ n)
    (hpow : ∀ y ∈ X, ∃ k : ℕ, y = g ^ k) {z : Fin 3 → ZMod p} (hz0 : z ≠ 0)
    (hXz : ∀ y ∈ X, (y : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ z = z) :
    ∀ y ∈ X, y ≠ 1 → ∀ v : Fin 3 → ZMod p,
      (y : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ v = v → ∃ c : ZMod p, v = c • z := by
  intro y hy hy1 v hyv
  by_contra hcon
  push Not at hcon
  obtain ⟨k, hk⟩ := hpow y hy
  refine K323Fr.false_of_fixed_outside horder hn hpn ?_ hz0 (hXz g hgX) (hXz y hy) hyv hcon ?_
  · rw [hk]
    exact (Commute.self_pow g k).eq
  · by_contra hno
    push Not at hno
    apply hy1
    refine Units.ext ?_
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun u => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hno u, Units.val_one, Matrix.one_mulVec]

theorem fixed_sq {X : Subgroup (GL (Fin 3) (ZMod p))} {g : GL (Fin 3) (ZMod p)} (hgX : g ∈ X)
    {n m : ℕ} (hm : 0 < m) (hnm : n = 4 * m) (horder : orderOf g = n) {z : Fin 3 → ZMod p}
    (hfr : ∀ y ∈ X, y ≠ 1 → ∀ v : Fin 3 → ZMod p,
      (y : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ v = v → ∃ c : ZMod p, v = c • z)
    {Z : Submodule (ZMod p) (Fin 3 → ZMod p)} (hzZ : z ∈ Z) (hZz : ∀ w ∈ Z, ∃ c : ZMod p, w = c • z)
    (hXZ : ∀ y ∈ X, ∀ w ∈ Z, (y : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ w = w) :
    orderOf (g ^ m) = 4 ∧ (g ^ m) ^ 4 = 1 ∧ g ^ m ∈ X ∧
      {v : Fin 3 → ZMod p | (((g ^ m) ^ 2 : GL (Fin 3) (ZMod p)) :
        Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ v = v} = (Z : Set (Fin 3 → ZMod p)) := by
  have hdvd : m ∣ orderOf g := by rw [horder, hnm]; exact Dvd.intro_left 4 rfl
  have hord : orderOf (g ^ m) = 4 := by
    rw [orderOf_pow_of_dvd hm.ne' hdvd, horder, hnm]
    exact Nat.mul_div_cancel 4 hm
  have hgm : g ^ m ∈ X := X.pow_mem hgX m
  refine ⟨hord, by rw [← hord]; exact pow_orderOf_eq_one _, hgm, ?_⟩
  ext v
  constructor
  · intro hv
    have ht : (g ^ m) ^ 2 ≠ 1 := by
      intro h
      have : orderOf (g ^ m) ∣ 2 := orderOf_dvd_of_pow_eq_one h
      rw [hord] at this
      omega
    obtain ⟨c, hc⟩ := hfr ((g ^ m) ^ 2) (X.pow_mem hgm 2) ht v hv
    rw [hc]
    exact Z.smul_mem c hzZ
  · intro hv
    exact hXZ _ (X.pow_mem hgm 2) v hv

end CFSG.LocalAnalysis.UniquenessCase.UC6.K323B
