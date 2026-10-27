module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieDef

public section

namespace CFSG.Quasithin.H13.NQCore.Psp4

open scoped commutatorElement

variable {A : Type} [Group A] {p : ℕ} {L P T : Subgroup A}

theorem mem_of_pow_mem_of_pow_eq_one {G : Type*} [Group G] (C : Subgroup G) {g : G} {n j : ℕ}
    (hn : Odd n) (hg : g ^ n ∈ C) (hj : g ^ 2 ^ j = 1) : g ∈ C := by
  have hcop : Nat.Coprime n (2 ^ j) := Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hn)
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  have h1 : g = (g ^ n) ^ a := by
    have e1 : g ^ (a * (n : ℤ) + b * ((2 ^ j : ℕ) : ℤ)) = g := by rw [hab, zpow_one]
    rw [zpow_add, mul_comm a, mul_comm b, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, hj,
      one_zpow, mul_one] at e1
    exact e1.symm
  rw [h1]
  exact C.zpow_mem hg a

theorem false_of_sq_centralizes [Finite A] [hp : Fact p.Prime] (h : OddCfg p L P T)
    (hPa : Nat.card P = p ^ 2) (hab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) {c : A}
    (hc : c ∈ T ⊓ Subgroup.normalizer (P : Set A))
    (hgen : ∀ s ∈ T ⊓ Subgroup.normalizer (P : Set A), ∃ k : ℕ, ∀ x ∈ P,
      s * x * s⁻¹ = c ^ k * x * (c ^ k)⁻¹)
    (hsq : ∀ x ∈ P, c ^ 2 * x * (c ^ 2)⁻¹ = x) : False := by
  have hσ : ∀ z ∈ P, c * z * c⁻¹ ∈ P := fun z hz => (Subgroup.mem_normalizer_iff.mp hc.2 z).mp hz
  have hP1 : P ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hPa
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.out.one_lt
    omega
  obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hP1
  have hx1' : x ≠ 1 := fun h' => hx1 (Subtype.ext h')
  obtain ⟨y, hyP, hy1, hcy⟩ : ∃ y ∈ P, y ≠ 1 ∧ c * y * c⁻¹ ∈ Subgroup.zpowers y := by
    by_cases hy : x * (c * x * c⁻¹) = 1
    · refine ⟨x, hx, hx1', ?_⟩
      have : c * x * c⁻¹ = x⁻¹ := eq_inv_of_mul_eq_one_right hy
      rw [this]
      exact Subgroup.inv_mem _ (Subgroup.mem_zpowers x)
    · refine ⟨x * (c * x * c⁻¹), P.mul_mem hx (hσ x hx), hy, ?_⟩
      have h1 : c * (x * (c * x * c⁻¹)) * c⁻¹ = x * (c * x * c⁻¹) := by
        have h2 : c * (x * (c * x * c⁻¹)) * c⁻¹ = (c * x * c⁻¹) * (c ^ 2 * x * (c ^ 2)⁻¹) := by
          group
        rw [h2, hsq x hx]
        exact (hab x hx _ (hσ x hx)).symm
      rw [h1]
      exact Subgroup.mem_zpowers _
  set W := Subgroup.zpowers y with hW
  have hWP : W ≤ P := Subgroup.zpowers_le.mpr hyP
  have hone : ∀ z ∈ W, c * z * c⁻¹ ∈ W := by
    intro z hz
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ hcy j
  have hcW : ∀ k : ℕ, ∀ z ∈ W, c ^ k * z * (c ^ k)⁻¹ ∈ W := by
    intro k
    induction k with
    | zero => intro z hz; simpa using hz
    | succ k ih =>
      intro z hz
      have h3 : c ^ (k + 1) * z * (c ^ (k + 1))⁻¹ = c * (c ^ k * z * (c ^ k)⁻¹) * c⁻¹ := by
        rw [pow_succ']
        group
      rw [h3]
      exact hone _ (ih z hz)
  have hWorder : Nat.card W = p := by
    rw [hW, Nat.card_zpowers, orderOf_eq_prime (h.exp y hyP) hy1]
  have hcomm : ⁅P, P⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun x hx =>
      Subgroup.mem_centralizer_iff.mpr fun g hg => hab g hg x hx
  rcases h.irred W (by rw [hcomm]; exact bot_le) hWP (fun s hs =>
      Subgroup.mem_normalizer_fintype (S := (W : Set A)) fun z hz => by
        obtain ⟨k, hk⟩ := hgen s hs
        rw [hk z (hWP hz)]
        exact hcW k z hz) with h1 | h1
  · have : y ∈ (⊥ : Subgroup A) := hcomm ▸ h1 ▸ Subgroup.mem_zpowers y
    exact hy1 (Subgroup.mem_bot.mp this)
  · have h2 : Nat.card W = Nat.card P := by rw [h1]
    rw [hWorder, hPa] at h2
    have : p < p ^ 2 := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 2 := Nat.pow_lt_pow_right hp.out.one_lt (by norm_num)
    omega

theorem even_of_pow_centralizes [Finite A] [hp : Fact p.Prime] (h : OddCfg p L P T)
    (hPa : Nat.card P = p ^ 2) (hab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) {c : A}
    (hc : c ∈ T ⊓ Subgroup.normalizer (P : Set A))
    (hgen : ∀ s ∈ T ⊓ Subgroup.normalizer (P : Set A), ∃ k : ℕ, ∀ x ∈ P,
      s * x * s⁻¹ = c ^ k * x * (c ^ k)⁻¹) {n : ℕ}
    (hcen : ∀ y ∈ P, c ^ (2 * n) * y * (c ^ (2 * n))⁻¹ = y) : Even n := by
  by_contra hn
  have hodd : Odd n := Nat.not_even_iff_odd.mp hn
  obtain ⟨j, hj⟩ := h.sylow.2.1 ⟨c, hc.1⟩
  have hcj : c ^ 2 ^ j = 1 := congrArg Subtype.val hj
  have hgC : c ^ 2 ∈ Subgroup.centralizer (P : Set A) := by
    refine mem_of_pow_mem_of_pow_eq_one _ hodd (j := j) ?_ ?_
    · rw [← pow_mul]
      refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
      calc y * c ^ (2 * n) = (c ^ (2 * n) * y * (c ^ (2 * n))⁻¹) * c ^ (2 * n) := by
            rw [hcen y hy]
        _ = c ^ (2 * n) * y := inv_mul_cancel_right _ _
    · rw [← pow_mul, mul_comm, pow_mul, hcj, one_pow]
  refine false_of_sq_centralizes h hPa hab hc hgen fun x hx => ?_
  rw [← Subgroup.mem_centralizer_iff.mp hgC x hx, mul_inv_cancel_right]

end CFSG.Quasithin.H13.NQCore.Psp4
