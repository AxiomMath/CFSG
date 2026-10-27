module

public import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting

public section

namespace CFSG.RankThree.PartTwo.Sec17.Proof17Res11

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem conj_mem {H : Subgroup G} {g x : G} (hg : g ∈ Subgroup.normalizer (H : Set G))
    (hx : x ∈ H) : g * x * g⁻¹ ∈ H :=
  (Subgroup.mem_normalizer_iff.mp hg x).mp hx

theorem isPGroup_zpowers_of_pow_three {c : G} (hc3 : c ^ 3 = 1) :
    IsPGroup 3 (Subgroup.zpowers c) := fun g => ⟨1, Subtype.ext (by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
  rw [pow_one, Subgroup.coe_pow, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
    zpow_natCast, hc3, one_zpow, Subgroup.coe_one])⟩

theorem conj_mem_commutator {H K : Subgroup G} {g : G} (hgH : g ∈ Subgroup.normalizer (H : Set G))
    (hgK : g ∈ Subgroup.normalizer (K : Set G)) {x : G} (hx : x ∈ ⁅H, K⁆) :
    g * x * g⁻¹ ∈ ⁅H, K⁆ := by
  have hle : ⁅H, K⁆ ≤ ⁅H, K⁆.comap (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro h hh k hk
    rw [Subgroup.mem_comap]
    change g * ⁅h, k⁆ * g⁻¹ ∈ ⁅H, K⁆
    have e : g * ⁅h, k⁆ * g⁻¹ = ⁅g * h * g⁻¹, g * k * g⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.commutator_mem_commutator (conj_mem hgH hh) (conj_mem hgK hk)
  exact hle hx

theorem le_normalizer_commutator_of [Finite G] {Γ H K : Subgroup G}
    (hH : Γ ≤ Subgroup.normalizer (H : Set G)) (hK : Γ ≤ Subgroup.normalizer (K : Set G)) :
    Γ ≤ Subgroup.normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := fun _ hg =>
  Subgroup.mem_normalizer_fintype fun _ hx => conj_mem_commutator (hH hg) (hK hg) hx

theorem exists_commute_of_coset [Finite G] {H : Subgroup G} {c y : G} (hc3 : c ^ 3 = 1)
    (hcH : c ∈ Subgroup.normalizer (H : Set G)) (hH3 : ¬ 3 ∣ Nat.card H)
    (hy : y⁻¹ * (c * y * c⁻¹) ∈ H) : ∃ y' : G, y⁻¹ * y' ∈ H ∧ c * y' * c⁻¹ = y' := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let S : Subgroup G :=
    { carrier := {a | a ∈ Subgroup.normalizer (H : Set G) ∧ y⁻¹ * (a * y * a⁻¹) ∈ H}
      one_mem' := ⟨one_mem _, by simp⟩
      mul_mem' := by
        rintro a b ⟨haN, ha⟩ ⟨hbN, hb⟩
        refine ⟨mul_mem haN hbN, ?_⟩
        have e : y⁻¹ * (a * b * y * (a * b)⁻¹) =
            (y⁻¹ * (a * y * a⁻¹)) * (a * (y⁻¹ * (b * y * b⁻¹)) * a⁻¹) := by group
        rw [e]
        exact mul_mem ha (conj_mem haN hb)
      inv_mem' := by
        rintro a ⟨haN, ha⟩
        refine ⟨inv_mem haN, ?_⟩
        have e : y⁻¹ * (a⁻¹ * y * a⁻¹⁻¹) = a⁻¹ * (y⁻¹ * (a * y * a⁻¹))⁻¹ * a⁻¹⁻¹ := by group
        rw [e]
        exact conj_mem (inv_mem haN) (inv_mem ha) }
  have hZS : Subgroup.zpowers c ≤ S := Subgroup.zpowers_le.mpr ⟨hcH, hy⟩
  let α : ↥(Subgroup.zpowers c) →* MulAut G := MulAut.conj.comp (Subgroup.zpowers c).subtype
  obtain ⟨y', hy', hfix⟩ := (CFSG.Semidihedral.Principal.coprime_invariant_coset_fixed 3
    (isPGroup_zpowers_of_pow_three hc3) α H hH3 y).2 (fun a x hx => by
      obtain ⟨haN, ha⟩ := hZS a.2
      change y⁻¹ * ((a : G) * x * (a : G)⁻¹) ∈ H
      have e : y⁻¹ * ((a : G) * x * (a : G)⁻¹) =
          (y⁻¹ * ((a : G) * y * (a : G)⁻¹)) * ((a : G) * (y⁻¹ * x) * (a : G)⁻¹) := by group
      rw [e]
      exact mul_mem ha (conj_mem haN hx))
  exact ⟨y', hy', hfix ⟨c, Subgroup.mem_zpowers c⟩⟩

theorem normal_subgroupOf_of_commutator_le {P D : Subgroup G} (hPP : ⁅P, P⁆ ≤ D) :
    (D.subgroupOf P).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have h1 := hPP (Subgroup.commutator_mem_commutator g.2 n.2)
  rw [commutatorElement_def] at h1
  have e : ((g * n * g⁻¹ : ↥P) : G) = ((g : G) * n * (g : G)⁻¹ * (n : G)⁻¹) * n := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e]
  exact D.mul_mem h1 hn

theorem quot_mul_comm {P D : Subgroup G} (hPP : ⁅P, P⁆ ≤ D) [(D.subgroupOf P).Normal]
    (a b : ↥P ⧸ D.subgroupOf P) : a * b = b * a := by
  induction a using QuotientGroup.induction_on with
  | H x =>
  induction b using QuotientGroup.induction_on with
  | H y =>
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have e : (((x * y)⁻¹ * (y * x) : ↥P) : G) = ⁅((y : G))⁻¹, ((x : G))⁻¹⁆ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def, inv_inv]
    group
  rw [e]
  exact hPP (Subgroup.commutator_mem_commutator (inv_mem y.2) (inv_mem x.2))

theorem mul_pow_mem_of_commutator_le {P R : Subgroup G} (hPP : ⁅P, P⁆ ≤ R) {x y : G}
    (hx : x ∈ P) (hy : y ∈ P) (n : ℕ) (hxn : x ^ n ∈ R) (hyn : y ^ n ∈ R) : (x * y) ^ n ∈ R := by
  have := normal_subgroupOf_of_commutator_le hPP
  have key : ∀ z : ↥P, (QuotientGroup.mk (z ^ n) : ↥P ⧸ R.subgroupOf P) = 1 ↔ (z : G) ^ n ∈ R :=
    fun z => by rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.coe_pow]
  have h := (key ⟨x * y, mul_mem hx hy⟩).mp
  apply h
  have hc : Commute (QuotientGroup.mk (⟨x, hx⟩ : ↥P) : ↥P ⧸ R.subgroupOf P)
      (QuotientGroup.mk (⟨y, hy⟩ : ↥P)) := quot_mul_comm hPP _ _
  rw [show (⟨x * y, mul_mem hx hy⟩ : ↥P) = ⟨x, hx⟩ * ⟨y, hy⟩ from rfl, QuotientGroup.mk_pow,
    QuotientGroup.mk_mul, hc.mul_pow, ← QuotientGroup.mk_pow, ← QuotientGroup.mk_pow,
    (key ⟨x, hx⟩).mpr hxn, (key ⟨y, hy⟩).mpr hyn, one_mul]

theorem eq_zero_of_four_smul {Y : Type*} [AddCommGroup Y] {m : ℕ} (hm : Odd m) {y : Y}
    (h4 : 4 • y = 0) (hmy : m • y = 0) : y = 0 := by
  obtain ⟨k, rfl⟩ := hm
  have h4k : ∀ j : ℕ, (4 * j) • y = 0 := fun j => by rw [mul_comm, mul_smul, h4, smul_zero]
  rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [show 2 * (j + j) + 1 = 4 * j + 1 by ring, add_smul, one_smul, h4k, zero_add] at hmy
    exact hmy
  · rw [show 2 * (2 * j + 1) + 1 = 4 * j + 3 by ring] at hmy
    have h := h4k (j + 1)
    rw [show 4 * (j + 1) = (4 * j + 3) + 1 by ring, add_smul, hmy, one_smul, zero_add] at h
    exact h

theorem conj_mul_inv_mem_of_fpf {P D : Subgroup G} (hPP : ⁅P, P⁆ ≤ D) {m : ℕ} (hm : Odd m)
    (hodd : ∀ x ∈ P, x ^ m ∈ D) {c u : G} (hc3 : c ^ 3 = 1)
    (hcP : c ∈ Subgroup.normalizer (P : Set G)) (hcD : c ∈ Subgroup.normalizer (D : Set G))
    (huP : u ∈ Subgroup.normalizer (P : Set G)) (huD : u ∈ Subgroup.normalizer (D : Set G))
    (hu2 : u * u = 1) (hcomm : u * (c * u * c⁻¹) = c * u * c⁻¹ * u)
    (hrel : u * (c * u * c⁻¹) * (c * (c * u * c⁻¹) * c⁻¹) = 1)
    (hfpf : ∀ x ∈ P, x * (c * x * c⁻¹) * (c * (c * x * c⁻¹) * c⁻¹) ∈ D) {x : G} (hx : x ∈ P) :
    u * x * u⁻¹ * x⁻¹ ∈ D := by
  classical
  have := normal_subgroupOf_of_commutator_le hPP
  let _ : CommGroup (↥P ⧸ D.subgroupOf P) :=
    { (inferInstance : Group (↥P ⧸ D.subgroupOf P)) with mul_comm := quot_mul_comm hPP }
  let ψ : G → Additive (↥P ⧸ D.subgroupOf P) := fun z =>
    if hz : z ∈ P then Additive.ofMul (QuotientGroup.mk (⟨z, hz⟩ : ↥P)) else 0
  have hψ : ∀ {z : G} (hz : z ∈ P),
      ψ z = Additive.ofMul (QuotientGroup.mk (⟨z, hz⟩ : ↥P) : ↥P ⧸ D.subgroupOf P) :=
    fun hz => by simp [ψ, hz]
  have hψmul : ∀ {z w : G}, z ∈ P → w ∈ P → ψ (z * w) = ψ z + ψ w := by
    intro z w hz hw
    rw [hψ (mul_mem hz hw), hψ hz, hψ hw, ← ofMul_mul]
    rfl
  have hψD : ∀ {z : G}, z ∈ P → (ψ z = 0 ↔ z ∈ D) := by
    intro z hz
    rw [hψ hz, ofMul_eq_zero, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hψinv : ∀ {z : G}, z ∈ P → ψ z⁻¹ = -ψ z := by
    intro z hz
    rw [eq_neg_iff_add_eq_zero, ← hψmul (inv_mem hz) hz, inv_mul_cancel, hψD (one_mem _)]
    exact one_mem _
  have hψpow : ∀ {z : G}, z ∈ P → ∀ n : ℕ, ψ (z ^ n) = n • ψ z := by
    intro z hz n
    induction n with
    | zero => rw [pow_zero, zero_smul, hψD (one_mem _)]; exact one_mem _
    | succ n ih => rw [pow_succ, hψmul (pow_mem hz n) hz, ih, succ_nsmul]
  obtain ⟨u₁, hu₁⟩ : ∃ v, v = c * u * c⁻¹ := ⟨_, rfl⟩
  obtain ⟨u₂, hu₂⟩ : ∃ v, v = c * u₁ * c⁻¹ := ⟨_, rfl⟩
  rw [← hu₁] at hcomm hrel
  rw [← hu₂] at hrel
  have hinv : ∀ {v : G}, v * v = 1 → v⁻¹ = v := fun h => inv_eq_of_mul_eq_one_right h
  have hu1sq : u₁ * u₁ = 1 := by
    rw [hu₁, show c * u * c⁻¹ * (c * u * c⁻¹) = c * (u * u) * c⁻¹ by group, hu2]
    group
  have hu2sq : u₂ * u₂ = 1 := by
    rw [hu₂, show c * u₁ * c⁻¹ * (c * u₁ * c⁻¹) = c * (u₁ * u₁) * c⁻¹ by group, hu1sq]
    group
  have R4 : u * u₁ = u₂ := by
    have h1 : u₂ = (u * u₁)⁻¹ := eq_inv_of_mul_eq_one_right hrel
    rw [h1, mul_inv_rev, hinv hu2, hinv hu1sq, ← hcomm]
  have R5 : u₁ * u = u₂ := by rw [← hcomm, R4]
  have R6 : u * u₂ = u₁ := by rw [← R4, ← mul_assoc, hu2, one_mul]
  have R7 : u₂ * u = u₁ := by rw [← R5, mul_assoc, hu2, mul_one]
  have R8 : u₁ * u₂ = u := by rw [← R5, ← mul_assoc, hu1sq, one_mul]
  have R9 : u₂ * u₁ = u := by rw [← R4, mul_assoc, hu1sq, mul_one]
  have hc3' : c * c * c = 1 := by rw [← pow_three', hc3]
  have C1 : c * u₂ * c⁻¹ = u := by
    rw [hu₂, hu₁, show c * (c * (c * u * c⁻¹) * c⁻¹) * c⁻¹ = (c * c * c) * u * (c * c * c)⁻¹ by
      group, hc3']
    group
  have K1 : u * c * u = u₂ * c := by
    rw [show u * c * u = u * (c * u * c⁻¹) * c by group, ← hu₁, R4]
  have K2 : u₁ * c * u₁ = u * c := by
    rw [show u₁ * c * u₁ = u₁ * (c * u₁ * c⁻¹) * c by group, ← hu₂, R8]
  have K3 : u₂ * c * u₂ = u₁ * c := by
    rw [show u₂ * c * u₂ = u₂ * (c * u₂ * c⁻¹) * c by group, C1, R7]
  have K4 : u * (c * c) * u = u₁ * (c * c) := by
    rw [show u * (c * c) * u = u * (c * (c * u * c⁻¹) * c⁻¹) * (c * c) by group, ← hu₁, ← hu₂,
      R6]
  have K5 : u₁ * (c * c) * u₁ = u₂ * (c * c) := by
    rw [show u₁ * (c * c) * u₁ = u₁ * (c * (c * u₁ * c⁻¹) * c⁻¹) * (c * c) by group, ← hu₂, C1,
      R5]
  have K6 : u₂ * (c * c) * u₂ = u * (c * c) := by
    rw [show u₂ * (c * c) * u₂ = u₂ * (c * (c * u₂ * c⁻¹) * c⁻¹) * (c * c) by group, C1, ← hu₁,
      R9]
  have hu₁P : u₁ ∈ Subgroup.normalizer (P : Set G) := by
    rw [hu₁]; exact mul_mem (mul_mem hcP huP) (inv_mem hcP)
  have hu₁D : u₁ ∈ Subgroup.normalizer (D : Set G) := by
    rw [hu₁]; exact mul_mem (mul_mem hcD huD) (inv_mem hcD)
  have hu₂P : u₂ ∈ Subgroup.normalizer (P : Set G) := by
    rw [hu₂]; exact mul_mem (mul_mem hcP hu₁P) (inv_mem hcP)
  have hu₂D : u₂ ∈ Subgroup.normalizer (D : Set G) := by
    rw [hu₂]; exact mul_mem (mul_mem hcD hu₁D) (inv_mem hcD)
  have hE : ∀ e : G, e ∈ Subgroup.normalizer (P : Set G) → e ∈ Subgroup.normalizer (D : Set G) →
      ∀ y ∈ P, ψ (e * y * e⁻¹) + ψ ((e * c) * y * (e * c)⁻¹) +
        ψ ((e * (c * c)) * y * (e * (c * c))⁻¹) = 0 := by
    intro e heP heD y hy
    have hecP : e * c ∈ Subgroup.normalizer (P : Set G) := mul_mem heP hcP
    have heccP : e * (c * c) ∈ Subgroup.normalizer (P : Set G) := mul_mem heP (mul_mem hcP hcP)
    have h := conj_mem heD (hfpf y hy)
    have e1 : e * (y * (c * y * c⁻¹) * (c * (c * y * c⁻¹) * c⁻¹)) * e⁻¹ =
        (e * y * e⁻¹) * ((e * c) * y * (e * c)⁻¹) * ((e * (c * c)) * y * (e * (c * c))⁻¹) := by
      group
    rw [e1] at h
    have h1 := conj_mem heP hy
    have h2 := conj_mem hecP hy
    have h3 := conj_mem heccP hy
    rw [← hψmul h1 h2, ← hψmul (mul_mem h1 h2) h3]
    exact (hψD (mul_mem (mul_mem h1 h2) h3)).mpr h
  have hF : ∀ e : G, e ∈ Subgroup.normalizer (P : Set G) → e ∈ Subgroup.normalizer (D : Set G) →
      e * e = 1 → ∀ y ∈ P, ψ y + ψ ((e * c * e) * y * (e * c * e)⁻¹) +
        ψ ((e * (c * c) * e) * y * (e * (c * c) * e)⁻¹) = 0 := by
    intro e heP heD he2 y hy
    have h := hE e heP heD (e * y * e⁻¹) (conj_mem heP hy)
    have e1 : e * (e * y * e⁻¹) * e⁻¹ = y := by
      rw [show e * (e * y * e⁻¹) * e⁻¹ = (e * e) * y * (e * e)⁻¹ by group, he2]
      group
    have e2 : (e * c) * (e * y * e⁻¹) * (e * c)⁻¹ = (e * c * e) * y * (e * c * e)⁻¹ := by group
    have e3 : (e * (c * c)) * (e * y * e⁻¹) * (e * (c * c))⁻¹ =
        (e * (c * c) * e) * y * (e * (c * c) * e)⁻¹ := by group
    rwa [e1, e2, e3] at h
  have hN : ∀ y ∈ P, ψ (u * y * u⁻¹) + ψ (u₁ * y * u₁⁻¹) + ψ (u₂ * y * u₂⁻¹) = 3 • ψ y := by
    intro y hy
    have Eu := hE u huP huD y hy
    have Eu₁ := hE u₁ hu₁P hu₁D y hy
    have Eu₂ := hE u₂ hu₂P hu₂D y hy
    have Fu := hF u huP huD hu2 y hy
    have Fu₁ := hF u₁ hu₁P hu₁D hu1sq y hy
    have Fu₂ := hF u₂ hu₂P hu₂D hu2sq y hy
    rw [K1, K4] at Fu
    rw [K2, K5] at Fu₁
    rw [K3, K6] at Fu₂
    rw [← sub_eq_zero]
    have e : ψ (u * y * u⁻¹) + ψ (u₁ * y * u₁⁻¹) + ψ (u₂ * y * u₂⁻¹) - 3 • ψ y =
        (ψ (u * y * u⁻¹) + ψ ((u * c) * y * (u * c)⁻¹) +
            ψ ((u * (c * c)) * y * (u * (c * c))⁻¹)) +
          (ψ (u₁ * y * u₁⁻¹) + ψ ((u₁ * c) * y * (u₁ * c)⁻¹) +
            ψ ((u₁ * (c * c)) * y * (u₁ * (c * c))⁻¹)) +
          (ψ (u₂ * y * u₂⁻¹) + ψ ((u₂ * c) * y * (u₂ * c)⁻¹) +
            ψ ((u₂ * (c * c)) * y * (u₂ * (c * c))⁻¹)) -
          ((ψ y + ψ ((u₂ * c) * y * (u₂ * c)⁻¹) +
              ψ ((u₁ * (c * c)) * y * (u₁ * (c * c))⁻¹)) +
            (ψ y + ψ ((u * c) * y * (u * c)⁻¹) +
              ψ ((u₂ * (c * c)) * y * (u₂ * (c * c))⁻¹)) +
            (ψ y + ψ ((u₁ * c) * y * (u₁ * c)⁻¹) +
              ψ ((u * (c * c)) * y * (u * (c * c))⁻¹))) := by
      abel
    rw [e, Eu, Eu₁, Eu₂, Fu, Fu₁, Fu₂]
    abel
  have hxu : u * x * u⁻¹ ∈ P := conj_mem huP hx
  have h1 := hN x hx
  have h2 := hN (u * x * u⁻¹) hxu
  have e1 : u * (u * x * u⁻¹) * u⁻¹ = x := by
    rw [show u * (u * x * u⁻¹) * u⁻¹ = (u * u) * x * (u * u)⁻¹ by group, hu2]
    group
  have e2 : u₁ * (u * x * u⁻¹) * u₁⁻¹ = u₂ * x * u₂⁻¹ := by
    rw [show u₁ * (u * x * u⁻¹) * u₁⁻¹ = (u₁ * u) * x * (u₁ * u)⁻¹ by group, R5]
  have e3 : u₂ * (u * x * u⁻¹) * u₂⁻¹ = u₁ * x * u₁⁻¹ := by
    rw [show u₂ * (u * x * u⁻¹) * u₂⁻¹ = (u₂ * u) * x * (u₂ * u)⁻¹ by group, R7]
  rw [e1, e2, e3] at h2
  have hw : u * x * u⁻¹ * x⁻¹ ∈ P := mul_mem hxu (inv_mem hx)
  have hψw : ψ (u * x * u⁻¹ * x⁻¹) = ψ (u * x * u⁻¹) - ψ x := by
    rw [hψmul hxu (inv_mem hx), hψinv hx, sub_eq_add_neg]
  have h4 : 4 • ψ (u * x * u⁻¹ * x⁻¹) = 0 := by
    rw [hψw]
    have e : 4 • (ψ (u * x * u⁻¹) - ψ x) =
        (ψ (u * x * u⁻¹) + ψ (u₁ * x * u₁⁻¹) + ψ (u₂ * x * u₂⁻¹) - 3 • ψ x) -
          (ψ x + ψ (u₂ * x * u₂⁻¹) + ψ (u₁ * x * u₁⁻¹) - 3 • ψ (u * x * u⁻¹)) := by
      abel
    rw [e, h1, h2]
    abel
  have hmw : m • ψ (u * x * u⁻¹ * x⁻¹) = 0 := by
    rw [← hψpow hw m]
    exact (hψD (pow_mem hw m)).mpr (hodd _ hw)
  exact (hψD hw).mp (eq_zero_of_four_smul hm h4 hmw)

end CFSG.RankThree.PartTwo.Sec17.Proof17Res11
