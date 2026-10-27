module

public import CFSG.GroupTheory.SubnormalJoin
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Walter

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem conj_commutatorElement_eq_inv {t : G} (ht : t * t = 1) (c : G) :
    t * ⁅c, t⁆ * t⁻¹ = ⁅c, t⁆⁻¹ := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  rw [commutatorElement_def, htinv]
  calc t * (c * t * c⁻¹ * t) * t = t * c * t * c⁻¹ * (t * t) := by group
    _ = t * c * t * c⁻¹ := by rw [ht, mul_one]
    _ = t⁻¹ * c * t⁻¹ * c⁻¹ := by rw [htinv]
    _ = (c * t * c⁻¹ * t)⁻¹ := by group

theorem exists_pow_sq_eq {x : G} (hx : Odd (orderOf x)) : ∃ k : ℕ, (x ^ 2) ^ k = x :=
  ⟨(orderOf x + 1) / 2, by
    rw [← pow_mul, mul_comm, Nat.div_mul_cancel (even_iff_two_dvd.mp hx.add_one), pow_succ,
      pow_orderOf_eq_one, one_mul]⟩

theorem commute_of_conj_eq_inv {τ x y : G} (hτ : τ * τ = 1) (hx : τ * x * τ⁻¹ = x⁻¹)
    (hxo : Odd (orderOf x)) (hy : τ * y = y * τ)
    (hy' : τ * (x * y * x⁻¹) = (x * y * x⁻¹) * τ) : x * y = y * x := by
  have hτinv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ
  have hx' : τ * x⁻¹ * τ⁻¹ = x := by
    rw [show τ * x⁻¹ * τ⁻¹ = (τ * x * τ⁻¹)⁻¹ by group, hx, inv_inv]
  have h1 : x * y * x⁻¹ = x⁻¹ * y * x := by
    have : x * y * x⁻¹ = τ * (x * y * x⁻¹) * τ⁻¹ := by rw [hy', mul_inv_cancel_right]
    rw [this, show τ * (x * y * x⁻¹) * τ⁻¹ =
      (τ * x * τ⁻¹) * (τ * y * τ⁻¹) * (τ * x⁻¹ * τ⁻¹) by group, hx, hx', hy,
      mul_inv_cancel_right]
  have h2 : Commute (x ^ 2) y := by
    rw [Commute, SemiconjBy, pow_two]
    calc x * x * y = x * (x * y * x⁻¹) * x := by group
      _ = x * (x⁻¹ * y * x) * x := by rw [h1]
      _ = y * (x * x) := by group
  obtain ⟨k, hk⟩ := exists_pow_sq_eq hxo
  have := h2.pow_left k
  rw [hk] at this
  exact this

theorem exists_mem_centralizer_mul_mem_commutator {A : Subgroup G} [Finite A] {t : G}
    (ht : t * t = 1) (htA : t ∈ Subgroup.normalizer (A : Set G)) (hA : Odd (Nat.card A))
    {a : G} (ha : a ∈ A) :
    ∃ c ∈ A ⊓ Subgroup.centralizer ({t} : Set G), ∃ m ∈ ⁅A, Subgroup.zpowers t⁆, a = c * m := by
  set n := ⁅a⁻¹, t⁆ with hn
  have htaA : t * a * t⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp htA a).mp ha
  have hna : a * n = t * a * t⁻¹ := by rw [hn, commutatorElement_def]; group
  have hnA : n ∈ A := by
    have : n = a⁻¹ * (t * a * t⁻¹) := by rw [← hna]; group
    rw [this]
    exact A.mul_mem (A.inv_mem ha) htaA
  have hnC : n ∈ ⁅A, Subgroup.zpowers t⁆ :=
    Subgroup.commutator_mem_commutator (A.inv_mem ha) (Subgroup.mem_zpowers t)
  have htn : t * n * t⁻¹ = n⁻¹ := conj_commutatorElement_eq_inv ht a⁻¹
  have hno : Odd (orderOf n) := by
    have h := Subgroup.orderOf_dvd_natCard A hnA
    exact Odd.of_dvd_nat hA h
  set k := (orderOf n + 1) / 2 with hk
  have h2k : n ^ k * n ^ k = n := by
    rw [← pow_add, ← two_mul, hk, Nat.mul_div_cancel' (even_iff_two_dvd.mp hno.add_one),
      pow_succ, pow_orderOf_eq_one, one_mul]
  have htnk : t * n ^ k * t⁻¹ = (n ^ k)⁻¹ := by
    rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply, htn, inv_pow]
  refine ⟨a * n ^ k, ⟨A.mul_mem ha (A.pow_mem hnA k), ?_⟩, (n ^ k)⁻¹,
    ⁅A, Subgroup.zpowers t⁆.inv_mem (⁅A, Subgroup.zpowers t⁆.pow_mem hnC k), by group⟩
  show a * n ^ k ∈ Subgroup.centralizer ({t} : Set G)
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hc : t * (a * n ^ k) * t⁻¹ = a * n ^ k := by
    calc t * (a * n ^ k) * t⁻¹ = (t * a * t⁻¹) * (t * n ^ k * t⁻¹) := by group
      _ = a * n * (n ^ k)⁻¹ := by rw [← hna, htnk]
      _ = a * (n ^ k * n ^ k) * (n ^ k)⁻¹ := by rw [h2k]
      _ = a * n ^ k := by group
  calc a * n ^ k * t = t * (a * n ^ k) * t⁻¹ * t := by rw [hc]
    _ = t * (a * n ^ k) := by group

theorem pow_mul_mul_inv_pow_of_commute {x y : G} (hc : Commute ⁅x, y⁆ x) :
    ∀ n : ℕ, x ^ n * y * (x ^ n)⁻¹ = ⁅x, y⁆ ^ n * y
  | 0 => by simp
  | n + 1 => by
    have ih := pow_mul_mul_inv_pow_of_commute hc n
    have hxy : x * y * x⁻¹ = ⁅x, y⁆ * y := by rw [commutatorElement_def]; group
    calc x ^ (n + 1) * y * (x ^ (n + 1))⁻¹ = x * (x ^ n * y * (x ^ n)⁻¹) * x⁻¹ := by
          rw [pow_succ']; group
      _ = x * (⁅x, y⁆ ^ n * y) * x⁻¹ := by rw [ih]
      _ = ⁅x, y⁆ ^ n * (x * y * x⁻¹) := by
          rw [show x * (⁅x, y⁆ ^ n * y) * x⁻¹ = (x * ⁅x, y⁆ ^ n) * y * x⁻¹ by group,
            ((hc.pow_left n).eq).symm]
          group
      _ = ⁅x, y⁆ ^ (n + 1) * y := by rw [hxy, pow_succ, mul_assoc]

theorem commutatorElement_pow_left {x y : G} (hc : Commute ⁅x, y⁆ x) (n : ℕ) :
    ⁅x ^ n, y⁆ = ⁅x, y⁆ ^ n := by
  rw [commutatorElement_def, pow_mul_mul_inv_pow_of_commute hc n, mul_inv_cancel_right]

theorem mul_pow_of_commute_commutator {x y : G} (hx : Commute ⁅y, x⁆ x)
    (hy : Commute ⁅y, x⁆ y) : ∀ n : ℕ, (x * y) ^ n = x ^ n * y ^ n * ⁅y, x⁆ ^ (n.choose 2)
  | 0 => by simp
  | n + 1 => by
    have ih := mul_pow_of_commute_commutator hx hy n
    set c := ⁅y, x⁆ with hc
    have hyn : y ^ n * x = c ^ n * x * y ^ n := by
      have h := pow_mul_mul_inv_pow_of_commute (x := y) (y := x) hy n
      calc y ^ n * x = (y ^ n * x * (y ^ n)⁻¹) * y ^ n := by group
        _ = c ^ n * x * y ^ n := by rw [h]
    have hcC : Commute (c ^ (n.choose 2)) (x * y) := (hx.pow_left _).mul_right (hy.pow_left _)
    have h1 : Commute (c ^ n) (x ^ (n + 1)) := (hx.pow_left _).pow_right _
    have h2 : Commute (c ^ n) (y ^ (n + 1)) := (hy.pow_left _).pow_right _
    have hch : (n + 1).choose 2 = n + n.choose 2 := by
      rw [Nat.choose_succ_succ', Nat.choose_one_right]
    calc (x * y) ^ (n + 1) = x ^ n * y ^ n * c ^ (n.choose 2) * (x * y) := by rw [pow_succ, ih]
      _ = x ^ n * (y ^ n * x) * y * c ^ (n.choose 2) := by
          rw [mul_assoc (x ^ n * y ^ n), hcC.eq]; group
      _ = c ^ n * x ^ (n + 1) * y ^ (n + 1) * c ^ (n.choose 2) := by
          rw [hyn, pow_succ, pow_succ]
          have h0 : Commute (c ^ n) (x ^ n) := (hx.pow_left _).pow_right _
          calc x ^ n * (c ^ n * x * y ^ n) * y * c ^ n.choose 2
              = (x ^ n * c ^ n) * x * (y ^ n * y) * c ^ n.choose 2 := by group
            _ = (c ^ n * x ^ n) * x * (y ^ n * y) * c ^ n.choose 2 := by rw [h0.eq]
            _ = c ^ n * (x ^ n * x) * (y ^ n * y) * c ^ n.choose 2 := by group
      _ = x ^ (n + 1) * y ^ (n + 1) * c ^ ((n + 1).choose 2) := by
          rw [h1.eq, mul_assoc (x ^ (n + 1)), h2.eq, hch, pow_add]
          group

theorem commutatorElement_mul_left_of_commute {a b x : G} (h1 : Commute a ⁅b, x⁆)
    (h2 : Commute ⁅a, x⁆ ⁅b, x⁆) : ⁅a * b, x⁆ = ⁅a, x⁆ * ⁅b, x⁆ := by
  calc ⁅a * b, x⁆ = a * ⁅b, x⁆ * x * a⁻¹ * x⁻¹ := by simp only [commutatorElement_def]; group
    _ = ⁅b, x⁆ * a * x * a⁻¹ * x⁻¹ := by rw [h1.eq]
    _ = ⁅b, x⁆ * ⁅a, x⁆ := by simp only [commutatorElement_def]; group
    _ = ⁅a, x⁆ * ⁅b, x⁆ := h2.eq.symm

theorem conj_eq_or_conj_eq_inv_of_card_eq_prime {Z : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hZ : Nat.card Z = p) {e : G} (he : e * e = 1) (heZ : e ∈ Subgroup.normalizer (Z : Set G)) :
    (∀ z ∈ Z, e * z * e⁻¹ = z) ∨ (∀ z ∈ Z, e * z * e⁻¹ = z⁻¹) := by
  have : Fact p.Prime := ⟨hp⟩
  have hfin : Finite Z := Nat.finite_of_card_ne_zero (hZ ▸ hp.ne_zero)
  have : IsCyclic Z := isCyclic_of_prime_card hZ
  let σ : Z →* Z :=
    { toFun := fun z => ⟨e * z * e⁻¹, (Subgroup.mem_normalizer_iff.mp heZ z).mp z.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  obtain ⟨m, hm⟩ := σ.map_cyclic
  have heinv : e⁻¹ = e := inv_eq_of_mul_eq_one_right he
  have hσσ : ∀ z : Z, σ (σ z) = z := fun z => Subtype.ext (by
    show e * (e * (z : G) * e⁻¹) * e⁻¹ = z
    rw [heinv]
    calc e * (e * (z : G) * e) * e = (e * e) * z * (e * e) := by group
      _ = z := by rw [he]; group)
  have hdvd : ∀ z : Z, z ^ (m * m) = z := by
    intro z
    have h := hσσ z
    rw [hm, hm, ← zpow_mul] at h
    exact h
  have hgen : ∃ g : Z, orderOf g = p := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Z)
    exact ⟨g, (orderOf_eq_card_of_forall_mem_zpowers hg).trans hZ⟩
  obtain ⟨g, hg⟩ := hgen
  have hmod : (p : ℤ) ∣ m * m - 1 := by
    have h := hdvd g
    have : g ^ (m * m - 1) = 1 := by rw [zpow_sub, h, zpow_one, mul_inv_cancel]
    rwa [← orderOf_dvd_iff_zpow_eq_one, hg] at this
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hfact : m * m - 1 = (m - 1) * (m + 1) := by ring
  rw [hfact] at hmod
  have hord : ∀ z : Z, orderOf z ∣ p := fun z => hZ ▸ orderOf_dvd_natCard z
  have key : ∀ z : Z, ∀ k : ℤ, (p : ℤ) ∣ m - k → z ^ m = z ^ k := by
    intro z k hk
    rw [zpow_eq_zpow_iff_modEq]
    exact (Int.modEq_iff_dvd.mpr ((Int.natCast_dvd_natCast.mpr (hord z)).trans hk)).symm
  have hσ : ∀ z (hz : z ∈ Z), e * z * e⁻¹ = (((⟨z, hz⟩ : Z) ^ m : Z) : G) := fun z hz =>
    congrArg Subtype.val (hm ⟨z, hz⟩)
  rcases hpz.dvd_or_dvd hmod with h | h
  · left
    intro z hz
    rw [hσ z hz, key ⟨z, hz⟩ 1 (by simpa using h), zpow_one]
  · right
    intro z hz
    rw [hσ z hz, key ⟨z, hz⟩ (-1) (by simpa using h), zpow_neg_one, Subgroup.coe_inv]

end CFSG.Walter
