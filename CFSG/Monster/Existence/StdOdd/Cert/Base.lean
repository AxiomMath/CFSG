module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Data.Nat.Prime.Int

public section

namespace CFSG.Monster.Existence.StdOdd.Cert

open Subgroup

section Orbit

variable {G X : Type*} [Group G] [MulAction G X]

theorem card_eq_ncard_orbit_mul (H : Subgroup G) (b : X) :
    Nat.card H = (MulAction.orbit H b).ncard * Nat.card ↥(H ⊓ MulAction.stabilizer G b) := by
  have h := Subgroup.index_mul_card (MulAction.stabilizer (↥H) b)
  rw [MulAction.index_stabilizer] at h
  have e : ↥(H ⊓ MulAction.stabilizer G b) ≃ ↥(MulAction.stabilizer (↥H) b) :=
    { toFun := fun g => ⟨⟨g.1, g.2.1⟩, g.2.2⟩
      invFun := fun g => ⟨g.1.1, g.1.2, g.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e]
  exact h.symm

end Orbit

section Centralizer

variable {G X : Type*} [Group G] [MulAction G X]

theorem smul_pow_smul_of_mem_centralizer {x c : G} (hc : c ∈ centralizer ({x} : Set G)) (j : ℕ)
    (b : X) : c • (x ^ j • b) = x ^ j • (c • b) := by
  have h : Commute c x := mem_centralizer_singleton_iff.1 hc
  rw [← mul_smul, ← mul_smul, (h.pow_right j).eq]

theorem fixes_pow_smul_of_mem_centralizer {x c : G} (hc : c ∈ centralizer ({x} : Set G)) {b : X}
    (hb : c • b = b) (j : ℕ) : c • (x ^ j • b) = x ^ j • b := by
  rw [smul_pow_smul_of_mem_centralizer hc, hb]

theorem smul_mem_profileSet {Y : Type*} (ρ : X → X → Y)
    (hρ : ∀ (g : G) (u w : X), ρ (g • u) (g • w) = ρ u w) (x : G) (b : X) (ks : Finset ℕ)
    (O : Finset X) (hO : ∀ (g : G), ∀ u ∈ O, g • u ∈ O) (hb : b ∈ O)
    [DecidablePred fun u => ∀ k ∈ ks, ρ u (x ^ k • u) = ρ b (x ^ k • b)] {c : G}
    (hc : c ∈ centralizer ({x} : Set G)) :
    c • b ∈ O.filter fun u => ∀ k ∈ ks, ρ u (x ^ k • u) = ρ b (x ^ k • b) := by
  refine Finset.mem_filter.2 ⟨hO c b hb, fun k _ => ?_⟩
  rw [← smul_pow_smul_of_mem_centralizer hc k b, hρ]

theorem stabilizer_inf_centralizer_le {x : G} {b : X} {K : Subgroup G}
    (hK : ∀ g : G, (∀ j < orderOf x, g • (x ^ j • b) = x ^ j • b) → g ∈ K) :
    MulAction.stabilizer G b ⊓ centralizer ({x} : Set G) ≤ K := fun g hg =>
  hK g fun j _ => fixes_pow_smul_of_mem_centralizer hg.2 (MulAction.mem_stabilizer_iff.1 hg.1) j

theorem ncard_orbit_centralizer_le {x : G} {b : X} {S : Finset X}
    (hS : ∀ c ∈ centralizer ({x} : Set G), c • b ∈ S) :
    (MulAction.orbit (centralizer ({x} : Set G)) b).ncard ≤ S.card := by
  rw [← Set.ncard_coe_finset S]
  refine Set.ncard_le_ncard ?_ (Finset.finite_toSet S)
  rintro _ ⟨c, rfl⟩
  exact hS c c.2

theorem card_centralizer_le_of_orbitBase [Finite G] (x : G) (b : X) (S : Finset X) (K : Subgroup G)
    (hS : ∀ c ∈ centralizer ({x} : Set G), c • b ∈ S)
    (hK : ∀ g : G, (∀ j < orderOf x, g • (x ^ j • b) = x ^ j • b) → g ∈ K) :
    Nat.card (centralizer ({x} : Set G)) ≤
      S.card * Nat.card ↥(K ⊓ centralizer ({x} : Set G)) := by
  rw [card_eq_ncard_orbit_mul (centralizer ({x} : Set G)) b]
  refine Nat.mul_le_mul (ncard_orbit_centralizer_le hS) (Subgroup.card_le_of_le ?_)
  exact fun g hg => ⟨stabilizer_inf_centralizer_le hK ⟨hg.2, hg.1⟩, hg.1⟩

theorem card_centralizer_eq_of_sifting [Finite G] (x : G) (b : X) (S : Finset X) (K : Subgroup G)
    (hS : ∀ c ∈ centralizer ({x} : Set G), c • b ∈ S) (hKb : K ≤ MulAction.stabilizer G b)
    (hK : ∀ g : G, (∀ j < orderOf x, g • (x ^ j • b) = x ^ j • b) → g ∈ K)
    (P : X → Prop) [DecidablePred P]
    (hP : ∀ u ∈ S, P u ↔ ∃ c ∈ centralizer ({x} : Set G), c • b = u) :
    Nat.card (centralizer ({x} : Set G)) =
      (S.filter P).card * Nat.card ↥(K ⊓ centralizer ({x} : Set G)) := by
  rw [card_eq_ncard_orbit_mul (centralizer ({x} : Set G)) b]
  have hinf : centralizer ({x} : Set G) ⊓ MulAction.stabilizer G b =
      K ⊓ centralizer ({x} : Set G) := by
    refine le_antisymm (fun g hg => ⟨stabilizer_inf_centralizer_le hK ⟨hg.2, hg.1⟩, hg.1⟩) ?_
    exact fun g hg => ⟨hg.2, hKb hg.1⟩
  have horb : MulAction.orbit (centralizer ({x} : Set G)) b = ↑(S.filter P) := by
    ext u
    rw [MulAction.mem_orbit_iff, Finset.mem_coe, Finset.mem_filter]
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨hS c c.2, (hP _ (hS c c.2)).2 ⟨c, c.2, rfl⟩⟩
    · rintro ⟨huS, hPu⟩
      obtain ⟨c, hc, rfl⟩ := (hP u huS).1 hPu
      exact ⟨⟨c, hc⟩, rfl⟩
  rw [hinf, horb, Set.ncard_coe_finset]

theorem card_centralizer_eq_of_cover [Finite G] (x : G) (b : X) (S : Finset X) (K : Subgroup G)
    (hS : ∀ c ∈ centralizer ({x} : Set G), c • b ∈ S) (hKb : K ≤ MulAction.stabilizer G b)
    (hK : ∀ g : G, (∀ j < orderOf x, g • (x ^ j • b) = x ^ j • b) → g ∈ K)
    (hcov : ∀ u ∈ S, ∃ c ∈ centralizer ({x} : Set G), c • b = u) :
    Nat.card (centralizer ({x} : Set G)) = S.card * Nat.card ↥(K ⊓ centralizer ({x} : Set G)) := by
  classical
  have h := card_centralizer_eq_of_sifting x b S K hS hKb hK (fun _ => True)
    (fun u hu => ⟨fun _ => hcov u hu, fun _ => trivial⟩)
  rwa [Finset.filter_true_of_mem fun _ _ => trivial] at h

theorem le_card_centralizer_of_orbit [Finite G] (x : G) (b : X) (T : Finset X) (K : Subgroup G)
    (hKb : K ≤ MulAction.stabilizer G b)
    (hT : ∀ u ∈ T, ∃ c ∈ centralizer ({x} : Set G), c • b = u) :
    T.card * Nat.card ↥(K ⊓ centralizer ({x} : Set G)) ≤ Nat.card (centralizer ({x} : Set G)) := by
  rw [card_eq_ncard_orbit_mul (centralizer ({x} : Set G)) b]
  refine Nat.mul_le_mul ?_ (Subgroup.card_le_of_le fun g hg => ⟨hg.2, hKb hg.1⟩)
  rw [← Set.ncard_coe_finset T]
  refine Set.ncard_le_ncard ?_ (Set.finite_range _)
  intro u hu
  obtain ⟨c, hc, rfl⟩ := hT u hu
  exact ⟨⟨c, hc⟩, rfl⟩

theorem card_centralizer_eq_of_le [Finite G] {x : G} {p : ℕ} (hx : orderOf x = p)
    (h : Nat.card (centralizer ({x} : Set G)) ≤ p) :
    Nat.card (centralizer ({x} : Set G)) = p := by
  have hmem : x ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.2 rfl
  have hdvd := Subgroup.orderOf_dvd_natCard _ hmem
  rw [hx] at hdvd
  exact le_antisymm h (Nat.le_of_dvd Nat.card_pos hdvd)

theorem card_inf_centralizer_eq_card_filter (x : G) (K : Subgroup G) (L : Finset G)
    (hL : ∀ g, g ∈ K ↔ g ∈ L) [DecidablePred fun g : G => g * x = x * g] :
    Nat.card ↥(K ⊓ centralizer ({x} : Set G)) = (L.filter fun g => g * x = x * g).card := by
  rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun g => by
    rw [Subgroup.mem_inf, hL, Finset.mem_filter, mem_centralizer_singleton_iff])

end Centralizer

section Sylow

variable {G : Type*} [Group G]

theorem orderOf_inv_mul_mul (y g : G) : orderOf (g⁻¹ * y * g) = orderOf y :=
  (SemiconjBy.orderOf_eq g⁻¹ (by simp [SemiconjBy, mul_assoc])).symm

theorem card_centralizer_eq_of_isConj [Finite G] {x y : G} (h : IsConj x y) :
    Nat.card (centralizer ({y} : Set G)) = Nat.card (centralizer ({x} : Set G)) := by
  have hx := Subgroup.index_mul_card (centralizer ({x} : Set G))
  have hy := Subgroup.index_mul_card (centralizer ({y} : Set G))
  rw [Subgroup.index_centralizer_eq_ncard] at hx hy
  rw [← h.conjugatesOf_eq] at hy
  have hpos : 0 < (conjugatesOf x).ncard := by
    rw [← Subgroup.index_centralizer_eq_ncard]
    exact Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  exact Nat.eq_of_mul_eq_mul_left hpos (hy.trans hx.symm)

theorem commute_of_mem_zpowers {x y g : G} (hy : y ∈ zpowers x) (h : Commute g x) :
    Commute g y := by
  obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hy
  exact h.zpow_right m

theorem centralizer_singleton_eq_of_zpowers_eq {x y : G} (h : zpowers x = zpowers y) :
    centralizer ({x} : Set G) = centralizer ({y} : Set G) := by
  ext g
  simp only [mem_centralizer_singleton_iff]
  have hy : y ∈ zpowers x := h ▸ mem_zpowers y
  have hx : x ∈ zpowers y := h ▸ mem_zpowers x
  exact ⟨fun hg => (commute_of_mem_zpowers hy hg : Commute g y), fun hg =>
    (commute_of_mem_zpowers hx hg : Commute g x)⟩

theorem centralizer_singleton_eq_of_mem_zpowers [Finite G] {x y : G} (hy : y ∈ zpowers x)
    (h : orderOf y = orderOf x) : centralizer ({y} : Set G) = centralizer ({x} : Set G) := by
  refine centralizer_singleton_eq_of_zpowers_eq (Subgroup.eq_of_le_of_card_ge ?_ ?_)
  · exact zpowers_le.2 hy
  · rw [Nat.card_zpowers, Nat.card_zpowers, h]

theorem exists_sylow_eq_of_card_eq_prime {p : ℕ} [Fact p.Prime] (hp2 : ¬ p ^ 2 ∣ Nat.card G)
    (P : Subgroup G) (hP : Nat.card P = p) : ∃ S : Sylow p G, (S : Subgroup G) = P := by
  have hPp : IsPGroup p P := IsPGroup.of_card (n := 1) (by rw [hP, pow_one])
  have hidx : ¬ p ∣ P.index := by
    intro h
    apply hp2
    have := Subgroup.card_mul_index P
    rw [hP] at this
    rw [← this, pow_two]
    exact mul_dvd_mul_left p h
  exact ⟨hPp.toSylow hidx, rfl⟩

theorem exists_conj_mem_sylow [Finite G] {p : ℕ} [Fact p.Prime] (S : Sylow p G) {y : G}
    (hy : IsPGroup p (zpowers y)) : ∃ g : G, g⁻¹ * y * g ∈ (S : Subgroup G) := by
  obtain ⟨Q, hQ⟩ := hy.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G S Q
  have hyQ : y ∈ ((c • S : Sylow p G) : Subgroup G) := by
    rw [hc]
    exact hQ (mem_zpowers y)
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hyQ
  obtain ⟨s, hs, hsy⟩ := hyQ
  refine ⟨c, ?_⟩
  have : c⁻¹ * y * c = s := by
    rw [← hsy]
    simp [MulAut.smul_def, mul_assoc]
  rwa [this]

theorem card_centralizer_eq_of_sylow_prime [Finite G] {p : ℕ} [Fact p.Prime]
    (hp2 : ¬ p ^ 2 ∣ Nat.card G) {x y : G} (hx : orderOf x = p) (hy : orderOf y = p) :
    Nat.card (centralizer ({y} : Set G)) = Nat.card (centralizer ({x} : Set G)) := by
  obtain ⟨S, hS⟩ := exists_sylow_eq_of_card_eq_prime hp2 (zpowers x) (by rw [Nat.card_zpowers, hx])
  have hyp : IsPGroup p (zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
  obtain ⟨g, hg⟩ := exists_conj_mem_sylow S hyp
  rw [hS] at hg
  have hconj : IsConj y (g⁻¹ * y * g) := isConj_iff.2 ⟨g⁻¹, by simp⟩
  have hord : orderOf (g⁻¹ * y * g) = orderOf x := by rw [orderOf_inv_mul_mul, hx, hy]
  rw [← card_centralizer_eq_of_isConj hconj, centralizer_singleton_eq_of_mem_zpowers hg hord]

theorem card_centralizer_dvd_of_sylow_prime [Finite G] {p D : ℕ} [Fact p.Prime]
    (hp2 : ¬ p ^ 2 ∣ Nat.card G) {x : G} (hx : orderOf x = p)
    (hD : Nat.card (centralizer ({x} : Set G)) ∣ D) :
    ∀ y : G, orderOf y = p → Nat.card (centralizer ({y} : Set G)) ∣ D := fun y hy => by
  rw [card_centralizer_eq_of_sylow_prime hp2 hx hy]
  exact hD

end Sylow

section Elementary

variable {G : Type*} [Group G]

@[expose] def commProd (x₀ y₀ : G) (h : Commute x₀ y₀) : Subgroup G where
  carrier := {g | ∃ a b : ℤ, g = x₀ ^ a * y₀ ^ b}
  mul_mem' := by
    have hc : ∀ m n : ℤ, y₀ ^ m * x₀ ^ n = x₀ ^ n * y₀ ^ m := fun m n =>
      (h.symm.zpow_zpow m n).eq
    rintro _ _ ⟨a, b, rfl⟩ ⟨a', b', rfl⟩
    refine ⟨a + a', b + b', ?_⟩
    calc x₀ ^ a * y₀ ^ b * (x₀ ^ a' * y₀ ^ b') = x₀ ^ a * (y₀ ^ b * x₀ ^ a') * y₀ ^ b' := by
          simp only [mul_assoc]
      _ = x₀ ^ a * (x₀ ^ a' * y₀ ^ b) * y₀ ^ b' := by rw [hc]
      _ = x₀ ^ (a + a') * y₀ ^ (b + b') := by rw [zpow_add, zpow_add]; simp only [mul_assoc]
  one_mem' := ⟨0, 0, by simp⟩
  inv_mem' := by
    have hc : ∀ m n : ℤ, y₀ ^ m * x₀ ^ n = x₀ ^ n * y₀ ^ m := fun m n =>
      (h.symm.zpow_zpow m n).eq
    rintro _ ⟨a, b, rfl⟩
    refine ⟨-a, -b, ?_⟩
    rw [mul_inv_rev, ← zpow_neg, ← zpow_neg, hc]

theorem mem_commProd {x₀ y₀ : G} {h : Commute x₀ y₀} {g : G} :
    g ∈ commProd x₀ y₀ h ↔ ∃ a b : ℤ, g = x₀ ^ a * y₀ ^ b := Iff.rfl

theorem isPGroup_commProd {p : ℕ} {x₀ y₀ : G} (h : Commute x₀ y₀) (hx : x₀ ^ p = 1)
    (hy : y₀ ^ p = 1) : IsPGroup p (commProd x₀ y₀ h) := by
  intro g
  obtain ⟨a, b, hg⟩ := g.2
  refine ⟨1, Subtype.ext ?_⟩
  have hxa : (x₀ ^ a) ^ p = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
  have hyb : (y₀ ^ b) ^ p = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy, one_zpow]
  simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
  rw [hg, (h.zpow_zpow a b).mul_pow, hxa, hyb, mul_one]

theorem not_mem_zpowers_of_forall_ne [Finite G] {x y : G} {n : ℕ} (hx : orderOf x = n)
    (h : ∀ k < n, x ^ k ≠ y) : y ∉ zpowers x := by
  intro hy
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
  have hn : 0 < n := hx ▸ orderOf_pos_iff.2 (isOfFinOrder_of_finite x)
  obtain ⟨m, hm⟩ : ∃ m : ℕ, k % (n : ℤ) = m :=
    ⟨(k % (n : ℤ)).toNat, (Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))).symm⟩
  have hmn : m < n := by
    have := Int.emod_lt_of_pos k (by omega : (0 : ℤ) < n)
    omega
  apply h m hmn
  rw [← zpow_natCast, ← hm, ← hx, zpow_mod_orderOf]

theorem exists_sylow_eq_commProd [Finite G] {p : ℕ} [Fact p.Prime] (hp3 : ¬ p ^ 3 ∣ Nat.card G)
    {x₀ y₀ : G} (hx₀ : orderOf x₀ = p) (hy₀ : orderOf y₀ = p) (h : Commute x₀ y₀)
    (hind : y₀ ∉ zpowers x₀) : ∃ S : Sylow p G, (S : Subgroup G) = commProd x₀ y₀ h := by
  have hPp := isPGroup_commProd h (hx₀ ▸ pow_orderOf_eq_one x₀) (hy₀ ▸ pow_orderOf_eq_one y₀)
  obtain ⟨k, hk⟩ := hPp.exists_card_eq
  have hle : zpowers x₀ ≤ commProd x₀ y₀ h := zpowers_le.2 ⟨1, 0, by simp⟩
  have hy₀P : y₀ ∈ commProd x₀ y₀ h := ⟨0, 1, by simp⟩
  have hlt : p < Nat.card (commProd x₀ y₀ h) := by
    by_contra hcon
    have := Subgroup.eq_of_le_of_card_ge hle
      (by rw [Nat.card_zpowers, hx₀]; exact Nat.le_of_not_lt hcon)
    exact hind (this ▸ hy₀P)
  have hk2 : 2 ≤ k := by
    by_contra h2
    have hpk : p ^ k ≤ p ^ 1 :=
      Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega)
    rw [pow_one] at hpk
    omega
  have hidx : ¬ p ∣ (commProd x₀ y₀ h).index := by
    intro hd
    apply hp3
    have := Subgroup.card_mul_index (commProd x₀ y₀ h)
    rw [hk] at this
    rw [← this]
    calc p ^ 3 = p ^ 2 * p := by ring
      _ ∣ p ^ k * (commProd x₀ y₀ h).index := mul_dvd_mul (pow_dvd_pow p hk2) hd
  exact ⟨hPp.toSylow hidx, rfl⟩

theorem exists_card_centralizer_eq_of_sylow_elementary [Finite G] {p : ℕ} [Fact p.Prime]
    (hp3 : ¬ p ^ 3 ∣ Nat.card G) {x₀ y₀ : G} (hx₀ : orderOf x₀ = p) (hy₀ : orderOf y₀ = p)
    (h : Commute x₀ y₀) (hind : y₀ ∉ zpowers x₀) (reps : Set G)
    (h0 : ∃ r ∈ reps, IsConj r x₀) (hi : ∀ i < p, ∃ r ∈ reps, IsConj r (x₀ ^ i * y₀))
    {y : G} (hy : orderOf y = p) :
    ∃ r ∈ reps, Nat.card (centralizer ({y} : Set G)) = Nat.card (centralizer ({r} : Set G)) := by
  obtain ⟨S, hS⟩ := exists_sylow_eq_commProd hp3 hx₀ hy₀ h hind
  have hyp : IsPGroup p (zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
  obtain ⟨g, hg⟩ := exists_conj_mem_sylow S hyp
  rw [hS] at hg
  obtain ⟨a, b, hab⟩ := hg
  have hconj : IsConj y (g⁻¹ * y * g) := isConj_iff.2 ⟨g⁻¹, by simp⟩
  have hcy := card_centralizer_eq_of_isConj hconj
  have hord : orderOf (g⁻¹ * y * g) = p := by rw [orderOf_inv_mul_mul, hy]
  have hpp : (0 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  by_cases hb : (p : ℤ) ∣ b
  · have hyb : y₀ ^ b = 1 := orderOf_dvd_iff_zpow_eq_one.1 (by rw [hy₀]; exact hb)
    have hmem : g⁻¹ * y * g ∈ zpowers x₀ := ⟨a, by rw [hab, hyb, mul_one]⟩
    obtain ⟨r, hr, hrc⟩ := h0
    refine ⟨r, hr, ?_⟩
    rw [← hcy, centralizer_singleton_eq_of_mem_zpowers hmem (by rw [hord, hx₀]),
      card_centralizer_eq_of_isConj hrc]
  · have hpint : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 (Fact.out : p.Prime)
    have hcop : IsCoprime (p : ℤ) b := (Irreducible.coprime_iff_not_dvd hpint.irreducible).2 hb
    obtain ⟨u, v, huv⟩ := hcop
    have hvb : v * b = 1 + (-u) * p := by linarith
    have hpow : ∀ w : G, w ^ p = 1 → w ^ (v * b) = w := fun w hw => by
      rw [hvb, zpow_add, zpow_one, zpow_mul', zpow_natCast, hw, one_zpow, mul_one]
    set y' := g⁻¹ * y * g with hy'
    have hy'p : y' ^ p = 1 := hord ▸ pow_orderOf_eq_one y'
    obtain ⟨i, hi'⟩ : ∃ i : ℕ, (a * v) % (p : ℤ) = i :=
      ⟨((a * v) % (p : ℤ)).toNat, (Int.toNat_of_nonneg (Int.emod_nonneg _ hpp.ne')).symm⟩
    have hip : i < p := by
      have := Int.emod_lt_of_pos (a * v) hpp
      omega
    have hz : y' ^ v = x₀ ^ i * y₀ := by
      have h1 : x₀ ^ (a * v) = x₀ ^ i := by
        rw [← zpow_mod_orderOf, hx₀, hi', zpow_natCast]
      have h2 : y₀ ^ (b * v) = y₀ := by
        rw [mul_comm, hpow y₀ (hy₀ ▸ pow_orderOf_eq_one y₀)]
      rw [hab, (h.zpow_zpow a b).mul_zpow, ← zpow_mul, ← zpow_mul, h1, h2]
    have hzy : (y' ^ v) ^ b = y' := by rw [← zpow_mul, hpow y' hy'p]
    have hzp : zpowers y' = zpowers (x₀ ^ i * y₀) :=
      le_antisymm (zpowers_le.2 (mem_zpowers_iff.2 ⟨b, by rw [← hz]; exact hzy⟩))
        (zpowers_le.2 (mem_zpowers_iff.2 ⟨v, hz⟩))
    obtain ⟨r, hr, hrc⟩ := hi i hip
    refine ⟨r, hr, ?_⟩
    rw [← hcy, centralizer_singleton_eq_of_zpowers_eq hzp, card_centralizer_eq_of_isConj hrc]

theorem card_centralizer_dvd_of_sylow_elementary [Finite G] {p D : ℕ} [Fact p.Prime]
    (hp3 : ¬ p ^ 3 ∣ Nat.card G) {x₀ y₀ : G} (hx₀ : orderOf x₀ = p) (hy₀ : orderOf y₀ = p)
    (h : Commute x₀ y₀) (hind : y₀ ∉ zpowers x₀) (reps : Set G)
    (h0 : ∃ r ∈ reps, IsConj r x₀) (hi : ∀ i < p, ∃ r ∈ reps, IsConj r (x₀ ^ i * y₀))
    (hD : ∀ r ∈ reps, Nat.card (centralizer ({r} : Set G)) ∣ D) :
    ∀ y : G, orderOf y = p → Nat.card (centralizer ({y} : Set G)) ∣ D := fun y hy => by
  obtain ⟨r, hr, hyr⟩ :=
    exists_card_centralizer_eq_of_sylow_elementary hp3 hx₀ hy₀ h hind reps h0 hi hy
  rw [hyr]
  exact hD r hr

end Elementary

end CFSG.Monster.Existence.StdOdd.Cert
