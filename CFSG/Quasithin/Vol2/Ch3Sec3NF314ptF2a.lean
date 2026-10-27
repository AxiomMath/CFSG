module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.Background.A1bPGroups

public section

namespace CFSG.Quasithin.H13.NF314pt

open CFSG.Open
open scoped commutatorElement

theorem f2_normal_subgroupOf {G : Type} [Group G] {H N : Subgroup G}
    (hN : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) : (N.subgroupOf H).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have := hN (g : G) g.2 (n : G) hn
  simpa using this

theorem f2_comm_iff {G : Type} [Group G] {H N : Subgroup G} [(N.subgroupOf H).Normal]
    (hN : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) (u v : ↥H) :
    Commute (QuotientGroup.mk' (N.subgroupOf H) u) (QuotientGroup.mk' (N.subgroupOf H) v) ↔
      ⁅(u : G), (v : G)⁆ ∈ N := by
  have hab : (u : G) * (v : G) ∈ H := H.mul_mem u.2 v.2
  rw [Commute, SemiconjBy, ← map_mul, ← map_mul, QuotientGroup.mk'_apply,
    QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [commutatorElement_def]
  constructor
  · intro ht
    have h1 := hN _ hab _ (N.inv_mem ht)
    convert h1 using 1
    group
  · intro hc
    have h1 := hN _ (H.inv_mem hab) _ hc
    have h2 : ((↑u * ↑v : G)⁻¹ * (↑v * ↑u)) ⁻¹ ∈ N := by
      convert h1 using 1
      group
    simpa using N.inv_mem h2

theorem f2_mk_eq_one {G : Type} [Group G] {H N : Subgroup G} [(N.subgroupOf H).Normal]
    (u : ↥H) : QuotientGroup.mk' (N.subgroupOf H) u = (1 : ↥H ⧸ N.subgroupOf H) ↔ (u : G) ∈ N := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem f2_zpow_dvd {G : Type} [Group G] {N : Subgroup G} {x : G} {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (hox : orderOf x = q) (hN2 : IsPGroup 2 N) {i : ℤ} (hi : x ^ i ∈ N) :
    (q : ℤ) ∣ i := by
  obtain ⟨k, hk⟩ := hN2 ⟨x ^ i, hi⟩
  have hk' : (x ^ i) ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have h1 : x ^ (i * ((2 ^ k : ℕ) : ℤ)) = 1 := by
    rw [zpow_mul, zpow_natCast]
    exact hk'
  have h2 : ((orderOf x : ℕ) : ℤ) ∣ i * ((2 ^ k : ℕ) : ℤ) := orderOf_dvd_iff_zpow_eq_one.2 h1
  rw [hox] at h2
  have hpZ : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  rcases hpZ.dvd_or_dvd h2 with h | h
  · exact h
  · exfalso
    have h3 : (q : ℤ) ∣ ((2 ^ k : ℕ) : ℤ) := h
    have h4 : q ∣ 2 ^ k := Int.natCast_dvd_natCast.mp h3
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h4))

theorem f2_not_dvd_card {G : Type} [Group G] [Finite G] {H N : Subgroup G} (hNH : N ≤ H)
    (hN2 : IsPGroup 2 N) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    ¬ q ∣ Nat.card (N.subgroupOf H) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hN2
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv, hn]
  intro h
  exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h))

theorem f2_card_mult_zmod (q : ℕ) [NeZero q] : Nat.card (Multiplicative (ZMod q)) = q := by
  rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

theorem f2_mult_zmod_pow (q : ℕ) [NeZero q] (m : Multiplicative (ZMod q)) : m ^ q = 1 := by
  rw [← toAdd_eq_zero, toAdd_pow, nsmul_eq_mul, ZMod.natCast_self, zero_mul]

theorem f2_exists_zmod_hom {Q : Type} [Group Q] (q : ℕ) [NeZero q] (X : Q) (hX : X ^ q = 1) :
    ∃ f : Multiplicative (ZMod q) →* Q,
      ∀ i : Multiplicative (ZMod q), f i = X ^ (Multiplicative.toAdd i).val := by
  refine ⟨MonoidHom.mk' (fun i => X ^ (Multiplicative.toAdd i).val) ?_, fun i => rfl⟩
  intro a b
  show X ^ (Multiplicative.toAdd (a * b)).val =
    X ^ (Multiplicative.toAdd a).val * X ^ (Multiplicative.toAdd b).val
  rw [toAdd_mul, ZMod.val_add, ← pow_eq_pow_mod _ hX, pow_add]

theorem f2_alg {Q : Type} [Group Q] {q : ℕ} (hq : q.Prime) {X Y W : Q}
    (hX : X ^ q = 1) (hY : Y ^ q = 1) (hW : W ^ q = 1) (hW1 : W ≠ 1)
    (hXY : Commute X Y) (hXW : Commute X W) (hYW : Commute Y W) (SA SB : Set Q)
    (hSA : ∀ g ∈ SA, Commute W g ∧ Commute Y g)
    (hSB : ∀ g ∈ SB, Commute W g ∧ Commute X g)
    (hA' : ∀ n : ℕ, (∀ g ∈ SA, Commute (X ^ n) g) → q ∣ n)
    (hB' : ∀ n : ℕ, (∀ g ∈ SB, Commute (Y ^ n) g) → q ∣ n) :
    ∀ a b c : ℕ, X ^ a * Y ^ b * W ^ c = 1 → q ∣ a ∧ q ∣ b ∧ q ∣ c := by
  intro a b c habc
  by_cases hc : q ∣ c
  · obtain ⟨m, rfl⟩ := hc
    have hWc : W ^ (q * m) = 1 := by rw [pow_mul, hW, one_pow]
    rw [hWc, mul_one] at habc
    have hXa : X ^ a = (Y ^ b)⁻¹ := eq_inv_of_mul_eq_one_left habc
    have hYb : Y ^ b = (X ^ a)⁻¹ := eq_inv_of_mul_eq_one_right habc
    have hdA : q ∣ a := hA' a fun g hg => by
      rw [hXa]
      exact ((hSA g hg).2.pow_left b).inv_left
    have hdB : q ∣ b := hB' b fun g hg => by
      rw [hYb]
      exact ((hSB g hg).2.pow_left a).inv_left
    exact ⟨hdA, hdB, dvd_mul_right q m⟩
  · exfalso
    have hcop : Nat.Coprime c q := ((Nat.Prime.coprime_iff_not_dvd hq).2 hc).symm
    obtain ⟨c', -, hcc⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hq.one_lt
    have hWcc : W ^ (c * c') = W := by
      rw [pow_eq_pow_mod (c * c') hW, hcc, pow_one]
    have hcXY : Commute (X ^ a) (Y ^ b) := hXY.pow_pow a b
    have hcXYW : Commute (X ^ a * Y ^ b) (W ^ c) :=
      (hXW.pow_pow a c).mul_left (hYW.pow_pow b c)
    have h2 : (X ^ a * Y ^ b * W ^ c) ^ c' = 1 := by rw [habc, one_pow]
    have h1 : X ^ (a * c') * Y ^ (b * c') * W = 1 := by
      rw [hcXYW.mul_pow, hcXY.mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, hWcc] at h2
      exact h2
    set A₀ := a * c' with hA₀
    set B₀ := b * c' with hB₀
    have hXA : X ^ A₀ = (Y ^ B₀ * W)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← mul_assoc]
      exact h1
    have hdA : q ∣ A₀ := hA' A₀ fun g hg => by
      rw [hXA]
      exact (((hSA g hg).2.pow_left B₀).mul_left (hSA g hg).1).inv_left
    have hXA1 : X ^ A₀ = 1 := by
      obtain ⟨m, hm⟩ := hdA
      rw [hm, pow_mul, hX, one_pow]
    have hYW1 : Y ^ B₀ * W = 1 := by
      rw [hXA1, one_mul] at h1
      exact h1
    have hYB : Y ^ B₀ = W⁻¹ := eq_inv_of_mul_eq_one_left hYW1
    have hdB : q ∣ B₀ := hB' B₀ fun g hg => by
      rw [hYB]
      exact (hSB g hg).1.inv_left
    have hYB1 : Y ^ B₀ = 1 := by
      obtain ⟨m, hm⟩ := hdB
      rw [hm, pow_mul, hY, one_pow]
    apply hW1
    rw [hYB1, one_mul] at hYW1
    exact hYW1

theorem f2_indep {G : Type} [Group G] {H N A B C : Subgroup G} (hNH : N ≤ H)
    (hN : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) (hN2 : IsPGroup 2 N)
    (hAH : A ≤ H) (hBH : B ≤ H) (hCH : C ≤ H)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hAB : ⁅A, B⁆ ≤ N) (hAC : ⁅A, C⁆ ≤ N) (hBC : ⁅B, C⁆ ≤ N)
    (hA : ∀ a ∈ A, (∀ x ∈ A, ⁅a, x⁆ ∈ N) → a ∈ N)
    (hB : ∀ b ∈ B, (∀ y ∈ B, ⁅b, y⁆ ∈ N) → b ∈ N)
    {x y w : G} (hx : x ∈ A) (hy : y ∈ B) (hw : w ∈ C)
    (hox : orderOf x = q) (hoy : orderOf y = q) (how : orderOf w = q) :
    ∀ a b c : ℕ, x ^ a * y ^ b * w ^ c ∈ N → q ∣ a ∧ q ∣ b ∧ q ∣ c := by
  haveI hfact : Fact q.Prime := ⟨hq⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI hNn : (N.subgroupOf H).Normal := f2_normal_subgroupOf hN
  intro a b c habc
  obtain ⟨x₁, hx₁⟩ : ∃ x₁ : ↥H, (x₁ : G) = x := ⟨⟨x, hAH hx⟩, rfl⟩
  obtain ⟨y₁, hy₁⟩ : ∃ y₁ : ↥H, (y₁ : G) = y := ⟨⟨y, hBH hy⟩, rfl⟩
  obtain ⟨w₁, hw₁⟩ : ∃ w₁ : ↥H, (w₁ : G) = w := ⟨⟨w, hCH hw⟩, rfl⟩
  have hx1 : x₁ ^ q = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hx₁, Subgroup.coe_one, ← hox, pow_orderOf_eq_one]
  have hy1 : y₁ ^ q = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hy₁, Subgroup.coe_one, ← hoy, pow_orderOf_eq_one]
  have hw1 : w₁ ^ q = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hw₁, Subgroup.coe_one, ← how, pow_orderOf_eq_one]
  set mkQ := QuotientGroup.mk' (N.subgroupOf H) with hmkQ
  have hXq : mkQ x₁ ^ q = 1 := by rw [← map_pow, hx1, map_one]
  have hYq : mkQ y₁ ^ q = 1 := by rw [← map_pow, hy1, map_one]
  have hWq : mkQ w₁ ^ q = 1 := by rw [← map_pow, hw1, map_one]
  have hcXY : Commute (mkQ x₁) (mkQ y₁) :=
    (f2_comm_iff hN x₁ y₁).2 (by rw [hx₁, hy₁]; exact hAB (Subgroup.commutator_mem_commutator hx hy))
  have hcXW : Commute (mkQ x₁) (mkQ w₁) :=
    (f2_comm_iff hN x₁ w₁).2 (by rw [hx₁, hw₁]; exact hAC (Subgroup.commutator_mem_commutator hx hw))
  have hcYW : Commute (mkQ y₁) (mkQ w₁) :=
    (f2_comm_iff hN y₁ w₁).2 (by rw [hy₁, hw₁]; exact hBC (Subgroup.commutator_mem_commutator hy hw))
  have hW1 : mkQ w₁ ≠ 1 := by
    intro h
    have hwN : w ∈ N := by
      rw [← hw₁]
      exact (f2_mk_eq_one w₁).1 h
    have hdiv := f2_zpow_dvd hq hq2 how hN2 (i := 1) (by rw [zpow_one]; exact hwN)
    have h5 := Int.le_of_dvd one_pos hdiv
    have h6 := hq.two_le
    omega
  set SA : Set (↥H ⧸ N.subgroupOf H) := {g | ∃ k : ↥H, (k : G) ∈ A ∧ g = mkQ k} with hSAdef
  set SB : Set (↥H ⧸ N.subgroupOf H) := {g | ∃ k : ↥H, (k : G) ∈ B ∧ g = mkQ k} with hSBdef
  have hSA : ∀ g ∈ SA, Commute (mkQ w₁) g ∧ Commute (mkQ y₁) g := by
    rintro g ⟨k, hk, rfl⟩
    refine ⟨?_, ?_⟩
    · exact ((f2_comm_iff hN k w₁).2
        (hAC (Subgroup.commutator_mem_commutator hk (by rw [hw₁]; exact hw)))).symm
    · exact ((f2_comm_iff hN k y₁).2
        (hAB (Subgroup.commutator_mem_commutator hk (by rw [hy₁]; exact hy)))).symm
  have hSB : ∀ g ∈ SB, Commute (mkQ w₁) g ∧ Commute (mkQ x₁) g := by
    rintro g ⟨k, hk, rfl⟩
    refine ⟨?_, ?_⟩
    · exact ((f2_comm_iff hN k w₁).2
        (hBC (Subgroup.commutator_mem_commutator hk (by rw [hw₁]; exact hw)))).symm
    · exact (f2_comm_iff hN x₁ k).2
        (hAB (Subgroup.commutator_mem_commutator (by rw [hx₁]; exact hx) hk))
  have hA' : ∀ n : ℕ, (∀ g ∈ SA, Commute (mkQ x₁ ^ n) g) → q ∣ n := by
    intro n hn
    have hxn : x ^ n ∈ N := by
      apply hA (x ^ n) (A.pow_mem hx n)
      intro k hk
      have hkH : k ∈ H := hAH hk
      have hc : Commute (mkQ x₁ ^ n) (mkQ ⟨k, hkH⟩) := hn _ ⟨⟨k, hkH⟩, hk, rfl⟩
      rw [← map_pow] at hc
      have := (f2_comm_iff hN (x₁ ^ n) ⟨k, hkH⟩).1 hc
      simpa [hx₁] using this
    have hdvd : (q : ℤ) ∣ (n : ℤ) :=
      f2_zpow_dvd hq hq2 hox hN2 (i := (n : ℤ)) (by rw [zpow_natCast]; exact hxn)
    exact Int.natCast_dvd_natCast.mp hdvd
  have hB' : ∀ n : ℕ, (∀ g ∈ SB, Commute (mkQ y₁ ^ n) g) → q ∣ n := by
    intro n hn
    have hyn : y ^ n ∈ N := by
      apply hB (y ^ n) (B.pow_mem hy n)
      intro k hk
      have hkH : k ∈ H := hBH hk
      have hc : Commute (mkQ y₁ ^ n) (mkQ ⟨k, hkH⟩) := hn _ ⟨⟨k, hkH⟩, hk, rfl⟩
      rw [← map_pow] at hc
      have := (f2_comm_iff hN (y₁ ^ n) ⟨k, hkH⟩).1 hc
      simpa [hy₁] using this
    have hdvd : (q : ℤ) ∣ (n : ℤ) :=
      f2_zpow_dvd hq hq2 hoy hN2 (i := (n : ℤ)) (by rw [zpow_natCast]; exact hyn)
    exact Int.natCast_dvd_natCast.mp hdvd
  have hfin := f2_alg hq hXq hYq hWq hW1 hcXY hcXW hcYW SA SB hSA hSB hA' hB'
  refine hfin a b c ?_
  have hmem : mkQ (x₁ ^ a * y₁ ^ b * w₁ ^ c) = 1 := by
    refine (f2_mk_eq_one _).2 ?_
    simpa [hx₁, hy₁, hw₁] using habc
  simpa only [map_mul, map_pow] using hmem

theorem f2_pRank_ge_three {G : Type} [Group G] [Finite G] {H N : Subgroup G} (hNH : N ≤ H)
    (hN : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) (hN2 : IsPGroup 2 N)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {x y w : G} (hx : x ∈ H) (hy : y ∈ H) (hw : w ∈ H)
    (hox : orderOf x = q) (hoy : orderOf y = q) (how : orderOf w = q)
    (hxy : ⁅x, y⁆ ∈ N) (hxw : ⁅x, w⁆ ∈ N) (hyw : ⁅y, w⁆ ∈ N)
    (hind : ∀ a b c : ℕ, x ^ a * y ^ b * w ^ c ∈ N → q ∣ a ∧ q ∣ b ∧ q ∣ c) :
    3 ≤ CFSG.Open.pRank q H := by
  haveI hfact : Fact q.Prime := ⟨hq⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI hNn : (N.subgroupOf H).Normal := f2_normal_subgroupOf hN
  obtain ⟨x₁, hx₁⟩ : ∃ x₁ : ↥H, (x₁ : G) = x := ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨y₁, hy₁⟩ : ∃ y₁ : ↥H, (y₁ : G) = y := ⟨⟨y, hy⟩, rfl⟩
  obtain ⟨w₁, hw₁⟩ : ∃ w₁ : ↥H, (w₁ : G) = w := ⟨⟨w, hw⟩, rfl⟩
  have hx1 : x₁ ^ q = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hx₁, Subgroup.coe_one, ← hox, pow_orderOf_eq_one]
  have hy1 : y₁ ^ q = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hy₁, Subgroup.coe_one, ← hoy, pow_orderOf_eq_one]
  have hw1 : w₁ ^ q = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hw₁, Subgroup.coe_one, ← how, pow_orderOf_eq_one]
  set mkQ := QuotientGroup.mk' (N.subgroupOf H) with hmkQ
  have hXq : mkQ x₁ ^ q = 1 := by rw [← map_pow, hx1, map_one]
  have hYq : mkQ y₁ ^ q = 1 := by rw [← map_pow, hy1, map_one]
  have hWq : mkQ w₁ ^ q = 1 := by rw [← map_pow, hw1, map_one]
  have hcXY : Commute (mkQ x₁) (mkQ y₁) :=
    (f2_comm_iff hN x₁ y₁).2 (by rw [hx₁, hy₁]; exact hxy)
  have hcXW : Commute (mkQ x₁) (mkQ w₁) :=
    (f2_comm_iff hN x₁ w₁).2 (by rw [hx₁, hw₁]; exact hxw)
  have hcYW : Commute (mkQ y₁) (mkQ w₁) :=
    (f2_comm_iff hN y₁ w₁).2 (by rw [hy₁, hw₁]; exact hyw)
  have hind' : ∀ a b c : ℕ, mkQ x₁ ^ a * mkQ y₁ ^ b * mkQ w₁ ^ c = 1 →
      q ∣ a ∧ q ∣ b ∧ q ∣ c := by
    intro a b c h
    have hmem : mkQ (x₁ ^ a * y₁ ^ b * w₁ ^ c) = 1 := by
      rw [map_mul, map_mul, map_pow, map_pow, map_pow]
      exact h
    have hm := (f2_mk_eq_one _).1 hmem
    apply hind a b c
    simpa [hx₁, hy₁, hw₁] using hm
  obtain ⟨f1, hf1⟩ := f2_exists_zmod_hom q (mkQ x₁) hXq
  obtain ⟨f2, hf2⟩ := f2_exists_zmod_hom q (mkQ y₁) hYq
  obtain ⟨f3, hf3⟩ := f2_exists_zmod_hom q (mkQ w₁) hWq
  have h12 : ∀ m n, Commute (f1 m) (f2 n) := by
    intro m n
    rw [hf1, hf2]
    exact hcXY.pow_pow _ _
  have h123 : ∀ m n, Commute ((f1.noncommCoprod f2 h12) m) (f3 n) := by
    intro m n
    rw [MonoidHom.noncommCoprod_apply]
    refine Commute.mul_left ?_ ?_
    · rw [hf1, hf3]
      exact hcXW.pow_pow _ _
    · rw [hf2, hf3]
      exact hcYW.pow_pow _ _
  have hcard : Nat.card ((Multiplicative (ZMod q) × Multiplicative (ZMod q)) ×
      Multiplicative (ZMod q)) = q ^ 3 := by
    rw [Nat.card_prod, Nat.card_prod, f2_card_mult_zmod q]
    ring
  have hpowA : ∀ a : (Multiplicative (ZMod q) × Multiplicative (ZMod q)) ×
      Multiplicative (ZMod q), a ^ q = 1 := by
    rintro ⟨⟨a1, a2⟩, a3⟩
    simp [Prod.ext_iff, f2_mult_zmod_pow q]
  have hinj : Function.Injective ((f1.noncommCoprod f2 h12).noncommCoprod f3 h123) := by
    rw [injective_iff_map_eq_one]
    intro a h
    obtain ⟨⟨a1, a2⟩, a3⟩ := a
    rw [MonoidHom.noncommCoprod_apply, MonoidHom.noncommCoprod_apply, hf1, hf2, hf3] at h
    obtain ⟨d1, d2, d3⟩ := hind' _ _ _ h
    have e1 : a1.toAdd.val = 0 := Nat.eq_zero_of_dvd_of_lt d1 (ZMod.val_lt _)
    have e2 : a2.toAdd.val = 0 := Nat.eq_zero_of_dvd_of_lt d2 (ZMod.val_lt _)
    have e3 : a3.toAdd.val = 0 := Nat.eq_zero_of_dvd_of_lt d3 (ZMod.val_lt _)
    have a1' : a1 = 1 := toAdd_eq_zero.mp ((ZMod.val_eq_zero _).mp e1)
    have a2' : a2 = 1 := toAdd_eq_zero.mp ((ZMod.val_eq_zero _).mp e2)
    have a3' : a3 = 1 := toAdd_eq_zero.mp ((ZMod.val_eq_zero _).mp e3)
    simp [a1', a2', a3']
  have key := CFSG.SectionRank.le_pRank_of_injective (G := ↥H ⧸ N.subgroupOf H) hq.one_lt
    (fun a b => mul_comm a b) hpowA hcard _ hinj (H := ⊤) le_top
  rw [CFSG.SectionRank.pRank_quotient_eq (N.subgroupOf H) (f2_not_dvd_card hNH hN2 hq hq2),
    CFSG.Quasithin.pRank_top_subtype H] at key
  exact key

end CFSG.Quasithin.H13.NF314pt
