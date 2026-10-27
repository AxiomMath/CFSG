module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Sporadic.J4.QT2A

open Subgroup

theorem closure_subset_of_closed {G : Type*} [Group G] [Finite G] (gens : Set G) (s : Set G)
    (h1 : (1 : G) ∈ s) (hs : ∀ x ∈ s, ∀ g ∈ gens, x * g ∈ s) :
    (Subgroup.closure gens : Set G) ⊆ s := by
  intro x hx
  have hx' : x ∈ Submonoid.closure gens := by
    rw [← Subgroup.closure_toSubmonoid_of_finite]
    exact hx
  exact Submonoid.closure_induction_right (motive := fun x _ => x ∈ s) h1
    (fun x _ y hy ih => hs x ih y hy) hx'

theorem isPGroup_two_of_no_odd_prime {M : Type*} [Group M] [Finite M]
    (h : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ∣ Nat.card M) : IsPGroup 2 M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [IsPGroup.iff_card]
  exact ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' (fun {d} hd hdvd => by
    by_contra hne
    exact h d hd hne hdvd)⟩

open scoped Pointwise in
theorem not_dvd_card_of_sylow {G : Type*} [Group G] [Finite G] (r : ℕ) [Fact r.Prime]
    (Y : Sylow r G) (M : Subgroup G) (hM : ∀ g : G, ∀ m ∈ M, g * m * g⁻¹ ∈ M)
    (h : ∀ y ∈ (Y : Subgroup G), y ≠ 1 → y ∉ M) : ¬ r ∣ Nat.card M := by
  intro hr
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := M) r hr
  have hxo : orderOf (x : G) = r := by rw [Subgroup.orderOf_coe]; exact hx
  have hp : IsPGroup r (Subgroup.zpowers (x : G)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hxo, pow_one]
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q Y
  have hxQ : (x : G) ∈ (Q : Subgroup G) := hQ (Subgroup.mem_zpowers _)
  have hxY : g * (x : G) * g⁻¹ ∈ (Y : Subgroup G) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hxQ
  have hne : g * (x : G) * g⁻¹ ≠ 1 := by
    intro h1
    have : (x : G) = 1 := by
      have := congrArg (fun t => g⁻¹ * t * g) h1
      simpa [mul_assoc] using this
    have hord : orderOf (x : G) = 1 := by rw [this]; exact orderOf_one
    rw [hxo] at hord
    exact (Fact.out : r.Prime).one_lt.ne' hord
  exact h _ hxY hne (hM g x x.2)

theorem not_dvd_card_of_sylow_sub {J : Type*} [Group J] [Finite J] (r : ℕ) [Fact r.Prime]
    (C Y M : Subgroup J) (hYC : Y ≤ C) (hMC : M ≤ C) (hY : IsPGroup r Y)
    (hidx : ¬ r ∣ Y.relIndex C) (hM : ∀ c ∈ C, ∀ m ∈ M, c * m * c⁻¹ ∈ M)
    (h : ∀ y ∈ Y, y ≠ 1 → y ∉ M) : ¬ r ∣ Nat.card M := by
  have hY' : IsPGroup r (Y.subgroupOf C) := hY.of_equiv (Subgroup.subgroupOfEquivOfLe hYC).symm
  have hidx' : ¬ r ∣ (Y.subgroupOf C).index := hidx
  let S : Sylow r C := hY'.toSylow hidx'
  have hcard : Nat.card (M.subgroupOf C) = Nat.card M :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMC).toEquiv
  rw [← hcard]
  refine not_dvd_card_of_sylow r S (M.subgroupOf C) ?_ ?_
  · intro g m hm
    rw [Subgroup.mem_subgroupOf] at hm ⊢
    simpa using hM g g.2 m hm
  · intro y hy hy1 hym
    rw [Subgroup.mem_subgroupOf] at hym
    have hyY : (y : J) ∈ Y := by
      have : y ∈ Y.subgroupOf C := hy
      exact this
    exact h y hyY (fun e => hy1 (Subtype.ext e)) hym

theorem relIndex_mul_card_of_le {J : Type*} [Group J] {C Y : Subgroup J} (hYC : Y ≤ C) :
    Y.relIndex C * Nat.card Y = Nat.card C := by
  have := Subgroup.relIndex_mul_card Y C
  rwa [inf_of_le_left hYC] at this

theorem eq_one_of_pgroup_of_zpowers {G : Type*} [Group G] {R : Subgroup G} (hR : IsPGroup 2 R)
    {y : G} (hy3 : orderOf y = 3) {g : G} (hgR : g ∈ R) (hgy : g ∈ Subgroup.zpowers y) :
    g = 1 := by
  obtain ⟨k, hk⟩ := hR ⟨g, hgR⟩
  have hk' : g ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have h3 : g ^ 3 = 1 := by
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hgy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hy3, pow_orderOf_eq_one,
      one_zpow]
  have hd2 : orderOf g ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hd3 : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left _ (by norm_num)
  have : orderOf g ∣ 1 := by
    have := Nat.dvd_gcd hd2 hd3
    rwa [hcop] at this
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 this)

theorem card_le_two_pow_fifteen {G : Type*} [Group G] [Finite G] (R S : Subgroup G) [R.Normal]
    (y : G) (hy3 : orderOf y = 3) (hR : IsPGroup 2 R) (hS : IsPGroup 2 S)
    (hSy : ∀ s ∈ S, s * y * s⁻¹ ∈ Subgroup.zpowers y)
    (conj : Fin 64 → G) (hconj : ∀ k, conj k ∈ R)
    (hinj : Function.Injective fun k => conj k * y * (conj k)⁻¹)
    (hmax : ∀ T : Subgroup G, IsPGroup 2 T → Nat.card T ≤ 2 ^ 21) :
    Nat.card S ≤ 2 ^ 15 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨C, hC⟩ : ∃ C : Subgroup G, C = Subgroup.centralizer {y} := ⟨_, rfl⟩
  have hmemC : ∀ g, g ∈ C ↔ y * g = g * y := by
    intro g
    rw [hC, Subgroup.mem_centralizer_iff]
    simp
  have h1 : R ⊓ S ≤ C ⊓ R := by
    intro x hx
    refine ⟨(hmemC x).2 ?_, hx.1⟩
    have hu := hSy x hx.2
    have hv : x * y * x⁻¹ * y⁻¹ ∈ R := by
      have : y * x⁻¹ * y⁻¹ ∈ R := Subgroup.Normal.conj_mem inferInstance _ (R.inv_mem hx.1) y
      have h2 := R.mul_mem hx.1 this
      simpa [mul_assoc] using h2
    have hw : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers y :=
      Subgroup.mul_mem _ hu (Subgroup.inv_mem _ (Subgroup.mem_zpowers y))
    have h0 := eq_one_of_pgroup_of_zpowers hR hy3 hv hw
    have h3 : x * y * x⁻¹ = y := mul_inv_eq_one.1 h0
    have h4 := congrArg (fun t => t * x) h3
    simpa [mul_assoc] using h4.symm
  have h2 : 64 ≤ C.relIndex R := by
    have hinj' : Function.Injective
        (fun k : Fin 64 => (QuotientGroup.mk (⟨conj k, hconj k⟩ : R) : R ⧸ C.subgroupOf R)) := by
      intro k k' hkk
      apply hinj
      have hq := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 hkk)
      have hc : ((conj k)⁻¹ * conj k') ∈ C := by simpa using hq
      have hc' := (hmemC _).1 hc
      show conj k * y * (conj k)⁻¹ = conj k' * y * (conj k')⁻¹
      have e : conj k' = conj k * ((conj k)⁻¹ * conj k') := by group
      calc conj k * y * (conj k)⁻¹
          = conj k * (((conj k)⁻¹ * conj k') * y * ((conj k)⁻¹ * conj k')⁻¹) * (conj k)⁻¹ := by
            rw [← hc']; group
        _ = conj k' * y * (conj k')⁻¹ := by rw [e]; group
    have := Nat.card_le_card_of_injective _ hinj'
    simpa [Subgroup.relIndex, Subgroup.index] using this
  have hA := Subgroup.relIndex_mul_card C R
  have hB := Subgroup.relIndex_mul_card R S
  have hD1 := Subgroup.relIndex_sup_right S R
  have hD2 := Subgroup.relIndex_mul_card R (S ⊔ R)
  have hRR : R ⊓ (S ⊔ R) = R := inf_eq_left.2 le_sup_right
  rw [hRR] at hD2
  have ht : Nat.card ↥(R ⊓ S) ≤ Nat.card ↥(C ⊓ R) := Subgroup.card_le_of_le h1
  have hSR : IsPGroup 2 ↥(S ⊔ R) := by
    obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 2)).1 hR
    obtain ⟨n, hn⟩ := hS.index (R.subgroupOf S)
    refine IsPGroup.of_card (n := n + a) ?_
    rw [← hD2, hD1, pow_add, ha]
    have : R.relIndex S = 2 ^ n := hn
    rw [this]
  have hu := hmax _ hSR
  rw [← hD2, hD1] at hu
  set ι := R.relIndex S
  have h64 : 64 * Nat.card S ≤ ι * Nat.card R := by
    rw [← hB]
    calc 64 * (ι * Nat.card ↥(R ⊓ S)) = ι * (64 * Nat.card ↥(R ⊓ S)) := by ring
      _ ≤ ι * (64 * Nat.card ↥(C ⊓ R)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ ht)
      _ ≤ ι * (C.relIndex R * Nat.card ↥(C ⊓ R)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h2)
      _ = ι * Nat.card R := by rw [hA]
  omega

theorem exists_central_involution {G : Type*} [Group G] [Finite G] (S S₀ : Subgroup G)
    (hS : IsPGroup 2 S) (h₀ : S₀ ≤ S) (hn : ∀ s ∈ S, ∀ x ∈ S₀, s * x * s⁻¹ ∈ S₀)
    (hne : S₀ ≠ ⊥) :
    ∃ z ∈ S₀, z ≠ 1 ∧ z * z = 1 ∧ ∀ s ∈ S, s * z = z * s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent S := hS.isNilpotent
  have hnorm : (S₀.subgroupOf S).Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have := hn g g.2 x hx
    simpa using this⟩
  have hne' : S₀.subgroupOf S ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have hxS : x ∈ S := h₀ hx
    have : (⟨x, hxS⟩ : S) ∈ S₀.subgroupOf S := hx
    rw [h] at this
    have h1 : (⟨x, hxS⟩ : S) = 1 := this
    have : x = 1 := congrArg Subtype.val h1
    simp [this]
  have hc := Group.IsNilpotent.inf_center_ne_bot_of_normal hne'
  obtain ⟨⟨z0, hz0S⟩, hz0⟩ : ∃ z : S, z ∈ S₀.subgroupOf S ⊓ Subgroup.center S ∧ z ≠ 1 := by
    by_contra hcon
    apply hc
    rw [eq_bot_iff]
    intro z hz
    by_contra hz1
    exact hcon ⟨z, hz, hz1⟩
  have hz0S₀ : z0 ∈ S₀ := hz0.1.1
  have hz0c : ∀ s ∈ S, s * z0 = z0 * s := by
    intro s hs
    have := Subgroup.mem_center_iff.1 hz0.1.2 ⟨s, hs⟩
    have := congrArg Subtype.val this
    simpa using this
  have hz1 : z0 ≠ 1 := fun h => hz0.2 (Subtype.ext h)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf (p := 2)).1 hS ⟨z0, hz0S⟩
  have hk' : orderOf z0 = 2 ^ k := by rw [← hk]; exact Subgroup.orderOf_coe (⟨z0, hz0S⟩ : S)
  have hkpos : 1 ≤ k := by
    by_contra h
    have : k = 0 := by omega
    rw [this, pow_zero] at hk'
    exact hz1 (orderOf_eq_one_iff.1 hk')
  refine ⟨z0 ^ (2 ^ (k - 1)), S₀.pow_mem hz0S₀ _, ?_, ?_, ?_⟩
  · intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hk'] at this
    have h2 : 2 ^ k ≤ 2 ^ (k - 1) := Nat.le_of_dvd (by positivity) this
    have : 2 ^ (k - 1) < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  · rw [← pow_two, ← pow_mul, ← pow_succ, Nat.sub_add_cancel hkpos, ← hk']
    exact pow_orderOf_eq_one z0
  · intro s hs
    exact (Commute.pow_right (hz0c s hs : Commute s z0) _).eq

theorem conj_mem_pair {G : Type*} [Group G] {y : G} (hy3 : orderOf y = 3) {u : G}
    (hu : u ∈ Subgroup.zpowers y) (hu1 : u ≠ 1) : u = y ∨ u = y⁻¹ := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
  have hy : y ^ 3 = 1 := by rw [← hy3]; exact pow_orderOf_eq_one y
  have h3 : y ^ (n % 3) = y ^ n := by
    have := zpow_mod_orderOf y n
    rwa [hy3] at this
  rw [← h3] at hu1 ⊢
  have hr : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hr with h | h | h
  · rw [h] at hu1; simp at hu1
  · left; rw [h]; simp
  · right; rw [h]
    have : y ^ (2 : ℤ) = y⁻¹ := by
      have : y ^ (3 : ℤ) = 1 := by exact_mod_cast hy
      rw [show (2 : ℤ) = 3 - 1 by norm_num, zpow_sub, this]; simp
    exact this

theorem relIndex_centralizer_le_two {G : Type*} [Group G] [Finite G] (S : Subgroup G) (y : G)
    (hy3 : orderOf y = 3) (hSy : ∀ s ∈ S, s * y * s⁻¹ ∈ Subgroup.zpowers y) :
    (Subgroup.centralizer ({y} : Set G)).relIndex S ≤ 2 := by
  by_contra h
  have h3 : 2 < Nat.card (S ⧸ (Subgroup.centralizer ({y} : Set G)).subgroupOf S) := by
    have : 2 < (Subgroup.centralizer ({y} : Set G)).relIndex S := by omega
    exact this
  have := Fintype.ofFinite (S ⧸ (Subgroup.centralizer ({y} : Set G)).subgroupOf S)
  rw [Nat.card_eq_fintype_card] at h3
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.1 h3
  set img : (S ⧸ (Subgroup.centralizer ({y} : Set G)).subgroupOf S) → G :=
    fun q => ((q.out : S) : G) * y * ((q.out : S) : G)⁻¹ with himg
  have key : ∀ q, img q = y ∨ img q = y⁻¹ := by
    intro q
    apply conj_mem_pair hy3 (hSy _ q.out.2)
    intro h1
    have : y = 1 := by
      have := congrArg (fun t => ((q.out : S) : G)⁻¹ * t * ((q.out : S) : G)) h1
      simpa [mul_assoc] using this
    rw [this] at hy3
    simp at hy3
  have same : ∀ q q', img q = img q' → q = q' := by
    intro q q' h1
    have hmem : (q.out⁻¹ * q'.out : S) ∈ (Subgroup.centralizer ({y} : Set G)).subgroupOf S := by
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
      set a : G := ((q.out : S) : G)
      set b : G := ((q'.out : S) : G)
      have h2 : a⁻¹ * (a * g * a⁻¹) * a = a⁻¹ * (b * g * b⁻¹) * a := by
        have := h1
        simp only [himg] at this
        rw [this]
      have h3 : g = a⁻¹ * b * g * (a⁻¹ * b)⁻¹ := by
        calc g = a⁻¹ * (a * g * a⁻¹) * a := by group
          _ = a⁻¹ * (b * g * b⁻¹) * a := h2
          _ = a⁻¹ * b * g * (a⁻¹ * b)⁻¹ := by group
      have h4 := congrArg (fun t => t * (a⁻¹ * b)) h3
      simpa [mul_assoc] using h4
    have := QuotientGroup.eq.2 hmem
    calc q = (QuotientGroup.mk q.out : _) := (QuotientGroup.out_eq' q).symm
      _ = QuotientGroup.mk q'.out := this
      _ = q' := QuotientGroup.out_eq' q'
  have pig : img a = img b ∨ img a = img c ∨ img b = img c := by
    rcases key a with ha | ha <;> rcases key b with hb | hb <;> rcases key c with hc | hc <;>
      simp [ha, hb, hc]
  rcases pig with h | h | h
  · exact hab (same _ _ h)
  · exact hac (same _ _ h)
  · exact hbc (same _ _ h)

theorem card_le_two_mul_centralizer {G : Type*} [Group G] [Finite G] (S : Subgroup G) (y : G)
    (hy3 : orderOf y = 3) (hSy : ∀ s ∈ S, s * y * s⁻¹ ∈ Subgroup.zpowers y) :
    Nat.card S ≤ 2 * Nat.card ↥(Subgroup.centralizer ({y} : Set G) ⊓ S) := by
  have h := relIndex_centralizer_le_two S y hy3 hSy
  have h2 := Subgroup.relIndex_mul_card (Subgroup.centralizer ({y} : Set G)) S
  rw [← h2]
  exact Nat.mul_le_mul_right _ h

theorem zpowers_nonid {G : Type*} [Group G] [Finite G] {y : G} {x : G}
    (hx : x ∈ Subgroup.zpowers y) (hx1 : x ≠ 1) :
    ∃ k : ℕ, 1 ≤ k ∧ k < orderOf y ∧ x = y ^ k := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have hpos : 0 < orderOf y := orderOf_pos y
  have h1 := zpow_mod_orderOf y n
  have hmod : 0 ≤ n % (orderOf y : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hpos.ne')
  have hlt : n % (orderOf y : ℤ) < orderOf y := Int.emod_lt_of_pos _ (by exact_mod_cast hpos)
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hmod
  refine ⟨k, ?_, ?_, ?_⟩
  · by_contra h
    have hk0 : k = 0 := by omega
    rw [hk0] at hk
    apply hx1
    rw [← h1, hk]
    simp
  · omega
  · rw [← h1, hk]
    simp

theorem exists_conj_mem_of_sylow_sub {J : Type*} [Group J] [Finite J] (r : ℕ) [Fact r.Prime]
    (L Y : Subgroup J) (hYL : Y ≤ L) (hY : IsPGroup r Y) (hidx : ¬ r ∣ Y.relIndex L) {x : J}
    (hxL : x ∈ L) (hx : orderOf x = r) : ∃ g ∈ L, g * x * g⁻¹ ∈ Y := by
  have hY' : IsPGroup r (Y.subgroupOf L) := hY.of_equiv (Subgroup.subgroupOfEquivOfLe hYL).symm
  have hidx' : ¬ r ∣ (Y.subgroupOf L).index := hidx
  let S : Sylow r L := hY'.toSylow hidx'
  let x' : L := ⟨x, hxL⟩
  have hx'o : orderOf x' = r := by rw [← hx]; exact Subgroup.orderOf_mk x hxL
  have hp : IsPGroup r (Subgroup.zpowers x') := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hx'o, pow_one]
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq L Q S
  have hxQ : x' ∈ (Q : Subgroup L) := hQ (Subgroup.mem_zpowers _)
  have hxY : g * x' * g⁻¹ ∈ (S : Subgroup L) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hxQ
  refine ⟨g, g.2, ?_⟩
  have : g * x' * g⁻¹ ∈ Y.subgroupOf L := hxY
  exact this

theorem card_le_of_isPGroup_sub {G : Type*} [Group G] [Finite G] (L : Subgroup G) {a m : ℕ}
    (hL : Nat.card L = 2 ^ a * m) (hm : ¬ 2 ∣ m) (T : Subgroup G) (hTL : T ≤ L)
    (hT : IsPGroup 2 T) : Nat.card T ≤ 2 ^ a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).1 hT
  have hd : 2 ^ n ∣ 2 ^ a * m := by
    rw [← hL, ← hn]
    exact Subgroup.card_dvd_of_le hTL
  have hcop : Nat.Coprime (2 ^ n) m := by
    apply Nat.Coprime.pow_left
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hm
  have h1 : 2 ^ n ∣ 2 ^ a := by
    have : Nat.Coprime (2 ^ n) m := hcop
    exact this.dvd_of_dvd_mul_right hd
  rw [hn]
  exact Nat.le_of_dvd (by positivity) h1

theorem card_le_two_pow_fifteen_sub {G : Type*} [Group G] [Finite G] (L R S : Subgroup G)
    (hRL : R ≤ L) (hSL : S ≤ L) (hRn : ∀ l ∈ L, ∀ r ∈ R, l * r * l⁻¹ ∈ R) (hR : IsPGroup 2 R)
    (hS : IsPGroup 2 S) {y : G} (hyL : y ∈ L) (hy3 : orderOf y = 3)
    (hSy : ∀ s ∈ S, s * y * s⁻¹ ∈ Subgroup.zpowers y) (conj : Fin 64 → G) (hconj : ∀ k, conj k ∈ R)
    (hinj : Function.Injective fun k => conj k * y * (conj k)⁻¹)
    (hmax : ∀ T : Subgroup G, T ≤ L → IsPGroup 2 T → Nat.card T ≤ 2 ^ 21) :
    Nat.card S ≤ 2 ^ 15 := by
  have hRn' : (R.subgroupOf L).Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have := hRn g g.2 x hx
    simpa using this⟩
  let y' : L := ⟨y, hyL⟩
  have hy3' : orderOf y' = 3 := by rw [← hy3]; exact Subgroup.orderOf_mk y hyL
  have hRp : IsPGroup 2 (R.subgroupOf L) := hR.of_equiv (Subgroup.subgroupOfEquivOfLe hRL).symm
  have hSp : IsPGroup 2 (S.subgroupOf L) := hS.of_equiv (Subgroup.subgroupOfEquivOfLe hSL).symm
  have hSy' : ∀ s ∈ S.subgroupOf L, s * y' * s⁻¹ ∈ Subgroup.zpowers y' := by
    intro s hs
    rw [Subgroup.mem_subgroupOf] at hs
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hSy s hs)
    refine Subgroup.mem_zpowers_iff.2 ⟨n, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_zpow, Subgroup.coe_mul, InvMemClass.coe_inv, y']
    exact hn
  have hmax' : ∀ T : Subgroup L, IsPGroup 2 T → Nat.card T ≤ 2 ^ 21 := by
    intro T hT
    have hT' : IsPGroup 2 (T.map L.subtype) := hT.map L.subtype
    have h1 := hmax (T.map L.subtype) (by rintro _ ⟨t, -, rfl⟩; exact t.2) hT'
    rwa [Subgroup.card_map_of_injective L.subtype_injective] at h1
  have key := card_le_two_pow_fifteen (R.subgroupOf L) (S.subgroupOf L) y' hy3' hRp hSp hSy'
    (fun k => ⟨conj k, hRL (hconj k)⟩) (fun k => by rw [Subgroup.mem_subgroupOf]; exact hconj k)
    (fun k k' h => hinj (by simpa using congrArg Subtype.val h)) hmax'
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSL).toEquiv] at key

theorem conj_mem_sup {G : Type*} [Group G] (A B : Subgroup G) (c : G)
    (hA : ∀ a ∈ A, c * a * c⁻¹ ∈ A ⊔ B) (hB : ∀ b ∈ B, c * b * c⁻¹ ∈ A ⊔ B) :
    ∀ n ∈ A ⊔ B, c * n * c⁻¹ ∈ A ⊔ B := by
  have h : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj c).toMonoidHom :=
    sup_le (fun a ha => by rw [Subgroup.mem_comap]; simpa [MulAut.conj_apply] using hA a ha)
      (fun b hb => by rw [Subgroup.mem_comap]; simpa [MulAut.conj_apply] using hB b hb)
  intro n hn
  have := h hn
  rw [Subgroup.mem_comap] at this
  simpa [MulAut.conj_apply] using this

theorem constrained_of_conj {G : Type*} [Group G] (g x : G)
    (h : ∃ N : Subgroup G, N ≤ Subgroup.centralizer ({g * x * g⁻¹} : Set G) ∧
      (∀ q ∈ Subgroup.centralizer ({g * x * g⁻¹} : Set G), ∀ e ∈ N, q * e * q⁻¹ ∈ N) ∧
      IsPGroup 2 N ∧ ∀ q ∈ Subgroup.centralizer ({g * x * g⁻¹} : Set G),
        (∀ e ∈ N, q * e = e * q) → q ∈ N) :
    ∃ N : Subgroup G, N ≤ Subgroup.centralizer ({x} : Set G) ∧
      (∀ q ∈ Subgroup.centralizer ({x} : Set G), ∀ e ∈ N, q * e * q⁻¹ ∈ N) ∧
      IsPGroup 2 N ∧ ∀ q ∈ Subgroup.centralizer ({x} : Set G),
        (∀ e ∈ N, q * e = e * q) → q ∈ N := by
  obtain ⟨N, hNC, hNn, hNp, hNs⟩ := h
  have hmem : ∀ e : G, e ∈ N.comap (MulAut.conj g).toMonoidHom ↔ g * e * g⁻¹ ∈ N := by
    intro e
    rw [Subgroup.mem_comap]
    simp [MulAut.conj_apply]
  have hcomm : ∀ q e : G, (g * q * g⁻¹) * (g * e * g⁻¹) = (g * e * g⁻¹) * (g * q * g⁻¹) ↔
      q * e = e * q := by
    intro q e
    constructor
    · intro h1
      have h2 : g * (q * e) * g⁻¹ = g * (e * q) * g⁻¹ := by
        simpa [mul_assoc] using h1
      simpa using h2
    · intro h1
      have : g * (q * e) * g⁻¹ = g * (e * q) * g⁻¹ := by rw [h1]
      simpa [mul_assoc] using this
  have hC : ∀ q : G, q ∈ Subgroup.centralizer ({x} : Set G) ↔
      g * q * g⁻¹ ∈ Subgroup.centralizer ({g * x * g⁻¹} : Set G) := by
    intro q
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    simp only [Set.mem_singleton_iff, forall_eq]
    rw [hcomm x q]
  refine ⟨N.comap (MulAut.conj g).toMonoidHom, ?_, ?_, ?_, ?_⟩
  · intro e he
    rw [hmem] at he
    have h1 := Subgroup.mem_centralizer_iff.1 (hNC he) (g * x * g⁻¹) rfl
    refine Subgroup.mem_centralizer_iff.2 fun x' hx' => ?_
    rw [Set.mem_singleton_iff] at hx'
    rw [hx']
    exact (hcomm x e).1 h1
  · intro q hq e he
    rw [hmem] at he ⊢
    have h1 := hNn (g * q * g⁻¹) ((hC q).1 hq) _ he
    have : g * (q * e * q⁻¹) * g⁻¹ = g * q * g⁻¹ * (g * e * g⁻¹) * (g * q * g⁻¹)⁻¹ := by group
    rw [this]
    exact h1
  · exact hNp.comap_of_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  · intro q hq h1
    rw [hmem]
    refine hNs (g * q * g⁻¹) ((hC q).1 hq) fun n hn => ?_
    have hn' : g⁻¹ * n * g ∈ N.comap (MulAut.conj g).toMonoidHom := by
      rw [hmem]
      have e : g * (g⁻¹ * n * g) * g⁻¹ = n := by group
      rw [e]
      exact hn
    have := h1 _ hn'
    have h2 := (hcomm q (g⁻¹ * n * g)).2 this
    simpa [mul_assoc] using h2

theorem conj_data {G : Type*} [Group G] (g : G) {S : Subgroup G} (hS : IsPGroup 2 S) {y : G}
    (hy3 : orderOf y = 3) (hSy : ∀ s ∈ S, s * y * s⁻¹ ∈ Subgroup.zpowers y) :
    IsPGroup 2 (S.map (MulAut.conj g).toMonoidHom) ∧
      Nat.card (S.map (MulAut.conj g).toMonoidHom) = Nat.card S ∧ orderOf (g * y * g⁻¹) = 3 ∧
      ∀ s ∈ S.map (MulAut.conj g).toMonoidHom,
        s * (g * y * g⁻¹) * s⁻¹ ∈ Subgroup.zpowers (g * y * g⁻¹) := by
  refine ⟨hS.map _, Subgroup.card_map_of_injective (MulAut.conj g).injective, ?_, ?_⟩
  · rw [← hy3]
    exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective y
  · rintro _ ⟨s, hs, rfl⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hSy s hs)
    refine Subgroup.mem_zpowers_iff.2 ⟨n, ?_⟩
    have e : (MulAut.conj g).toMonoidHom s = g * s * g⁻¹ := rfl
    rw [e, conj_zpow, hn]
    group

theorem map_conj_le {G : Type*} [Group G] (g : G) {S L L' : Subgroup G} (hSL : S ≤ L)
    (h : ∀ x ∈ L, g * x * g⁻¹ ∈ L') : S.map (MulAut.conj g).toMonoidHom ≤ L' := by
  rintro _ ⟨s, hs, rfl⟩
  simpa [MulAut.conj_apply] using h s (hSL hs)

theorem card_le_of_sylow_data {G : Type*} [Group G] [Finite G] (L R Y : Subgroup G)
    (hYL : Y ≤ L) (hRL : R ≤ L) (hRn : ∀ l ∈ L, ∀ r ∈ R, l * r * l⁻¹ ∈ R) (hR : IsPGroup 2 R)
    (hY : Nat.card Y = 27) {k : ℕ} (hL3 : Nat.card L = 27 * k) (hk3 : ¬ 3 ∣ k)
    {m : ℕ} (hL2 : Nat.card L = 2 ^ 21 * m) (hm2 : ¬ 2 ∣ m)
    (hconj : ∀ y ∈ Y, y ≠ 1 → ∃ conj : Fin 64 → G, (∀ j, conj j ∈ R) ∧
      Function.Injective fun j => conj j * y * (conj j)⁻¹)
    {S : Subgroup G} (hS : IsPGroup 2 S) (hSL : S ≤ L) {y : G} (hyL : y ∈ L)
    (hy3 : orderOf y = 3) (hSy : ∀ s ∈ S, s * y * s⁻¹ ∈ Subgroup.zpowers y) :
    Nat.card S ≤ 2 ^ 15 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hY3 : IsPGroup 3 Y := IsPGroup.of_card (n := 3) (by rw [hY]; norm_num)
  have hidx : ¬ 3 ∣ Y.relIndex L := by
    have h := relIndex_mul_card_of_le (C := L) (Y := Y) hYL
    rw [hY, hL3] at h
    have : Y.relIndex L = k := by omega
    rw [this]
    exact hk3
  obtain ⟨g, hgL, hgy⟩ := exists_conj_mem_of_sylow_sub 3 L Y hYL hY3 hidx hyL hy3
  obtain ⟨hS', hcard, hy3', hSy'⟩ := conj_data g hS hy3 hSy
  have hL' : ∀ x ∈ L, g * x * g⁻¹ ∈ L := fun x hx => L.mul_mem (L.mul_mem hgL hx) (L.inv_mem hgL)
  have hSL' := map_conj_le g hSL hL'
  have hne : g * y * g⁻¹ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hy3'
    omega
  obtain ⟨conj, hconj1, hinj⟩ := hconj _ hgy hne
  have hmax : ∀ T : Subgroup G, T ≤ L → IsPGroup 2 T → Nat.card T ≤ 2 ^ 21 := fun T hTL hT =>
    card_le_of_isPGroup_sub L hL2 hm2 T hTL hT
  have key := card_le_two_pow_fifteen_sub L R _ hRL hSL' hRn hR hS' (hL' y hyL) hy3' hSy' conj
    hconj1 hinj hmax
  rwa [hcard] at key

end CFSG.Sporadic.J4.QT2A
