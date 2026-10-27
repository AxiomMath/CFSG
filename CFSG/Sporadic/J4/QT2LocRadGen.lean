module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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

public section

namespace CFSG.Sporadic.J4.QT2

open scoped Pointwise

@[expose] def Radical {G : Type*} [Group G] (y : G) (N : Subgroup G) : Prop :=
  IsPGroup 2 ↥N ∧ y ∈ N ∧ N ≤ Subgroup.centralizer ({y} : Set G) ∧
    (∀ q ∈ Subgroup.centralizer ({y} : Set G), ∀ e ∈ N, q * e * q⁻¹ ∈ N) ∧
    (∀ q ∈ Subgroup.centralizer ({y} : Set G), (∀ e ∈ N, q * e = e * q) → q ∈ N) ∧
    ∀ g ∈ Subgroup.centralizer ({y} : Set G), orderOf g = 5 →
      16 < (N ⊓ Subgroup.centralizer ({g} : Set G)).relIndex N

@[expose] def conjSub {G : Type*} [Group G] (c : G) (N : Subgroup G) : Subgroup G :=
  N.map (MulAut.conj c).toMonoidHom

theorem mem_conjSub {G : Type*} [Group G] {c : G} {N : Subgroup G} {x : G} :
    x ∈ conjSub c N ↔ c⁻¹ * x * c ∈ N := by
  unfold conjSub
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

theorem conjSub_centralizer {G : Type*} [Group G] (c g : G) :
    Subgroup.centralizer ({c * g * c⁻¹} : Set G) =
      (Subgroup.centralizer ({g} : Set G)).map (MulAut.conj c).toMonoidHom := by
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  simp only [MulAut.conj_symm_apply]
  constructor
  · intro h
    calc c⁻¹ * x * c * g = c⁻¹ * (x * (c * g * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * g * c⁻¹) * x) * c := by rw [h]
      _ = g * (c⁻¹ * x * c) := by group
  · intro h
    calc x * (c * g * c⁻¹) = c * ((c⁻¹ * x * c) * g) * c⁻¹ := by group
      _ = c * (g * (c⁻¹ * x * c)) * c⁻¹ := by rw [h]
      _ = (c * g * c⁻¹) * x := by group

theorem relIndex_conj {G : Type*} [Group G] (c : G) (H K : Subgroup G) :
    (H.map (MulAut.conj c).toMonoidHom).relIndex (K.map (MulAut.conj c).toMonoidHom) =
      H.relIndex K :=
  Subgroup.relIndex_map_map_of_injective H K (MulAut.conj c).injective

theorem Radical.conj {G : Type*} [Group G] {y : G} {N : Subgroup G} (h : Radical y N) (c : G) :
    Radical (c * y * c⁻¹) (conjSub c N) := by
  obtain ⟨hp, hy, hle, hnorm, hself, h5⟩ := h
  have hcen : ∀ q, q ∈ Subgroup.centralizer ({c * y * c⁻¹} : Set G) ↔
      c⁻¹ * q * c ∈ Subgroup.centralizer ({y} : Set G) := by
    intro q
    rw [conjSub_centralizer, Subgroup.mem_map_equiv]
    simp [MulAut.conj_symm_apply]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine hp.of_injective
      { toFun := fun x : ↥(conjSub c N) => (⟨c⁻¹ * x * c, mem_conjSub.1 x.2⟩ : ↥N)
        map_one' := by ext; simp
        map_mul' := fun a b => by ext; simp [mul_assoc] } ?_
    intro a b hab
    have := congrArg Subtype.val hab
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, mul_left_inj, mul_right_inj] at this
    exact Subtype.ext this
  · rw [mem_conjSub]
    simpa [mul_assoc] using hy
  · intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hx' := Subgroup.mem_centralizer_singleton_iff.1 (hle (mem_conjSub.1 hx))
    calc x * (c * y * c⁻¹) = c * ((c⁻¹ * x * c) * y) * c⁻¹ := by group
      _ = c * (y * (c⁻¹ * x * c)) * c⁻¹ := by rw [hx']
      _ = (c * y * c⁻¹) * x := by group
  · intro q hq e he
    rw [mem_conjSub] at he ⊢
    have := hnorm _ ((hcen q).1 hq) _ he
    have e1 : c⁻¹ * (q * e * q⁻¹) * c =
        (c⁻¹ * q * c) * (c⁻¹ * e * c) * (c⁻¹ * q * c)⁻¹ := by group
    rw [e1]
    exact this
  · intro q hq hc
    rw [mem_conjSub]
    refine hself _ ((hcen q).1 hq) fun e he => ?_
    have := hc (c * e * c⁻¹) (by rw [mem_conjSub]; simpa [mul_assoc] using he)
    calc c⁻¹ * q * c * e = c⁻¹ * (q * (c * e * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * e * c⁻¹) * q) * c := by rw [this]
      _ = e * (c⁻¹ * q * c) := by group
  · intro g hg hg5
    have hg' : c⁻¹ * g * c ∈ Subgroup.centralizer ({y} : Set G) := (hcen g).1 hg
    have ho : orderOf (c⁻¹ * g * c) = 5 := by
      rw [← hg5]
      have := orderOf_injective (MulAut.conj c⁻¹).toMonoidHom (MulAut.conj c⁻¹).injective g
      simpa [MulAut.conj_apply, mul_assoc] using this
    have key := h5 _ hg' ho
    have hf : Function.Injective (MulAut.conj c).toMonoidHom := (MulAut.conj c).injective
    have e1 : (Subgroup.centralizer ({c⁻¹ * g * c} : Set G)).map (MulAut.conj c).toMonoidHom =
        Subgroup.centralizer ({g} : Set G) := by
      have := conjSub_centralizer c (c⁻¹ * g * c)
      rw [show c * (c⁻¹ * g * c) * c⁻¹ = g by group] at this
      exact this.symm
    have e2 : conjSub c N ⊓ Subgroup.centralizer ({g} : Set G) =
        (N ⊓ Subgroup.centralizer ({c⁻¹ * g * c} : Set G)).map (MulAut.conj c).toMonoidHom := by
      rw [Subgroup.map_inf _ _ _ hf, e1]
      rfl
    rw [e2]
    show 16 < ((N ⊓ Subgroup.centralizer ({c⁻¹ * g * c} : Set G)).map
      (MulAut.conj c).toMonoidHom).relIndex (N.map (MulAut.conj c).toMonoidHom)
    rw [relIndex_conj]
    exact key

theorem exists_conj_pow_of_card {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hcard : (Nat.card G).factorization p = 1) {x y : G} (hx : orderOf x = p)
    (hy : orderOf y = p) : ∃ g : G, ∃ k : ℕ, y = g * x ^ k * g⁻¹ := by
  have hpx : Nat.card (Subgroup.zpowers x) = p ^ (Nat.card G).factorization p := by
    rw [Nat.card_zpowers, hx, hcard, pow_one]
  have hpy : Nat.card (Subgroup.zpowers y) = p ^ (Nat.card G).factorization p := by
    rw [Nat.card_zpowers, hy, hcard, pow_one]
  let P : Sylow p G := Sylow.ofCard (Subgroup.zpowers x) hpx
  let Q : Sylow p G := Sylow.ofCard (Subgroup.zpowers y) hpy
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  have hQ : (Q : Subgroup G) = MulAut.conj g • Subgroup.zpowers x := by
    rw [← hg, Sylow.coe_subgroup_smul, Sylow.coe_ofCard]
  have hyQ : y ∈ (Q : Subgroup G) := by
    rw [Sylow.coe_ofCard]
    exact Subgroup.mem_zpowers y
  rw [hQ] at hyQ
  obtain ⟨t, ht, hty⟩ := (Subgroup.mem_smul_pointwise_iff_exists y (MulAut.conj g) _).1 hyQ
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht
  have hp0 : (0 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  refine ⟨g, (n % (p : ℤ)).toNat, ?_⟩
  have hn : x ^ n = x ^ ((n % (p : ℤ)).toNat) := by
    rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ hp0.ne'), ← hx, zpow_mod_orderOf]
  rw [← hn, ← hty]
  simp [MulAut.smul_def, MulAut.conj_apply]

theorem centralizer_pow_eq {G : Type*} [Group G] {y : G} {p : ℕ} (hp : p.Prime)
    (hy : orderOf y = p) {k : ℕ} (hk : ¬ p ∣ k) :
    Subgroup.centralizer ({y ^ k} : Set G) = Subgroup.centralizer ({y} : Set G) := by
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    have hcop : Nat.Coprime k (orderOf y) := by
      rw [hy]
      exact ((Nat.Prime.coprime_iff_not_dvd hp).2 hk).symm
    obtain ⟨m, hyy⟩ := exists_pow_eq_self_of_coprime hcop
    have hc : Commute x (y ^ k) := hx
    have := hc.pow_right m
    rw [hyy] at this
    exact this
  · intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    have hc : Commute x y := hx
    exact hc.pow_right k

theorem lt_relIndex_of_sylow {G : Type*} [Group G] [Finite G] (K N : Subgroup G)
    (hKN : ∀ c ∈ K, ∀ n ∈ N, c * n * c⁻¹ ∈ N) (hcard : (Nat.card ↥K).factorization 5 = 1)
    {y : G} (hyK : y ∈ K) (hy5 : orderOf y = 5)
    (hy : 16 < (N ⊓ Subgroup.centralizer ({y} : Set G)).relIndex N)
    {g : G} (hgK : g ∈ K) (hg5 : orderOf g = 5) :
    16 < (N ⊓ Subgroup.centralizer ({g} : Set G)).relIndex N := by
  have hfact : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨c, k, hk⟩ := exists_conj_pow_of_card (G := ↥K) (p := 5) hcard
    (x := ⟨y, hyK⟩) (y := ⟨g, hgK⟩) (by rw [Subgroup.orderOf_mk]; exact hy5)
    (by rw [Subgroup.orderOf_mk]; exact hg5)
  have hk' : g = (c : G) * y ^ k * (c : G)⁻¹ := by
    have := congrArg Subtype.val hk
    simpa using this
  have hk5 : ¬ 5 ∣ k := by
    rintro ⟨j, rfl⟩
    have : y ^ (5 * j) = 1 := by rw [pow_mul, ← hy5, pow_orderOf_eq_one, one_pow]
    rw [this] at hk'
    have : g = 1 := by simpa using hk'
    rw [this, orderOf_one] at hg5
    exact absurd hg5 (by norm_num)
  have hcN : conjSub (c : G) N = N := by
    ext x
    rw [mem_conjSub]
    constructor
    · intro hx
      have := hKN c c.2 _ hx
      simpa [mul_assoc] using this
    · intro hx
      have := hKN c⁻¹ (Subgroup.inv_mem K c.2) _ hx
      simpa [mul_assoc] using this
  have hcen : Subgroup.centralizer ({g} : Set G) =
      (Subgroup.centralizer ({y} : Set G)).map (MulAut.conj (c : G)).toMonoidHom := by
    rw [hk', conjSub_centralizer, centralizer_pow_eq (by norm_num) hy5 hk5]
  have hf : Function.Injective (MulAut.conj (c : G)).toMonoidHom := (MulAut.conj (c : G)).injective
  have e2 : N ⊓ Subgroup.centralizer ({g} : Set G) =
      (N ⊓ Subgroup.centralizer ({y} : Set G)).map (MulAut.conj (c : G)).toMonoidHom := by
    rw [Subgroup.map_inf _ _ _ hf, ← hcen]
    have : N.map (MulAut.conj (c : G)).toMonoidHom = N := hcN
    rw [this]
  rw [e2]
  have h3 := relIndex_conj (c : G) (N ⊓ Subgroup.centralizer ({y} : Set G)) N
  have h4 : N.map (MulAut.conj (c : G)).toMonoidHom = N := hcN
  rw [h4] at h3
  rw [h3]
  exact hy

theorem radical_of_centralizer_le {G : Type*} [Group G] (H E : Subgroup G) (y : G)
    (hE2 : IsPGroup 2 ↥E) (hab : ∀ x ∈ E, ∀ e ∈ E, x * e = e * x) (hy : y ∈ E)
    (hHE : ∀ h ∈ H, ∀ e ∈ E, h * e * h⁻¹ ∈ E) (hself : ∀ h ∈ H, (∀ e ∈ E, h * e = e * h) → h ∈ E)
    (hcent : ∀ q ∈ Subgroup.centralizer ({y} : Set G), q ∈ H)
    (h5 : ∀ g ∈ H, orderOf g = 5 → 16 < (E ⊓ Subgroup.centralizer ({g} : Set G)).relIndex E) :
    Radical y E := by
  refine ⟨hE2, hy, ?_, fun q hq e he => hHE q (hcent q hq) e he,
    fun q hq hc => hself q (hcent q hq) hc, fun g hg hg5 => h5 g (hcent g hg) hg5⟩
  intro e he
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact hab e he y hy

theorem relIndex_ne_zero_of_finite {G : Type*} [Group G] [Finite G] (H K : Subgroup G) :
    H.relIndex K ≠ 0 :=
  Subgroup.index_ne_zero_of_finite

theorem lt_relIndex_inf_of_le {G : Type*} [Group G] [Finite G] {Q N : Subgroup G} (hQN : Q ≤ N)
    (C : Subgroup G) (h : 16 < C.relIndex Q) : 16 < (N ⊓ C).relIndex N := by
  rw [inf_comm, Subgroup.inf_relIndex_right]
  exact lt_of_lt_of_le h (Subgroup.relIndex_le_of_le_right hQN (relIndex_ne_zero_of_finite C N))

end CFSG.Sporadic.J4.QT2
