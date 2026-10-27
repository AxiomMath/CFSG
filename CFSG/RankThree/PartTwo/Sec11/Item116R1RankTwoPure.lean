module

public import CFSG.Walter.AStar.Subnormal
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
public import Mathlib.Tactic.Basify
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

open Subgroup

namespace CFSG.RankThree.PartTwo.Sec11

@[expose] def IsRankTwoByCyclic (S : Type*) [Group S] : Prop :=
  ∃ (N : Subgroup S) (_ : N.Normal), IsMulCommutative N ∧
    Nat.card {x : N // x ^ 3 = 1} ≤ 9 ∧ IsCyclic (S ⧸ N)

theorem card_pow_three_eq_one_eq_card_quotient (A : Type*) [CommGroup A] [Finite A] :
    Nat.card {x : A // x ^ 3 = 1} = Nat.card (A ⧸ (powMonoidHom 3 : A →* A).range) := by
  have hker : Nat.card {x : A // x ^ 3 = 1} = Nat.card ↥(powMonoidHom 3 : A →* A).ker := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight (fun x => ?_)
    rw [MonoidHom.mem_ker, powMonoidHom_apply]
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (powMonoidHom 3 : A →* A).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (powMonoidHom 3 : A →* A)).toEquiv] at h1
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (powMonoidHom 3 : A →* A).range
  have hpos : 0 < Nat.card ↥(powMonoidHom 3 : A →* A).range := Nat.card_pos
  rw [hker]
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [← h1, h2, mul_comm]

theorem card_pow_three_le_of_surjective {A B : Type*} [CommGroup A] [CommGroup B] [Finite A] [Finite B] (g : A →* B)
    (hg : Function.Surjective g) : Nat.card {y : B // y ^ 3 = 1} ≤ Nat.card {x : A // x ^ 3 = 1} := by
  rw [card_pow_three_eq_one_eq_card_quotient B, card_pow_three_eq_one_eq_card_quotient A]
  have hle : (powMonoidHom 3 : A →* A).range ≤ ((powMonoidHom 3 : B →* B).range).comap g := by
    rintro _ ⟨a, rfl⟩
    rw [Subgroup.mem_comap, MonoidHom.mem_range]
    exact ⟨g a, by rw [powMonoidHom_apply, powMonoidHom_apply, map_pow]⟩
  have hq : Function.Surjective (QuotientGroup.map _ _ g hle) :=
    QuotientGroup.map_surjective_of_surjective _ _ g (QuotientGroup.mk_surjective.comp hg) hle
  exact Nat.card_le_card_of_surjective _ hq

theorem IsRankTwoByCyclic.of_surjective {S Q : Type*} [Group S] [Finite S] [Group Q]
    (h : IsRankTwoByCyclic S) (f : S →* Q) (hf : Function.Surjective f) : IsRankTwoByCyclic Q := by
  obtain ⟨N, hN, hcomm, hrank, hcyc⟩ := h
  have hNM : (N.map f).Normal := hN.map f hf
  have hMc : IsMulCommutative ↥(N.map f) := by
    refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 ha
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hb
    have hxy : x * y = y * x := congrArg Subtype.val (hcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    apply Subtype.ext
    show f x * f y = f y * f x
    rw [← map_mul, ← map_mul, hxy]
  have hfin : Finite ↥(N.map f) := Finite.of_surjective (f.subgroupMap N) (f.subgroupMap_surjective N)
  letI : CommGroup ↥N :=
    { (inferInstance : Group ↥N) with mul_comm := fun a b => hcomm.is_comm.comm a b }
  letI : CommGroup ↥(N.map f) :=
    { (inferInstance : Group ↥(N.map f)) with mul_comm := fun a b => hMc.is_comm.comm a b }
  have hcard := card_pow_three_le_of_surjective (f.subgroupMap N) (f.subgroupMap_surjective N)
  have hq : Function.Surjective (QuotientGroup.map N (N.map f) f (Subgroup.le_comap_map f N)) :=
    QuotientGroup.map_surjective_of_surjective N (N.map f) f (QuotientGroup.mk_surjective.comp hf)
      (Subgroup.le_comap_map f N)
  unfold IsRankTwoByCyclic
  refine ⟨N.map f, hNM, hMc, hcard.trans hrank, ?_⟩
  exact isCyclic_of_surjective (QuotientGroup.map N (N.map f) f (Subgroup.le_comap_map f N)) hq

theorem IsRankTwoByCyclic.of_mulEquiv {S Q : Type*} [Group S] [Finite S] [Group Q]
    (e : S ≃* Q) (h : IsRankTwoByCyclic S) : IsRankTwoByCyclic Q :=
  h.of_surjective e.toMonoidHom e.surjective

def subgroupOfHom {S : Type*} [Group S] (N T : Subgroup S) : ↥(N.subgroupOf T) →* ↥N where
  toFun x := ⟨x.1.1, Subgroup.mem_subgroupOf.mp x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem subgroupOfHom_injective {S : Type*} [Group S] (N T : Subgroup S) :
    Function.Injective (subgroupOfHom N T) := by
  intro x y hxy
  have h1 : ((subgroupOfHom N T x : ↥N) : S) = ((subgroupOfHom N T y : ↥N) : S) := congrArg Subtype.val hxy
  have h2 : ((x.1 : ↥T) : S) = ((y.1 : ↥T) : S) := h1
  exact Subtype.ext (Subtype.ext h2)

instance isMulCommutative_subgroupOf_of_isMulCommutative {S : Type*} [Group S] (N T : Subgroup S)
    [IsMulCommutative N] : IsMulCommutative (N.subgroupOf T) :=
  isMulCommutative_iff.mpr fun a b => subgroupOfHom_injective N T (by
    rw [map_mul, map_mul]
    exact (isMulCommutative_iff.mp (inferInstance : IsMulCommutative N)) _ _)

theorem card_pow_three_subgroupOf_le {S : Type*} [Group S] [Finite S] (N T : Subgroup S)
    (hrank : Nat.card {x : N // x ^ 3 = 1} ≤ 9) :
    Nat.card {x : N.subgroupOf T // x ^ 3 = 1} ≤ 9 := by
  have hpow : ∀ x : {x : N.subgroupOf T // x ^ 3 = 1}, subgroupOfHom N T x.1 ^ 3 = 1 := by
    intro x
    rw [← map_pow, x.2, map_one]
  let F : {x : N.subgroupOf T // x ^ 3 = 1} → {x : N // x ^ 3 = 1} :=
    fun x => ⟨subgroupOfHom N T x.1, hpow x⟩
  have hF : Function.Injective F := by
    intro x y hxy
    have h1 : subgroupOfHom N T x.1 = subgroupOfHom N T y.1 := congrArg Subtype.val hxy
    exact Subtype.ext (subgroupOfHom_injective N T h1)
  exact le_trans (Nat.card_le_card_of_injective F hF) hrank

theorem subgroupOf_le_comap_subtype {S : Type*} [Group S] (N T : Subgroup S) :
    N.subgroupOf T ≤ N.comap T.subtype := le_rfl

theorem quotientMap_subgroupOf_injective {S : Type*} [Group S] (N T : Subgroup S) [hN : N.Normal]
    [hNT : (N.subgroupOf T).Normal] :
    Function.Injective (QuotientGroup.map (N.subgroupOf T) N T.subtype (subgroupOf_le_comap_subtype N T)) := by
  refine (injective_iff_map_eq_one _).mpr ?_
  intro q hq
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  rw [QuotientGroup.map_mk, QuotientGroup.eq_one_iff] at hq
  rw [QuotientGroup.eq_one_iff]
  exact Subgroup.mem_subgroupOf.mpr hq

theorem IsRankTwoByCyclic.subgroup {S : Type*} [Group S] [Finite S] (h : IsRankTwoByCyclic S)
    (T : Subgroup S) : IsRankTwoByCyclic ↥T := by
  unfold IsRankTwoByCyclic at h ⊢
  obtain ⟨N, hN, hcomm, hrank, hcyc⟩ := h
  have hNT : (N.subgroupOf T).Normal := Subgroup.Normal.subgroupOf hN T
  exact ⟨N.subgroupOf T, hNT, isMulCommutative_subgroupOf_of_isMulCommutative N T, card_pow_three_subgroupOf_le N T hrank,
    isCyclic_of_injective _ (quotientMap_subgroupOf_injective N T)⟩

theorem IsRankTwoByCyclic.mono {X : Type*} [Group X] [Finite X] {H K : Subgroup X} (hHK : H ≤ K)
    (h : IsRankTwoByCyclic ↥K) : IsRankTwoByCyclic ↥H :=
  IsRankTwoByCyclic.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hHK) (h.subgroup (H.subgroupOf K))

theorem IsRankTwoByCyclic.map {X Y : Type*} [Group X] [Finite X] [Group Y] {H : Subgroup X}
    (h : IsRankTwoByCyclic ↥H) (f : X →* Y) : IsRankTwoByCyclic ↥(H.map f) :=
  IsRankTwoByCyclic.of_surjective h (f.subgroupMap H) (f.subgroupMap_surjective H)

theorem IsRankTwoByCyclic.sylow_conj {Y : Type*} [Group Y] [Finite Y] {T T' : Sylow 3 Y}
    (h : IsRankTwoByCyclic ↥(T' : Subgroup Y)) : IsRankTwoByCyclic ↥(T : Subgroup Y) := by
  haveI : Finite (Sylow 3 Y) :=
    Finite.of_injective (fun P : Sylow 3 Y => ((P : Subgroup Y) : Set Y))
      (fun P Q hPQ => Sylow.ext (SetLike.coe_injective hPQ))
  exact IsRankTwoByCyclic.of_mulEquiv (Sylow.equiv T' T) h

theorem card_pow_three_le_nine_of_exists_zpow_mul_zpow {A : Type*} [CommGroup A] [Finite A] (p q : A)
    (hgen : ∀ a : A, ∃ m n : ℤ, p ^ m * q ^ n = a) :
    Nat.card {x : A // x ^ 3 = 1} ≤ 9 := by
  rw [card_pow_three_eq_one_eq_card_quotient A]
  refine le_trans (Nat.card_le_card_of_surjective (fun π : Fin 3 × Fin 3 =>
    (QuotientGroup.mk (p ^ ((π.1 : ℕ) : ℤ) * q ^ ((π.2 : ℕ) : ℤ)) :
      A ⧸ (powMonoidHom 3 : A →* A).range)) ?_) (le_of_eq (by simp))
  intro qq
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective qq
  obtain ⟨m, n, rfl⟩ := hgen a
  have hi : (((m % 3).toNat : ℕ) : ℤ) = m % 3 := Int.toNat_of_nonneg (by omega)
  have hj : (((n % 3).toNat : ℕ) : ℤ) = n % 3 := Int.toNat_of_nonneg (by omega)
  have hi3 : (m % 3).toNat < 3 := by omega
  have hj3 : (n % 3).toNat < 3 := by omega
  refine ⟨(⟨(m % 3).toNat, hi3⟩, ⟨(n % 3).toNat, hj3⟩), ?_⟩
  dsimp only
  rw [QuotientGroup.eq, hi, hj]
  have e1 : p ^ m = p ^ (m % 3) * (p ^ (m / 3)) ^ (3 : ℕ) := by
    rw [← zpow_natCast, ← zpow_mul, ← zpow_add]
    congr 1
    omega
  have e2 : q ^ n = q ^ (n % 3) * (q ^ (n / 3)) ^ (3 : ℕ) := by
    rw [← zpow_natCast, ← zpow_mul, ← zpow_add]
    congr 1
    omega
  have key : (p ^ (m % 3) * q ^ (n % 3))⁻¹ * (p ^ m * q ^ n) =
      (p ^ (m / 3) * q ^ (n / 3)) ^ (3 : ℕ) := by
    rw [e1, e2, mul_pow]
    calc (p ^ (m % 3) * q ^ (n % 3))⁻¹ *
          (p ^ (m % 3) * (p ^ (m / 3)) ^ (3 : ℕ) * (q ^ (n % 3) * (q ^ (n / 3)) ^ (3 : ℕ)))
        = (p ^ (m % 3) * q ^ (n % 3))⁻¹ * (p ^ (m % 3) * q ^ (n % 3)) *
            ((p ^ (m / 3)) ^ (3 : ℕ) * (q ^ (n / 3)) ^ (3 : ℕ)) := by ac_rfl
      _ = (p ^ (m / 3)) ^ (3 : ℕ) * (q ^ (n / 3)) ^ (3 : ℕ) := by
          rw [inv_mul_cancel, one_mul]
  rw [key]
  exact MonoidHom.mem_range.mpr ⟨p ^ (m / 3) * q ^ (n / 3), rfl⟩

theorem exists_zpow_mul_zpow_of_closure_pair {X : Type*} [Group X] (u v : X) (huv : u * v = v * u) {a : X}
    (ha : a ∈ Subgroup.closure ({u, v} : Set X)) : ∃ m n : ℤ, u ^ m * v ^ n = a := by
  have hc : Commute u v := huv
  induction ha using Subgroup.closure_induction with
  | mem z hz =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with h | h
    · exact ⟨1, 0, by simp [h]⟩
    · exact ⟨0, 1, by simp [h]⟩
  | one => exact ⟨0, 0, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨m, n, rfl⟩ := hx
    obtain ⟨m', n', rfl⟩ := hy
    refine ⟨m + m', n + n', ?_⟩
    have hc2 : Commute (v ^ n) (u ^ m') := hc.symm.zpow_zpow n m'
    rw [zpow_add, zpow_add]
    calc u ^ m * u ^ m' * (v ^ n * v ^ n') = u ^ m * (u ^ m' * v ^ n) * v ^ n' := by
          simp only [mul_assoc]
      _ = u ^ m * (v ^ n * u ^ m') * v ^ n' := by rw [hc2.eq]
      _ = u ^ m * v ^ n * (u ^ m' * v ^ n') := by simp only [mul_assoc]
  | inv x _ hx =>
    obtain ⟨m, n, rfl⟩ := hx
    refine ⟨-m, -n, ?_⟩
    rw [zpow_neg, zpow_neg, mul_inv_rev]
    exact (Commute.inv_inv (hc.zpow_zpow m n)).eq

theorem card_pow_three_closure_pair_le {X : Type*} [Group X] [Finite X] (u v : X)
    (huv : u * v = v * u) :
    Nat.card {x : (Subgroup.closure ({u, v} : Set X)) // x ^ 3 = 1} ≤ 9 := by
  have hpair : (({u, v} : Set X)).Pairwise Commute := by
    intro a ha b hb _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      first | exact Commute.refl _ | exact huv | exact huv.symm
  have hcomm : IsMulCommutative (Subgroup.closure ({u, v} : Set X)) :=
    Subgroup.isMulCommutative_closure hpair
  letI : CommGroup (Subgroup.closure ({u, v} : Set X)) := by
    open scoped IsMulCommutative in exact inferInstance
  obtain ⟨p, hp⟩ : ∃ p : Subgroup.closure ({u, v} : Set X), (p : X) = u :=
    ⟨⟨u, Subgroup.subset_closure (by simp)⟩, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : Subgroup.closure ({u, v} : Set X), (q : X) = v :=
    ⟨⟨v, Subgroup.subset_closure (by simp)⟩, rfl⟩
  refine card_pow_three_le_nine_of_exists_zpow_mul_zpow p q ?_
  intro a
  obtain ⟨m, n, hmn⟩ := exists_zpow_mul_zpow_of_closure_pair u v huv a.2
  refine ⟨m, n, Subtype.ext ?_⟩
  rw [Subgroup.coe_mul, Subgroup.coe_zpow, Subgroup.coe_zpow, hp, hq]
  exact hmn

theorem isRankTwoByCyclic_of_generators {R : Type*} [Group R] [Finite R] (r x s : R)
    (hgen : Subgroup.closure ({r, x, s} : Set R) = ⊤) (hxs : x * s = s * x)
    (hnx : ∀ y : R, ∃ e : ℤ, y * x * y⁻¹ = x ^ e) (hns : ∀ y : R, ∃ e : ℤ, y * s * y⁻¹ = s ^ e) :
    IsRankTwoByCyclic R := by
  unfold IsRankTwoByCyclic
  have hsN : s ∈ Subgroup.closure ({s, x} : Set R) := Subgroup.subset_closure (by simp)
  have hxN : x ∈ Subgroup.closure ({s, x} : Set R) := Subgroup.subset_closure (by simp)
  have hconj : ∀ y : R, ∀ g ∈ Subgroup.closure ({s, x} : Set R),
      y * g * y⁻¹ ∈ Subgroup.closure ({s, x} : Set R) := by
    intro y g hg
    induction hg using Subgroup.closure_induction with
    | mem z hz =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with h | h
      · obtain ⟨e, he⟩ := hns y
        rw [h, he]
        exact zpow_mem hsN e
      · obtain ⟨e, he⟩ := hnx y
        rw [h, he]
        exact zpow_mem hxN e
    | one => simp
    | mul a b _ _ ha hb =>
      have hab : y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) := by group
      rw [hab]
      exact mul_mem ha hb
    | inv a _ ha =>
      have hai : y * a⁻¹ * y⁻¹ = (y * a * y⁻¹)⁻¹ := by group
      rw [hai]
      exact inv_mem ha
  haveI hnorm : (Subgroup.closure ({s, x} : Set R)).Normal := ⟨fun n hn g => hconj g n hn⟩
  have hpair : (({s, x} : Set R)).Pairwise Commute := by
    intro a ha b hb _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      first | exact Commute.refl _ | exact hxs.symm | exact hxs
  have hcomm : IsMulCommutative (Subgroup.closure ({s, x} : Set R)) :=
    Subgroup.isMulCommutative_closure hpair
  have hcard : Nat.card {y : (Subgroup.closure ({s, x} : Set R)) // y ^ 3 = 1} ≤ 9 :=
    card_pow_three_closure_pair_le s x hxs.symm
  have hcyc : IsCyclic (R ⧸ Subgroup.closure ({s, x} : Set R)) := by
    refine ⟨⟨(QuotientGroup.mk r : R ⧸ Subgroup.closure ({s, x} : Set R)), fun q => ?_⟩⟩
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    have key : ∀ b ∈ Subgroup.closure ({r, x, s} : Set R), ∃ k : ℤ,
        (QuotientGroup.mk r : R ⧸ Subgroup.closure ({s, x} : Set R)) ^ k =
          QuotientGroup.mk b := by
      intro b hb
      induction hb using Subgroup.closure_induction with
      | mem z hz =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with h | h | h
        · exact ⟨1, by rw [h, zpow_one]⟩
        · exact ⟨0, by rw [h, zpow_zero]; exact ((QuotientGroup.eq_one_iff x).mpr hxN).symm⟩
        · exact ⟨0, by rw [h, zpow_zero]; exact ((QuotientGroup.eq_one_iff s).mpr hsN).symm⟩
      | one => exact ⟨0, by rw [zpow_zero, QuotientGroup.mk_one]⟩
      | mul c d _ _ hc hd =>
        obtain ⟨k, hk⟩ := hc
        obtain ⟨l, hl⟩ := hd
        exact ⟨k + l, by rw [zpow_add, hk, hl, QuotientGroup.mk_mul]⟩
      | inv c _ hc =>
        obtain ⟨k, hk⟩ := hc
        exact ⟨-k, by rw [zpow_neg, hk, QuotientGroup.mk_inv]⟩
    have ha : a ∈ Subgroup.closure ({r, x, s} : Set R) := by
      rw [hgen]
      exact Subgroup.mem_top a
    exact key a ha
  exact ⟨Subgroup.closure ({s, x} : Set R), hnorm, hcomm, hcard, hcyc⟩

theorem rankTwoByCyclic_sylow_section {X : Type*} [Group X] [Finite X] (Rs : Sylow 3 X)
    (hR : IsRankTwoByCyclic ↥(Rs : Subgroup X)) {J : Subgroup X} (hJ : J.IsSubnormal)
    {Q : Type*} [Group Q] [Finite Q] (ψ : J →* Q) (hψ : Function.Surjective ψ) (T : Sylow 3 Q) :
    IsRankTwoByCyclic ↥(T : Subgroup Q) := by
  obtain ⟨P, hP⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Rs hJ
  have hMeet : IsRankTwoByCyclic ↥((Rs : Subgroup X) ⊓ J) := hR.mono inf_le_left
  have e : ↥(P : Subgroup J) ≃* ↥((Rs : Subgroup X) ⊓ J) :=
    (Subgroup.equivMapOfInjective (P : Subgroup J) J.subtype J.subtype_injective).trans
      (MulEquiv.subgroupCongr hP)
  have hPJ : IsRankTwoByCyclic ↥(P : Subgroup J) := IsRankTwoByCyclic.of_mulEquiv e.symm hMeet
  have hMap : IsRankTwoByCyclic ↥((P : Subgroup J).map ψ) := hPJ.map ψ
  have hT' : IsRankTwoByCyclic ↥((P.mapSurjective hψ : Sylow 3 Q) : Subgroup Q) := by
    rw [Sylow.coe_mapSurjective]
    exact hMap
  exact IsRankTwoByCyclic.sylow_conj hT'

end CFSG.RankThree.PartTwo.Sec11
