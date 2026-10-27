module

public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.Models
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
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
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

namespace CFSG.Monster.B.Recog

namespace StrongEmbedding

variable {G : Type*} [Group G] [Finite G]

theorem exists_involution_centralized {P N : Subgroup G} (hP : P ≠ ⊥) (hPN : P ≤ N)
    (hN : N ≤ Subgroup.normalizer (P : Set G)) (hN2 : IsPGroup 2 N) :
    ∃ z ∈ P, orderOf z = 2 ∧ N ≤ Subgroup.centralizer {z} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent N := hN2.isNilpotent
  let H : Subgroup N := P.subgroupOf N
  have hH : H.Normal := (Subgroup.normal_subgroupOf_iff hPN).2 fun h k hh hk =>
    (Subgroup.mem_normalizer_iff.1 (hN hk) h).1 hh
  have hHne : H ≠ ⊥ := by
    obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hP
    refine Subgroup.ne_bot_iff_exists_ne_one.2 ⟨⟨⟨x, hPN hx⟩, ?_⟩, ?_⟩
    · exact Subgroup.mem_subgroupOf.2 hx
    · intro h
      apply hx1
      exact Subtype.ext (congrArg (fun a : H => ((a : N) : G)) h)
  have hK := Group.IsNilpotent.inf_center_ne_bot_of_normal hHne
  have hK2 : IsPGroup 2 ↥(H ⊓ Subgroup.center ↥N) := hN2.to_subgroup _
  have hcard : 2 ∣ Nat.card ↥(H ⊓ Subgroup.center ↥N) := by
    rcases hK2.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.card_eq_one.1 h) hK
    · exact h
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 hcard
  refine ⟨((y : N) : G), Subgroup.mem_subgroupOf.1 y.2.1, ?_, fun n hn => ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hy]
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_center_iff.1 y.2.2 ⟨n, hn⟩
    exact congrArg Subtype.val this

theorem exists_sylow_eq {D P : Subgroup G}
    (hD : ∀ u ∈ D, orderOf u = 2 → Subgroup.centralizer {u} ≤ D)
    (hP2 : IsPGroup 2 P) (hPD : P ≤ D) (hP : P ≠ ⊥)
    (hmax : ∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ D → Nat.card Q ≤ Nat.card P) :
    ∃ T : Sylow 2 G, (T : Subgroup G) = P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hPT⟩ := hP2.exists_le_sylow
  refine ⟨T, ?_⟩
  let N := Subgroup.normalizer (P : Set G) ⊓ (T : Subgroup G)
  have hN2 : IsPGroup 2 N := T.isPGroup'.to_le inf_le_right
  have hPN : P ≤ N := le_inf P.le_normalizer hPT
  obtain ⟨z, hzP, hz2, hNz⟩ := exists_involution_centralized hP hPN inf_le_left hN2
  have hND : N ≤ D := hNz.trans (hD z (hPD hzP) hz2)
  have hNP : N = P := (Subgroup.eq_of_le_of_card_ge hPN (hmax N hN2 hND)).symm
  have : Group.IsNilpotent T := T.isPGroup'.isNilpotent
  have hself : Subgroup.normalizer ((P.subgroupOf T : Subgroup T) : Set T) = P.subgroupOf T := by
    rw [← Subgroup.subgroupOf_normalizer_eq hPT]
    ext x
    simp only [Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have : (x : G) ∈ N := ⟨hx, x.2⟩
      rwa [hNP] at this
    · exact fun hx => P.le_normalizer hx
  have htop := normalizerCondition_iff_only_full_group_self_normalizing.1
    Group.normalizerCondition_of_isNilpotent _ hself
  exact le_antisymm (Subgroup.subgroupOf_eq_top.1 htop) hPT

omit [Finite G] in
theorem centralizer_le_inf {M : Subgroup G}
    (hC : ∀ t ∈ M, orderOf t = 2 → Subgroup.centralizer {t} ≤ M) (g : G) :
    ∀ u ∈ M ⊓ M.map (MulAut.conj g).toMonoidHom, orderOf u = 2 →
      Subgroup.centralizer {u} ≤ M ⊓ M.map (MulAut.conj g).toMonoidHom := by
  rintro u ⟨huM, hug⟩ hu2 x hx
  refine ⟨hC u huM hu2 hx, ?_⟩
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hug
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hx hu2 ⊢
  have hm2 : orderOf m = 2 := by
    rw [← MulEquiv.orderOf_eq (MulAut.conj g) m, MulAut.conj_apply]
    exact hu2
  have hx' : g⁻¹ * x * g ∈ Subgroup.centralizer {m} := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    calc g⁻¹ * x * g * m = g⁻¹ * (x * (g * m * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * m * g⁻¹) * x) * g := by rw [hx]
      _ = m * (g⁻¹ * x * g) := by group
  exact Subgroup.mem_map.2 ⟨_, hC m hm hm2 hx', by simp [mul_assoc]⟩

end StrongEmbedding

open StrongEmbedding

theorem isStronglyEmbeddedOrder_of_centralizer_le {G : Type*} [Group G] [Finite G]
    {M : Subgroup G} (hM : M ≠ ⊤) (heven : Even (Nat.card M))
    (hC : ∀ t ∈ M, orderOf t = 2 → Subgroup.centralizer {t} ≤ M)
    (S : Sylow 2 G) (hN : Subgroup.normalizer (S : Set G) ≤ M) :
    CFSG.BenderSuzuki.IsStronglyEmbeddedOrder M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hM, heven, fun g hg => ?_⟩
  set D := M ⊓ M.map (MulAut.conj g).toMonoidHom with hDdef
  by_contra hodd
  have hDeven : 2 ∣ Nat.card D := (Nat.not_odd_iff_even.1 hodd).two_dvd
  have hD := centralizer_le_inf hC g
  obtain ⟨P, ⟨hP2, hPD⟩, hmax⟩ := Set.exists_max_image
    {Q : Subgroup G | IsPGroup 2 Q ∧ Q ≤ D} (fun Q => Nat.card Q) (Set.toFinite _)
    ⟨⊥, IsPGroup.of_bot, bot_le⟩
  have hP : P ≠ ⊥ := by
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 hDeven
    have hu2 : orderOf (u : G) = 2 := by rw [Subgroup.orderOf_coe, hu]
    have hZ : IsPGroup 2 (Subgroup.zpowers (u : G)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu2, pow_one])
    have := hmax _ ⟨hZ, Subgroup.zpowers_le.2 u.2⟩
    rw [Nat.card_zpowers, hu2] at this
    intro hbot
    rw [hbot, Subgroup.card_bot] at this
    omega
  obtain ⟨T, hT⟩ := exists_sylow_eq hD hP2 hPD hP fun Q hQ hQD => hmax Q ⟨hQ, hQD⟩
  have hTM : (T : Subgroup G) ≤ M := hT ▸ hPD.trans inf_le_left
  have hTg : (T : Subgroup G) ≤ M.map (MulAut.conj g).toMonoidHom := hT ▸ hPD.trans inf_le_right
  have hTM' : ((g⁻¹ • T : Sylow 2 G) : Subgroup G) ≤ M := by
    change (T : Subgroup G).map (MulAut.conj g⁻¹).toMonoidHom ≤ M
    rw [Subgroup.map_le_iff_le_comap]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 (hTg hx)
    simpa [mul_assoc] using hy
  have hSM : (S : Subgroup G) ≤ M := S.le_normalizer.trans hN
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M (T.subtype hTM) (S.subtype hSM)
  obtain ⟨m', hm'⟩ := MulAction.exists_smul_eq M ((g⁻¹ • T).subtype hTM') (S.subtype hSM)
  rw [Sylow.smul_subtype] at hm hm'
  have e₁ : (m : G) • T = S := Sylow.subtype_injective hm
  have e₂ : (m' : G) • g⁻¹ • T = S := Sylow.subtype_injective hm'
  have h₃ : ((m : G) * g * (m' : G)⁻¹) • S = S := by
    calc ((m : G) * g * (m' : G)⁻¹) • S = (m : G) • g • (m' : G)⁻¹ • S := by
          rw [mul_smul, mul_smul]
      _ = (m : G) • g • (m' : G)⁻¹ • ((m' : G) • g⁻¹ • T) := by rw [e₂]
      _ = S := by rw [inv_smul_smul, smul_inv_smul, e₁]
  have h₄ : (m : G) * g * (m' : G)⁻¹ ∈ M := hN (Sylow.smul_eq_iff_mem_normalizer.1 h₃)
  apply hg
  have := M.mul_mem (M.mul_mem (M.inv_mem m.2) h₄) m'.2
  simpa [mul_assoc] using this

theorem isStronglyEmbeddedOrder_of_centralizer_le_of_unique {G : Type*} [Group G] [Finite G]
    {M : Subgroup G} (hM : M ≠ ⊤)
    (hC : ∀ t ∈ M, orderOf t = 2 → Subgroup.centralizer {t} ≤ M)
    (S : Sylow 2 G) (hSM : (S : Subgroup G) ≤ M) {z : G} (hzS : z ∈ (S : Subgroup G))
    (hz : orderOf z = 2) (hzc : ∀ s ∈ (S : Subgroup G), z * s = s * z)
    (huniq : ∀ x ∈ (S : Subgroup G), orderOf x = 2 → (∀ s ∈ (S : Subgroup G), x * s = s * x) →
      x = z) :
    CFSG.BenderSuzuki.IsStronglyEmbeddedOrder M := by
  have heven : Even (Nat.card M) := by
    rw [even_iff_two_dvd, ← hz, ← Subgroup.orderOf_mk z (hSM hzS)]
    exact orderOf_dvd_natCard _
  refine isStronglyEmbeddedOrder_of_centralizer_le hM heven hC S fun n hn => ?_
  have hn' := Subgroup.mem_normalizer_iff.1 hn
  have hn'' := Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (S : Set G)).inv_mem hn)
  have hconj : n * z * n⁻¹ = z := by
    refine huniq _ ((hn' z).1 hzS) ?_ fun s hs => ?_
    · rw [← MulEquiv.orderOf_eq (MulAut.conj n) z, MulAut.conj_apply] at hz
      exact hz
    · have hs' : n⁻¹ * s * n ∈ (S : Subgroup G) := by simpa using (hn'' s).1 hs
      have := hzc _ hs'
      calc n * z * n⁻¹ * s = n * (z * (n⁻¹ * s * n)) * n⁻¹ := by group
        _ = n * ((n⁻¹ * s * n) * z) * n⁻¹ := by rw [this]
        _ = s * (n * z * n⁻¹) := by group
  refine hC z (hSM hzS) hz (Subgroup.mem_centralizer_singleton_iff.2 ?_)
  calc n * z = n * z * n⁻¹ * n := by group
    _ = z * n := by rw [hconj]

end CFSG.Monster.B.Recog
