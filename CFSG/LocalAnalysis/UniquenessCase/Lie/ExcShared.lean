module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20o
import CFSG.LocalAnalysis.UniquenessCase.Lie.BorelSL

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

theorem uc22pwex_borelWit_of_equiv {G C : Type} [Group G] [Finite G] [Group C] (e : G ≃* C)
    {p k : ℕ} (U : Subgroup C) (hU : IsPGroup 2 U) (hidx : ¬ 2 ∣ U.index) (F : Subgroup C)
    (hF : F ≤ normalizer (U : Set C)) (hFe : IsElemAbelian p F) (hc : Nat.card F = p ^ k) :
    uc22p20oBorelWit G p k := by
  haveI : Finite C := Finite.of_equiv G e.toEquiv
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU' : IsPGroup 2 (U.map e.symm.toMonoidHom) := hU.map _
  have hidx' : ¬ 2 ∣ (U.map e.symm.toMonoidHom).index := by
    rw [Subgroup.index_map_of_bijective e.symm.bijective]
    exact hidx
  refine uc22pwlie_borelWit_of_sylow (hU'.toSylow hidx') (F.map e.symm.toMonoidHom) ?_
    (uc22p20d_isElemAbelian_map _ e.symm.injective hFe)
    (by rw [Subgroup.card_map_of_injective e.symm.injective, hc])
  show F.map e.symm.toMonoidHom ≤ normalizer ((U.map e.symm.toMonoidHom : Subgroup G) : Set G)
  exact (Subgroup.map_mono hF).trans (Subgroup.map_equiv_normalizer_eq U e.symm).le

theorem uc22pwex_rankWit_of_equiv {G C : Type} [Group G] [Group C] (e : G ≃* C) {p k : ℕ}
    (E : Subgroup C) (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ k) : uc22p20oRankWit G p k :=
  ⟨E.map e.symm.toMonoidHom, uc22p20d_isElemAbelian_map _ e.symm.injective hE,
    by rw [Subgroup.card_map_of_injective e.symm.injective, hc]⟩

theorem uc22pwex_elemAbelian_range {A C : Type} [Group A] [Finite A] [Group C] {p k : ℕ}
    (Ψ : A →* C) (hΨ : Function.Injective Ψ) (hcomm : ∀ a b : A, a * b = b * a)
    (hpow : ∀ a : A, a ^ p = 1) (hA : Nat.card A = p ^ k) :
    IsElemAbelian p Ψ.range ∧ Nat.card Ψ.range = p ^ k := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · refine IsMulCommutative.of_setLike_mul_comm fun x hx y hy => ?_
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    rw [← map_mul, ← map_mul, hcomm]
  · rintro _ ⟨a, rfl⟩
    rw [← map_pow, hpow, map_one]
  · rw [← hA]
    exact (Nat.card_congr (MonoidHom.ofInjective hΨ).toEquiv).symm

theorem uc22pwex_exists_mu {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hpK : p ∣ Nat.card K - 1) :
    ∃ μ : Subgroup Kˣ, Nat.card μ = p ∧ ∀ x : μ, (x : Kˣ) ^ p = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h1 : p ∣ Nat.card Kˣ := by rwa [Nat.card_units]
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p h1
  refine ⟨Subgroup.zpowers g, by rw [Nat.card_zpowers, hg], ?_⟩
  rintro ⟨x, hx⟩
  obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  show (g ^ z) ^ p = 1
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hg, pow_orderOf_eq_one,
    one_zpow]

theorem uc22pwex_mem_normalizer_subgroupOf {M : Type} [Group M] {C U : Subgroup M} {x : C}
    (hx : (x : M) ∈ normalizer (U : Set M)) :
    x ∈ normalizer ((U.subgroupOf C : Subgroup C) : Set C) := by
  rw [mem_normalizer_iff] at hx ⊢
  intro y
  exact hx (y : M)

theorem uc22pwex_charP_two {K : Type} [Field K] [Finite K] {m : ℕ} (h : Nat.card K = 2 ^ m) :
    CharP K 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := Fintype.ofFinite K
  exact charP_of_card_eq_prime_pow (f := m) (by rw [← Nat.card_eq_fintype_card, h])

theorem uc22pwex_equiv_quot_of_center_eq_bot {K : Type} [Group K] (h : center K = ⊥) :
    Nonempty (K ≃* K ⧸ center K) :=
  ⟨((QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot).symm⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
