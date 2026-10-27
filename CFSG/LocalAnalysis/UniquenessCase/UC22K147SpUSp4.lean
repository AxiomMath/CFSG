module

import CFSG.LocalAnalysis.UniquenessCase.UC22K147SpUSp4Inv
import CFSG.LocalAnalysis.UniquenessCase.UC22K147SpUSp4Grp
import CFSG.LocalAnalysis.UniquenessCase.UC22K147Excl
import CFSG.LocalAnalysis.UniquenessCase.UC22K148Vocab
import CFSG.LocalAnalysis.RankThreeUC.Section5.InvariantElemAbelianFixed
import CFSG.LinearAlgebra.CoprimeActions.InvolutionDimensionBounds
import CFSG.Timmesfeld.Orders.Bang
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpOuter
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bLower
public import CFSG.LocalAnalysis.UniquenessCase.UC22Lie
public import CFSG.LocalAnalysis.UniquenessCase.UCFront05

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K147SpU

open Subgroup
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.QuasithinUnique.Setup CFSG.LinearAlgebra.CoprimeActions

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem range_mul_le_sup (ρ : Representation (ZMod 2) G V) (a b : G) :
    LinearMap.range ((ρ (a * b) : V →ₗ[ZMod 2] V) - 1) ≤
      LinearMap.range ((ρ a : V →ₗ[ZMod 2] V) - 1) ⊔ LinearMap.range ((ρ b : V →ₗ[ZMod 2] V) - 1) := by
  rintro _ ⟨v, rfl⟩
  have h : ((ρ (a * b) : V →ₗ[ZMod 2] V) - 1) v =
      ((ρ a : V →ₗ[ZMod 2] V) - 1) (ρ b v) + ((ρ b : V →ₗ[ZMod 2] V) - 1) v := by
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_mul, Module.End.mul_apply]
    abel
  rw [h]
  exact Submodule.add_mem_sup ⟨_, rfl⟩ ⟨_, rfl⟩

theorem finrank_range_conj (ρ : Representation (ZMod 2) G V) (a l : G) :
    Module.finrank (ZMod 2) (LinearMap.range ((ρ (l⁻¹ * a * l) : V →ₗ[ZMod 2] V) - 1)) =
      Module.finrank (ZMod 2) (LinearMap.range ((ρ a : V →ₗ[ZMod 2] V) - 1)) := by
  have h : LinearMap.range ((ρ (l⁻¹ * a * l) : V →ₗ[ZMod 2] V) - 1) =
      (LinearMap.range ((ρ a : V →ₗ[ZMod 2] V) - 1)).map
        (InvolutionDimensionBounds.toEquivHom ρ l⁻¹ : V →ₗ[ZMod 2] V) := by
    ext w
    simp only [LinearMap.mem_range, Submodule.mem_map, LinearMap.sub_apply, Module.End.one_apply,
      LinearEquiv.coe_coe, InvolutionDimensionBounds.toEquivHom_apply, map_mul, Module.End.mul_apply]
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨ρ a (ρ l v) - ρ l v, ⟨ρ l v, rfl⟩, by rw [map_sub, Representation.inv_self_apply]⟩
    · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
      exact ⟨ρ l⁻¹ u, by rw [map_sub, Representation.self_inv_apply]⟩
  rw [h, LinearEquiv.finrank_map_eq]

theorem four_mul_le_of_commute [Finite G] [Finite V] (ρ : Representation (ZMod 2) G V)
    (hρ : Function.Injective ρ) (hirr : ρ.IsIrreducible) {L : Subgroup G} (hLn : L.Normal) {n : ℕ}
    (hSp : IsSp4 ↥L n) {t : G} (ht1 : t ≠ 1) (hc : ∀ x ∈ L, t * x = x * t) :
    4 * n ≤ Module.finrank (ZMod 2) (LinearMap.range ((ρ t : V →ₗ[ZMod 2] V) - 1)) := by
  obtain ⟨hn, K, _, _, _, hK, ⟨e⟩⟩ := K148.exists_antiSp_of_isSp4 hSp
  haveI : IsSimpleGroup ↥L := K148.isSimpleGroup_of_isSp4 hSp
  obtain ⟨ℓ, hppd⟩ :=
    CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor (k := 4 * n) (by omega) (by omega)
  have hℓ : ℓ.Prime := hppd.prime
  have hℓ2 : ℓ ≠ 2 := hppd.ne_two (by omega)
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hord : 4 * n ≤ orderOf (2 : ZMod ℓ) := by
    have h2pow : (2 : ZMod ℓ) ^ (4 * n) = 1 :=
      (CFSG.Timmesfeld.Bang.dvd_two_pow_sub_one_iff (4 * n)).mp hppd.dvd
    have hpos : 0 < orderOf (2 : ZMod ℓ) :=
      orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨4 * n, by omega, h2pow⟩)
    exact Nat.le_of_dvd hpos ((hppd.dvd_sub_one_iff (by omega) _).mp
      ((CFSG.Timmesfeld.Bang.dvd_two_pow_sub_one_iff _).mpr (pow_orderOf_eq_one _)))
  have hdvd : ℓ ∣ Nat.card ↥L := by
    rw [Nat.card_congr e.toEquiv, card_antiSp hK,
      show (2 ^ n) ^ 4 - 1 = 2 ^ (4 * n) - 1 by rw [← pow_mul, mul_comm]]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_left hppd.dvd _) _
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' ℓ hdvd
  have hxℓ : orderOf (x : G) = ℓ := by rw [Subgroup.orderOf_coe, hx]
  set W : Submodule (ZMod 2) V := LinearMap.range ((ρ t : V →ₗ[ZMod 2] V) - 1) with hWdef
  have hWinv : ∀ c ∈ L, ∀ w ∈ W, ρ c w ∈ W := by
    rintro c hcL _ ⟨v, rfl⟩
    refine ⟨ρ c v, ?_⟩
    have h1 : ρ t (ρ c v) = ρ c (ρ t v) := by
      rw [← Module.End.mul_apply, ← map_mul, hc c hcL, map_mul, Module.End.mul_apply]
    simp [h1]
  have hne : ∃ w ∈ W, ρ (x : G) w ≠ w := by
    by_contra hcon
    push Not at hcon
    let N : Subgroup ↥L := (Excl147.ptStab ρ W).comap L.subtype
    have hmemN : ∀ y : ↥L, y ∈ N ↔ ∀ w ∈ W, ρ (y : G) w = w := fun y => Iff.rfl
    haveI hN : N.Normal := ⟨fun a ha b => (hmemN _).2 fun w hw => by
      have hb' : ρ ((b : G)⁻¹) w ∈ W := hWinv _ (inv_mem b.2) w hw
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul, Module.End.mul_apply,
        Module.End.mul_apply, (hmemN a).1 ha _ hb', Representation.self_inv_apply]⟩
    have hxN : x ∈ N := (hmemN x).2 hcon
    have hNtop : N = ⊤ := (IsSimpleGroup.eq_bot_or_eq_top_of_normal N).resolve_left fun hbot => by
      rw [hbot, Subgroup.mem_bot] at hxN
      rw [hxN, orderOf_one] at hx
      exact hℓ.one_lt.ne hx
    have hfix : ∀ y ∈ L, ∀ w ∈ W, ρ y w = w := fun y hy =>
      (hmemN ⟨y, hy⟩).1 (by rw [hNtop]; exact Subgroup.mem_top _)
    have hL1 : L ≠ ⊥ := by
      intro hbot
      have hx1 : (x : G) = 1 := (Subgroup.eq_bot_iff_forall L).mp hbot _ x.2
      rw [hx1, orderOf_one] at hxℓ
      exact hℓ.one_lt.ne hxℓ
    have htop := CFSG.LocalAnalysis.RankThreeUC.Section5.InvariantElemAbelianFixed.commSpace_eq_top_of_normal
      hρ hirr hLn hL1
    have hker : CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.commSpace ρ L ≤
        LinearMap.ker ((ρ t : V →ₗ[ZMod 2] V) - 1) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨y, hy, v, rfl⟩
      have h1 : ρ t (ρ y v) = ρ y (ρ t v) := by
        rw [← Module.End.mul_apply, ← map_mul, hc y hy, map_mul, Module.End.mul_apply]
      have hw : ρ t v - v ∈ W := ⟨v, by simp⟩
      have h2 : ρ y (ρ t v - v) = ρ t v - v := hfix y hy _ hw
      rw [map_sub, sub_eq_iff_eq_add] at h2
      show ((ρ t : V →ₗ[ZMod 2] V) - 1) (ρ y v - v) = 0
      rw [LinearMap.sub_apply, Module.End.one_apply, map_sub, h1, h2]
      abel
    apply ht1
    apply hρ
    rw [map_one]
    refine LinearMap.ext fun v => ?_
    have hv : v ∈ LinearMap.ker ((ρ t : V →ₗ[ZMod 2] V) - 1) := hker (by rw [htop]; exact Submodule.mem_top)
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv
    exact hv
  have := Excl147.orderOf_two_le_finrank_of_stable ρ hℓ hℓ2 hxℓ W (hWinv x x.2)
    (hWinv _ (inv_mem x.2)) hne
  omega

theorem sp4_lt_mGV [Finite G] [Finite V] (ρ : Representation (ZMod 2) G V) (hρ : Function.Injective ρ)
    (hirr : ρ.IsIrreducible) {L : Subgroup G} (hLn : L.Normal) {n : ℕ} (hn3 : 3 ≤ n) (hodd : Odd n)
    (hSp : IsSp4 ↥L n) {g : G} (hg : ActsNontrivOnDiagramIn L g) : n + 1 < F05.mGV ρ := by
  obtain ⟨-, K, _, _, _, -, ⟨e⟩⟩ := K148.exists_antiSp_of_isSp4 hSp
  have hev : ∃ t : G, orderOf t = 2 := by
    refine ⟨(e.symm (X7b.lowUSp 0 1 0 1) : G), ?_⟩
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact orderOf_eq_prime (by rw [sq]; exact lowUSp_zero_one_zero_one_mul_self)
      lowUSp_zero_one_zero_one_ne_one
  have key : ∀ t : G, orderOf t = 2 →
      n + 2 ≤ Module.finrank (ZMod 2) (LinearMap.range ((ρ t : V →ₗ[ZMod 2] V) - 1)) := by
    intro t ht
    obtain ⟨htt, ht1⟩ := Excl147.mul_self_and_ne_one ht
    by_cases hc : ∀ x ∈ L, t * x = x * t
    · have := four_mul_le_of_commute ρ hρ hirr hLn hSp ht1 hc
      omega
    · push Not at hc
      have htN : t ∈ normalizer (L : Set G) := mem_normalizer_iff.mpr fun h =>
        ⟨fun hh => hLn.conj_mem h hh t, fun hh => by
          have := hLn.conj_mem _ hh t⁻¹
          rwa [show t⁻¹ * (t * h * t⁻¹) * t⁻¹⁻¹ = h by group] at this⟩
      obtain ⟨l, -, hyL, hy1, hy2⟩ := exists_mul_conj_involution hSp hodd htN htt hc
      have h3 := three_mul_le_finrank_range_of_diagram ρ hρ hSp hg hyL hy2 hy1
      have h4 := Submodule.finrank_mono (range_mul_le_sup ρ t (l⁻¹ * t * l))
      have h5 := Submodule.finrank_add_le_finrank_add_finrank
        (LinearMap.range ((ρ t : V →ₗ[ZMod 2] V) - 1))
        (LinearMap.range ((ρ (l⁻¹ * t * l) : V →ₗ[ZMod 2] V) - 1))
      rw [finrank_range_conj] at h5
      omega
  have := Excl147.le_mGV ρ (k := n + 2) hev fun t ht => by
    rw [Excl147.finrank_quotient_fixSub_eq ρ ht,
      InvolutionDimensionBounds.commSpace_zpowers_eq_range ρ t
        (orderOf_pos_iff.mp (by omega))]
    exact key t ht
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC22.K147SpU
