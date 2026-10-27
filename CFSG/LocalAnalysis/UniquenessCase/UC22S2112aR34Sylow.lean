module

import CFSG.Milestones.ASVolI.A3OddFacts
import CFSG.LocalAnalysis.WeakClosure81.TwelveThreeA
import CFSG.ClassicalInvolution.ModelFacts.FundamentalSL2All
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.FundamentalLie
public import CFSG.LocalAnalysis.UniquenessCase.UCFront14
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open scoped MatrixGroups
open CFSG.LocalAnalysis.UniquenessCase.UC22.F14 (FunSet)
open CFSG.ClassicalInvolution.ModelFacts
  (nonempty_equiv_sl2_galoisField_of_mem_fundamentalSubgroups)

theorem uc22s2112r34_psl2_orderOf_eq_three_pow {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (he : 1 ≤ e) {S : Subgroup PSL(2, GaloisField p e)}
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) {y : PSL(2, GaloisField p e)}
    (hy : y ∈ normalizer (S : Set PSL(2, GaloisField p e))) (hodd : Odd (orderOf y)) :
    ∃ k : ℕ, orderOf y = 3 ^ k := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hk
  have hcard : Nat.card (zpowers y) = orderOf y := Nat.card_zpowers y
  have hle : zpowers y ≤ normalizer (S : Set PSL(2, GaloisField p e)) := zpowers_le.2 hy
  have hcfg : CFSG.ASVolI.burnsideA315x_Config _ S (zpowers y) := by
    refine ⟨hS, by rw [hcard]; exact hodd, fun h3 => ?_, Or.inl inferInstance, ?_⟩
    · obtain ⟨k, h⟩ := IsPGroup.iff_card.1 h3
      exact hk ⟨k, hcard ▸ h⟩
    · rw [← coe_mul_of_left_le_normalizer_right _ _ hle,
        ← coe_mul_of_right_le_normalizer_left _ _ hle, sup_comm]
  obtain ⟨-, -, s, hs, hinv⟩ := CFSG.ASVolI.burnsideA315x_l2_core hp2 he hcfg
  have h1 : y = 1 := CFSG.LocalAnalysis.WeakClosure81.eq_one_of_inverted_of_mem_normalizer
    hS.2.1 hs hy (hinv y (mem_zpowers y)) hodd
  exact hk ⟨0, by rw [h1, orderOf_one, pow_zero]⟩

theorem uc22s2112r34_orderOf_eq_three_pow_of_sl2 {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (he : 1 ≤ e) {X : Type} [Group X] [Finite X] (φ : SL(2, GaloisField p e) →* X)
    (hker : φ.ker ≤ center SL(2, GaloisField p e)) {Q : Subgroup X}
    (hQ : CFSG.ABGLocalTools.IsSylowOf 2 Q φ.range) {x : X} (hx : x ∈ φ.range)
    (hxN : x ∈ normalizer (Q : Set X)) (hodd : Odd (orderOf x)) :
    ∃ k : ℕ, orderOf x = 3 ^ k := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hQ2, hQi⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1 hQ
  have hsq : ∀ z ∈ center SL(2, GaloisField p e), z ^ 2 = 1 := fun z hz => by
    rcases Matrix.SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one.1 hz with rfl | rfl
    · exact one_pow 2
    · rw [sq, neg_mul_neg, mul_one]
  obtain ⟨g₀, rfl⟩ := hx
  obtain ⟨j, hj⟩ := hodd
  have hx1 : φ g₀ ^ orderOf (φ g₀) = 1 := pow_orderOf_eq_one _
  have hc : g₀ ^ orderOf (φ g₀) ∈ center SL(2, GaloisField p e) :=
    hker (by rw [MonoidHom.mem_ker, map_pow, hx1])
  have hg₀ : g₀ ^ (orderOf (φ g₀) * 2) = 1 := by rw [pow_mul, hsq _ hc]
  set g := g₀ ^ (orderOf (φ g₀) + 1) with hgdef
  have hφg : φ g = φ g₀ := by rw [hgdef, map_pow, pow_succ, hx1, one_mul]
  have hgm : g ^ orderOf (φ g₀) = 1 := by
    have h : (orderOf (φ g₀) + 1) * orderOf (φ g₀) = orderOf (φ g₀) * 2 * (j + 1) := by
      rw [hj]; ring
    rw [hgdef, ← pow_mul, h, pow_mul, hg₀, one_pow]
  set Q' : Subgroup SL(2, GaloisField p e) := Q.comap φ with hQ'
  set π := QuotientGroup.mk' (center SL(2, GaloisField p e)) with hπ
  have hQ'2 : IsPGroup 2 Q' := by
    intro h
    obtain ⟨k, hk⟩ := hQ2 ⟨φ h, h.2⟩
    have hk' : φ ((h : SL(2, GaloisField p e)) ^ 2 ^ k) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hk
    refine ⟨k + 1, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, pow_succ, pow_mul, hsq _ (hker hk'), OneMemClass.coe_one]
  have hQ'i : ¬ 2 ∣ Q'.index := by
    have hcomap : Q' = (Q.subgroupOf φ.range).comap φ.rangeRestrict := by
      ext h
      simp [hQ', mem_subgroupOf]
    rw [hcomap, index_comap_of_surjective _ φ.rangeRestrict_surjective]
    exact hQi
  have hS : CFSG.QuasithinUnique.IsSylowTwoOf (Q'.map π) ⊤ := by
    refine ⟨le_top, hQ'2.map π, fun h2 => hQ'i (h2.trans ?_)⟩
    change (Q'.map π).relIndex ⊤ ∣ Q'.index
    rw [relIndex_top_right]
    exact index_map_dvd _ (QuotientGroup.mk'_surjective _)
  have hgN : g ∈ normalizer (Q' : Set SL(2, GaloisField p e)) := by
    rw [mem_normalizer_iff]
    intro h
    simp only [hQ', mem_comap, map_mul, map_inv, hφg]
    exact mem_normalizer_iff.1 hxN (φ h)
  have hyN : π g ∈ normalizer ((Q'.map π : Subgroup _) : Set PSL(2, GaloisField p e)) :=
    le_normalizer_map π (mem_map_of_mem π hgN)
  have hdvd : orderOf (π g) ∣ orderOf (φ g₀) :=
    (orderOf_map_dvd π g).trans (orderOf_dvd_of_pow_eq_one hgm)
  have hyodd : Odd (orderOf (π g)) := Odd.of_dvd_nat ⟨j, hj⟩ hdvd
  obtain ⟨k, hk⟩ := uc22s2112r34_psl2_orderOf_eq_three_pow hp2 he hS hyN hyodd
  have hgc : g ^ orderOf (π g) ∈ center SL(2, GaloisField p e) := by
    have h1 : π (g ^ orderOf (π g)) = 1 := by rw [map_pow]; exact pow_orderOf_eq_one _
    exact (QuotientGroup.eq_one_iff (N := center SL(2, GaloisField p e)) _).1 h1
  have h2d : orderOf (φ g₀) ∣ orderOf (π g) * 2 := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← hφg, ← map_pow, pow_mul, hsq _ hgc, map_one]
  have hcop : Nat.Coprime (orderOf (φ g₀)) 2 := Nat.coprime_two_right.2 ⟨j, hj⟩
  exact ⟨k, (Nat.dvd_antisymm (hcop.dvd_of_dvd_mul_right h2d) hdvd).trans hk⟩

section Fund


theorem uc22s2112r34_exists_sl2_cover {X : Type} [Group X] {q : ℕ} {K : Subgroup X}
    (hK : IsFundamentalOver q K) :
    ∃ (p e₀ e : ℕ) (_ : Fact p.Prime), p ≠ 2 ∧ 1 ≤ e₀ ∧ q = p ^ e₀ ∧ (e = e₀ ∨ e = 3 * e₀) ∧
      ∃ φ : SL(2, GaloisField p e) →* X, φ.range = K ∧ φ.ker ≤ center SL(2, GaloisField p e) := by
  obtain ⟨t, n, p, e₀, hp, hp2, hq, hfund, hadm, ψ, -, hψker, R, hR, rfl⟩ := hK
  have : Fact p.Prime := ⟨hp⟩
  have he₀ : 1 ≤ e₀ := hadm.2.1
  have key : ∀ {e : ℕ} (eR : ↥R ≃* SL(2, GaloisField p e)), ∃ φ : SL(2, GaloisField p e) →* X,
      φ.range = R.map ψ ∧ φ.ker ≤ center SL(2, GaloisField p e) := by
    intro e eR
    refine ⟨ψ.comp (R.subtype.comp eR.symm.toMonoidHom), ?_, ?_⟩
    · rw [MonoidHom.range_comp, MonoidHom.range_comp,
        MonoidHom.range_eq_top.2 eR.symm.surjective, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    · intro g hg
      have hz := hψker (MonoidHom.mem_ker.2 hg)
      rw [mem_center_iff]
      intro h
      apply eR.symm.injective
      apply Subtype.ext
      rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul]
      exact mem_center_iff.1 hz _
  rcases nonempty_equiv_sl2_galoisField_of_mem_fundamentalSubgroups hp2 hfund hadm hR with
    h | ⟨-, h⟩
  · obtain ⟨eR⟩ := h
    obtain ⟨φ, h1, h2⟩ := key eR
    exact ⟨p, e₀, e₀, inferInstance, hp2, he₀, hq, Or.inl rfl, φ, h1, h2⟩
  · obtain ⟨eR⟩ := h
    obtain ⟨φ, h1, h2⟩ := key eR
    exact ⟨p, e₀, 3 * e₀, inferInstance, hp2, he₀, hq, Or.inr rfl, φ, h1, h2⟩

theorem uc22s2112r34_orderOf_eq_three_pow_of_mem_funSet {X : Type} [Group X] [Finite X]
    {q : ℕ} {P K : Subgroup X} (hK : K ∈ FunSet (fundPred q) X P) {x : X} (hxK : x ∈ K)
    (hxP : x ∈ normalizer (P : Set X)) (hodd : Odd (orderOf x)) :
    ∃ k : ℕ, orderOf x = 3 ^ k := by
  obtain ⟨hfund, hsyl⟩ := hK
  obtain ⟨p, e₀, e, _, hp2, he₀, -, he, φ, hrange, hker⟩ := uc22s2112r34_exists_sl2_cover hfund
  have he1 : 1 ≤ e := by rcases he with rfl | rfl <;> omega
  have hxN : x ∈ normalizer ((P ⊓ K : Subgroup X) : Set X) := by
    rw [mem_normalizer_iff]
    intro h
    rw [mem_inf, mem_inf, mem_normalizer_iff.1 hxP h,
      mem_normalizer_iff.1 (le_normalizer hxK) h]
  subst hrange
  exact uc22s2112r34_orderOf_eq_three_pow_of_sl2 hp2 he1 φ hker hsyl hxK hxN hodd

end Fund

end CFSG.LocalAnalysis.UniquenessCase.UC22
