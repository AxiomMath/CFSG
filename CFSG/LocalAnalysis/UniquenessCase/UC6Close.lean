module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S18
public import CFSG.LocalAnalysis.UniquenessCase.UC6Zgrp
public import CFSG.RankThree.Transfer.Yoshida
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.GroupTheory.PCore.Transport
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.theorem_3_6
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection5.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection6.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.ABGLocalTools

theorem not_commutative_wreath {q : ℕ} (hq : q.Prime) :
    ∃ a b : Multiplicative (ZMod q) ≀ᵣ Multiplicative (ZMod q), a * b ≠ b * a := by
  haveI : Fact q.Prime := ⟨hq⟩
  let f : Multiplicative (ZMod q) → Multiplicative (ZMod q) :=
    fun x => if x = 1 then Multiplicative.ofAdd (1 : ZMod q) else 1
  let a : Multiplicative (ZMod q) ≀ᵣ Multiplicative (ZMod q) := ⟨f, 1⟩
  let b : Multiplicative (ZMod q) ≀ᵣ Multiplicative (ZMod q) := ⟨1, Multiplicative.ofAdd (1 : ZMod q)⟩
  refine ⟨a, b, fun h => ?_⟩
  have h1 := congrFun (congrArg RegularWreathProduct.left h) 1
  have hne : (Multiplicative.ofAdd (1 : ZMod q) : Multiplicative (ZMod q)) ≠ 1 := by
    intro h0
    exact one_ne_zero (α := ZMod q) (Multiplicative.ofAdd.injective h0)
  have hne' : (Multiplicative.ofAdd (1 : ZMod q))⁻¹ ≠ (1 : Multiplicative (ZMod q)) := by
    intro h0
    exact hne (inv_eq_one.1 h0)
  simp only [a, b, f, RegularWreathProduct.mul_left, Pi.mul_apply, Pi.one_apply, inv_one,
    one_mul, mul_one, if_true, mul_inv_cancel] at h1
  split_ifs at h1 with hh
  · exact hne' hh
  · exact hne h1

theorem isEmpty_wreath_of_isCyclic {q : ℕ} (hq : q.Prime) {P : Type*} [Group P] [IsCyclic P]
    (N : Subgroup P) [N.Normal] :
    IsEmpty ((P ⧸ N) ≃* (Multiplicative (ZMod q) ≀ᵣ Multiplicative (ZMod q))) := by
  refine ⟨fun e => ?_⟩
  haveI : IsCyclic (P ⧸ N) :=
    isCyclic_of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  obtain ⟨a, b, hab⟩ := not_commutative_wreath hq
  apply hab
  have hc : ∀ x y : P ⧸ N, x * y = y * x := fun x y => by
    letI := IsCyclic.commGroup (α := P ⧸ N)
    exact mul_comm x y
  have h2 := congrArg e (hc (e.symm a) (e.symm b))
  simpa using h2

theorem eq_of_card_eq_of_isCyclic {G : Type*} [Group G] [Finite G] {Q Y Y' : Subgroup G}
    (hQ : IsCyclic Q) (hY : Y ≤ Q) (hY' : Y' ≤ Q) (h : Nat.card Y = Nat.card Y') : Y = Y' := by
  have h1 : Y.subgroupOf Q = Y'.subgroupOf Q := by
    refine (IsCyclic.subgroup_eq_iff_card_eq (H := Y.subgroupOf Q) (K := Y'.subgroupOf Q)).2 ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY').toEquiv]
    exact h
  rw [Subgroup.subgroupOf_inj, inf_of_le_left hY, inf_of_le_left hY'] at h1
  exact h1

theorem false_of_zgroup_control {G : Type} [Group G] [Finite G] {K X Q Y : Subgroup G} {q : ℕ}
    (hq : q.Prime) (hXK : X ≤ K) (hQ : IsSylowOf q Q X) (hQcyc : IsCyclic Q) (hYQ : Y ≤ Q)
    (hYcard : Nat.card Y = q) (hcontrol : normalizer (Y : Set G) ⊓ K ≤ X)
    (hQnot : ¬ Q ≤ (commutator ↥X).map X.subtype)
    (hK : ∀ (N : Subgroup ↥K) [N.Normal], IsPGroup q (↥K ⧸ N) → N = ⊤) : False := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hQp : IsPGroup q Q := hQ.isPGroup
  have hQX : Q ≤ X := hQ.le
  have hQK : Q ≤ K := hQX.trans hXK
  have hNQ : ∀ n : G, n ∈ normalizer (Q : Set G) → n ∈ normalizer (Y : Set G) := by
    intro n hn
    set Y' : Subgroup G := Y.map (MulAut.conj n).toMonoidHom with hY'
    have hY'Q : Y' ≤ Q := by
      rintro _ ⟨y, hy, rfl⟩
      have := (mem_normalizer_iff.1 hn y).1 (hYQ hy)
      simpa using this
    have hY'card : Nat.card Y' = Nat.card Y :=
      Subgroup.card_map_of_injective (MulAut.conj n).injective
    have hYY' : Y = Y' := eq_of_card_eq_of_isCyclic hQcyc hYQ hY'Q hY'card.symm
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have : n * x * n⁻¹ ∈ Y' := ⟨x, hx, by simp⟩
      rwa [← hYY'] at this
    · intro hx
      rw [hYY'] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have hyx' : n * y * n⁻¹ = n * x * n⁻¹ := hyx
      have hyxeq : y = x := by simpa using hyx'
      exact hyxeq ▸ hy
  have hNQK : ∀ n ∈ K, n ∈ normalizer (Q : Set G) → n ∈ X := fun n hnK hnQ =>
    hcontrol ⟨hNQ n hnQ, hnK⟩
  have hQsyl : IsSylowOf q Q K := by
    obtain ⟨S, hS, hQS⟩ := exists_isSylowOf_ge hQK hQp
    by_cases hSQ : Q = S
    · rw [hSQ]; exact hS
    · exfalso
      have hlt : Q < S := lt_of_le_of_ne hQS hSQ
      have hN : Q < S ⊓ normalizer (Q : Set G) :=
        CFSG.RankThreeCoreUniqueness.Helpers.pGroup_proper_subgroup_lt_internal_normalizer q hq S Q
          hS.isPGroup hlt
      have hNX : S ⊓ normalizer (Q : Set G) ≤ X := fun n hn => hNQK n (hS.le hn.1) hn.2
      have := hQ.eq_of_le hN.le hNX hS.isPGroup.to_inf_left
      exact hN.ne this.symm
  obtain ⟨P, hP⟩ := hQsyl
  have hPcyc : IsCyclic ↥(P : Subgroup ↥K) := by
    have e : (P : Subgroup ↥K) ≃* Q := by
      have := Subgroup.equivMapOfInjective (P : Subgroup ↥K) K.subtype K.subtype_injective
      rw [hP] at this
      exact this
    exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  have hW : ∀ (N : Subgroup (P : Subgroup ↥K)) [N.Normal],
      IsEmpty ((↥(P : Subgroup ↥K) ⧸ N) ≃*
        (Multiplicative (ZMod q) ≀ᵣ Multiplicative (ZMod q))) := fun N _ =>
    isEmpty_wreath_of_isCyclic hq N
  have hY := (CFSG.RankThree.Transfer.yoshida_transfer_toolkit_form ↥K q hq P hW).2 hK
  apply hQnot
  intro a ha
  rw [← hP] at ha
  obtain ⟨a', ha', rfl⟩ := ha
  have hle : ⁅(P : Subgroup ↥K), normalizer ((P : Subgroup ↥K) : Set ↥K)⁆ ≤
      ((commutator ↥X).map X.subtype).subgroupOf K := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    have h1 : (g₁ : G) ∈ Q := by rw [← hP]; exact ⟨g₁, hg₁, rfl⟩
    have h2 : (g₂ : G) ∈ normalizer (Q : Set G) := by
      rw [← hP]; exact coe_mem_normalizer_map_subtype hg₂
    have h3 : (g₂ : G) ∈ X := hNQK _ g₂.2 h2
    rw [Subgroup.mem_subgroupOf]
    have hcm : (⟨(g₁ : G), hQX h1⟩ : ↥X) * (⟨(g₂ : G), h3⟩ : ↥X) * (⟨(g₁ : G), hQX h1⟩ : ↥X)⁻¹ *
        (⟨(g₂ : G), h3⟩ : ↥X)⁻¹ ∈ commutator ↥X := by
      rw [commutator_def]
      have := Subgroup.commutator_mem_commutator
        (Subgroup.mem_top (⟨(g₁ : G), hQX h1⟩ : ↥X)) (Subgroup.mem_top (⟨(g₂ : G), h3⟩ : ↥X))
      simpa [commutatorElement_def] using this
    exact ⟨_, hcm, by simp [commutatorElement_def]⟩
  exact hle (hY.le ha')

end CFSG.LocalAnalysis.UniquenessCase.UC6
