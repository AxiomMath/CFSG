module

public import CFSG.LocalAnalysis.WeakClosure81.W15SixE
public import CFSG.LocalAnalysis.WeakClosure81.W15SixC
public import CFSG.LocalAnalysis.WeakClosure81.TwelveSixC
public import CFSG.Goldschmidt.Steps.G2Grp
public import CFSG.GroupTheory.PCore.Transport
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.LocalAnalysis.WeakClosure81.FiveFourThree
public import CFSG.LocalAnalysis.WeakClosure81.FiveNineTwo
public import CFSG.Monster.Code.Weights
public import CFSG.Quasithin.Background.B2FactorizationOffender
public import CFSG.Quasithin.Background.B2FactorizationR2
public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Quasithin.Background.B2FactorizationSum
public import CFSG.Quasithin.Background.B4Statement
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.B6Offenders
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Quasithin.Background.F918P1
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11
open Subgroup
open scoped CFSG.Goldschmidt.G2 commutatorElement

theorem le_ker_of_isPGroup_map_of_odd_relIndex {H L : Type*} [Group H] [Finite H] [Group L]
    (φ : H →* L) {K₀ K : Subgroup H} (hK₀K : K₀ ≤ K) (hker : K₀ ≤ φ.ker)
    (hodd : Odd (K₀.relIndex K)) (h2 : IsPGroup 2 (K.map φ)) : K ≤ φ.ker := by
  let ψ : ↥K →* L := φ.comp K.subtype
  have hrange : ψ.range = K.map φ := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hψker : K₀.subgroupOf K ≤ ψ.ker := fun x hx => hker hx
  have hdvd : ψ.ker.index ∣ (K₀.subgroupOf K).index := Subgroup.index_dvd_of_le hψker
  have hcard : ψ.ker.index = Nat.card ψ.range := Subgroup.index_ker ψ
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite ↥(K.map φ) := by
    rw [← hrange]
    exact Finite.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 h2
  rw [← hrange] at hk
  have hk0 : k = 0 := by
    by_contra hk0
    have h2dvd : 2 ∣ K₀.relIndex K := by
      have h1 : 2 ∣ ψ.ker.index := by
        rw [hcard, hk]
        exact dvd_pow_self 2 hk0
      exact h1.trans hdvd
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2dvd)
  intro x hx
  have hcard1 : Nat.card ψ.range = 1 := by rw [hk, hk0, pow_zero]
  have hbot : ψ.range = ⊥ := (Subgroup.eq_bot_iff_card ψ.range).2 hcard1
  have hx1 : ψ ⟨x, hx⟩ = 1 := by
    have : ψ ⟨x, hx⟩ ∈ ψ.range := ⟨⟨x, hx⟩, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  exact hx1

private theorem kerIn_top_eq_normalCore' {Γ : Type*} [Group Γ] (K : Subgroup Γ) :
    CFSG.Quasithin.kerIn K ⊤ = K.normalCore := by
  ext x
  simp only [CFSG.Quasithin.kerIn, Subgroup.mem_mk, Subgroup.mem_top, forall_true_left,
    Subgroup.normalCore, Set.mem_setOf_eq]

variable {G : Type} [Group G] [Finite G]

namespace Cex156

variable {M V₀ V U S A X T : Subgroup G}

theorem card_A (h : Cex156 M V₀ V U S A X T) : Nat.card A = 2 ^ mSub V₀ := by
  obtain ⟨g, rfl⟩ := h.conj_A
  rw [E3.card_conjSubgroup]
  exact card_eq_two_pow_mSub h.cex.hyp.elemAbelian₀.isPGroup

theorem two_lt_relIndex (h : Cex156 M V₀ V U S A X T) : 2 < (A ⊓ kerMOf M X).relIndex A := by
  rw [h.inf_ker_eq_bot, Subgroup.relIndex_bot_left, h.card_A]
  calc 2 < 2 ^ 2 := by norm_num
    _ ≤ 2 ^ mSub V₀ := Nat.pow_le_pow_right (by norm_num) h.cex.one_lt_mSub

theorem setting12Two (h : Cex156 M V₀ V U S A X T) {n : ℕ}
    (hn : IsPSL 2 2 n (KerQuot M X) ∨ IsSz n (KerQuot M X)) :
    Setting12Two (A.subgroupOf X) (M.subgroupOf X) n where
  A_two := h.isElemAbelian_A.isPGroup.comap_subtype
  A_le_M := fun x hx => h.A_le_M hx
  M_ne := fun htop => h.min.toPairAt.not_le_M (Subgroup.subgroupOf_eq_top.1 htop)
  unique_max := by
    intro N hAN hNtop x hx
    have hNX : N.map X.subtype ≤ X := Subgroup.map_subtype_le N
    have hAN' : A ≤ N.map X.subtype := fun a ha =>
      ⟨⟨a, h.A_le_X ha⟩, hAN (Subgroup.mem_subgroupOf.2 ha), rfl⟩
    have hne : N.map X.subtype ≠ X := by
      intro heq
      apply hNtop
      rw [eq_top_iff]
      intro y _
      have hy : (y : G) ∈ N.map X.subtype := by
        rw [heq]
        exact y.2
      obtain ⟨n, hn, hny⟩ := hy
      have : n = y := Subtype.ext hny
      exact this ▸ hn
    exact h.min.unique_max hNX hAN' hne ⟨x, hx, rfl⟩
  type := by
    have e : (↥X ⧸ (M.subgroupOf X).normalCore) ≃* (↥X ⧸ CFSG.Quasithin.kerIn (M.subgroupOf X) ⊤) :=
      QuotientGroup.quotientMulEquivOfEq (kerIn_top_eq_normalCore' _).symm
    rcases hn with hn | hn
    · exact Or.inl (isPSL_congr e hn)
    · exact Or.inr (isSz_congr e hn)
  one_lt_n := one_lt_of_isPSL_or_isSz hn

@[expose] def rep [Fact (IsElemAbelian 2 (eSub V₀ X T))] (h : Cex156 M V₀ V U S A X T) :
    ↥X →* LGL 2 (Additive ↥(eSub V₀ X T)) :=
  CFSG.Goldschmidt.G2.conjRep (A := eSub V₀ X T) h.X_le_normalizer_eSub

theorem rep_apply [Fact (IsElemAbelian 2 (eSub V₀ X T))] (h : Cex156 M V₀ V U S A X T) (x : ↥X)
    (v : Additive ↥(eSub V₀ X T)) :
    ((Additive.toMul (h.rep x v) : ↥(eSub V₀ X T)) : G) =
      (x : G) * (Additive.toMul v : ↥(eSub V₀ X T)) * (x : G)⁻¹ :=
  rfl

theorem ker_rep [Fact (IsElemAbelian 2 (eSub V₀ X T))] (h : Cex156 M V₀ V U S A X T) :
    (h.rep).ker = (X ⊓ centralizer (eSub V₀ X T : Set G)).subgroupOf X :=
  CFSG.Goldschmidt.G2.ker_conjRep h.X_le_normalizer_eSub

theorem repQuad [Fact (IsElemAbelian 2 (eSub V₀ X T))] (h : Cex156 M V₀ V U S A X T) :
    RepQuad h.rep (A.subgroupOf X) := by
  have hgen : ∀ (a : G) (ha : a ∈ A) (b : G) (hb : b ∈ A) (v : Additive ↥(eSub V₀ X T)),
      h.rep ⟨a, h.A_le_X ha⟩ (h.rep ⟨b, h.A_le_X hb⟩ v - v) = h.rep ⟨b, h.A_le_X hb⟩ v - v := by
    intro a ha b hb v
    obtain ⟨e, he⟩ : ∃ e : ↥(eSub V₀ X T), v = Additive.ofMul e := ⟨Additive.toMul v, rfl⟩
    rw [he]
    apply Additive.toMul.injective
    apply Subtype.ext
    have := h.quad a ha b hb (e : G) e.2
    simp only [h.rep_apply, toMul_sub, toMul_ofMul, Subgroup.coe_mul, Subgroup.coe_inv,
      div_eq_mul_inv, mul_assoc, commutatorElement_def] at this ⊢
    exact this
  have hle : commSub ((A.subgroupOf X).map h.rep) ≤ fixSub ((A.subgroupOf X).map h.rep) := by
    refine Submodule.span_le.2 ?_
    rintro w ⟨b, ⟨b', hb', rfl⟩, v, rfl⟩ k ⟨a', ha', rfl⟩
    exact hgen a' ha' b' hb' v
  unfold RepQuad commSpace
  rw [Submodule.span_eq_bot]
  rintro w ⟨k, hk, u, hu, rfl⟩
  rw [hle hu k hk, sub_self]

theorem ker_le_centralizer (hMult : SchurMultiplierInput) (h : Cex156 M V₀ V U S A X T) {n : ℕ}
    (hn : IsPSL 2 2 n (KerQuot M X) ∨ IsSz n (KerQuot M X)) :
    kerMOf M X ≤ centralizer (eSub V₀ X T : Set G) := by
  haveI : Fact (IsElemAbelian 2 (eSub V₀ X T)) := ⟨h.isElemAbelian_eSub⟩
  have hmap := Setting12Two.isPGroup_map_ker hMult (h.setting12Two hn) h.rep h.repQuad
  have hkerIn : CFSG.Quasithin.kerIn (M.subgroupOf X) ⊤ = (kerMOf M X).subgroupOf X := by
    rw [kerIn_top_eq_normalCore', subgroupOf_kerMOf]
  rw [hkerIn] at hmap
  have hT₀K : (T ⊓ kerMOf M X).subgroupOf X ≤ (kerMOf M X).subgroupOf X := fun x hx =>
    Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 hx).2
  have hT₀ker : (T ⊓ kerMOf M X).subgroupOf X ≤ h.rep.ker := by
    rw [h.ker_rep]
    intro x hx
    exact Subgroup.mem_subgroupOf.2 ⟨x.2, h.le_centralizer_of_normal inf_le_left
      (h.min.normal_inf_ker h.sylow h.A_le_T) (Subgroup.mem_subgroupOf.1 hx)⟩
  have hodd : Odd (((T ⊓ kerMOf M X).subgroupOf X).relIndex ((kerMOf M X).subgroupOf X)) := by
    rw [Subgroup.relIndex_subgroupOf (kerMOf_le_group M X)]
    exact h.min.odd_relIndex_inf_ker h.sylow
  have hle := le_ker_of_isPGroup_map_of_odd_relIndex h.rep hT₀K hT₀ker hodd hmap
  intro x hx
  have hx' : (⟨x, kerMOf_le_group M X hx⟩ : ↥X) ∈ h.rep.ker := hle (Subgroup.mem_subgroupOf.2 hx)
  rw [h.ker_rep] at hx'
  exact (Subgroup.mem_subgroupOf.1 hx').2

end Cex156

end CFSG.LocalAnalysis.WeakClosure81
