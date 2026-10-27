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
public import Mathlib.GroupTheory.SchurZassenhaus
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

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup Pointwise
open scoped Pointwise

private theorem s16h_exists_complement_of_isPGroup_two {G : Type*} [Group G] [Finite G]
    {N S : Subgroup G} [hN : N.Normal] (hNodd : Odd (Nat.card N))
    (hcop : Nat.Coprime (Nat.card N) N.index) (hS2 : IsPGroup 2 S)
    (hSidx : ¬ 2 ∣ S.index) :
    ∃ X : Subgroup G, IsComplement' N X ∧ S ≤ X := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨X, hX⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  let P : Sylow 2 X := Sylow.nonempty.some
  let S' : Subgroup G := (P : Subgroup X).map X.subtype
  have hS'2 : IsPGroup 2 S' := P.isPGroup'.map X.subtype
  have hXindex : X.index = Nat.card N := hX.index_eq_card
  have hS'index : S'.index = (P : Subgroup X).index * X.index :=
    Subgroup.index_map_subtype (P : Subgroup X)
  have hS'idx : ¬ 2 ∣ S'.index := by
    rw [hS'index, hXindex, mul_comm]
    exact Nat.Prime.not_dvd_mul Nat.prime_two hNodd.not_two_dvd_nat P.not_dvd_index
  let P' : Sylow 2 G := hS'2.toSylow hS'idx
  have hP'coe : (P' : Subgroup G) = S' := IsPGroup.toSylow_coe hS'2 hS'idx
  let Q : Sylow 2 G := hS2.toSylow hSidx
  have hQcoe : (Q : Subgroup G) = S := IsPGroup.toSylow_coe hS2 hSidx
  obtain ⟨q, hq⟩ := MulAction.exists_smul_eq G P' Q
  have hqsub : MulAut.conj q • S' = S := by
    have h := congrArg (fun R : Sylow 2 G => (R : Subgroup G)) hq
    rwa [Sylow.coe_subgroup_smul, hP'coe, hQcoe] at h
  have hS'leX : S' ≤ X := by
    simpa only [S'] using Subgroup.map_subtype_le (P : Subgroup X)
  have hSle : S ≤ MulAut.conj q • X := by
    intro s hs
    rw [← hqsub] at hs
    rw [Subgroup.pointwise_smul_def] at hs ⊢
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hs
    exact Subgroup.mem_map.mpr ⟨t, hS'leX ht, rfl⟩
  have hcard : Nat.card N * Nat.card ↥(MulAut.conj q • X) = Nat.card G := by
    rw [Subgroup.pointwise_smul_def]
    rw [Subgroup.card_map_of_injective (K := X)
      (f := MulDistribMulAction.toMonoidEnd (MulAut G) G (MulAut.conj q))
      (MulAut.conj q).injective]
    exact hX.card_mul_card
  have hdisj : Disjoint N (MulAut.conj q • X) := by
    rw [disjoint_iff_inf_le]
    intro x hx
    obtain ⟨hxN, hxX⟩ := Subgroup.mem_inf.mp hx
    rw [Subgroup.pointwise_smul_def] at hxX
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxX
    have hyN : y ∈ N := by
      have hy' : y = q⁻¹ * x * q := by
        rw [← hyx]
        simp [MulAut.conj_apply]
        group
      rw [hy']
      simpa using hN.conj_mem x hxN q⁻¹
    have hybot : y ∈ (⊥ : Subgroup G) := by
      rw [← hX.disjoint.eq_bot]
      exact ⟨hyN, hy⟩
    rw [Subgroup.mem_bot] at hybot
    rw [← hyx, hybot]
    simp [MulAut.conj_apply]
  exact ⟨MulAut.conj q • X,
    Subgroup.isComplement'_iff_card_mul_and_disjoint.mpr ⟨hcard, hdisj⟩, hSle⟩

theorem s16h_exists_permuting_three_of_ker {A Q : Type*} [Group A] [Finite A] [Group Q]
    (φ : A →* Q) {T : Subgroup A} (hT2 : IsPGroup 2 ↥T) (hTsyl : ¬ 2 ∣ T.index)
    {J : Subgroup Q} (hJr : J ≤ φ.range) (hTJ : T.map φ ≤ J) {x y : ℕ}
    (hJ : Nat.card ↥J = 2 ^ x * 3 ^ y) (hK : ¬ 3 ∣ Nat.card ↥φ.ker) :
    ∃ Y : Subgroup A, IsPGroup 3 ↥Y ∧ Nat.card ↥Y = 3 ^ y ∧
      (Y : Set A) * (T : Set A) = (T : Set A) * (Y : Set A) ∧ Y ≤ J.comap φ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite ↥φ.range :=
    Finite.of_surjective (MonoidHom.rangeRestrict φ) (MonoidHom.rangeRestrict_surjective φ)
  haveI : Finite ↥J :=
    Finite.of_injective (Subgroup.inclusion hJr) (Subgroup.inclusion_injective hJr)
  set C : Subgroup A := φ.ker with hCdef
  set H : Subgroup A := J.comap φ with hHdef
  set C₂ : Subgroup A := T ⊓ C with hC₂def
  set N₁ : Subgroup A := Subgroup.normalizer (C₂ : Set A) ⊓ H with hN₁def
  set C₁ : Subgroup A := C ⊓ N₁ with hC₁def
  have hC_normal : C.Normal := by rw [hCdef]; exact φ.normal_ker
  have hC_le_H : C ≤ H := by
    rw [hHdef]; exact MonoidHom.ker_le_comap φ J
  have hT_H : T ≤ H := Subgroup.map_le_iff_le_comap.mp hTJ
  have hC₂_le_T : C₂ ≤ T := by rw [hC₂def]; exact inf_le_left
  have hC₂_le_C : C₂ ≤ C := by rw [hC₂def]; exact inf_le_right
  have hC₂_le_H : C₂ ≤ H := hC₂_le_C.trans hC_le_H
  have hT_normC₂ : T ≤ Subgroup.normalizer (C₂ : Set A) := by
    rw [Subgroup.le_normalizer_iff]
    intro t ht x hx
    rw [hC₂def] at hx ⊢
    exact ⟨T.mul_mem (T.mul_mem ht hx.1) (T.inv_mem ht),
      hC_normal.conj_mem x hx.2 t⟩
  have hT_N₁ : T ≤ N₁ := by
    rw [hN₁def]; exact le_inf hT_normC₂ hT_H
  have hC₂_le_N₁ : C₂ ≤ N₁ := hC₂_le_T.trans hT_N₁
  have hC₁_le_N₁ : C₁ ≤ N₁ := by rw [hC₁def]; exact inf_le_right
  have hC₁_le_C : C₁ ≤ C := by rw [hC₁def]; exact inf_le_left
  have hC₂_le_C₁ : C₂ ≤ C₁ := by rw [hC₁def]; exact le_inf hC₂_le_C hC₂_le_N₁
  have hC₂2 : IsPGroup 2 C₂ := hT2.to_inf_left
  have hC₂odd : ¬ 2 ∣ C₂.relIndex C := by
    have e1 : C₂.relIndex T * T.relIndex (T ⊔ C) = C₂.relIndex (T ⊔ C) :=
      Subgroup.relIndex_mul_relIndex C₂ T (T ⊔ C) hC₂_le_T le_sup_left
    have e2 : C₂.relIndex C * C.relIndex (T ⊔ C) = C₂.relIndex (T ⊔ C) :=
      Subgroup.relIndex_mul_relIndex C₂ C (T ⊔ C) hC₂_le_C le_sup_right
    have hCT : C.relIndex (T ⊔ C) = C₂.relIndex T := by
      rw [Subgroup.relIndex_sup_right (H := T) (K := C)]
      simpa [hC₂def, inf_comm] using (Subgroup.inf_relIndex_right (H := C) (K := T)).symm
    have hEq : C₂.relIndex C = T.relIndex (T ⊔ C) := by
      haveI : Finite ↥T := inferInstance
      haveI : (C₂.subgroupOf T).FiniteIndex := Subgroup.finiteIndex_of_finite
      have hpos : C₂.relIndex T ≠ 0 :=
        Subgroup.FiniteIndex.index_ne_zero (H := C₂.subgroupOf T)
      have h := e2.trans e1.symm
      rw [hCT] at h
      have h' : C₂.relIndex T * C₂.relIndex C =
          C₂.relIndex T * T.relIndex (T ⊔ C) := by
        rw [mul_comm]; exact h
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hpos) h'
    rw [hEq]
    intro h2
    exact hTsyl (h2.trans ⟨(T ⊔ C).index,
      (Subgroup.relIndex_mul_index (le_sup_left : T ≤ T ⊔ C)).symm⟩)
  have hC₂oddC₁ : ¬ 2 ∣ C₂.relIndex C₁ := by
    have hdvd : C₂.relIndex C₁ ∣ C₂.relIndex C :=
      ⟨C₁.relIndex C, (Subgroup.relIndex_mul_relIndex C₂ C₁ C hC₂_le_C₁ hC₁_le_C).symm⟩
    exact fun h => hC₂odd (h.trans hdvd)
  have hC₂sub2 : IsPGroup 2 (C₂.subgroupOf C) :=
    hC₂2.of_equiv (Subgroup.subgroupOfEquivOfLe hC₂_le_C).symm
  let PC : Sylow 2 ↥C := hC₂sub2.toSylow hC₂odd
  have hPCcoe : (PC : Subgroup ↥C) = C₂.subgroupOf C :=
    IsPGroup.toSylow_coe hC₂sub2 hC₂odd
  have hPCmap : PC.map C.subtype = C₂ := by
    rw [hPCcoe, Subgroup.map_subgroupOf_eq_of_le hC₂_le_C]
  have hfrattini : Subgroup.normalizer (C₂ : Set A) ⊔ C = ⊤ := by
    have h := Sylow.normalizer_sup_eq_top (p := 2) (N := C) PC
    rwa [hPCmap] at h
  have hH_sup : H = N₁ ⊔ C := by
    refine le_antisymm ?_ (sup_le inf_le_right hC_le_H)
    intro h hh
    have hh' : h ∈ Subgroup.normalizer (C₂ : Set A) ⊔ C := by
      rw [hfrattini]; exact Subgroup.mem_top h
    rw [Subgroup.mem_sup_of_normal_right (t := C)] at hh'
    obtain ⟨n, hn, c, hc, rfl⟩ := hh'
    have hnH : n ∈ H := by
      have : n = (n * c) * c⁻¹ := by group
      rw [this]
      exact H.mul_mem hh (H.inv_mem (hC_le_H hc))
    exact Subgroup.mem_sup_of_normal_right (t := C) |>.mpr ⟨n, ⟨hn, hnH⟩, c, hc, rfl⟩
  have hmapH : H.map φ = J := by
    rw [hHdef]; exact Subgroup.map_comap_eq_self hJr
  have hmapN₁ : N₁.map φ = J := by
    have hsup : (N₁ ⊔ C).map φ = N₁.map φ := by
      rw [Subgroup.map_sup, hCdef, Subgroup.map_ker_self, sup_bot_eq]
    rw [← hsup, ← hH_sup, hmapH]
  have hEindex : (C₁.subgroupOf N₁).index = Nat.card ↥J := by
    have hker : (φ.comp N₁.subtype).ker = C₁.subgroupOf N₁ := by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf, hC₁def,
        Subgroup.mem_inf, MonoidHom.mem_ker]
      exact ⟨fun h => ⟨h, x.2⟩, fun h => h.1⟩
    have hrange : (φ.comp N₁.subtype).range = J := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
      exact hmapN₁
    rw [← hker, Subgroup.index_ker, hrange]
  set D : Subgroup ↥N₁ := C₂.subgroupOf N₁ with hDdef
  set E : Subgroup ↥N₁ := C₁.subgroupOf N₁ with hEdef
  have hD_le_E : D ≤ E := by
    intro x hx
    rw [hDdef, Subgroup.mem_subgroupOf] at hx
    rw [hEdef, Subgroup.mem_subgroupOf, hC₁def]
    exact ⟨hC₂_le_C hx, x.2⟩
  have hD_normal : D.Normal := by
    rw [hDdef, Subgroup.normal_subgroupOf_iff_le_normalizer hC₂_le_N₁]
    exact inf_le_left
  have hE_normal : E.Normal := by
    rw [hEdef, Subgroup.normal_subgroupOf_iff hC₁_le_N₁]
    intro h k hh hk
    rw [hC₁def] at hh ⊢
    exact ⟨hC_normal.conj_mem h hh.1 k,
      N₁.mul_mem (N₁.mul_mem hk hh.2) (N₁.inv_mem hk)⟩
  have hDErel : D.relIndex E = C₂.relIndex C₁ := by
    rw [hDdef, hEdef]
    exact Subgroup.relIndex_subgroupOf hC₁_le_N₁
  have hDodd : ¬ 2 ∣ D.relIndex E := by
    rw [hDErel]; exact hC₂oddC₁
  let Q₁ := ↥N₁ ⧸ D
  let q : ↥N₁ →* Q₁ := QuotientGroup.mk' D
  let K : Subgroup Q₁ := E.map q
  haveI : D.Normal := hD_normal
  haveI : E.Normal := hE_normal
  have hK_normal : K.Normal := QuotientGroup.map_normal (N := D) (M := E)
  haveI : K.Normal := hK_normal
  have hKindex : K.index = Nat.card ↥J := by
    have hthird : K.index = Nat.card (↥N₁ ⧸ E) := by
      rw [Subgroup.index_eq_card]
      exact Nat.card_congr (QuotientGroup.quotientQuotientEquivQuotient D E hD_le_E).toEquiv
    rw [hthird, ← Subgroup.index_eq_card]
    exact hEindex
  have hKcard : Nat.card ↥K = D.relIndex E := by
    have hker : (q.comp E.subtype).ker = D.subgroupOf E := by
      ext x
      change (QuotientGroup.mk (E.subtype x) : Q₁) = 1 ↔ x ∈ D.subgroupOf E
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      rfl
    have hrange : (q.comp E.subtype).range = K := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hrange, ← Subgroup.index_ker (q.comp E.subtype), hker]
    rfl
  have hKodd : Odd (Nat.card ↥K) := by
    rw [hKcard, hDErel]
    exact Nat.not_even_iff_odd.mp fun he => hC₂oddC₁ (even_iff_two_dvd.mp he)
  have hKnot3 : ¬ 3 ∣ Nat.card ↥K := by
    rw [hKcard, hDErel]
    intro h3
    have hdvdC : C₂.relIndex C₁ ∣ Nat.card ↥C := by
      have h1 : C₂.relIndex C₁ ∣ C₂.relIndex C :=
        ⟨C₁.relIndex C, (Subgroup.relIndex_mul_relIndex C₂ C₁ C hC₂_le_C₁ hC₁_le_C).symm⟩
      have h2 : C₂.relIndex C ∣ Nat.card ↥C :=
        ⟨Nat.card ↥(C₂ ⊓ C), (Subgroup.relIndex_mul_card C₂ C).symm⟩
      exact h1.trans h2
    rw [hCdef] at hdvdC
    exact hK (h3.trans hdvdC)
  have hKcop : Nat.Coprime (Nat.card ↥K) K.index := by
    rw [hKindex, hJ]
    have h2 : Nat.Coprime (Nat.card ↥K) (2 ^ x) :=
      Nat.Prime.coprime_pow_of_not_dvd Nat.prime_two (fun h => hKodd.not_two_dvd_nat h)
    have h3 : Nat.Coprime (Nat.card ↥K) (3 ^ y) :=
      Nat.Prime.coprime_pow_of_not_dvd Nat.prime_three hKnot3
    rw [Nat.coprime_mul_iff_right]
    exact ⟨h2, h3⟩
  have hT_Hodd : ¬ 2 ∣ T.relIndex H := by
    intro h2
    exact hTsyl (h2.trans ⟨H.index, (Subgroup.relIndex_mul_index hT_H).symm⟩)
  have hTNidx : ¬ 2 ∣ T.relIndex N₁ := by
    intro h2
    exact hT_Hodd (h2.trans ⟨N₁.relIndex H,
      (Subgroup.relIndex_mul_relIndex T N₁ H hT_N₁ (inf_le_right : N₁ ≤ H)).symm⟩)
  have hTN2 : IsPGroup 2 (T.subgroupOf N₁) := hT2.comap_subtype
  let PT : Sylow 2 ↥N₁ := hTN2.toSylow hTNidx
  have hPTcoe : (PT : Subgroup ↥N₁) = T.subgroupOf N₁ :=
    IsPGroup.toSylow_coe hTN2 hTNidx
  let PT' : Sylow 2 Q₁ := PT.mapSurjective (QuotientGroup.mk'_surjective D)
  have hPT'coe : (PT' : Subgroup Q₁) = (T.subgroupOf N₁).map q := by
    have h : (PT' : Subgroup Q₁) = (PT : Subgroup ↥N₁).map q := rfl
    rw [h, hPTcoe]
  have hQ₁card : Nat.card Q₁ = Nat.card ↥K * Nat.card ↥J := by
    rw [← Subgroup.index_eq_card (H := D)]
    rw [← Subgroup.relIndex_mul_index hD_le_E, hKcard, hEindex]
  have hQ₁fac : Nat.factorization (Nat.card Q₁) 2 = x := by
    rw [hQ₁card, Nat.factorization_mul (Nat.card_pos (α := ↥K)).ne'
        (Nat.card_pos (α := ↥J)).ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hKodd.not_two_dvd_nat,
      hJ]
    rw [Nat.factorization_mul (pow_ne_zero _ (by norm_num))
      (pow_ne_zero _ (by norm_num)), Finsupp.add_apply, Nat.factorization_pow,
      Nat.factorization_pow, Finsupp.smul_apply, Finsupp.smul_apply,
      Nat.Prime.factorization_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3)]
    simp
  have hPT'card : Nat.card ↥PT' = 2 ^ x := by
    rw [show Nat.card ↥PT' = Nat.card ↥(PT' : Subgroup Q₁) from rfl,
      PT'.card_eq_multiplicity, hQ₁fac]
  have hDTN : D ≤ T.subgroupOf N₁ := by
    intro x hx
    rw [hDdef, Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_subgroupOf]
    exact hC₂_le_T hx
  have hDrelT : D.relIndex (T.subgroupOf N₁) = 2 ^ x := by
    have hker : (q.comp (T.subgroupOf N₁).subtype).ker = D.subgroupOf (T.subgroupOf N₁) := by
      ext x
      change (QuotientGroup.mk ((T.subgroupOf N₁).subtype x) : Q₁) = 1 ↔
        x ∈ D.subgroupOf (T.subgroupOf N₁)
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      rfl
    have hrange : (q.comp (T.subgroupOf N₁).subtype).range = (T.subgroupOf N₁).map q := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have hcardPT : Nat.card ↥PT' = Nat.card ↥((T.subgroupOf N₁).map q) :=
      congrArg (fun S : Subgroup Q₁ => Nat.card ↥S) hPT'coe
    have hidx : D.relIndex (T.subgroupOf N₁) = Nat.card ↥PT' := by
      rw [hcardPT, ← hrange, ← Subgroup.index_ker (q.comp (T.subgroupOf N₁).subtype), hker]
      rfl
    rw [hidx, hPT'card]
  have hTcard : Nat.card ↥T = Nat.card ↥D * 2 ^ x := by
    have hcardT : Nat.card ↥(T.subgroupOf N₁) = Nat.card ↥T :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT_N₁).toEquiv
    have hcard := Subgroup.relIndex_mul_card (H := D) (K := T.subgroupOf N₁)
    rw [inf_of_le_left hDTN] at hcard
    rw [← hcardT, ← hcard, hDrelT, mul_comm]
  obtain ⟨Xbar, hXcomp, hTbar_le⟩ :=
    s16h_exists_complement_of_isPGroup_two (N := K) hKodd hKcop PT'.isPGroup'
      PT'.not_dvd_index
  set X₁ : Subgroup ↥N₁ := Xbar.comap q with hX₁def
  have hT_X₁ : T.subgroupOf N₁ ≤ X₁ := by
    intro x hx
    rw [hX₁def, Subgroup.mem_comap]
    exact hTbar_le (by
      rw [hPT'coe]
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  have hXbarcard : Nat.card ↥Xbar = Nat.card ↥J := by
    have h := hXcomp.card_mul_card
    rw [hQ₁card] at h
    exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥K)) h
  have hX₁card : Nat.card ↥X₁ = Nat.card ↥D * Nat.card ↥J := by
    have hker : (q.comp X₁.subtype).ker = D.subgroupOf X₁ := by
      ext x
      change (QuotientGroup.mk (X₁.subtype x) : Q₁) = 1 ↔ x ∈ D.subgroupOf X₁
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      rfl
    have hrange : (q.comp X₁.subtype).range = Xbar := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
      exact Subgroup.map_comap_eq_self_of_surjective
        (QuotientGroup.mk'_surjective D) Xbar
    have hidx : D.relIndex X₁ = Nat.card ↥Xbar := by
      rw [← hrange, ← Subgroup.index_ker (q.comp X₁.subtype), hker]
      rfl
    have hcard := Subgroup.relIndex_mul_card (H := D) (K := X₁)
    rw [inf_of_le_left (hDTN.trans hT_X₁)] at hcard
    rw [← hcard, hidx, hXbarcard, mul_comm]
  have hD2 : IsPGroup 2 D :=
    hC₂2.of_equiv (Subgroup.subgroupOfEquivOfLe hC₂_le_N₁).symm
  obtain ⟨c, hc⟩ := hD2.exists_card_eq
  have hX₁card3 : Nat.card ↥X₁ = Nat.card ↥D * 2 ^ x * 3 ^ y := by
    rw [hX₁card, hJ, mul_assoc]
  have hX₁card2 : Nat.card ↥X₁ = 2 ^ (c + x) * 3 ^ y := by
    rw [hX₁card3, hc, ← pow_add]
  have hX₁fac3 : Nat.factorization (Nat.card ↥X₁) 3 = y := by
    rw [hX₁card2, Nat.factorization_mul (pow_ne_zero _ (by norm_num))
      (pow_ne_zero _ (by norm_num)), Finsupp.add_apply]
    simp [Nat.factorization_pow, Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 2),
      Nat.Prime.factorization_self Nat.prime_three]
  let P3 : Sylow 3 ↥X₁ := Sylow.nonempty.some
  let Y₁ : Subgroup ↥X₁ := (P3 : Subgroup ↥X₁)
  have hY₁card : Nat.card ↥Y₁ = 3 ^ y := by
    rw [show Nat.card ↥Y₁ = Nat.card ↥(P3 : Subgroup ↥X₁) from rfl,
      P3.card_eq_multiplicity, hX₁fac3]
  let YN : Subgroup ↥N₁ := Y₁.map X₁.subtype
  let Y : Subgroup A := YN.map N₁.subtype
  have hYcard : Nat.card ↥Y = 3 ^ y := by
    change Nat.card ↥(YN.map N₁.subtype) = 3 ^ y
    rw [Subgroup.card_subtype N₁ YN]
    change Nat.card ↥(Y₁.map X₁.subtype) = 3 ^ y
    rw [Subgroup.card_subtype X₁ Y₁, hY₁card]
  have hY3 : IsPGroup 3 ↥Y := by
    change IsPGroup 3 ↥(YN.map N₁.subtype)
    exact (P3.isPGroup'.map X₁.subtype).map N₁.subtype
  set XA : Subgroup A := X₁.map N₁.subtype with hXAdef
  have hXAcard : Nat.card ↥XA = Nat.card ↥X₁ := by
    rw [hXAdef]; exact Subgroup.card_subtype N₁ X₁
  have hT_XA : T ≤ XA := by
    intro t ht
    have htX : (⟨t, hT_N₁ ht⟩ : ↥N₁) ∈ X₁ :=
      hT_X₁ (by rw [Subgroup.mem_subgroupOf]; exact ht)
    exact Subgroup.mem_map.mpr ⟨⟨t, hT_N₁ ht⟩, htX, rfl⟩
  have hY_XA : Y ≤ XA := by
    rw [hXAdef]
    change YN.map N₁.subtype ≤ X₁.map N₁.subtype
    exact Subgroup.map_mono (Subgroup.map_subtype_le Y₁)
  have hY_le_N₁ : Y ≤ N₁ :=
    hY_XA.trans (by rw [hXAdef]; exact Subgroup.map_subtype_le X₁)
  have hTcard2 : Nat.card ↥T = 2 ^ (c + x) := by
    rw [hTcard, hc, ← pow_add]
  have hYsubcard : Nat.card ↥(Y.subgroupOf XA) = 3 ^ y := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY_XA).toEquiv, hYcard]
  have hTsubcard : Nat.card ↥(T.subgroupOf XA) = Nat.card ↥T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT_XA).toEquiv
  have hprod : Nat.card ↥(Y.subgroupOf XA) * Nat.card ↥(T.subgroupOf XA) =
      Nat.card ↥XA := by
    rw [hYsubcard, hTsubcard, hTcard2, hXAcard, hX₁card2]
    ring
  have hcopYT : Nat.Coprime (Nat.card ↥(Y.subgroupOf XA))
      (Nat.card ↥(T.subgroupOf XA)) := by
    rw [hYsubcard, hTsubcard, hTcard2]
    exact Nat.coprime_pow_primes y (c + x) Nat.prime_three Nat.prime_two (by norm_num)
  have hcomplA : (Y.subgroupOf XA).IsComplement' (T.subgroupOf XA) :=
    Subgroup.isComplement'_of_coprime hprod hcopYT
  have himgY : XA.subtype '' ((Y.subgroupOf XA : Subgroup ↥XA) : Set ↥XA) =
      (Y : Set A) := by
    rw [← Subgroup.coe_map, Subgroup.map_subgroupOf_eq_of_le hY_XA]
  have himgT : XA.subtype '' ((T.subgroupOf XA : Subgroup ↥XA) : Set ↥XA) =
      (T : Set A) := by
    rw [← Subgroup.coe_map, Subgroup.map_subgroupOf_eq_of_le hT_XA]
  have himgu : XA.subtype '' (Set.univ : Set ↥XA) = (XA : Set A) := by
    rw [Set.image_univ, ← MonoidHom.coe_range, Subgroup.range_subtype]
  have hYT : (Y : Set A) * (T : Set A) = (XA : Set A) := by
    have h := congrArg (Set.image XA.subtype) hcomplA.mul_eq
    rw [Set.image_mul XA.subtype, himgY, himgT, himgu] at h
    exact h
  have hTY : (T : Set A) * (Y : Set A) = (XA : Set A) := by
    have h := congrArg (Set.image XA.subtype) hcomplA.symm.mul_eq
    rw [Set.image_mul XA.subtype, himgT, himgY, himgu] at h
    exact h
  refine ⟨Y, hY3, hYcard, hYT.trans hTY.symm, ?_⟩
  exact hY_le_N₁.trans inf_le_right

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
