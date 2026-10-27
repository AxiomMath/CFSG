module

public import CFSG.RankThree.GF2n.Stroth78.Sec4PSULift

import CFSG.GF2Type.Smith1979.CaseIClosure
import CFSG.GF2Type.Smith1979.CaseIIRderFix
import CFSG.GH74.Exceptional.UnitaryFourTwo
import CFSG.LargeExtraspecial.O62Rank
import CFSG.RankThree.GF2n.Stroth78.Sec2EighteenR
import CFSG.RankThree.GF2n.Stroth78.Sec2FiveO4
import CFSG.RankThree.GF2n.Stroth78.Sec3Five
import CFSG.RankThree.GF2n.Stroth78.Sec4PSUEndAut
import CFSG.RankThree.GF2n.Stroth78.Sec4PSUEndCent
import CFSG.RankThree.GF2n.Stroth78.Sec4PlusFixedSq
import CFSG.RankThree.GF2n.Stroth78.Sec4ThreeAct
public import CFSG.LargeExtraspecial.O62Basic
import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions CFSG.GroupTheory.ThreeTranspositions
open CFSG.Blueprint.Fischer CFSG.Fischer.Classification CFSG.Fischer.Classification.Unitary
open Matrix Module

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

namespace Sec4PSUEnd

private theorem card_le_of_elemAbelian_mulAut {A : Type}
    [Group A] (φ : A ≃* U2 4) {P : Subgroup (MulAut A)}
    (hab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (h2 : ∀ x ∈ P, x ^ 2 = 1) :
    Nat.card P ≤ 2 ^ 4 := by
  obtain ⟨e⟩ := nonempty_mulAut_mulEquiv_oMinusSixTwo φ
  let f := (TauCeti.QuadraticMap.orthogonalGroup
    (CFSG.LieType.Universal.Spin.quadMinus 3 (ZMod 2) 1 1)).subtype.comp e.toMonoidHom
  have hf : Function.Injective f := (Subgroup.subtype_injective _).comp e.injective
  rw [← Subgroup.card_map_of_injective hf]
  refine CFSG.LargeExtraspecial.O62.card_le_of_elemAbelian
    (Q := CFSG.LieType.Universal.Spin.quadMinus 3 (ZMod 2) 1 1) ?_
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite 3 (ZMod 2)
      (b := 1) (c := 1) (by decide)) ?_ ?_ ?_
  · rw [Module.finrank_fintype_fun_eq_card]
    rfl
  · rintro _ ⟨x, -, rfl⟩
    exact (e x).2
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hab x hx y hy]
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, h2 x hx, map_one]

private theorem card_range_actL_le (S : Setting z E F) {a : G}
    {w : ℕ} (h : Sec3Hyp S a w) {α₀ : Hbar z} (hα₀ : α₀ ∈ Rbar S a)
    (φ₀ : ↥(threeResidualQuot (alphaInX S h hα₀)) ≃* U2 4) :
    Nat.card (actL S h hα₀).range ≤ 2 ^ 4 := by
  refine card_le_of_elemAbelian_mulAut φ₀ ?_ ?_
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul,
      show x * y = y * x from Subtype.ext (commute_of_mem_Lbar S h.mem_Q h.isConj x.2 y.2)]
  · rintro _ ⟨x, rfl⟩
    rw [← map_pow, show x ^ 2 = 1 from Subtype.ext (by
      rw [SubgroupClass.coe_pow]
      exact sq_eq_one_of_mem_Lbar S h.mem_Q h.isConj x.2), map_one]

private theorem two_pow_le_card_Lbar (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3) :
    2 ^ w ≤ Nat.card (Lbar S a) := by
  have hge : 2 ^ (1 + w - 1) ≤ Nat.card (Lbar S a) :=
    card_Lbar_ge_of_width_r S h.isConj h.mem_Q h.not_mem_ZQ h.mem_Qa h.card_F
      ((card_Rbar_eq_two S h h217 h3).trans (pow_one 2).symm)
  rwa [show 1 + w - 1 = w by omega] at hge

theorem le_five (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {α : Hbar z} (hα : α ∈ Tset S a)
    (hpsu : fischerCentralQuotientModel
      (threeResidualClass (⟨α, subset_Xsub S a (Tset_subset_Eset S a hα)⟩ : ↥(Xsub S a)))
      (fischerMatrixGroup fun A => A.det = 1 ∧
        ∀ x y, fischerHermitianF4 4 (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 4 x y)
      (fischerTransvections (fischerHermitianF4 4) fun v => v ≠ 0 ∧ fischerHermitianF4 4 v v = 0)) :
    w ≤ 5 := by
  obtain ⟨d₀, hd₀R, hd₀1, φ₀, -⟩ := Sec4PSU.exists_mem_Rbar_mulEquiv_U2 S h h217 h3 hα hpsu
  have h5 : 2 ^ w ≤ 2 ^ 5 :=
    calc 2 ^ w ≤ Nat.card (Lbar S a) := two_pow_le_card_Lbar S h h217 h3
      _ ≤ 2 * Nat.card (actL S h hd₀R).range :=
        card_Lbar_le_two_mul_card_range_actL S h h217 h3 hd₀R hd₀1
      _ ≤ 2 * 2 ^ 4 := Nat.mul_le_mul_left 2 (card_range_actL_le S h hd₀R φ₀)
      _ = 2 ^ 5 := by norm_num
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h5

private theorem card_modEq_card_inf_fixSpace {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] {T : V ≃ₗ[ZMod 2] V} (hT : T ^ 5 = 1) {U : Submodule (ZMod 2) V}
    (hU : ∀ u ∈ U, T u ∈ U) :
    Nat.card U ≡ Nat.card ↥(U ⊓ fixSpace T) [MOD 5] := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let f : U → U := fun u => ⟨T u, hU u u.2⟩
  have hf : f^[5] = id := by
    funext u
    apply Subtype.ext
    have h5 : (T ^ 5) (u : V) = u := by rw [hT]; rfl
    rw [LinearEquiv.pow_apply] at h5
    exact h5
  have hmod := CFSG.GF2Type.Smith1979.Case2.card_fixed_modEq f hf
  rw [← Nat.card_coe_set_eq] at hmod
  have e : ↥(Function.fixedPoints f) ≃ ↥(U ⊓ fixSpace T) :=
    { toFun := fun u => ⟨(u.1 : V), Submodule.mem_inf.mpr ⟨u.1.2,
        mem_fixSpace.mpr (congrArg Subtype.val (Function.mem_fixedPoints.mp u.2).eq)⟩⟩
      invFun := fun v => ⟨⟨v.1, (Submodule.mem_inf.mp v.2).1⟩, Function.mem_fixedPoints.mpr
        (show f _ = _ from Subtype.ext (mem_fixSpace.mp (Submodule.mem_inf.mp v.2).2))⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rwa [Nat.card_congr e] at hmod

private theorem eq_of_two_pow_modEq_five {a b : ℕ} (h : 2 ^ a ≡ 2 ^ b [MOD 5]) (hba : b ≤ a)
    (hab : a ≤ b + 3) : a = b := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hba
  have h' : 2 ^ b * 2 ^ k ≡ 2 ^ b * 1 [MOD 5] := by rwa [mul_one, ← pow_add]
  have hk := Nat.ModEq.cancel_left_of_coprime
    (Nat.Coprime.pow_right b (by norm_num : Nat.Coprime 5 2)) h'
  have hk3 : k ≤ 3 := by omega
  interval_cases k
  · rfl
  all_goals exact absurd hk (by decide)

private theorem eq_one_of_pow_five_of_commute {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Module.Finite (ZMod 2) V] {A T : V ≃ₗ[ZMod 2] V} (hAA : A * A = 1) (hTA : T * A = A * T)
    (hT : T ^ 5 = 1) (hV : finrank (ZMod 2) V = 6) (hW : finrank (ZMod 2) (commSpace A) = 2) :
    T = 1 := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have hcard : ∀ U : Submodule (ZMod 2) V, Nat.card U = 2 ^ finrank (ZMod 2) U := fun U => by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hTAv : ∀ v, T (A v) = A (T v) := fun v => by
    rw [← LinearEquiv.mul_apply, hTA, LinearEquiv.mul_apply]
  have hK : finrank (ZMod 2) (fixSpace A) = 4 := by
    have := finrank_commSpace_add_finrank_fixSpace A
    omega
  have hWF : commSpace A ≤ fixSpace T := by
    have h1 := card_modEq_card_inf_fixSpace hT (U := commSpace A) fun u hu => by
      obtain ⟨v, rfl⟩ := mem_commSpace.mp hu
      exact mem_commSpace.mpr ⟨T v, by rw [map_sub, hTAv]⟩
    rw [hcard, hcard, hW] at h1
    have hle := Submodule.finrank_mono (inf_le_left : commSpace A ⊓ fixSpace T ≤ commSpace A)
    have h2 := eq_of_two_pow_modEq_five h1 (by omega) (by omega)
    have heq := Submodule.eq_of_le_of_finrank_eq
      (inf_le_left : commSpace A ⊓ fixSpace T ≤ commSpace A) (by omega)
    rw [← heq]
    exact inf_le_right
  have hKF : fixSpace A ≤ fixSpace T := by
    have h1 := card_modEq_card_inf_fixSpace hT (U := fixSpace A) fun u hu => by
      rw [mem_fixSpace] at hu ⊢
      rw [← hTAv, hu]
    rw [hcard, hcard, hK] at h1
    have hle := Submodule.finrank_mono (inf_le_left : fixSpace A ⊓ fixSpace T ≤ fixSpace A)
    have hge := Submodule.finrank_mono (le_inf (commSpace_le_fixSpace hAA) hWF)
    have h2 := eq_of_two_pow_modEq_five h1 (by omega) (by omega)
    have heq := Submodule.eq_of_le_of_finrank_eq
      (inf_le_left : fixSpace A ⊓ fixSpace T ≤ fixSpace A) (by omega)
    rw [← heq]
    exact inf_le_right
  have h1 := card_modEq_card_inf_fixSpace hT (U := ⊤) fun _ _ => Submodule.mem_top
  rw [hcard, hcard, finrank_top, hV, top_inf_eq] at h1
  have hle := Submodule.finrank_le (fixSpace T)
  have hge := Submodule.finrank_mono hKF
  have h2 := eq_of_two_pow_modEq_five h1 (by omega) (by omega)
  have hF : fixSpace T = ⊤ := Submodule.eq_top_of_finrank_eq (by omega)
  ext v
  have hv : v ∈ fixSpace T := hF ▸ Submodule.mem_top
  simpa using mem_fixSpace.mp hv

private theorem three_le (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {α : Hbar z} (hα : α ∈ Tset S a)
    (hpsu : fischerCentralQuotientModel
      (threeResidualClass (⟨α, subset_Xsub S a (Tset_subset_Eset S a hα)⟩ : ↥(Xsub S a)))
      (fischerMatrixGroup fun A => A.det = 1 ∧
        ∀ x y, fischerHermitianF4 4 (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 4 x y)
      (fischerTransvections (fischerHermitianF4 4) fun v => v ≠ 0 ∧ fischerHermitianF4 4 v v = 0)) :
    3 ≤ w := by
  by_contra hlt
  have : Finite (Additive (QbarOf S)) := inferInstance
  have : Module.Finite (ZMod 2) (Additive (QbarOf S)) := Module.Finite.of_finite
  have hV := finrank_QbarOf_eq_two_mul S h.card_F
  have hfix := rhoLin_eq_self_of_finrank_le_five S h h217 h3 hα hpsu (U := ⊤)
    (fun _ _ _ _ => Submodule.mem_top) (by rw [finrank_top, hV]; omega)
  obtain ⟨x, hx, hxa⟩ := exists_rhoLin_aVec_ne S h h217 h3 hα hpsu
  exact hxa (hfix x hx _ Submodule.mem_top)

private theorem le_four (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {α : Hbar z} (hα : α ∈ Tset S a)
    (hpsu : fischerCentralQuotientModel
      (threeResidualClass (⟨α, subset_Xsub S a (Tset_subset_Eset S a hα)⟩ : ↥(Xsub S a)))
      (fischerMatrixGroup fun A => A.det = 1 ∧
        ∀ x y, fischerHermitianF4 4 (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 4 x y)
      (fischerTransvections (fischerHermitianF4 4) fun v => v ≠ 0 ∧ fischerHermitianF4 4 v v = 0)) :
    w ≤ 4 := by
  have hodd := odd_card_centralizer_Xsub S h h217 h3 hα hpsu (le_five S h h217 h3 hα hpsu)
  obtain ⟨d₀, hd₀R, hd₀1, φ₀, -⟩ := Sec4PSU.exists_mem_Rbar_mulEquiv_U2 S h h217 h3 hα hpsu
  have hinj : Function.Injective (actL S h hd₀R) := by
    rw [injective_iff_map_eq_one]
    intro ℓ hℓ
    obtain ⟨c, hc⟩ : ∃ c : Subgroup.centralizer (Xsub S a : Set (Hbar z)), (c : Hbar z) = ℓ :=
      ⟨⟨ℓ, mem_centralizer_of_actL_eq_one S h h217 h3 hd₀R hd₀1 hℓ⟩, rfl⟩
    have hc2 : c ^ 2 = 1 := Subtype.ext (by
      rw [SubgroupClass.coe_pow, hc]
      exact sq_eq_one_of_mem_Lbar S h.mem_Q h.isConj ℓ.2)
    have hc1 : c = 1 := by
      have hoddc := hodd.of_dvd_nat (orderOf_dvd_natCard c)
      rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hc2) with h' | h'
      · exact orderOf_eq_one_iff.mp h'
      · rw [h'] at hoddc
        exact absurd hoddc (by decide)
    exact Subtype.ext (by rw [← hc, hc1]; rfl)
  have hcard : Nat.card (Lbar S a) = Nat.card (actL S h hd₀R).range :=
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  have h4 : 2 ^ w ≤ 2 ^ 4 := (two_pow_le_card_Lbar S h h217 h3).trans
    (hcard ▸ card_range_actL_le S h hd₀R φ₀)
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h4

private theorem ne_three (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {α : Hbar z} (hα : α ∈ Tset S a)
    (hpsu : fischerCentralQuotientModel
      (threeResidualClass (⟨α, subset_Xsub S a (Tset_subset_Eset S a hα)⟩ : ↥(Xsub S a)))
      (fischerMatrixGroup fun A => A.det = 1 ∧
        ∀ x y, fischerHermitianF4 4 (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 4 x y)
      (fischerTransvections (fischerHermitianF4 4) fun v => v ≠ 0 ∧ fischerHermitianF4 4 v v = 0)) :
    w ≠ 3 := by
  classical
  intro hw
  have : Finite (Additive (QbarOf S)) := inferInstance
  have : Module.Finite (ZMod 2) (Additive (QbarOf S)) := Module.Finite.of_finite
  have : Finite (Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)) :=
    CFSG.LargeExtraspecial.O62.finite_linearEquiv
  have hV : finrank (ZMod 2) (Additive (QbarOf S)) = 6 := by
    rw [finrank_QbarOf_eq_two_mul S h.card_F, hw]
  have hQ := qS_nondegenerate S
  let f : Hbar z →* (Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)) :=
    (TauCeti.QuadraticMap.orthogonalGroup (qS S)).subtype.comp (rhoBar S)
  have hf : Function.Injective f := (Subgroup.subtype_injective _).comp (rhoBar_injective S)
  have hXΩ : (Xsub S a).map f ≤ omegaGroup (qS S) hQ := by
    rw [Subgroup.map_le_iff_le_comap]
    refine Xsub_le_of_Eset_le S a fun e he => ?_
    obtain ⟨-, -, -, hWe, -⟩ := isTypeA_rhoBar_of_isA2Hbar S (Eset_subset_A2set S a he)
    have hev : Even (finrank (ZMod 2) (commSpace (rhoBar S e :
        Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)))) := by
      rw [hWe]
      exact even_two
    exact Subgroup.mem_comap.mpr (mem_omegaGroup.mpr ⟨(rhoBar S e).2, hev⟩)
  have hXcard : 25920 ≤ Nat.card (Xsub S a) := by
    obtain ⟨φ⟩ := nonempty_mulEquiv_U2 S h h217 h3 hα hpsu
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥(Xsub S a))
    rw [Nat.card_congr φ.toEquiv, CFSG.GH74.Exceptional.card_U2_four] at h1
    have h2 : 0 < Nat.card (Subgroup.center ↥(Xsub S a)) := Nat.card_pos
    omega
  have hle := Subgroup.card_le_of_le hXΩ
  rw [Subgroup.card_map_of_injective hf] at hle
  have hΩ : Nat.card (omegaGroup (qS S) hQ) = 25920 := by
    rcases CFSG.LargeExtraspecial.O62.card_omegaGroup hV hQ with h' | h' <;> omega
  have hXΩeq : (Xsub S a).map f = omegaGroup (qS S) hQ :=
    Subgroup.eq_of_le_of_card_ge hXΩ (by rw [Subgroup.card_map_of_injective hf]; omega)
  have hp0 : aVec S h.mem_Q ≠ 0 := aV_ne_zero S h.mem_Q h.not_mem_ZQ
  have hpq : qS S (aVec S h.mem_Q) = 0 := qS_aVec_eq_zero S h.mem_Q h.isConj
  have horb : MulAction.orbit (omegaGroup (qS S) hQ) (aVec S h.mem_Q) =
      {v | v ≠ 0 ∧ qS S v = 0} := by
    ext v
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨fun h0 => hp0 ((LinearEquiv.map_eq_zero_iff
        (x : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))).mp h0), ?_⟩
      exact (TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup
        (omegaGroup_le (qS S) hQ x.2) _).trans hpq
    · rintro ⟨hv0, hv⟩
      obtain ⟨x, hx, hxa⟩ := CFSG.LargeExtraspecial.O62.exists_mem_omegaGroup_apply_eq hQ
        (by omega) hp0 hv0 (by rw [hpq, hv])
      exact ⟨⟨x, hx⟩, hxa⟩
  have key : Nat.card (MulAction.orbit (omegaGroup (qS S) hQ) (aVec S h.mem_Q)) *
      Nat.card (MulAction.stabilizer (omegaGroup (qS S) hQ) (aVec S h.mem_Q)) =
        Nat.card (omegaGroup (qS S) hQ) := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup _ _)
  have h27 : {v : Additive (QbarOf S) | v ≠ 0 ∧ qS S v = 0}.ncard = 27 := by
    rcases CFSG.LargeExtraspecial.O62.ncard_singular_nonsingular hV hQ with ⟨h35, -⟩ | ⟨h27, -⟩
    · rw [horb, Nat.card_coe_set_eq, h35, hΩ] at key
      omega
    · exact h27
  obtain ⟨c, hcΩ, hca, hc5, hc1⟩ :=
    CFSG.GF2Type.Smith1979.CaseIClosure.exists_order_five_stab hV hQ hp0 hpq h27
  rw [← hXΩeq] at hcΩ
  obtain ⟨y, hyX, rfl⟩ := Subgroup.mem_map.mp hcΩ
  have hy5 : y ^ 5 = 1 := hf (by rw [map_pow, hc5, map_one])
  have hy1 : y ≠ 1 := fun h1 => hc1 (by rw [h1, map_one])
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hord : orderOf y = 5 := orderOf_eq_prime hy5 hy1
  have hZ1 := rhoZ_Xsub_eq_one S h h217 h3 hα hpsu
  have hyC : y ∈ CHbar S a :=
    mem_CHbar_of_odd_orderOf S h.mem_Q
      (Y := (MulAction.stabilizer (Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))
        (aVec S h.mem_Q)).comap f ⊓ Xsub S a)
      (fun y' hy' => MulAction.mem_stabilizer_iff.mp
        (Subgroup.mem_comap.mp (Subgroup.mem_inf.mp hy').1))
      (fun y' hy' u => by rw [hZ1 y' (Subgroup.mem_inf.mp hy').2]; rfl)
      (Subgroup.mem_inf.mpr ⟨Subgroup.mem_comap.mpr (MulAction.mem_stabilizer_iff.mpr hca), hyX⟩)
      (by rw [hord]; decide)
  obtain ⟨⟨α₀, hα₀R⟩, hα₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.Rbar_ne_bot
  have hα₀1' : α₀ ≠ 1 := fun h1 => hα₀1 (Subtype.ext h1)
  have hcomm := commute_of_mem_CHbar_of_card_Rbar_eq_two S a (card_Rbar_eq_two S h h217 h3)
    hα₀R hα₀1' hyC
  obtain ⟨-, -, hAA, hW2, -⟩ := isTypeA_rhoBar_of_isA2Hbar S
    (isA2Hbar_of_mem_Rbar S h.mem_Q h.isConj h.not_mem_ZQ h.mem_Qa h.centerIn_Qa_not_le_Q α₀
      hα₀R hα₀1')
  have hTA : f y * f α₀ = f α₀ * f y := by rw [← map_mul, ← map_mul, hcomm]
  have hT5 : f y ^ 5 = 1 := by rw [← map_pow, hy5, map_one]
  exact hy1 (hf ((eq_one_of_pow_five_of_commute (A := f α₀) hAA hTA hT5 hV hW2).trans
    (map_one f).symm))

theorem eq_four (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {α : Hbar z} (hα : α ∈ Tset S a)
    (hpsu : fischerCentralQuotientModel
      (threeResidualClass (⟨α, subset_Xsub S a (Tset_subset_Eset S a hα)⟩ : ↥(Xsub S a)))
      (fischerMatrixGroup fun A => A.det = 1 ∧
        ∀ x y, fischerHermitianF4 4 (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 4 x y)
      (fischerTransvections (fischerHermitianF4 4) fun v => v ≠ 0 ∧ fischerHermitianF4 4 v v = 0)) :
    w = 4 := by
  have h3le := three_le S h h217 h3 hα hpsu
  have hle4 := le_four S h h217 h3 hα hpsu
  have hne3 := ne_three S h h217 h3 hα hpsu
  omega

end Sec4PSUEnd

end CFSG.RankThree.GF2n.Stroth78
