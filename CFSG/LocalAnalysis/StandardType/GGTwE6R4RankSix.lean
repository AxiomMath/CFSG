module

public import CFSG.LocalAnalysis.StandardType.GGTwE6RecipeTransport
public import CFSG.LocalAnalysis.StandardType.GGTwE6KGA1Defs
public import CFSG.LocalAnalysis.StandardType.GGTwE6KGA1TIn
public import CFSG.LocalAnalysis.StandardType.GGTwE6KGA1RankSix
public import CFSG.LocalAnalysis.StandardType.GGTwE6KGA1Compat

public section

namespace CFSG.StandardType.TwE6R4

open CFSG.Open CFSG.StandardType.NoOffTwE6Three
open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.HardMathSupport.Lang.E6Descent


private theorem rs_isAlgebraic_of_ringEquiv
    {k K Ω : Type*} [Field k] [Field K] [Field Ω] [Algebra K Ω] [Algebra k Ω]
    (τ : k ≃+* K)
    (halg : ∀ x, algebraMap k Ω x = algebraMap K Ω (τ x))
    (h : Algebra.IsAlgebraic K Ω) : Algebra.IsAlgebraic k Ω := by
  refine Algebra.IsAlgebraic.mk fun ω => ?_
  obtain ⟨p, hp, hp0⟩ := h.isAlgebraic ω
  refine ⟨p.map τ.symm.toRingHom, ?_, ?_⟩
  · rw [Polynomial.map_ne_zero_iff τ.symm.injective]
    exact hp
  · rw [Polynomial.aeval_def] at hp0 ⊢
    rw [Polynomial.eval₂_map]
    have hcomp : (algebraMap k Ω).comp τ.symm.toRingHom = algebraMap K Ω := by
      ext x
      change (algebraMap k Ω) (τ.symm x) = (algebraMap K Ω) x
      rw [halg (τ.symm x), RingEquiv.apply_symm_apply]
    rw [hcomp]
    exact hp0

private theorem rs_conj_injective {R : Type*} [Group R] (hR : Subgroup.center R = ⊥) :
    Function.Injective (MulAut.conj : R →* MulAut R) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro r hr
  rw [MonoidHom.mem_ker] at hr
  rw [Subgroup.mem_bot]
  have hc : r ∈ Subgroup.center R := by
    rw [Subgroup.mem_center_iff]
    intro x
    have h1 : (MulAut.conj r) x = (1 : MulAut R) x := by rw [hr]
    rw [MulAut.conj_apply, MulAut.one_apply] at h1
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  rwa [hR, Subgroup.mem_bot] at hc

private theorem rs_conj_conj {R : Type*} [Group R] (φ : MulAut R) (v : R) :
    φ * MulAut.conj v * φ⁻¹ = MulAut.conj (φ v) := by
  ext x
  simp [MulAut.conj_apply]

private theorem rs_conj_mem {n : ℕ} {K : Type} [Field K] (r : TwE6Delta.RecipeR K n) :
    MulAut.conj r ∈ TwE6Delta.RecipeI K n :=
  Subgroup.subset_closure (Set.mem_union_left _ ⟨r, rfl⟩)

theorem exists_rankSix_recipe (h82 : GGTwE6ThreeTwoLocalInnToralInput)
    (h84 : GGTwE6ThreeToralTypeMinusOneInput) {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) (h3 : 3 ∣ 2 ^ n + 1)
    {S : Subgroup (MulAut (TwE6Delta.RecipeR K n))} (hS : IsElemAbelian 3 S)
    (hSI : ∀ φ ∈ S, φ ∈ TwE6Delta.RecipeI K n) (h4 : Nat.card S = 3 ^ 4)
    {V : Subgroup (TwE6Delta.RecipeR K n)} (hV : V ≠ ⊥) (hV2 : IsPGroup 2 V)
    (hSV : ∀ φ ∈ S, ∀ v ∈ V, φ v ∈ V) :
    ∃ Y : Subgroup (MulAut (TwE6Delta.RecipeR K n)),
      S ≤ Y ∧ (∀ φ ∈ Y, φ ∈ TwE6Delta.RecipeI K n) ∧ IsElemAbelian 3 Y ∧ Nat.card Y = 3 ^ 6 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨σ, hσ, ε, hε⟩ := TwE6Transport.exists_recipeConj (K := K) hn hK
  let k := GaloisField 2 (2 * n)
  let Ω := AlgebraicClosure K
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype k := Fintype.ofFinite k
  have hcard : Fintype.card (GaloisField 2 (2 * n)) = Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      CFSG.LieType.Universal.card_galoisField_two_mul 2 n hn, hK]
  let τ : k ≃+* K := FiniteField.ringEquivOfCardEq hcard
  haveI : CharP K 2 := charP_of_injective_ringHom (f := τ.toRingHom) τ.injective 2
  letI : Algebra k Ω := ((algebraMap K Ω).comp τ.toRingHom).toAlgebra
  haveI : IsAlgClosure k Ω :=
    ⟨IsAlgClosure.isAlgClosed K,
      rs_isAlgebraic_of_ringEquiv τ (fun x => rfl) (AlgebraicClosure.isAlgebraic K)⟩
  haveI : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  let Fr : Ω →+* Ω := iterateFrobenius Ω 2 n
  have hFr : ∀ c, Fr c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
  let Φ : ↥(TwistedDiag.Rgrp Ω Fr) →*
      MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) :=
    NoOffTwE6Three.rgrpConjAut hn hK σ hσ Fr hFr
  have hΦinj : Function.Injective Φ :=
    NoOffTwE6Three.rgrpConjAut_injective hn hK σ hσ Fr hFr
  have hΦrange : Φ.range = (RecipeExcLang.twConj K σ).range :=
    NoOffTwE6Three.rgrpConjAut_range hn hK σ hσ Fr hFr
  let Ψ : ↥(TwistedDiag.Rgrp Ω Fr) →* MulAut (TwE6Delta.RecipeR K n) :=
    (MulAut.congr ε).toMonoidHom.comp Φ
  have hΨinj : Function.Injective Ψ := (MulAut.congr ε).injective.comp hΦinj
  have hΨrange : Ψ.range = (TwE6Transport.recipeConj σ ε).range := by
    change ((MulAut.congr ε).toMonoidHom.comp Φ).range =
      (TwE6Transport.recipeConj σ ε).range
    rw [MonoidHom.range_comp, hΦrange]
    exact (MonoidHom.range_comp (MulAut.congr ε).toMonoidHom
      (RecipeExcLang.twConj K σ)).symm
  have hSI' : S ≤ Ψ.range := by
    intro φ hφ
    rw [hΨrange]
    exact (hε φ).2 (hSI φ hφ)
  let SZ : Subgroup ↥(TwistedDiag.Rgrp Ω Fr) := S.comap Ψ
  have hSZel : IsElemAbelian 3 SZ := hS.comap hΨinj
  have hSZcard : Nat.card SZ = 3 ^ 4 := by
    have h1 : SZ.map Ψ = S := Subgroup.map_comap_eq_self (f := Ψ) hSI'
    rw [← Subgroup.card_map_of_injective hΨinj, h1, h4]
  let UZ : Subgroup ↥(TwistedDiag.Rgrp Ω Fr) :=
    (V.map (MulAut.conj : TwE6Delta.RecipeR K n →* MulAut (TwE6Delta.RecipeR K n))).comap Ψ
  have hUZ2 : IsPGroup 2 UZ :=
    (hV2.map (MulAut.conj : TwE6Delta.RecipeR K n →*
      MulAut (TwE6Delta.RecipeR K n))).comap_of_injective Ψ hΨinj
  have hconjInj : Function.Injective
      (MulAut.conj : TwE6Delta.RecipeR K n →* MulAut (TwE6Delta.RecipeR K n)) :=
    rs_conj_injective (TwE6Delta.center_recipeR_eq_bot hn hK)
  have hVconjNe : V.map (MulAut.conj : TwE6Delta.RecipeR K n →*
      MulAut (TwE6Delta.RecipeR K n)) ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ hconjInj]
    exact hV
  have hVconjLe : V.map (MulAut.conj : TwE6Delta.RecipeR K n →*
      MulAut (TwE6Delta.RecipeR K n)) ≤ Ψ.range := by
    intro φ hφ
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 hφ
    rw [hΨrange]
    exact (hε _).2 (rs_conj_mem v)
  have hUZne : UZ ≠ ⊥ := by
    intro hbot
    apply hVconjNe
    have hmap : UZ.map Ψ = V.map (MulAut.conj : TwE6Delta.RecipeR K n →*
        MulAut (TwE6Delta.RecipeR K n)) := Subgroup.map_comap_eq_self (f := Ψ) hVconjLe
    rw [hbot, Subgroup.map_bot] at hmap
    exact hmap.symm
  have hSZnorm : SZ ≤ Subgroup.normalizer (UZ : Set ↥(TwistedDiag.Rgrp Ω Fr)) := by
    rw [Subgroup.le_normalizer_iff]
    intro s hs u hu
    obtain ⟨v, hv, hv_eq⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 hu)
    rw [Subgroup.mem_comap]
    have hcomm : Ψ (s * u * s⁻¹) = MulAut.conj ((Ψ s) v) := by
      rw [map_mul, map_mul, map_inv, ← hv_eq]
      exact rs_conj_conj (Ψ s) v
    rw [hcomm]
    exact Subgroup.mem_map.2
      ⟨(Ψ s) v, hSV (Ψ s) (Subgroup.mem_comap.1 hs) v hv, rfl⟩
  obtain ⟨ΦG, hΦGinj, hΦGrange, -⟩ :=
    NoOffTwE6Three.exists_rgrpAut_baseChange hn Ω Fr hFr
  let X : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 k (frobQ 2 n))) := SZ.map ΦG
  let U : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 k (frobQ 2 n))) := UZ.map ΦG
  have hXle : X ≤ LayerSixE.twInndiagAut n := by
    rw [← hΦGrange]
    exact Subgroup.map_le_range ΦG SZ
  have hXel : IsElemAbelian 3 X := hSZel.map ΦG
  have hXcard : Nat.card X = 3 ^ 4 := by
    rw [Subgroup.card_map_of_injective hΦGinj, hSZcard]
  have hU2 : IsPGroup 2 U := hUZ2.map ΦG
  have hUle : U ≤ LayerSixE.twInndiagAut n := by
    rw [← hΦGrange]
    exact Subgroup.map_le_range ΦG UZ
  have hUne : U ≠ ⊥ := by
    change UZ.map ΦG ≠ ⊥
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective UZ hΦGinj]
    exact hUZne
  have hXU : X ≤ Subgroup.normalizer (U : Set _) := by
    rw [Subgroup.le_normalizer_iff]
    intro x hx u hu
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨u', hu', rfl⟩ := Subgroup.mem_map.1 hu
    have hconj : ΦG s * ΦG u' * (ΦG s)⁻¹ = ΦG (s * u' * s⁻¹) := by
      rw [map_mul, map_mul, map_inv]
    rw [hconj]
    exact Subgroup.mem_map.2
      ⟨s * u' * s⁻¹, (Subgroup.le_normalizer_iff.1 hSZnorm s hs) u' hu', rfl⟩
  have hUI : U ⊓ LayerSixE.twInndiagAut n ≠ ⊥ := by
    rwa [inf_eq_left.2 hUle]
  have htor : IsToralE6 Ω ((X.comap ΦG).map (TwistedDiag.Rgrp Ω Fr).subtype) :=
    NoOffTwE6Three.isToralE6_of_inf_twInndiagAut_ne_bot h82 hn h3 Ω Fr hFr ΦG hΦGinj
      hΦGrange hXle hXel hXcard hU2 hXU hUI
  obtain ⟨Y₀, hY₀I, hXY₀, hY₀el, hY₀c⟩ :=
    NoOffTwE6Three.exists_overgroup_of_isToral h84 hn h3 Ω Fr hFr ΦG hΦGinj hΦGrange
      hXle hXel hXcard htor
  refine ⟨(Y₀.comap ΦG).map Ψ, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_comap_eq_self (f := Ψ) hSI']
    exact Subgroup.map_mono fun s hs => by
      rw [Subgroup.mem_comap]
      exact hXY₀ (Subgroup.mem_map.2 ⟨s, hs, rfl⟩)
  · intro φ hφ
    have hφrange : φ ∈ Ψ.range := Subgroup.map_le_range Ψ (Y₀.comap ΦG) hφ
    rw [hΨrange] at hφrange
    exact (hε φ).1 hφrange
  · exact (hY₀el.comap hΦGinj).map Ψ
  · have h1 : Nat.card ((Y₀.comap ΦG).map Ψ) = Nat.card (Y₀.comap ΦG) :=
      Subgroup.card_map_of_injective hΨinj
    have h2 : Nat.card (Y₀.comap ΦG) = Nat.card Y₀ := by
      have hmap : (Y₀.comap ΦG).map ΦG = Y₀ :=
        Subgroup.map_comap_eq_self (f := ΦG) (by rw [hΦGrange]; exact hY₀I)
      rw [← Subgroup.card_map_of_injective hΦGinj, hmap]
    rw [h1, h2, hY₀c]

end CFSG.StandardType.TwE6R4
