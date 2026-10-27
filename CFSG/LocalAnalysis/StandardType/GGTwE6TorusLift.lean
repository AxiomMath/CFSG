module

public import CFSG.LocalAnalysis.StandardType.GGTwE6TorusDefs
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeTwE6TwoSc
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeTwE6TwoCore
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyDefs
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExc
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.PartOne.KE.E8D4Family
public import CFSG.RankThree.PartOne.KE.ThreeA1Group
public import CFSG.Walter.JRFacts
public import Certificates.Certificate1953
public import Certificates.Certificate1954

public section

namespace CFSG.StandardType.TwE6Tori

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3
  CFSG.LieType.Steinberg.CentralExt.MinusculeClosed

private theorem l10mlift_e6StarS_map {k L : Type} [Field k] [Field L] (ι : k →+* L)
    (j : Fin Tag.E6.rank) (v : Fin Tag.E6.rank → kˣ) :
    e6StarS j (fun l => Units.map ι.toMonoidHom (v l)) =
      fun l => Units.map ι.toMonoidHom (e6StarS j v l) := by
  funext l
  simp only [e6StarS, Pi.mul_apply, map_mul]
  congr 1
  by_cases hl : l = j
  · subst hl
    simp only [Pi.mulSingle_eq_same]
    rw [map_prod]
    exact Finset.prod_congr rfl fun i _ => (map_zpow (Units.map ι.toMonoidHom) (v i) _).symm
  · rw [Pi.mulSingle_eq_of_ne hl, Pi.mulSingle_eq_of_ne hl, map_one]

theorem twE6Fp_map {k L : Type} [Field k] [Field L] (ι : k →+* L) (θ : k →+* k) (Fr : L →+* L)
    (h : Fr.comp ι = ι.comp θ) (ω : List (Fin Tag.E6.rank)) (u : Fin Tag.E6.rank → kˣ) :
    twE6Fp Fr ω (fun j => Units.map ι.toMonoidHom (u j)) =
      fun j => Units.map ι.toMonoidHom (twE6Fp θ ω u j) := by
  have h' : ∀ c : k, Fr (ι c) = ι (θ c) := fun c => RingHom.congr_fun h c
  induction ω generalizing u with
  | nil =>
    funext j
    simp only [twE6Fp, List.foldr_nil]
    apply Units.ext
    simp only [Units.coe_map]
    exact h' _
  | cons j ω ih =>
    have h1 : twE6Fp Fr (j :: ω) (fun j => Units.map ι.toMonoidHom (u j)) =
        e6StarS j (twE6Fp Fr ω (fun j => Units.map ι.toMonoidHom (u j))) := by
      simp only [twE6Fp, List.foldr_cons]
    have h2 : twE6Fp θ (j :: ω) u = e6StarS j (twE6Fp θ ω u) := by
      simp only [twE6Fp, List.foldr_cons]
    rw [h1, h2, ih, l10mlift_e6StarS_map]

private theorem l10mlift_sigma_minTorus
    {k : Type} [Field k] (θ : k →+* k) (u : Fin Tag.E6.rank → kˣ) :
    TwistedE6.sigma k θ (minTorus e6Data_valid k u) =
      minTorus e6Data_valid k (fun l => Units.map θ.toMonoidHom (u (e6RhoFour l))) := by
  induction u using CFSG.LieType.Chevalley.ExceptionalCover.torusVec_induction with
  | h1 =>
    have e : (fun l => Units.map θ.toMonoidHom ((1 : Fin Tag.E6.rank → kˣ) (e6RhoFour l))) =
        1 := by
      funext l
      simp
    rw [map_one, map_one, e, map_one]
  | hmul t t' ht ht' =>
    have e : (fun l => Units.map θ.toMonoidHom ((t * t') (e6RhoFour l))) =
        (fun l => Units.map θ.toMonoidHom (t (e6RhoFour l))) *
          fun l => Units.map θ.toMonoidHom (t' (e6RhoFour l)) := by
      funext l
      simp
    rw [map_mul, map_mul, ht, ht', e, map_mul]
  | hsingle a s =>
    have e : (fun l => Units.map θ.toMonoidHom
        ((Pi.mulSingle a s : Fin Tag.E6.rank → kˣ) (e6RhoFour l))) =
        Pi.mulSingle (e6RhoFour a) (Units.map θ.toMonoidHom s) := by
      funext l
      by_cases hl : l = e6RhoFour a
      · subst hl
        simp [e6RhoFour_apply_apply]
      · have : e6RhoFour l ≠ a := fun h => hl (by rw [← h, e6RhoFour_apply_apply])
        simp [Pi.mulSingle_eq_of_ne hl, Pi.mulSingle_eq_of_ne this]
    rw [e, minTorus_mulSingle, minTorus_mulSingle, TwistedE6.sigma_hm]
    rfl

private theorem l10mlift_sigma_minBC
    {k k' : Type} [Field k] [Field k'] (ι : k →+* k')
    (θ : k →+* k) (θ' : k' →+* k') (h : θ'.comp ι = ι.comp θ) (g : e6Data_valid.minGroup k) :
    TwistedE6.sigma k' θ' (minBC e6Data_valid ι g) =
      minBC e6Data_valid ι (TwistedE6.sigma k θ g) := by
  have hh : (TwistedE6.sigma k' θ').comp (minBC e6Data_valid ι) =
      (minBC e6Data_valid ι).comp (TwistedE6.sigma k θ) := by
    refine MonoidHom.eq_of_eqOn_dense (closure_xm_simple_eq_top e6Data_valid k) ?_
    rintro _ ⟨i, c, rfl | rfl⟩
    · simp only [MonoidHom.comp_apply]
      rw [minBC_xm_single, TwistedE6.sigma_xm_single, TwistedE6.sigma_xm_single, minBC_xm_single]
      exact congrArg _ (RingHom.congr_fun h c)
    · simp only [MonoidHom.comp_apply]
      rw [minBC_xm_neg_single, TwistedE6.sigma_xm_neg_single, TwistedE6.sigma_xm_neg_single,
        minBC_xm_neg_single]
      exact congrArg _ (RingHom.congr_fun h c)
  exact DFunLike.congr_fun hh g

private theorem l10mlift_nWord_sigma_minTorus
    {k : Type} [Field k] (θ : k →+* k) (ω : List (Fin Tag.E6.rank))
    (u : Fin Tag.E6.rank → kˣ) :
    e6NWord k ω * TwistedE6.sigma k θ (minTorus e6Data_valid k u) * (e6NWord k ω)⁻¹ =
      minTorus e6Data_valid k (twE6Fp θ ω u) := by
  rw [twE6Fp, l10mlift_sigma_minTorus, e6RhoFour_eq_twistPerm, nWord_conj_minTorus]
  rfl

theorem twE6_fixed_lift
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2) {k : Type} [Field k] [Finite k] [CharP k 2] (ι : K →+* k)
    (ω : List (Fin Tag.E6.rank)) {g₀ : ModGL Tag.E6 k} (hg₀ : g₀ ∈ adjointGroup Tag.E6 k)
    (hLang : twistHom TwistTag.E6 k (iterateFrobenius k 2 1) g₀ =
      g₀ * canonicalRep (coxeterSystem Tag.E6) k ((coxeterSystem Tag.E6).wordProd ω))
    {t : ModGL Tag.E6 K} (ht : t ∈ twistedE6RootGroup K σ) :
    ∃ sl : e6Data_valid.minGroup k,
      e6NWord k ω * TwistedE6.sigma k (iterateFrobenius k 2 1) sl * (e6NWord k ω)⁻¹ = sl ∧
        ((e6Isogeny k sl : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) =
          g₀⁻¹ * baseChangeGL ι t * g₀ := by
  have hK2 : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  have hσ2 : ∀ c, σ c = c ^ (2 ^ 1) := fun c => by rw [hσ]; norm_num
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hder, -, -, -⟩ :=
    CFSG.LieType.Chevalley.twisted_E6_all_characteristic_exact_automorphism_normal_form
      Nat.prime_two le_rfl K hK2 σ hσ2
  have hθθ : ∀ c, σ.toRingHom (σ.toRingHom c) = c := fun c => by
    have : Fintype K := Fintype.ofFinite K
    have h := FiniteField.pow_card c
    rw [← Nat.card_eq_fintype_card, hK] at h
    simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ, ← pow_mul]
    exact h
  have hk4 : 4 ≤ Nat.card K := hK.ge
  obtain ⟨⟨sK, hsKfix⟩, hsK⟩ : t ∈ (e6IsogenyFixed σ.toRingHom).range := by
    rw [range_e6IsogenyFixed σ.toRingHom hθθ hk4, hder]
    exact ht
  have hsKσ : TwistedE6.sigma K σ.toRingHom sK = sK := (TwistedE6.mem_fixedGroup _).1 hsKfix
  have hsKt : ((e6Isogeny K sK : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) = t := hsK
  obtain ⟨gt, hgt⟩ := e6Isogeny_surjective k ⟨g₀, hg₀⟩
  have hgtπ : ((e6Isogeny k gt : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) = g₀ := by rw [hgt]
  obtain ⟨θk, hθkdef⟩ : ∃ θk : k →+* k, θk = iterateFrobenius k 2 1 := ⟨_, rfl⟩
  rw [← hθkdef] at hLang ⊢
  have hθkc : ∀ c, θk c = c ^ 2 := fun c => by rw [hθkdef, iterateFrobenius_two_one]
  have hcomp : θk.comp ι = ι.comp σ.toRingHom := RingHom.ext fun c => by
    simp only [RingHom.comp_apply, hθkc, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ,
      map_pow]
  have hn : ((e6Isogeny k (e6NWord k ω) : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) =
      canonicalRep (coxeterSystem Tag.E6) k ((coxeterSystem Tag.E6).wordProd ω) := by
    rw [e6Isogeny_nWord,
      CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_wordProd_of_charTwo]
  have hσgt : ((e6Isogeny k (TwistedE6.sigma k θk gt) : adjointGroup Tag.E6 k) :
      ModGL Tag.E6 k) = g₀ * canonicalRep (coxeterSystem Tag.E6) k
        ((coxeterSystem Tag.E6).wordProd ω) := by
    rw [e6Isogeny_sigma θk gt, ← hLang, ← hgtπ]
    rfl
  obtain ⟨z, hz⟩ : ∃ z, z = (gt * e6NWord k ω)⁻¹ * TwistedE6.sigma k θk gt := ⟨_, rfl⟩
  have hzc : z ∈ Subgroup.center (e6Data_valid.minGroup k) := by
    refine mem_center_of_isogeny_eq_one ?_
    rw [hz, map_mul, map_inv, map_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul,
      hgtπ, hn, hσgt]
    group
  have hσg : TwistedE6.sigma k θk gt = gt * e6NWord k ω * z := by rw [hz]; group
  have hzc' : ∀ w : e6Data_valid.minGroup k, z⁻¹ * w * z = w := fun w => by
    have h := Subgroup.mem_center_iff.1 hzc w
    calc z⁻¹ * w * z = z⁻¹ * (w * z) := by group
      _ = z⁻¹ * (z * w) := by rw [h]
      _ = w := by group
  refine ⟨gt⁻¹ * minBC e6Data_valid ι sK * gt, ?_, ?_⟩
  · rw [map_mul, map_mul, map_inv, hσg, l10mlift_sigma_minBC ι σ.toRingHom θk hcomp, hsKσ]
    calc e6NWord k ω * ((gt * e6NWord k ω * z)⁻¹ * minBC e6Data_valid ι sK *
          (gt * e6NWord k ω * z)) * (e6NWord k ω)⁻¹ =
        e6NWord k ω * (z⁻¹ * ((e6NWord k ω)⁻¹ * gt⁻¹ * minBC e6Data_valid ι sK * gt *
          e6NWord k ω) * z) * (e6NWord k ω)⁻¹ := by group
      _ = e6NWord k ω * ((e6NWord k ω)⁻¹ * gt⁻¹ * minBC e6Data_valid ι sK * gt *
          e6NWord k ω) * (e6NWord k ω)⁻¹ := by rw [hzc']
      _ = gt⁻¹ * minBC e6Data_valid ι sK * gt := by group
  · rw [map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hgtπ,
      e6Isogeny_minBC, hsKt]

theorem twE6_fixed_lift_torus
    {k : Type} [Field k] [Finite k] [CharP k 2] (ω : List (Fin Tag.E6.rank))
    {sl : e6Data_valid.minGroup k}
    (hsl : e6NWord k ω * TwistedE6.sigma k (iterateFrobenius k 2 1) sl * (e6NWord k ω)⁻¹ = sl)
    (u₀ : Fin Tag.E6.rank → kˣ)
    (hπ : ((e6Isogeny k sl : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) =
      rootDiagUnit Tag.E6 (e6RootParams u₀)) :
    ∃ u : Fin Tag.E6.rank → kˣ,
      twE6Fp (iterateFrobenius k 2 1) ω u = u ∧ e6RootParams u = e6RootParams u₀ := by
  have hπT : ((e6Isogeny k (minTorus e6Data_valid k u₀) : adjointGroup Tag.E6 k) :
      ModGL Tag.E6 k) = rootDiagUnit Tag.E6 (e6RootParams u₀) := e6Isogeny_minTorus u₀
  have hzπ : ((e6Isogeny k (sl * (minTorus e6Data_valid k u₀)⁻¹) : adjointGroup Tag.E6 k) :
      ModGL Tag.E6 k) = 1 := by
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hπ, hπT]
    group
  have hzc : sl * (minTorus e6Data_valid k u₀)⁻¹ ∈
      Subgroup.center (e6Data_valid.minGroup k) := mem_center_of_isogeny_eq_one hzπ
  obtain ⟨v, hv, hv3⟩ := exists_minTorus_of_mem_center_E6 hzc
  have hsl' : sl = minTorus e6Data_valid k (v * u₀) := by
    have h : sl = minTorus e6Data_valid k v * minTorus e6Data_valid k u₀ := by
      rw [← hv]; group
    rw [h, ← map_mul]
  have hfix : twE6Fp (iterateFrobenius k 2 1) ω (v * u₀) = v * u₀ := by
    have h1 : e6NWord k ω * TwistedE6.sigma k (iterateFrobenius k 2 1)
        (minTorus e6Data_valid k (v * u₀)) * (e6NWord k ω)⁻¹ =
        minTorus e6Data_valid k (v * u₀) := by
      rw [← hsl']
      exact hsl
    rw [l10mlift_nWord_sigma_minTorus] at h1
    exact minTorus_injective e6Data_valid k h1
  have hparam_v : e6RootParams v = 1 := by
    have h1 : rootDiagUnit Tag.E6 (e6RootParams v) = 1 := by
      rw [← e6Isogeny_minTorus v, ← hv]
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hπ, hπT]
      group
    exact CFSG.LieType.Chevalley.rootDiagUnit_injective (τ := Tag.E6) (K := k)
      (by rw [h1, rootDiagUnit_one (τ := Tag.E6) (K := k)])
  refine ⟨v * u₀, hfix, ?_⟩
  have hparam_mul : e6RootParams (v * u₀) = e6RootParams v * e6RootParams u₀ := by
    funext j
    simp only [e6RootParams, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]
  rw [hparam_mul, hparam_v, one_mul]

end CFSG.StandardType.TwE6Tori

end
