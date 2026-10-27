module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutOutdiagTwE6Glue
public import CFSG.LocalAnalysis.StandardType.GGTwE6DD2Torus
public import CFSG.LocalAnalysis.StandardType.GGTwE6FrameCard
public import CFSG.LocalAnalysis.StandardType.GGTwE6FrameNoPpdBlocks
public import CFSG.LocalAnalysis.StandardType.GGTwE6FrameNoPpdTorus
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToral
public import CFSG.LieType.Steinberg.Exceptional.Fields

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Tables.T1b CFSG.HardMathSupport.Lang.E6Descent

open CFSG.StandardType.NoOffTwE6Three CFSG.StandardType.TwE6FrameNoPpd
  CFSG.StandardType.TwE6FrameCard CFSG.StandardType.TwE6DD2
  CFSG.HardMathSupport.Lang.E6Descent.TwistedDiag

private lemma no_ppd_dvd {r e f ℓ : ℕ} (hr : r.Prime) (he : e = 12 ∨ e = 18)
    (hf : 1 ≤ f) (ho : orderOf (2 : ZMod r) = e * f)
    (hℓ1 : 1 ≤ ℓ) (hℓ10 : ℓ ≤ 10) (hℓ9 : ℓ ≠ 9) :
    ¬ (r : ℤ) ∣ (-(2 ^ f : ℤ)) ^ ℓ - 1 := by
  haveI : Fact r.Prime := ⟨hr⟩
  have h2ne : (2 : ZMod r) ≠ 0 := by
    intro h0
    rw [h0, orderOf_zero] at ho
    rcases he with rfl | rfl <;> omega
  have hneg1 : (-1 : ZMod r) ≠ 1 := by
    intro h
    apply h2ne
    calc (2 : ZMod r) = 1 + 1 := by norm_num
      _ = 1 + -1 := by rw [h]
      _ = 0 := add_neg_cancel 1
  intro hdvd_int
  let Q : ZMod r := (2 : ZMod r) ^ f
  have hQord : orderOf Q = e := by
    have hfdvd : f ∣ orderOf (2 : ZMod r) := by
      rw [ho]
      exact ⟨e, Nat.mul_comm e f⟩
    have hfne : f ≠ 0 := by omega
    calc orderOf Q = orderOf ((2 : ZMod r) ^ f) := rfl
      _ = orderOf (2 : ZMod r) / f := orderOf_pow_of_dvd hfne hfdvd
      _ = e * f / f := by rw [ho]
      _ = e := Nat.mul_div_cancel e (by omega : 0 < f)
  have hpow : (-Q) ^ ℓ = 1 := by
    have hz : (((-(2 ^ f : ℤ)) ^ ℓ - 1 : ℤ) : ZMod r) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hdvd_int
    have h := hz
    push_cast at h
    rw [sub_eq_zero] at h
    exact h
  rcases he with rfl | rfl
  · have hQ12 : Q ^ 12 = 1 := by
      rw [← hQord]
      exact pow_orderOf_eq_one Q
    have hQ6ne : Q ^ 6 ≠ 1 := by
      intro h
      have hd : orderOf Q ∣ 6 := orderOf_dvd_iff_pow_eq_one.mpr h
      rw [hQord] at hd
      norm_num at hd
    have hQ4ne : Q ^ 4 ≠ 1 := by
      intro h
      have hd : orderOf Q ∣ 4 := orderOf_dvd_iff_pow_eq_one.mpr h
      rw [hQord] at hd
      norm_num at hd
    have hQ6neg : Q ^ 6 = -1 := by
      have hsq : (Q ^ 6) ^ 2 = 1 := by
        rw [← pow_mul, show 6 * 2 = 12 by norm_num, hQ12]
      rcases sq_eq_one_iff.mp hsq with h | h
      · exact absurd h hQ6ne
      · exact h
    have hR12 : (-Q) ^ 12 = 1 :=
      (Even.neg_pow (by decide : Even 12) Q).trans hQ12
    have hR4ne : (-Q) ^ 4 ≠ 1 :=
      (Even.neg_pow (by decide : Even 4) Q).symm ▸ hQ4ne
    have hR6neg : (-Q) ^ 6 = -1 :=
      (Even.neg_pow (by decide : Even 6) Q).trans hQ6neg
    have hR6ne : (-Q) ^ 6 ≠ 1 := by
      rw [hR6neg]
      exact hneg1
    have hRord : orderOf (-Q) = 12 := by
      refine orderOf_eq_of_pow_and_pow_div_prime (n := 12) (by norm_num) hR12 ?_
      intro p hp hpd
      have hp23 : p = 2 ∨ p = 3 := by
        have hle : p ≤ 12 := Nat.le_of_dvd (by norm_num) hpd
        have hp2 : 2 ≤ p := hp.two_le
        interval_cases p <;> (norm_num at hp <;> try norm_num at hpd)
        · exact Or.inl rfl
        · exact Or.inr rfl
      rcases hp23 with rfl | rfl
      · simpa using hR6ne
      · simpa using hR4ne
    have hdvdℓ : 12 ∣ ℓ := hRord ▸ orderOf_dvd_iff_pow_eq_one.mpr hpow
    obtain ⟨k, hk⟩ := hdvdℓ
    omega
  · have hQ18 : Q ^ 18 = 1 := by
      rw [← hQord]
      exact pow_orderOf_eq_one Q
    have hQ9ne : Q ^ 9 ≠ 1 := by
      intro h
      have hd : orderOf Q ∣ 9 := orderOf_dvd_iff_pow_eq_one.mpr h
      rw [hQord] at hd
      norm_num at hd
    have hQ9neg : Q ^ 9 = -1 := by
      have hsq : (Q ^ 9) ^ 2 = 1 := by
        rw [← pow_mul, show 9 * 2 = 18 by norm_num, hQ18]
      rcases sq_eq_one_iff.mp hsq with h | h
      · exact absurd h hQ9ne
      · exact h
    have hR9 : (-Q) ^ 9 = 1 :=
      (Odd.neg_pow (by decide : Odd 9) Q).trans (by rw [hQ9neg]; exact neg_neg 1)
    have hR3ne : (-Q) ^ 3 ≠ 1 := by
      intro h
      have h' : (-Q) ^ 3 = -(Q ^ 3) := Odd.neg_pow (by decide : Odd 3) Q
      have hneg3 : -(Q ^ 3) = 1 := by rw [← h', h]
      have hQ3 : Q ^ 3 = -1 := neg_eq_iff_eq_neg.mp hneg3
      have hQ6 : Q ^ 6 = 1 := by
        have hsq : Q ^ 6 = (Q ^ 3) ^ 2 := by ring
        rw [hsq, hQ3]
        exact neg_one_sq
      have hd : orderOf Q ∣ 6 := orderOf_dvd_iff_pow_eq_one.mpr hQ6
      rw [hQord] at hd
      norm_num at hd
    have hRord : orderOf (-Q) = 9 := by
      simpa using orderOf_eq_prime_pow (p := 3) (n := 1) (x := -Q) hR3ne hR9
    have hdvdℓ : 9 ∣ ℓ := hRord ▸ orderOf_dvd_iff_pow_eq_one.mpr hpow
    obtain ⟨k, hk⟩ := hdvdℓ
    have hℓeq : ℓ = 9 := by omega
    exact hℓ9 hℓeq

theorem ggTwE6FrameNoPpdInput_holds :
    GGTwE6FrameNoPpdInput := by
  intro f hf h3 M' S hInn hSM hSI hSel hmax α hαS hα1 r hex z hz hαz
  obtain ⟨e, he, hppd⟩ := hex
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K := GaloisField 2 (2 * f)
  have hK : Nat.card K = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  let σ : K ≃+* K := frobQEquiv hf
  have hσ : ∀ c : K, σ c = c ^ 2 ^ f := fun c => by
    change frobQ 2 f c = c ^ 2 ^ f
    exact frobQ_apply 2 f c
  let Ω := AlgebraicClosure K
  let Fr : Ω →+* Ω := iterateFrobenius Ω 2 f
  have hFr : ∀ c : Ω, Fr c = c ^ 2 ^ f := fun c => iterateFrobenius_def 2 f c
  haveI : CharP K 2 := charP_two_of_card (m := f * 2) (by rw [hK, pow_mul])
  haveI : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have hcard : 3 ^ 5 ≤ Nat.card S :=
    three_pow_five_le_card_of_maximal (f := f) h3 hInn hmax
  have hSI' : S ≤ (RecipeExcLang.twConj K σ).range := by
    rw [← twInndiagAut_eq_range_twConj (f := f) hf]
    exact hSI
  obtain ⟨g, hg, hgn, hSY⟩ :=
    exists_cubeTorus_lang (n := f) hf hK σ hσ h3 Fr hFr hSel hSI' hcard
  obtain ⟨b, hb3, hxbR, hαeq⟩ :=
    (mem_langCube (n := f) hf hK σ hσ Fr hFr (g := g)).1 (hSY hαS)
  have hb1 : b ≠ 1 := by
    intro hb
    apply hα1
    rw [← hαeq]
    have hd : g * rootDiagUnit Tag.E6 b * g⁻¹ = 1 := by
      rw [hb, rootDiagUnit_one, mul_one]
      group
    have hs1 : (⟨g * rootDiagUnit Tag.E6 b * g⁻¹, hxbR⟩ :
        ↥(TwistedDiag.Rgrp Ω Fr)) = 1 := Subtype.ext hd
    rw [hs1, map_one]
    rfl
  let s : ModGL Tag.E6 Ω := g * rootDiagUnit Tag.E6 b * g⁻¹
  have hsR : s ∈ TwistedDiag.Rgrp Ω Fr := hxbR
  let w : ↥(RecipeExcLang.twInndiagGroup K σ) :=
    (twInndiagEquivRgrp hf hK σ hσ Fr hFr).symm ⟨s, hsR⟩
  let wTag : ModGL Tag.E6 K := (w : ModGL TwistTag.E6.tag K)
  let zTag : ModGL Tag.E6 K := (z : ModGL TwistTag.E6.tag K)
  have hαeq2 : RecipeExcLang.twConj K σ w = α := by
    rw [← hαeq]
    rfl
  have hzw : RecipeExcLang.twConj K σ w z = z := by
    rw [hαeq2]
    exact hαz
  have hwz : wTag * zTag * wTag⁻¹ = zTag := by
    have hthis : ((RecipeExcLang.twConj K σ w z : _) : ModGL TwistTag.E6.tag K) =
        (z : ModGL TwistTag.E6.tag K) :=
      congrArg (fun y : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) =>
        (y : ModGL TwistTag.E6.tag K)) hzw
    exact (RecipeExcLang.coe_twConj (K := K) σ w z).symm.trans hthis
  have hbase : baseChangeGL (τ := Tag.E6) (algebraMap K Ω) wTag *
      baseChangeGL (τ := Tag.E6) (algebraMap K Ω) zTag *
      (baseChangeGL (τ := Tag.E6) (algebraMap K Ω) wTag)⁻¹ =
      baseChangeGL (τ := Tag.E6) (algebraMap K Ω) zTag := by
    have hthis := congrArg (baseChangeGL (τ := Tag.E6) (algebraMap K Ω)) hwz
    calc baseChangeGL (τ := Tag.E6) (algebraMap K Ω) wTag *
          baseChangeGL (τ := Tag.E6) (algebraMap K Ω) zTag *
          (baseChangeGL (τ := Tag.E6) (algebraMap K Ω) wTag)⁻¹
        = baseChangeGL (τ := Tag.E6) (algebraMap K Ω) (wTag * zTag * wTag⁻¹) := by
          rw [map_mul, map_mul, map_inv]
      _ = baseChangeGL (τ := Tag.E6) (algebraMap K Ω) zTag := hthis
  let ιz : ModGL Tag.E6 Ω := baseChangeGL (τ := Tag.E6) (algebraMap K Ω) zTag
  have hbw : baseChangeGL (τ := Tag.E6) (algebraMap K Ω) wTag = s := by
    have h := twInndiagEquivRgrp_apply hf hK σ hσ Fr hFr w
    rw [show (twInndiagEquivRgrp hf hK σ hσ Fr hFr) w =
        (⟨s, hsR⟩ : ↥(TwistedDiag.Rgrp Ω Fr)) from
      (twInndiagEquivRgrp hf hK σ hσ Fr hFr).apply_symm_apply _] at h
    exact h.symm
  have hbase' : s * ιz * s⁻¹ = ιz := by
    rw [← hbw]
    exact hbase
  let x : ModGL Tag.E6 Ω := g⁻¹ * ιz * g
  have hxcomm : x * rootDiagUnit Tag.E6 b = rootDiagUnit Tag.E6 b * x := by
    have h1 : rootDiagUnit Tag.E6 b * x * (rootDiagUnit Tag.E6 b)⁻¹ = x := by
      calc rootDiagUnit Tag.E6 b * x * (rootDiagUnit Tag.E6 b)⁻¹ =
          g⁻¹ * (s * ιz * s⁻¹) * g := by
            change rootDiagUnit Tag.E6 b * (g⁻¹ * ιz * g) *
                (rootDiagUnit Tag.E6 b)⁻¹ =
              g⁻¹ * ((g * rootDiagUnit Tag.E6 b * g⁻¹) * ιz *
                (g * rootDiagUnit Tag.E6 b * g⁻¹)⁻¹) * g
            group
        _ = g⁻¹ * ιz * g := by rw [hbase']
        _ = x := rfl
    have h2 : rootDiagUnit Tag.E6 b * x = x * rootDiagUnit Tag.E6 b := by
      calc rootDiagUnit Tag.E6 b * x =
          rootDiagUnit Tag.E6 b * x * (rootDiagUnit Tag.E6 b)⁻¹ *
            rootDiagUnit Tag.E6 b := by group
        _ = x * rootDiagUnit Tag.E6 b := by rw [h1]
    exact h2.symm
  have hιzR : ιz ∈ TwistedDiag.Rgrp Ω Fr := by
    let zΓ : ↥(RecipeExcLang.twInndiagGroup K σ) :=
      ⟨(z : ModGL TwistTag.E6.tag K), RecipeExcLang.graphFixedRootGroup_le_twInndiag σ z.2⟩
    have h := (twInndiagEquivRgrp hf hK σ hσ Fr hFr zΓ).2
    change baseChangeGL (τ := Tag.E6) (algebraMap K Ω) zTag ∈ TwistedDiag.Rgrp Ω Fr at h
    simpa [ιz] using h
  have hxR : g * x * g⁻¹ ∈ TwistedDiag.Rgrp Ω Fr := by
    have hxg : g * x * g⁻¹ = ιz := by
      change g * (g⁻¹ * ιz * g) * g⁻¹ = ιz
      group
    rw [hxg]
    exact hιzR
  have hxθ : x ∈ TwistedDiag.thetaFixed Fr :=
    (TwistedDiag.mem_thetaFixed_iff_conj Fr hg hgn x).2 hxR
  have hzpow' : (z : ModGL TwistTag.E6.tag K) ^ r = 1 := by
    have hp := pow_orderOf_eq_one z
    rw [hz] at hp
    have h := congrArg (fun y : ↥(graphFixedRootGroup TwistTag.E6 K (frobQ 2 f)) =>
      (y : ModGL TwistTag.E6.tag K)) hp
    simpa using h
  have hzpow : zTag ^ r = 1 := hzpow'
  have hιzpow : ιz ^ r = 1 := by
    change (baseChangeGL (τ := Tag.E6) (algebraMap K Ω) zTag) ^ r = 1
    rw [← map_pow, hzpow, map_one]
  have hxr : x ^ r = 1 := by
    calc x ^ r = g⁻¹ * ιz ^ r * g := by
          rw [show x = g⁻¹ * ιz * g from rfl]
          rw [show g⁻¹ * ιz * g = (g⁻¹) * ιz * (g⁻¹)⁻¹ by group]
          exact conj_pow
      _ = 1 := by rw [hιzpow]; group
  have hx1 : x ≠ 1 := by
    intro hxone
    have hιzone : ιz = 1 := by
      calc ιz = g * x * g⁻¹ := by
            rw [show x = g⁻¹ * ιz * g from rfl]
            group
        _ = 1 := by rw [hxone]; group
    have hzone : zTag = 1 := by
      apply baseChangeGL_injective (algebraMap K Ω) (τ := Tag.E6)
      simpa [ιz] using hιzone
    have hz1 : z = 1 := Subtype.ext hzone
    rw [hz1, orderOf_one] at hz
    exact hppd.1.ne_one hz.symm
  have he12 : e = 12 ∨ e = 18 := by
    simpa [ggOutdiagExpsTwE6] using he
  haveI : Fact r.Prime := ⟨hppd.1⟩
  have h12 : 12 ≤ e * f := by
    rcases he12 with rfl | rfl <;> nlinarith [hf]
  have h2ne : (2 : ZMod r) ≠ 0 := by
    intro h0
    have ho : orderOf (2 : ZMod r) = e * f := hppd.2
    rw [h0, orderOf_zero] at ho
    omega
  have hdvd : e * f ∣ r - 1 := hppd.2 ▸ ZMod.orderOf_dvd_card_sub_one h2ne
  have hr13 : 13 ≤ r := by
    have hpos : 0 < r - 1 := by
      have := hppd.1.two_le
      omega
    have hle := Nat.le_of_dvd hpos hdvd
    omega
  have hr5 : 5 < r := by omega
  have hr3 : 3 < r := by omega
  have halg : letI := ZMod.algebra Ω 2; Algebra.IsAlgebraic (ZMod 2) Ω :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.isAlgebraic_zmod_algebraicClosure_of_finite K 2
  obtain ⟨c, u, hcr, hcne, hu, hcu⟩ :=
    exists_weylAct_eq_of_mem_thetaFixed (Ω := Ω) (n := f) halg Fr hFr hxθ hxcomm
      hppd.1 hr5 hxr hx1
  obtain ⟨ℓ, hℓ1, hℓ10, hℓ9, hdvdℓ⟩ :=
    exists_dvd_pow_sub_one_of_mem_kernelReflectionGroup (K := Ω) hb3 hb1 hu hppd.1 hr3
      hcr hcne (m := -(2 ^ f : ℤ)) hcu
  exact (no_ppd_dvd hppd.1 he12 hf hppd.2 hℓ1 hℓ10 hℓ9) hdvdℓ

end CFSG.StandardType
