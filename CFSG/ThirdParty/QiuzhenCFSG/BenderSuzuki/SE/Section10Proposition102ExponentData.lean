module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section10Proposition102Fitting

namespace CFSG
end CFSG
open CFSG

/-!
# Section 10, Proposition 10.2(c): source-specific exponent data

This module specializes the generic inverted-set arithmetic to the nilpotent
derived subgroup from Proposition 10.2(a).  A chosen prime divisor of
`|E' ∩ V|` yields a nontrivial `r`-subgroup in `A₁`, the factorization
`|I| = r^a (2^p - 1)`, and `r ∣ 2^p - 1`.  The later uniqueness, Sylow, and
Fitting conclusions are deliberately left to the Proposition 10.2 assembly.
-/

noncomputable section

set_option maxHeartbeats 2000000

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise

universe u

public theorem proposition102_pSubgroup_le_mapped_pCore_of_nilpotent
    {X : Type u} [Group X] [Finite X]
    {r : ℕ} (hr : r.Prime) {H B : Subgroup X}
    (hBH : B ≤ H) (hBp : IsPGroup r B)
    (hnil : Group.IsNilpotent H) :
    B ≤ (pCore r H).map H.subtype := by
  letI : Fact r.Prime := ⟨hr⟩
  have hBHp : IsPGroup r (B.subgroupOf H) := by
    exact hBp.of_equiv (Subgroup.subgroupOfEquivOfLe hBH).symm
  obtain ⟨S, hBS⟩ := hBHp.exists_le_sylow
  have hSnormal : (S : Subgroup H).Normal :=
    hnil.sylow_normal r S
  have hScore : (S : Subgroup H) ≤ pCore r H :=
    le_sSup ⟨hSnormal, S.isPGroup'⟩
  intro x hx
  let xH : H := ⟨x, hBH hx⟩
  have hxBH : xH ∈ B.subgroupOf H := by
    exact hx
  have hxS : xH ∈ (S : Subgroup H) := hBS hxBH
  have hxCore : xH ∈ pCore r H := hScore hxS
  exact ⟨xH, hxCore, rfl⟩

public theorem proposition102_invertedCard_eq_kset_card
    {X : Type u} [Group X] [Finite X]
    {D H : Subgroup X} {t : X}
    (ht : IsInvolution t) (hHD : H ≤ D)
    (hKH : peterfalviKSet D t ⊆ H) :
    theorem4bInvertedCard t H =
      Nat.card {x : X // x ∈ peterfalviKSet D t} := by
  have hset :
      {x : X | x ∈ H ∧ t * x * t⁻¹ = x⁻¹} =
        peterfalviKSet D t := by
    ext x
    constructor
    · intro hx
      refine ⟨hHD hx.1, ?_⟩
      simpa [peterfalviKSet, rightConjugateElem, ht.inv_eq_self] using hx.2
    · intro hx
      exact ⟨hKH hx, by
        simpa [peterfalviKSet, rightConjugateElem, ht.inv_eq_self] using hx.2⟩
  calc
    theorem4bInvertedCard t H =
        Nat.card {x : X // x ∈ H ∧ t * x * t⁻¹ = x⁻¹} := rfl
    _ = Nat.card {x : X // x ∈ peterfalviKSet D t} :=
      Nat.card_congr (Set.equivOfEq hset)

public theorem proposition102_invertedCard_centralizer_eq_kset_card
    {X : Type u} [Group X] [Finite X]
    {D H R : Subgroup X} {t : X}
    (ht : IsInvolution t) (hHD : H ≤ D)
    (hKH : peterfalviKSet D t ⊆ H) :
    theorem4bInvertedCard t (subgroupCentralizerIn H R) =
      Nat.card {x : X // x ∈ peterfalviKSet D t ∧
        x ∈ Subgroup.centralizer (R : Set X)} := by
  have hset :
      {x : X | x ∈ subgroupCentralizerIn H R ∧
          t * x * t⁻¹ = x⁻¹} =
        {x : X | x ∈ peterfalviKSet D t ∧
          x ∈ Subgroup.centralizer (R : Set X)} := by
    ext x
    constructor
    · intro hx
      refine ⟨⟨hHD hx.1.1, by
        simpa [peterfalviKSet, rightConjugateElem, ht.inv_eq_self] using hx.2⟩,
        hx.1.2⟩
    · intro hx
      exact ⟨⟨hKH hx.1, hx.2⟩, by
        simpa [peterfalviKSet, rightConjugateElem, ht.inv_eq_self] using hx.1.2⟩
  calc
    theorem4bInvertedCard t (subgroupCentralizerIn H R) =
        Nat.card {x : X // x ∈ subgroupCentralizerIn H R ∧
          t * x * t⁻¹ = x⁻¹} := rfl
    _ = Nat.card {x : X // x ∈ peterfalviKSet D t ∧
        x ∈ Subgroup.centralizer (R : Set X)} :=
      Nat.card_congr (Set.equivOfEq hset)

public theorem proposition102_involution_mem_normalizer_centralizer_singleton
    {X : Type u} [Group X] {t : X} (ht : IsInvolution t) :
    t ∈ Subgroup.normalizer
      (Subgroup.centralizer ({t} : Set X) : Set X) := by
  have htt : t * t = 1 := by
    simpa [pow_two] using ht.sq_eq_one
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx y hy
    simp only [Set.mem_singleton_iff] at hy
    subst y
    have hxt := hx t rfl
    rw [ht.inv_eq_self]
    calc
      t * (t * x * t) = (t * t) * x * t := by group
      _ = x * t := by rw [htt, one_mul]
      _ = t * x := hxt.symm
      _ = t * x * (t * t) := by rw [htt, mul_one]
      _ = (t * x * t) * t := by group
  · intro hx y hy
    simp only [Set.mem_singleton_iff] at hy
    subst y
    have hxt := hx t rfl
    rw [ht.inv_eq_self] at hxt
    calc
      t * x = t * x * (t * t) := by rw [htt, mul_one]
      _ = (t * x * t) * t := by group
      _ = t * (t * x * t) := hxt.symm
      _ = (t * t) * x * t := by group
      _ = x * t := by rw [htt, one_mul]

public structure Proposition102ExponentConclusion
    {X : Type u} [Group X] [Finite X]
    (M W D E : Subgroup X) (t : X)
    (d : Lemma101Conclusion M W D E (peterfalviV D t) t) where
  r : ℕ
  r_prime : r.Prime
  r_ne_p : r ≠ d.choice.p
  a : ℕ
  a_pos : 1 ≤ a
  R : Subgroup X
  R_eq :
    R =
      (pCore r ((derivedSubgroup E).map E.subtype)).map
          ((derivedSubgroup E).map E.subtype).subtype ⊓
        peterfalviV D t
  R_ne_bot : R ≠ ⊥
  R_isPGroup : IsPGroup r R
  R_le_A1 : R ≤ d.choice.initial.A1
  R_le_derived_inf_V :
    R ≤ (derivedSubgroup E).map E.subtype ⊓ peterfalviV D t
  r_dvd_derived_inf_card :
    r ∣ Nat.card
      ((derivedSubgroup E).map E.subtype ⊓ peterfalviV D t : Subgroup X)
  r_dvd_derived_card :
    r ∣ Nat.card ((derivedSubgroup E).map E.subtype)
  kset_card_eq :
    Nat.card {x : X // x ∈ peterfalviKSet D t} =
      r ^ a * (2 ^ d.choice.p - 1)
  r_dvd_mersenne : r ∣ (2 ^ d.choice.p - 1)

public theorem proposition102_exponent_data_of_prime_dvd
    {X : Type u} [Group X] [Finite X]
    {M W D E : Subgroup X} {t : X}
    (d : Lemma101Conclusion M W D E (peterfalviV D t) t)
    (h : Proposition102PartAConclusion M W D E (peterfalviV D t) t d)
    (ht : IsInvolution t)
    (hDodd : Odd (Nat.card D))
    (hED : E ≤ D)
    (htnormD : t ∈ Subgroup.normalizer (D : Set X))
    (htnormE : t ∈ Subgroup.normalizer (E : Set X))
    (hVC : peterfalviV D t ⊓
      Subgroup.centralizer (peterfalviKSet D t) = ⊥)
    {r : ℕ} (hr : r.Prime)
    (hrdvd : r ∣ Nat.card
      ((derivedSubgroup E).map E.subtype ⊓ peterfalviV D t : Subgroup X)) :
    ∃ e : Proposition102ExponentConclusion M W D E t d, e.r = r := by
  let V : Subgroup X := peterfalviV D t
  let H : Subgroup X := (derivedSubgroup E).map E.subtype
  let P : Subgroup X := d.choice.P
  let A1 : Subgroup X := d.choice.initial.A1
  let Kset : Set X := peterfalviKSet D t
  let hnil : Group.IsNilpotent H := proposition102_derived_nilpotent h
  have hHleE : H ≤ E := by
    change (derivedSubgroup E).map E.subtype ≤ E
    exact Subgroup.map_subtype_le (derivedSubgroup E)
  have hHleD : H ≤ D := hHleE.trans hED
  have hKH : Kset ⊆ H := by
    intro x hx
    have hxK : x ∈ Subgroup.closure Kset := Subgroup.subset_closure hx
    have hcl : Subgroup.closure Kset ≤ lemma106H d := le_sup_left
    have hxH : x ∈ lemma106H d := hcl hxK
    simpa [H, h.derived_eq_H] using hxH
  letI : Fact r.Prime := ⟨hr⟩
  let HV : Subgroup X := H ⊓ V
  change r ∣ Nat.card HV at hrdvd
  let T : Sylow r HV := default
  have hrdvdT : r ∣ Nat.card (T : Subgroup HV) :=
    T.dvd_card_of_dvd_card hrdvd
  have hTne : (T : Subgroup HV) ≠ ⊥ := by
    intro hTbot
    have hcardT : Nat.card (T : Subgroup HV) = 1 := by simp [hTbot]
    rw [hcardT] at hrdvdT
    exact hr.not_dvd_one hrdvdT
  let B : Subgroup X := (T : Subgroup HV).map HV.subtype
  have hBne : B ≠ ⊥ := by
    intro hBbot
    apply hTne
    exact (Subgroup.map_eq_bot_iff_of_injective
      (T : Subgroup HV) HV.subtype_injective).mp hBbot
  have hBHV : B ≤ H ⊓ V := by
    intro x hx
    exact Subgroup.map_subtype_le (T : Subgroup HV) hx
  have hBp : IsPGroup r B := by
    simpa [B] using T.isPGroup'.map HV.subtype
  have hBS1 : B ≤ (pCore r H).map H.subtype := by
    exact proposition102_pSubgroup_le_mapped_pCore_of_nilpotent hr
      (hBHV.trans inf_le_left) hBp hnil
  let S1 : Subgroup X := (pCore r H).map H.subtype
  let S2 : Subgroup X := (pPrimeCore r H).map H.subtype
  let R : Subgroup X := S1 ⊓ V
  have hBR : B ≤ R := by
    exact le_inf (hBS1) (hBHV.trans inf_le_right)
  have hRne : R ≠ ⊥ := ne_bot_of_le_ne_bot hBne hBR
  have hRleV : R ≤ V := inf_le_right
  have hRleS1 : R ≤ S1 := inf_le_left
  have hRleHV : R ≤ H ⊓ V := by
    exact le_inf (hRleS1.trans (by
      simpa [S1] using Subgroup.map_subtype_le (pCore r H))) hRleV
  have hprod0 :=
    proposition102_nilpotent_internalDirectProduct_pCore_pPrimeCore r hr hnil
  have hprod : Section2.IsInternalDirectProduct H S1 S2 := by
    simpa [S1, S2] using
      proposition102_internalDirectProduct_map_subtype_top hprod0
  have htNormH : t ∈ Subgroup.normalizer (H : Set X) := by
    simpa [H] using
      (proposition102_normalizer_le_normalizer_map_subtype_of_characteristic
        E (derivedSubgroup E)) htnormE
  have htNormS1 : t ∈ Subgroup.normalizer (S1 : Set X) := by
    simpa [S1] using
      (proposition102_normalizer_le_normalizer_map_subtype_of_characteristic
        H (pCore r H)) htNormH
  have htNormS2 : t ∈ Subgroup.normalizer (S2 : Set X) := by
    simpa [S2] using
      (proposition102_normalizer_le_normalizer_map_subtype_of_characteristic
        H (pPrimeCore r H)) htNormH
  have htNormV : t ∈ Subgroup.normalizer (V : Set X) := by
    have htNormC := proposition102_involution_mem_normalizer_centralizer_singleton ht
    exact (Subgroup.le_normalizer_inf
      (A := Subgroup.zpowers t)
      (H := D) (K := Subgroup.centralizer ({t} : Set X))
      (Subgroup.zpowers_le.mpr htnormD)
      (Subgroup.zpowers_le.mpr htNormC)) (Subgroup.mem_zpowers t)
  have htNormR : t ∈ Subgroup.normalizer (R : Set X) := by
    exact (Subgroup.le_normalizer_inf
      (A := Subgroup.zpowers t)
      (H := S1) (K := V)
      (Subgroup.zpowers_le.mpr htNormS1)
      (Subgroup.zpowers_le.mpr htNormV)) (Subgroup.mem_zpowers t)
  have hPE : P ≤ E := by
    simpa [P] using d.choice.P_eq_map ▸
      (Subgroup.map_subtype_le (d.choice.S : Subgroup E))
  have hHnormE : E ≤ Subgroup.normalizer (H : Set X) := by
    have hHnormalE : (H.subgroupOf E).Normal := by
      change (((derivedSubgroup E).map E.subtype).subgroupOf E).Normal
      rw [subgroupOf_map_subtype_eq]
      infer_instance
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hHleE).mp hHnormalE
  have hPnormH : P ≤ Subgroup.normalizer (H : Set X) := hPE.trans hHnormE
  have hPnormS1 : P ≤ Subgroup.normalizer (S1 : Set X) := by
    intro p hp
    simpa [S1] using
      (proposition102_normalizer_le_normalizer_map_subtype_of_characteristic
        H (pCore r H)) (hPnormH hp)
  have hPnormS2 : P ≤ Subgroup.normalizer (S2 : Set X) := by
    intro p hp
    simpa [S2] using
      (proposition102_normalizer_le_normalizer_map_subtype_of_characteristic
        H (pPrimeCore r H)) (hPnormH hp)
  have hPnormV : P ≤ Subgroup.normalizer (V : Set X) := by
    exact d.choice.P_le_V.trans (Subgroup.le_normalizer (H := V))
  have hPnormR : P ≤ Subgroup.normalizer (R : Set X) := by
    exact Subgroup.le_normalizer_inf hPnormS1 hPnormV
  have hA1V : A1 ≤ V := by
    change d.choice.initial.A1 ≤ V
    rw [d.choice.initial.A1_eq]
    exact inf_le_left
  have hVnormA1 : V ≤ Subgroup.normalizer (A1 : Set X) := by
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hA1V).mp
      d.choice.initial.A1_normal_V
  have hPnormA1 : P ≤ Subgroup.normalizer (A1 : Set X) :=
    d.choice.P_le_V.trans hVnormA1
  have hcommA1 : ⁅A1, P⁆ ≤ A1 :=
    section12_commutator_le_left_of_le_normalizer hPnormA1
  have hRleA1 : R ≤ A1 := by
    calc
      R ≤ H ⊓ V := hRleHV
      _ = ⁅A1, P⁆ := by
        simpa [H, V, A1, P] using h.derived_inf_V
      _ ≤ A1 := hcommA1
  have hcentralRcard :
      Nat.card {x : X // x ∈ Kset ∧
        x ∈ Subgroup.centralizer (R : Set X)} = 2 ^ d.choice.p - 1 := by
    have hset := d.centralizer_uniform R hRleA1 hRne hPnormR
    calc
      Nat.card {x : X // x ∈ Kset ∧
          x ∈ Subgroup.centralizer (R : Set X)} =
          Nat.card {x : X // x ∈ peterfalviKSet D t ∧
            x ∈ Subgroup.centralizer (d.choice.initial.A1 : Set X)} := by
        exact Nat.card_congr (Set.equivOfEq hset)
      _ = Nat.card d.choice.initial.J := by
        exact Nat.card_congr (Set.equivOfEq d.centralizer_A1.symm)
      _ = 2 ^ d.choice.p - 1 := d.centralizer_A1_card
  let C1 : Subgroup X := subgroupCentralizerIn S1 R
  have htNormCentR : t ∈ Subgroup.normalizer
      (Subgroup.centralizer (R : Set X) : Set X) := by
    exact (le_normalizer_centralizer_of_le_normalizer
      (Subgroup.zpowers_le.mpr htNormR)) (Subgroup.mem_zpowers t)
  have htNormC1 : t ∈ Subgroup.normalizer (C1 : Set X) := by
    simpa [C1, subgroupCentralizerIn] using
      (Subgroup.le_normalizer_inf
        (A := Subgroup.zpowers t)
        (Subgroup.zpowers_le.mpr htNormS1)
        (Subgroup.zpowers_le.mpr htNormCentR)) (Subgroup.mem_zpowers t)
  have hprodC : Section2.IsInternalDirectProduct
      (subgroupCentralizerIn H R) C1 S2 := by
    simpa [C1] using
      proposition102_centralizer_factor_internalDirectProduct hprod hRleS1
  let m : ℕ := Nat.card {x : X // x ∈ Kset}
  let q : ℕ := 2 ^ d.choice.p - 1
  let i1 : ℕ := theorem4bInvertedCard t S1
  let ci1 : ℕ := theorem4bInvertedCard t C1
  let i2 : ℕ := theorem4bInvertedCard t S2
  have hmul : m = i1 * i2 := by
    calc
      m = theorem4bInvertedCard t H := by
        exact (proposition102_invertedCard_eq_kset_card ht hHleD hKH).symm
      _ = theorem4bInvertedCard t S1 * theorem4bInvertedCard t S2 :=
        proposition102_invertedCard_mul_of_internalDirectProduct
          hprod htNormS1 htNormS2
      _ = i1 * i2 := rfl
  have hqmul : q = ci1 * i2 := by
    calc
      q = Nat.card {x : X // x ∈ Kset ∧
          x ∈ Subgroup.centralizer (R : Set X)} := hcentralRcard.symm
      _ = theorem4bInvertedCard t (subgroupCentralizerIn H R) := by
        exact (proposition102_invertedCard_centralizer_eq_kset_card
          ht hHleD hKH).symm
      _ = theorem4bInvertedCard t C1 * theorem4bInvertedCard t S2 :=
        proposition102_invertedCard_mul_of_internalDirectProduct
          hprodC htNormC1 htNormS2
      _ = ci1 * i2 := rfl
  have hm_ne_q : m ≠ q := by
    have hne := proposition102_kset_card_ne_centralizer_card
      hRleV hRne hVC
    intro hmq
    apply hne
    calc
      Nat.card {x : X // x ∈ peterfalviKSet D t} = m := rfl
      _ = q := hmq
      _ = Nat.card {x : X // x ∈ peterfalviKSet D t ∧
          x ∈ Subgroup.centralizer (R : Set X)} := hcentralRcard.symm
  have hS1p : IsPGroup r S1 := by
    simpa [S1] using (pCore_isPGroup (G := H) (p := r)).map H.subtype
  have hS1leD : S1 ≤ D := by
    have hS1leH : S1 ≤ H := by
      simpa [S1] using Subgroup.map_subtype_le (pCore r H)
    exact hS1leH.trans hHleD
  have hS1odd : Odd (Nat.card S1) :=
    hDodd.of_dvd_nat (Subgroup.card_dvd_of_le hS1leD)
  have hC1leS1 : C1 ≤ S1 := by
    intro x hx
    exact hx.1
  have hC1p : IsPGroup r C1 := by
    exact (hS1p.to_subgroup (C1.subgroupOf S1)).of_equiv
      (Subgroup.subgroupOfEquivOfLe hC1leS1)
  have hC1leD : C1 ≤ D := hC1leS1.trans hS1leD
  have hC1odd : Odd (Nat.card C1) :=
    hDodd.of_dvd_nat (Subgroup.card_dvd_of_le hC1leD)
  have hi1pow : ∃ b : ℕ, i1 = r ^ b := by
    simpa [i1] using proposition102_invertedCard_eq_prime_pow
      hr hS1p ht hS1odd htNormS1
  have hci1pow : ∃ c : ℕ, ci1 = r ^ c := by
    simpa [ci1, C1] using proposition102_invertedCard_eq_prime_pow
      hr hC1p ht hC1odd htNormC1
  have hci1_dvd_i1 : ci1 ∣ i1 := by
    obtain ⟨b, hb⟩ := hi1pow
    obtain ⟨c, hc⟩ := hci1pow
    have hle : ci1 ≤ i1 := by
      exact theorem4bInvertedCard_mono hC1leS1
    have hpowle : r ^ c ≤ r ^ b := by
      rw [← hc, ← hb]
      exact hle
    have hcb : c ≤ b :=
      (Nat.pow_le_pow_iff_right hr.one_lt).mp hpowle
    rw [hc, hb]
    exact Nat.pow_dvd_pow r hcb
  let Z : Subgroup X := (Subgroup.center S1).map S1.subtype
  have hZleS1 : Z ≤ S1 := by
    simpa [Z] using Subgroup.map_subtype_le (Subgroup.center S1)
  have hS1ne : S1 ≠ ⊥ := ne_bot_of_le_ne_bot hRne hRleS1
  haveI : Nontrivial S1 := (Subgroup.nontrivial_iff_ne_bot S1).mpr hS1ne
  have hZcenterNe : Subgroup.center S1 ≠ ⊥ := by
    exact (Subgroup.nontrivial_iff_ne_bot (Subgroup.center S1)).mp
      hS1p.center_nontrivial
  have hZne : Z ≠ ⊥ := by
    intro hZbot
    apply hZcenterNe
    exact (Subgroup.map_eq_bot_iff_of_injective
      (Subgroup.center S1) S1.subtype_injective).mp hZbot
  have htNormZ : t ∈ Subgroup.normalizer (Z : Set X) := by
    simpa [Z] using
      (proposition102_normalizer_le_normalizer_map_subtype_of_characteristic
        S1 (Subgroup.center S1)) htNormS1
  have hZleD : Z ≤ D := hZleS1.trans hS1leD
  have hZodd : Odd (Nat.card Z) :=
    hDodd.of_dvd_nat (Subgroup.card_dvd_of_le hZleD)
  have hZleC1 : Z ≤ C1 := by
    intro z hz
    refine ⟨hZleS1 hz, ?_⟩
    change z ∈ Subgroup.centralizer (R : Set X)
    rw [Subgroup.mem_centralizer_iff]
    intro r0 hr0
    rcases Subgroup.mem_map.mp hz with ⟨zS, hzS, rfl⟩
    exact congrArg Subtype.val
      ((Subgroup.mem_center_iff.mp hzS) ⟨r0, hRleS1 hr0⟩)
  have hfixedZ : Z ⊓ Subgroup.centralizer ({t} : Set X) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    have hzKcent : z ∈ Subgroup.centralizer Kset := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      rcases hprod.mul_surjective k (hKH hk) with ⟨a, ha, b, hb, hab⟩
      rcases Subgroup.mem_map.mp hz.1 with ⟨zS, hzS, rfl⟩
      have hza : a * (zS : X) = (zS : X) * a := by
        exact congrArg Subtype.val
          ((Subgroup.mem_center_iff.mp hzS) ⟨a, ha⟩)
      have hzb : b * (zS : X) = (zS : X) * b :=
        (hprod.commute (zS : X)
          (by exact hZleS1 hz.1) b hb).symm
      calc
        k * (zS : X) = (a * b) * (zS : X) := by rw [hab]
        _ = a * (b * (zS : X)) := by group
        _ = a * ((zS : X) * b) := by rw [hzb]
        _ = (a * (zS : X)) * b := by group
        _ = ((zS : X) * a) * b := by rw [hza]
        _ = (zS : X) * (a * b) := by group
        _ = (zS : X) * k := by rw [hab]
    have hzV : z ∈ V := by
      change z ∈ D ∧ z ∈ Subgroup.centralizer ({t} : Set X)
      exact ⟨hZleD hz.1, hz.2⟩
    have hzbot : z ∈ (⊥ : Subgroup X) := by
      rw [← hVC]
      exact ⟨hzV, by simpa [Kset] using hzKcent⟩
    simpa using hzbot
  have hci1ne : ci1 ≠ 1 := by
    simpa [ci1, C1] using
      proposition102_invertedCard_ne_one_of_fixed_bot
        ht hZodd htNormZ hZne hfixedZ hZleC1
  have hrci1 : r ∣ ci1 := by
    obtain ⟨c, hc⟩ := hci1pow
    have hcne : c ≠ 0 := by
      intro hc0
      apply hci1ne
      rw [hc, hc0]
      simp
    rw [hc]
    exact dvd_pow_self r hcne
  obtain ⟨a, ha, hformula, hrq⟩ := proposition102_exponent_arithmetic
    hr hi1pow hci1pow hci1_dvd_i1 hmul hqmul hm_ne_q hrci1
  have hRp : IsPGroup r R := by
    exact (hS1p.to_subgroup (R.subgroupOf S1)).of_equiv
      (Subgroup.subgroupOfEquivOfLe hRleS1)
  haveI : Nontrivial R := (Subgroup.nontrivial_iff_ne_bot R).mpr hRne
  obtain ⟨n, hn_pos, hRcard⟩ :=
    (IsPGroup.nontrivial_iff_card (p := r) (G := R) hRp).mp inferInstance
  have hrdvdR : r ∣ Nat.card R := by
    rw [hRcard]
    exact dvd_pow_self r hn_pos.ne'
  have hrdvdA1 : r ∣ Nat.card A1 :=
    hrdvdR.trans (Subgroup.card_dvd_of_le hRleA1)
  letI : Fact d.choice.p.Prime := ⟨d.choice.p_prime⟩
  have hcardA1 : Nat.card A1 = Nat.card (pPrimeCore d.choice.p V) := by
    change Nat.card d.choice.initial.A1 =
      Nat.card (pPrimeCore d.choice.p V)
    rw [d.A1_eq_pPrimeCore,
      Subgroup.card_map_of_injective V.subtype_injective]
  have hcopA1 : Nat.Coprime d.choice.p (Nat.card A1) := by
    rw [hcardA1]
    exact pPrimeCore_coprime_card
  have hrnep : r ≠ d.choice.p := by
    intro hrp
    have hpnot : ¬ d.choice.p ∣ Nat.card A1 :=
      d.choice.p_prime.coprime_iff_not_dvd.mp hcopA1
    exact hpnot (by simpa [hrp] using hrdvdA1)
  have hrdvdHV : r ∣ Nat.card HV := by
    simpa [HV, H, V] using hrdvd
  have hrdvdH : r ∣ Nat.card H :=
    hrdvdHV.trans (Subgroup.card_dvd_of_le inf_le_left)
  exact ⟨{
    r := r
    r_prime := hr
    r_ne_p := hrnep
    a := a
    a_pos := ha
    R := R
    R_eq := by rfl
    R_ne_bot := hRne
    R_isPGroup := hRp
    R_le_A1 := by simpa [A1] using hRleA1
    R_le_derived_inf_V := by simpa [H, V] using hRleHV
    r_dvd_derived_inf_card := by simpa [HV, H, V] using hrdvd
    r_dvd_derived_card := by simpa [H] using hrdvdH
    kset_card_eq := by simpa [m, q, Kset] using hformula
    r_dvd_mersenne := by simpa [q] using hrq }, rfl⟩

public theorem proposition102_exponent_data
    {X : Type u} [Group X] [Finite X]
    {M W D E : Subgroup X} {t : X}
    (d : Lemma101Conclusion M W D E (peterfalviV D t) t)
    (h : Proposition102PartAConclusion M W D E (peterfalviV D t) t d)
    (ht : IsInvolution t)
    (hDodd : Odd (Nat.card D))
    (hED : E ≤ D)
    (htnormD : t ∈ Subgroup.normalizer (D : Set X))
    (htnormE : t ∈ Subgroup.normalizer (E : Set X))
    (hHVne : (derivedSubgroup E).map E.subtype ⊓ peterfalviV D t ≠ ⊥)
    (hVC : peterfalviV D t ⊓
      Subgroup.centralizer (peterfalviKSet D t) = ⊥) :
    Nonempty (Proposition102ExponentConclusion M W D E t d) := by
  let H : Subgroup X := (derivedSubgroup E).map E.subtype
  let V : Subgroup X := peterfalviV D t
  have hcardHVne : Nat.card (H ⊓ V : Subgroup X) ≠ 1 := by
    exact ((Subgroup.one_lt_card_iff_ne_bot (H ⊓ V)).mpr hHVne).ne'
  obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd hcardHVne
  obtain ⟨e, _⟩ := proposition102_exponent_data_of_prime_dvd d h ht hDodd hED
    htnormD htnormE hVC hr (by simpa [H, V] using hrdvd)
  exact ⟨e⟩

/- The exponent formula is independent of the chosen prime divisor of
`|E' ∩ V|`; this is the source-specific uniqueness step needed before the
Sylow/Fitting assembly. -/
public theorem proposition102_prime_eq_of_dvd_derived_inf_card
    {X : Type u} [Group X] [Finite X]
    {M W D E : Subgroup X} {t : X}
    (d : Lemma101Conclusion M W D E (peterfalviV D t) t)
    (h : Proposition102PartAConclusion M W D E (peterfalviV D t) t d)
    (ht : IsInvolution t)
    (hDodd : Odd (Nat.card D))
    (hED : E ≤ D)
    (htnormD : t ∈ Subgroup.normalizer (D : Set X))
    (htnormE : t ∈ Subgroup.normalizer (E : Set X))
    (hVC : peterfalviV D t ⊓
      Subgroup.centralizer (peterfalviKSet D t) = ⊥)
    (e : Proposition102ExponentConclusion M W D E t d)
    {s : ℕ} (hs : s.Prime)
    (hsdvd : s ∣ Nat.card
      ((derivedSubgroup E).map E.subtype ⊓ peterfalviV D t : Subgroup X)) :
    s = e.r := by
  obtain ⟨es, hes⟩ := proposition102_exponent_data_of_prime_dvd
    d h ht hDodd hED htnormD htnormE hVC hs hsdvd
  let q : ℕ := 2 ^ d.choice.p - 1
  have hqpos : 0 < q := by
    dsimp [q]
    exact Nat.sub_pos_of_lt
      (Nat.one_lt_pow d.choice.p_prime.ne_zero (by decide : 1 < (2 : ℕ)))
  have hmul : e.r ^ e.a * q = es.r ^ es.a * q := by
    rw [← e.kset_card_eq, ← es.kset_card_eq]
  have hpows : e.r ^ e.a = es.r ^ es.a :=
    Nat.eq_of_mul_eq_mul_right hqpos hmul
  have hsdvdPow : s ∣ e.r ^ e.a := by
    rw [hpows, hes]
    exact dvd_pow_self s (Nat.ne_of_gt es.a_pos)
  exact Nat.prime_eq_prime_of_dvd_pow hs e.r_prime hsdvdPow

/- Once every prime divisor is the selected `r`, the derived intersection is
an `r`-group. -/
public theorem proposition102_derived_inf_isPGroup
    {X : Type u} [Group X] [Finite X]
    {M W D E : Subgroup X} {t : X}
    (d : Lemma101Conclusion M W D E (peterfalviV D t) t)
    (h : Proposition102PartAConclusion M W D E (peterfalviV D t) t d)
    (ht : IsInvolution t)
    (hDodd : Odd (Nat.card D))
    (hED : E ≤ D)
    (htnormD : t ∈ Subgroup.normalizer (D : Set X))
    (htnormE : t ∈ Subgroup.normalizer (E : Set X))
    (hVC : peterfalviV D t ⊓
      Subgroup.centralizer (peterfalviKSet D t) = ⊥)
    (e : Proposition102ExponentConclusion M W D E t d) :
    IsPGroup e.r
      ((derivedSubgroup E).map E.subtype ⊓ peterfalviV D t : Subgroup X) := by
  letI : Fact e.r.Prime := ⟨e.r_prime⟩
  let H : Subgroup X := (derivedSubgroup E).map E.subtype
  let V : Subgroup X := peterfalviV D t
  refine (IsPGroup.iff_card (p := e.r) (G := ↥(H ⊓ V))).2 ?_
  refine ⟨(Nat.card (H ⊓ V : Subgroup X)).primeFactorsList.length, ?_⟩
  apply Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
  intro s hs hsdvd
  exact proposition102_prime_eq_of_dvd_derived_inf_card d h ht hDodd hED
    htnormD htnormE hVC e hs (by simpa [H, V] using hsdvd)

/- The selected subgroup is exactly the derived intersection: the reverse
containment follows by putting the `r`-group `E' ∩ V` into the mapped
`r`-core of the nilpotent derived subgroup. -/
public theorem proposition102_exponent_R_eq_derived_inf
    {X : Type u} [Group X] [Finite X]
    {M W D E : Subgroup X} {t : X}
    (d : Lemma101Conclusion M W D E (peterfalviV D t) t)
    (h : Proposition102PartAConclusion M W D E (peterfalviV D t) t d)
    (ht : IsInvolution t)
    (hDodd : Odd (Nat.card D))
    (hED : E ≤ D)
    (htnormD : t ∈ Subgroup.normalizer (D : Set X))
    (htnormE : t ∈ Subgroup.normalizer (E : Set X))
    (hVC : peterfalviV D t ⊓
      Subgroup.centralizer (peterfalviKSet D t) = ⊥)
    (e : Proposition102ExponentConclusion M W D E t d) :
    e.R = (derivedSubgroup E).map E.subtype ⊓ peterfalviV D t := by
  let H : Subgroup X := (derivedSubgroup E).map E.subtype
  let V : Subgroup X := peterfalviV D t
  have hHVp : IsPGroup e.r (H ⊓ V : Subgroup X) := by
    simpa [H, V] using proposition102_derived_inf_isPGroup d h ht hDodd
      hED htnormD htnormE hVC e
  have hHVcore : H ⊓ V ≤
      (pCore e.r H).map H.subtype := by
    exact proposition102_pSubgroup_le_mapped_pCore_of_nilpotent e.r_prime
      inf_le_left hHVp (proposition102_derived_nilpotent h)
  have hHVleR : H ⊓ V ≤ e.R := by
    rw [e.R_eq]
    exact le_inf hHVcore inf_le_right
  apply le_antisymm
  · simpa [H, V] using e.R_le_derived_inf_V
  · exact hHVleR

/- Normality is separated from the Hall input: once `E'` is normal in `D`,
the equality above makes `R` normal in `V`. -/
public theorem proposition102_exponent_R_normal_in_V
    {X : Type u} [Group X] [Finite X]
    {M W D E : Subgroup X} {t : X}
    (d : Lemma101Conclusion M W D E (peterfalviV D t) t)
    (h : Proposition102PartAConclusion M W D E (peterfalviV D t) t d)
    (ht : IsInvolution t)
    (hDodd : Odd (Nat.card D))
    (hED : E ≤ D)
    (htnormD : t ∈ Subgroup.normalizer (D : Set X))
    (htnormE : t ∈ Subgroup.normalizer (E : Set X))
    (hVC : peterfalviV D t ⊓
      Subgroup.centralizer (peterfalviKSet D t) = ⊥)
    (e : Proposition102ExponentConclusion M W D E t d)
    (hHnormalD :
      (((derivedSubgroup E).map E.subtype).subgroupOf D).Normal) :
    (e.R.subgroupOf (peterfalviV D t)).Normal := by
  let H : Subgroup X := (derivedSubgroup E).map E.subtype
  let V : Subgroup X := peterfalviV D t
  have hEq := proposition102_exponent_R_eq_derived_inf d h ht hDodd hED
    htnormD htnormE hVC e
  rw [hEq]
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).2
  have hHleD : H ≤ D := by
    exact (Subgroup.map_subtype_le (derivedSubgroup E)).trans hED
  have hDnormH : D ≤ Subgroup.normalizer (H : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHleD).mp hHnormalD
  have hVleD : V ≤ D := by
    exact inf_le_left
  have hVnormH : V ≤ Subgroup.normalizer (H : Set X) :=
    hVleD.trans hDnormH
  have hVnormInf : V ≤
      Subgroup.normalizer (H : Set X) ⊓
        Subgroup.normalizer (V : Set X) :=
    le_inf hVnormH (Subgroup.le_normalizer (H := V))
  exact hVnormInf.trans Subgroup.inf_normalizer_le_normalizer_inf

/- With the local Hall conclusion in `D`, the normal `r`-subgroup `R` is a
Sylow `r`-subgroup of `V`. -/
public theorem proposition102_exponent_R_sylow_V_of_hall_D
    {X : Type u} [Group X] [Finite X]
    {M W D E : Subgroup X} {t : X}
    (d : Lemma101Conclusion M W D E (peterfalviV D t) t)
    (h : Proposition102PartAConclusion M W D E (peterfalviV D t) t d)
    (ht : IsInvolution t)
    (hDodd : Odd (Nat.card D))
    (hED : E ≤ D)
    (htnormD : t ∈ Subgroup.normalizer (D : Set X))
    (htnormE : t ∈ Subgroup.normalizer (E : Set X))
    (hVC : peterfalviV D t ⊓
      Subgroup.centralizer (peterfalviKSet D t) = ⊥)
    (e : Proposition102ExponentConclusion M W D E t d)
    (hHnormalD :
      (((derivedSubgroup E).map E.subtype).subgroupOf D).Normal)
    (hHallD :
      IsHallSubgroup
        (subgroupPrimeSet ((derivedSubgroup E).map E.subtype))
        (((derivedSubgroup E).map E.subtype).subgroupOf D)) :
    theorem4bIsSylowSubgroupOf e.r e.R (peterfalviV D t) := by
  let H : Subgroup X := (derivedSubgroup E).map E.subtype
  let V : Subgroup X := peterfalviV D t
  have hEq : e.R = H ⊓ V := by
    simpa [H, V] using proposition102_exponent_R_eq_derived_inf d h ht hDodd
      hED htnormD htnormE hVC e
  have hRV : e.R ≤ V := by
    rw [hEq]
    exact inf_le_right
  letI : Fact e.r.Prime := ⟨e.r_prime⟩
  let RV : Subgroup V := e.R.subgroupOf V
  have hRVp : IsPGroup e.r RV := by
    exact e.R_isPGroup.of_equiv
      (Subgroup.subgroupOfEquivOfLe hRV).symm
  have hRidx : ¬ e.r ∣ RV.index := by
    intro hrdvd
    have hidxEq : RV.index = e.R.relIndex V := by
      rw [← Subgroup.relIndex_top_right (H := RV)]
      simpa [RV] using
        (Subgroup.relIndex_subgroupOf
          (H := e.R) (K := V) (L := V) (hKL := le_rfl))
    have hrdvdRel : e.r ∣ (H ⊓ V).relIndex V := by
      rw [← hEq]
      simpa [hidxEq] using hrdvd
    have hHD : H ≤ D :=
      (Subgroup.map_subtype_le (derivedSubgroup E)).trans hED
    have hVD : V ≤ D := inf_le_left
    let HD : Subgroup D := H.subgroupOf D
    let VD : Subgroup D := V.subgroupOf D
    have hsubInf : (H ⊓ V).subgroupOf D = HD ⊓ VD := by
      ext x
      rfl
    have hrelD : (H ⊓ V).relIndex V = (HD ⊓ VD).relIndex VD := by
      have hrel := Subgroup.relIndex_subgroupOf
        (H := H ⊓ V) (K := V) (L := D) (hKL := hVD)
      rw [hsubInf] at hrel
      simpa [VD] using hrel.symm
    haveI : HD.Normal := by simpa [HD, H] using hHnormalD
    have hrelSup : (HD ⊓ VD).relIndex VD = HD.relIndex (HD ⊔ VD) := by
      calc
        (HD ⊓ VD).relIndex VD = HD.relIndex VD := by
          simpa [inf_comm] using
            (Subgroup.inf_relIndex_left (H := VD) (K := HD))
        _ = HD.relIndex (HD ⊔ VD) := by
          rw [sup_comm]
          exact (Subgroup.relIndex_sup_right (H := VD) (K := HD)).symm
    have hrdvdSup : e.r ∣ HD.relIndex (HD ⊔ VD) := by
      simpa [hrelD, hrelSup] using hrdvdRel
    have hrdvdIndex : e.r ∣ HD.index :=
      hrdvdSup.trans
        (Subgroup.relIndex_dvd_index_of_le (H := HD) (K := HD ⊔ VD)
          le_sup_left)
    let rPrime : Nat.Primes := ⟨e.r, e.r_prime⟩
    have hrH : e.r ∣ Nat.card H := by
      change e.r ∣ Nat.card ((derivedSubgroup E).map E.subtype)
      exact e.r_dvd_derived_card
    have hrmem : rPrime ∈ subgroupPrimeSet H := by
      change (rPrime : ℕ) ∣ Nat.card H
      exact hrH
    have hrnot := hHallD.p_in_pi_of_p_dvd_index rPrime
      (by simpa [HD, H] using hrdvdIndex)
    exact hrnot hrmem
  let S : Sylow e.r V := hRVp.toSylow hRidx
  refine ⟨S, ?_⟩
  change e.R = (S : Subgroup V).map V.subtype
  rw [show (S : Subgroup V) = RV by
    exact IsPGroup.toSylow_coe hRVp hRidx]
  exact (Subgroup.map_subgroupOf_eq_of_le hRV).symm

public theorem proposition102_exponent_formula
    {X : Type u} [Group X] [Finite X]
    {M W D E : Subgroup X} {t : X}
    (d : Lemma101Conclusion M W D E (peterfalviV D t) t)
    (h : Proposition102PartAConclusion M W D E (peterfalviV D t) t d)
    (ht : IsInvolution t)
    (hDodd : Odd (Nat.card D))
    (hED : E ≤ D)
    (htnormD : t ∈ Subgroup.normalizer (D : Set X))
    (htnormE : t ∈ Subgroup.normalizer (E : Set X))
    (hHVne : (derivedSubgroup E).map E.subtype ⊓ peterfalviV D t ≠ ⊥)
    (hVC : peterfalviV D t ⊓
      Subgroup.centralizer (peterfalviKSet D t) = ⊥) :
    ∃ r : ℕ, ∃ a : ℕ,
      r.Prime ∧ r ≠ d.choice.p ∧ 1 ≤ a ∧
      Nat.card {x : X // x ∈ peterfalviKSet D t} =
        r ^ a * (2 ^ d.choice.p - 1) ∧
      r ∣ (2 ^ d.choice.p - 1) := by
  obtain ⟨e⟩ := proposition102_exponent_data d h ht hDodd hED htnormD
    htnormE hHVne hVC
  exact ⟨e.r, e.a, e.r_prime, e.r_ne_p, e.a_pos,
    e.kset_card_eq, e.r_dvd_mersenne⟩

end CFSG.BenderSuzuki
