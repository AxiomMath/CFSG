module

public import CFSG.Quasithin.SteinbergCCLocalSylowAction
public import CFSG.Quasithin.H13.NQBlockControlledThompson
public import CFSG.Quasithin.Background.A1bBasic
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup CFSG.Open
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj normalizerCoreQuotConj)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem normalizerCoreQuotConj_eq_one_iff {X : Subgroup G} (n : normalizer (X : Set G)) :
    normalizerCoreQuotConj X n = 1 ↔ ∀ x ∈ X, (n : G) * x * (n : G)⁻¹ * x⁻¹ ∈ pCoreOf 2 X := by
  have hq : pCoreOf 2 X = (CFSG.pCore 2 ↥X).map X.subtype := by
    rw [pCoreOf]
  have key : ∀ x : X, normalizerCoreQuotConj X n (x : X ⧸ CFSG.pCore 2 X) =
      (x : X ⧸ CFSG.pCore 2 X) ↔ (n : G) * x * (n : G)⁻¹ * (x : G)⁻¹ ∈ pCoreOf 2 X := by
    intro x
    change ((X.normalizerMonoidHom n x : X) : X ⧸ CFSG.pCore 2 X) = _ ↔ _
    rw [QuotientGroup.eq_iff_div_mem, hq, ← Subgroup.mem_map_iff_mem X.subtype_injective]
    simp only [Subgroup.coe_subtype, div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv,
      Subgroup.normalizerMonoidHom_apply_apply_coe]
  constructor
  · intro hn x hx
    exact (key ⟨x, hx⟩).mp (by rw [hn]; rfl)
  · intro h
    ext z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
    exact (key x).mpr (h x x.2)

omit [Finite G] in
theorem normalizerFrattiniConj_eq_one_of {X : Subgroup G} {n : normalizer (X : Set G)}
    (hn : normalizerCoreQuotConj X n = 1) : normalizerFrattiniConj X n = 1 := by
  show CFSG.SectionRank.Ccomm.autQuotient _ (normalizerCoreQuotConj X n) = 1
  rw [hn, map_one]

omit [Finite G] in
theorem mem_normalizer_inf {A B : Subgroup G} {y : G} (hA : y ∈ normalizer (A : Set G))
    (hB : y ∈ normalizer (B : Set G)) : y ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff] at hA hB ⊢
  intro g
  simp only [mem_inf]
  rw [hA g, hB g]

theorem exists_mul_of_isSylowOf' {p : ℕ} [Fact p.Prime] {B N : Subgroup G}
    (hB : CFSG.ABGLocalTools.IsSylowOf p B N) {k : G} (hkN : k ∈ normalizer (N : Set G)) :
    ∃ n ∈ N, ∃ m ∈ normalizer (B : Set G), k = n * m := by
  have hle : B.map (MulAut.conj k).toMonoidHom ≤ N := by
    rintro _ ⟨b, hb, rfl⟩
    exact (mem_normalizer_iff.mp hkN b).mp (hB.le hb)
  have hB' : CFSG.ABGLocalTools.IsSylowOf p (B.map (MulAut.conj k).toMonoidHom) N := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card hle ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj k).injective]
    exact hB.card_eq
  obtain ⟨n, hn, hnk⟩ := NQBlock.exists_map_conj_eq_of_isSylowOf' hB hB'
  refine ⟨n, hn, n⁻¹ * k, ?_, by group⟩
  rw [mem_normalizer_iff]
  have key : ∀ b, b ∈ B ↔ k * b * k⁻¹ ∈ B.map (MulAut.conj n).toMonoidHom := by
    intro b
    rw [← hnk]
    constructor
    · intro hb
      exact ⟨b, hb, rfl⟩
    · rintro ⟨b', hb', hbb'⟩
      have h2 : k * b' * k⁻¹ = k * b * k⁻¹ := hbb'
      rwa [mul_left_cancel (mul_right_cancel h2)] at hb'
  intro b
  rw [key b]
  constructor
  · rintro ⟨b', hb', hbb'⟩
    have h1 : n * b' * n⁻¹ = k * b * k⁻¹ := hbb'
    have : n⁻¹ * k * b * (n⁻¹ * k)⁻¹ = b' := by
      calc n⁻¹ * k * b * (n⁻¹ * k)⁻¹ = n⁻¹ * (k * b * k⁻¹) * n := by group
        _ = n⁻¹ * (n * b' * n⁻¹) * n := by rw [h1]
        _ = b' := by group
    rw [this]
    exact hb'
  · intro hb
    refine ⟨_, hb, ?_⟩
    change n * (n⁻¹ * k * b * (n⁻¹ * k)⁻¹) * n⁻¹ = k * b * k⁻¹
    group

theorem exists_mem_normalizer_pCoreOf_not_two_power {T D X : Subgroup G}
    (hT : quasithinIsSylowTwo T) (hTD : T ≤ normalizer (D : Set G)) (hDp : ⁅D, D⁆ = D)
    (hXD : X ≤ D) (hDTX : D ⊔ T ≤ normalizer (X : Set G))
    (hnt : ∃ d : normalizer (X : Set G), (d : G) ∈ D ∧ normalizerFrattiniConj X d ≠ 1) :
    ∃ y : normalizer (X : Set G), (y : G) ∈ D ∧
      (y : G) ∈ normalizer (pCoreOf 2 (X ⊔ T) : Set G) ∧
      ∀ k : ℕ, normalizerFrattiniConj X y ^ 2 ^ k ≠ 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := normalizer (X : Set G) with hNdef
  set R := pCoreOf 2 (X ⊔ T) with hRdef
  set q := pCoreOf 2 X with hqdef
  have hXN : X ≤ N := le_normalizer
  have hDN : D ≤ N := le_sup_left.trans hDTX
  have hTN : T ≤ N := le_sup_right.trans hDTX
  have hXTR : X ⊔ T ≤ normalizer (R : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hNq : N ≤ normalizer (q : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X
  have hqX : q ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  have hq2 : IsPGroup 2 q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
  have hTsyl : CFSG.ABGLocalTools.IsSylowOf 2 T (D ⊔ T) :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨le_sup_right, hT.1, fun hd =>
      hT.2 (hd.trans (Subgroup.relIndex_dvd_index_of_le le_sup_right))⟩
  have hqT : q ≤ T := by
    have h1 := (CFSG.ABGLocalTools.isSylowOf_iff.mp hTsyl)
    exact IsSylowIn.le_of_normal ⟨h1.1, h1.2.1, h1.2.2⟩ (hqX.trans (hXD.trans le_sup_left))
      ((normal_subgroupOf_iff_le_normalizer (hqX.trans (hXD.trans le_sup_left))).mpr
        (hDTX.trans hNq)) hq2
  set K : Subgroup G := (D ⊔ T) ⊓ (normalizerCoreQuotConj X).ker.map N.subtype with hKdef
  have hmemK : ∀ g, g ∈ K ↔ g ∈ D ⊔ T ∧ ∀ x ∈ X, g * x * g⁻¹ * x⁻¹ ∈ q := by
    intro g
    rw [hKdef, mem_inf]
    refine and_congr_right fun hg => ?_
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact (normalizerCoreQuotConj_eq_one_iff n).mp hn
    · intro h
      exact ⟨⟨g, hDTX hg⟩, (normalizerCoreQuotConj_eq_one_iff _).mpr h, rfl⟩
  have hKDT : K ≤ D ⊔ T := inf_le_left
  have hKn : D ⊔ T ≤ normalizer (K : Set G) := by
    intro h hh
    have hhN : h ∈ N := hDTX hh
    rw [mem_normalizer_iff]
    intro g
    rw [hmemK, hmemK]
    constructor
    · rintro ⟨hg, hgx⟩
      refine ⟨mul_mem (mul_mem hh hg) (inv_mem hh), fun x hx => ?_⟩
      have hx' : h⁻¹ * x * h ∈ X := by
        have := (mem_normalizer_iff.mp (inv_mem hhN) x).mp hx
        rwa [inv_inv] at this
      have h1 := hgx _ hx'
      have h2 := (mem_normalizer_iff.mp (hNq hhN) _).mp h1
      have h3 : h * (g * (h⁻¹ * x * h) * g⁻¹ * (h⁻¹ * x * h)⁻¹) * h⁻¹ =
          h * g * h⁻¹ * x * (h * g * h⁻¹)⁻¹ * x⁻¹ := by group
      rwa [h3] at h2
    · rintro ⟨hg, hgx⟩
      have hg' : g ∈ D ⊔ T := by
        have := mul_mem (mul_mem (inv_mem hh) hg) hh
        rwa [show h⁻¹ * (h * g * h⁻¹) * h = g by group] at this
      refine ⟨hg', fun x hx => ?_⟩
      have hx' : h * x * h⁻¹ ∈ X := (mem_normalizer_iff.mp hhN x).mp hx
      have h1 := hgx _ hx'
      have h2 := (mem_normalizer_iff.mp (hNq (inv_mem hhN)) _).mp h1
      have h3 : h⁻¹ * (h * g * h⁻¹ * (h * x * h⁻¹) * (h * g * h⁻¹)⁻¹ * (h * x * h⁻¹)⁻¹) * h⁻¹⁻¹ =
          g * x * g⁻¹ * x⁻¹ := by group
      rwa [h3] at h2
  have hqK : q ≤ K := by
    intro g hg
    rw [hmemK]
    refine ⟨hqX.trans (hXD.trans le_sup_left) hg, fun x hx => ?_⟩
    have h1 : x * g⁻¹ * x⁻¹ ∈ q := (mem_normalizer_iff.mp (hNq (hXN hx)) _).mp (inv_mem hg)
    have h2 : g * x * g⁻¹ * x⁻¹ = g * (x * g⁻¹ * x⁻¹) := by group
    rw [h2]
    exact mul_mem hg h1
  have hRT : R ≤ T :=
    CFSG.QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf ⟨le_sup_right, hT.1, fun hd =>
      hT.2 (hd.trans (Subgroup.relIndex_dvd_index_of_le le_sup_right))⟩
  have hRK : R ≤ K := by
    intro r hr
    rw [hmemK]
    refine ⟨mem_sup_right (hRT hr), fun x hx => ?_⟩
    have hrN : r ∈ N := hTN (hRT hr)
    have h1 : r * x * r⁻¹ * x⁻¹ ∈ X :=
      mul_mem ((mem_normalizer_iff.mp hrN x).mp hx) (inv_mem hx)
    have h2 : r * x * r⁻¹ * x⁻¹ ∈ R := by
      have h3 : x * r⁻¹ * x⁻¹ ∈ R :=
        (mem_normalizer_iff.mp (hXTR (mem_sup_left hx)) _).mp (inv_mem hr)
      have h4 : r * x * r⁻¹ * x⁻¹ = r * (x * r⁻¹ * x⁻¹) := by group
      rw [h4]
      exact mul_mem hr h3
    have hXRq : X ⊓ R ≤ q :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
        (fun y hy => mem_normalizer_inf (le_normalizer hy) (hXTR (mem_sup_left hy)))
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_right)
    exact hXRq (mem_inf.mpr ⟨h1, h2⟩)
  have hfwd : ∀ x ∈ X, ∀ s ∈ T ⊓ K, x * s * x⁻¹ ∈ T ⊓ K := by
    intro x hx s hs
    obtain ⟨hsT, hsK⟩ := mem_inf.mp hs
    have h1 : x * s * x⁻¹ * s⁻¹ ∈ q := by
      have := ((hmemK s).mp hsK).2 x hx
      have h2 : x * s * x⁻¹ * s⁻¹ = (s * x * s⁻¹ * x⁻¹)⁻¹ := by group
      rw [h2]
      exact inv_mem this
    have h3 : x * s * x⁻¹ = (x * s * x⁻¹ * s⁻¹) * s := by group
    rw [h3]
    exact mem_inf.mpr ⟨mul_mem (hqT h1) hsT, mul_mem (hqK h1) hsK⟩
  have hTKR : T ⊓ K ≤ R := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (inf_le_left.trans le_sup_right) (sup_le (fun x hx => ?_)
        (fun t ht => mem_normalizer_inf (le_normalizer ht) (hKn (mem_sup_right ht))))
      (hT.1.to_le inf_le_left)
    rw [mem_normalizer_iff]
    intro s
    refine ⟨hfwd x hx s, fun hs => ?_⟩
    have := hfwd x⁻¹ (inv_mem hx) _ hs
    rwa [show x⁻¹ * (x * s * x⁻¹) * x⁻¹⁻¹ = s by group] at this
  have hReq : R = T ⊓ K := le_antisymm (le_inf hRT hRK) hTKR
  have hRsyl : CFSG.ABGLocalTools.IsSylowOf 2 R K := by
    rw [hReq]
    exact hTsyl.inf_of_le_normalizer hKDT hKn
  have hdec : ∀ d ∈ D, ∃ y ∈ D ⊓ normalizer (R : Set G), ∃ t ∈ T, ∃ k ∈ K, d = k * y * t := by
    intro d hd
    obtain ⟨k, hk, m, hm, rfl⟩ := exists_mul_of_isSylowOf' hRsyl (hKn (mem_sup_left hd))
    have hmDT : m ∈ D ⊔ T := by
      have := mul_mem (inv_mem (hKDT hk)) (mem_sup_left hd : k * m ∈ D ⊔ T)
      rwa [inv_mul_cancel_left] at this
    have hmDT' : m ∈ ((D : Set G) * (T : Set G)) := by
      rw [← coe_mul_of_right_le_normalizer_left D T hTD]
      exact hmDT
    obtain ⟨y, hy, t, ht, rfl⟩ := hmDT'
    refine ⟨y, mem_inf.mpr ⟨hy, ?_⟩, t, ht, k, hk, by group⟩
    have h1 : y = y * t * t⁻¹ := by group
    rw [h1]
    exact mul_mem hm (inv_mem (hXTR (mem_sup_right ht)))
  by_contra hcon
  push Not at hcon
  set ρ := normalizerFrattiniConj X with hρ
  set A : Subgroup N := (D ⊓ normalizer (R : Set G)).subgroupOf N with hA
  set TA : Subgroup N := T.subgroupOf N with hTA
  set DA : Subgroup N := D.subgroupOf N with hDA
  have hA2 : IsPGroup 2 (A.map ρ) := by
    rintro ⟨_, a, ha, rfl⟩
    obtain ⟨k, hk⟩ := hcon a (mem_inf.mp ha).1 (mem_inf.mp ha).2
    exact ⟨k, Subtype.ext (by simp only [Subgroup.coe_pow, OneMemClass.coe_one]; exact hk)⟩
  have hT2 : IsPGroup 2 (TA.map ρ) :=
    (hT.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTN).symm).map ρ
  have hTAn : TA ≤ normalizer (A : Set N) := by
    intro t ht
    rw [mem_normalizer_iff]
    intro a
    have htD := hTD ht
    have htR : (t : G) ∈ normalizer ((normalizer (R : Set G) : Subgroup G) : Set G) :=
      le_normalizer (hXTR (mem_sup_right ht))
    rw [mem_normalizer_iff] at htD htR
    show (a : G) ∈ D ⊓ normalizer (R : Set G) ↔
      ((t * a * t⁻¹ : N) : G) ∈ D ⊓ normalizer (R : Set G)
    simp only [mem_inf, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [htD (a : G), htR (a : G)]
    exact Iff.rfl
  have hTnorm : TA.map ρ ≤ normalizer ((A.map ρ : Subgroup _) : Set _) :=
    (map_mono hTAn).trans (Subgroup.le_normalizer_map ρ)
  have hS2 : IsPGroup 2 ↥(A.map ρ ⊔ TA.map ρ) := IsPGroup.to_sup_of_normal_left' hA2 hT2 hTnorm
  have hDS : DA.map ρ ≤ A.map ρ ⊔ TA.map ρ := by
    rintro _ ⟨d, hd, rfl⟩
    obtain ⟨y, hy, t, ht, k, hk, hdk⟩ := hdec d hd
    have hkN : k ∈ N := hDTX (hKDT hk)
    have hyN : y ∈ N := hDN (mem_inf.mp hy).1
    have htN : t ∈ N := hTN ht
    have hd' : d = ⟨k, hkN⟩ * ⟨y, hyN⟩ * ⟨t, htN⟩ := Subtype.ext hdk
    have hρk : ρ ⟨k, hkN⟩ = 1 := by
      refine normalizerFrattiniConj_eq_one_of ((normalizerCoreQuotConj_eq_one_iff _).mpr ?_)
      exact ((hmemK k).mp hk).2
    rw [hd', map_mul, map_mul, hρk, one_mul]
    exact mul_mem (mem_sup_left ⟨⟨y, hyN⟩, hy, rfl⟩) (mem_sup_right ⟨⟨t, htN⟩, ht, rfl⟩)
  have hDAp : ⁅DA, DA⁆ = DA := by
    apply map_injective N.subtype_injective
    rw [map_commutator, Subgroup.map_subgroupOf_eq_of_le hDN]
    exact hDp
  have hDperf : Group.IsPerfect ↥(DA.map ρ) := by
    rw [Subgroup.isPerfect_iff, ← map_commutator, hDAp]
  have hDbot := SteinbergCC.eq_bot_of_isPerfect_of_isPGroup hDperf (hS2.to_le hDS)
  obtain ⟨d, hdD, hdne⟩ := hnt
  exact hdne ((mem_bot).mp (hDbot ▸ mem_map_of_mem ρ (show d ∈ DA from hdD)))

end CFSG.Quasithin.H13.NQCore
