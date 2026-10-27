module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Nine92Layer
public import CFSG.LocalAnalysis.StandardType.FS81.BasisCoprimeCore
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Nine92Step
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Nine92Weak
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Nine92JFacts
public import CFSG.GroupTheory.PLayer.CentralQuotient
public import CFSG.GroupTheory.PLayer.PIndex
public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.InnOrthType
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Aux.Descent
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Split
public import CFSG.HardMathSupport.Solomon.Coordinator.C25Borel
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BAutAbelian
public import CFSG.RankThree.PartTwo.KFacts.K72L3Omega

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.SignalizerFunctorTheorem
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.UniquenessMaximal

abbrev centralizerBTwo {G : Type} [Group G] (b₂ : G) : Subgroup G :=
  Subgroup.centralizer ({b₂} : Set G)

abbrev primeCoreCentralizerBTwo {G : Type} [Group G] (b₂ : G) : Subgroup G :=
  GLAPPrimeCoreOf 3 (centralizerBTwo b₂)

abbrev barCentralizerBTwo {G : Type} [Group G] (b₂ : G) : Type :=
  ↥(centralizerBTwo b₂) ⧸ ((primeCoreCentralizerBTwo b₂).subgroupOf (centralizerBTwo b₂))

attribute [local instance] gLAPPrimeCoreOf_normal

abbrev twD5BarMap {G : Type} [Group G] (b₂ : G) :
    ↥(centralizerBTwo b₂) →* barCentralizerBTwo b₂ :=
  QuotientGroup.mk' ((primeCoreCentralizerBTwo b₂).subgroupOf (centralizerBTwo b₂))

abbrev twD5BarSub {G : Type} [Group G] (b₂ : G) (L : Subgroup ↥(centralizerBTwo b₂)) :
    Subgroup (barCentralizerBTwo b₂) :=
  L.map (twD5BarMap b₂)

abbrev twD5BarBZero {G : Type} [Group G] (b₂ b₀ : G) (hb0 : b₀ ∈ centralizerBTwo b₂) :
    barCentralizerBTwo b₂ :=
  twD5BarMap b₂ ⟨b₀, hb0⟩

abbrev twD5BarBTwo {G : Type} [Group G] (b₂ : G) : barCentralizerBTwo b₂ :=
  twD5BarMap b₂ ⟨b₂, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

theorem map_subgroupOf_zpowers_sup_eq {G : Type} [Group G] {b₀ b₂ : G}
    (hb0 : b₀ ∈ centralizerBTwo b₂) (hb2 : b₂ ∈ centralizerBTwo b₂) :
    ((Subgroup.zpowers b₀ ⊔ Subgroup.zpowers b₂).subgroupOf (centralizerBTwo b₂)).map
        (twD5BarMap b₂) =
      Subgroup.zpowers (twD5BarBZero b₂ b₀ hb0) ⊔ Subgroup.zpowers (twD5BarBTwo b₂) := by
  rw [Subgroup.subgroupOf_sup (Subgroup.zpowers_le.mpr hb0) (Subgroup.zpowers_le.mpr hb2),
    Subgroup.map_sup]
  congr 1
  · ext z
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp hz)
      rw [show z = (⟨b₀, hb0⟩ : ↥(centralizerBTwo b₂)) ^ k from Subtype.ext hk.symm, map_zpow]
      rw [Subgroup.mem_zpowers_iff]
      exact ⟨k, rfl⟩
    · intro hz
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
      refine Subgroup.mem_map.mpr ⟨⟨b₀ ^ k, Subgroup.zpow_mem (centralizerBTwo b₂) hb0 k⟩, ?_, ?_⟩
      · exact Subgroup.mem_subgroupOf.mpr ((Subgroup.mem_zpowers_iff).mpr ⟨k, rfl⟩)
      · rw [show (⟨b₀ ^ k, Subgroup.zpow_mem (centralizerBTwo b₂) hb0 k⟩ :
            ↥(centralizerBTwo b₂)) = (⟨b₀, hb0⟩ : ↥(centralizerBTwo b₂)) ^ k from rfl,
          map_zpow, hk]
  · ext z
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp hz)
      rw [show z = (⟨b₂, hb2⟩ : ↥(centralizerBTwo b₂)) ^ k from Subtype.ext hk.symm, map_zpow]
      rw [Subgroup.mem_zpowers_iff]
      exact ⟨k, rfl⟩
    · intro hz
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
      refine Subgroup.mem_map.mpr ⟨⟨b₂ ^ k, Subgroup.zpow_mem (centralizerBTwo b₂) hb2 k⟩, ?_, ?_⟩
      · exact Subgroup.mem_subgroupOf.mpr ((Subgroup.mem_zpowers_iff).mpr ⟨k, rfl⟩)
      · rw [show (⟨b₂ ^ k, Subgroup.zpow_mem (centralizerBTwo b₂) hb2 k⟩ :
            ↥(centralizerBTwo b₂)) = (⟨b₂, hb2⟩ : ↥(centralizerBTwo b₂)) ^ k from rfl,
          map_zpow, hk]

theorem glaPPrimeCore_barCentralizerBTwo_eq_bot {G : Type} [Group G] [Finite G] (b₂ : G) :
    GLAPPrimeCore 3 (barCentralizerBTwo (G := G) b₂) = ⊥ := by
  show GLAPPrimeCore 3
    (↥(Subgroup.centralizer ({b₂} : Set G)) ⧸
      ((GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b₂} : Set G))).subgroupOf
        (Subgroup.centralizer ({b₂} : Set G)))) = ⊥
  let C : Subgroup G := Subgroup.centralizer ({b₂} : Set G)
  have h : (GLAPPrimeCoreOf 3 C).subgroupOf C = GLAPPrimeCore 3 ↥C :=
    Subgroup.comap_map_eq_self_of_injective C.subtype_injective _
  have hbot : pPrimeCore 3 (↥C ⧸ GLAPPrimeCore 3 ↥C) = ⊥ :=
    @CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot _ _ _ 3 ⟨Nat.prime_three⟩
  let e : (↥C ⧸ (GLAPPrimeCoreOf 3 C).subgroupOf C) ≃*
      (↥C ⧸ GLAPPrimeCore 3 ↥C) := QuotientGroup.quotientMulEquivOfEq h
  have hmap := CFSG.pPrimeCore_map_iso 3 e
  rw [hbot] at hmap
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hmap

theorem bar_pow_three_eq_one {G : Type} [Group G] {b₀ b₂ : G} (h3 : b₀ ^ 3 = 1)
    (hb0 : b₀ ∈ centralizerBTwo b₂) :
    (QuotientGroup.mk' ((primeCoreCentralizerBTwo b₂).subgroupOf (centralizerBTwo b₂))
      ⟨b₀, hb0⟩ : barCentralizerBTwo b₂) ^ 3 = 1 := by
  have h : (⟨b₀, hb0⟩ : ↥(centralizerBTwo b₂)) ^ 3 = 1 := Subtype.ext (by simpa using h3)
  rw [← map_pow, h, map_one]

theorem bar_b₂_mem_center {G : Type} [Group G] {b₂ : G} :
    (QuotientGroup.mk' ((primeCoreCentralizerBTwo b₂).subgroupOf (centralizerBTwo b₂))
      ⟨b₂, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ :
        barCentralizerBTwo b₂) ∈ Subgroup.center (barCentralizerBTwo b₂) := by
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective
    ((primeCoreCentralizerBTwo b₂).subgroupOf (centralizerBTwo b₂)) y
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp w.2)

theorem map_subgroupOf_sup_zpowers_sup_eq {G : Type} [Group G] {b₀ b₂ : G}
    (hb0 : b₀ ∈ centralizerBTwo b₂) (hb2 : b₂ ∈ centralizerBTwo b₂)
    {A : Subgroup G} (hA : A ≤ centralizerBTwo b₂) :
    (((Subgroup.zpowers b₀ ⊔ Subgroup.zpowers b₂) ⊔ A).subgroupOf
        (centralizerBTwo b₂)).map (twD5BarMap b₂) =
      Subgroup.zpowers (twD5BarBZero b₂ b₀ hb0) ⊔ Subgroup.zpowers (twD5BarBTwo b₂) ⊔
        (A.subgroupOf (centralizerBTwo b₂)).map (twD5BarMap b₂) := by
  have hS : (Subgroup.zpowers b₀ ⊔ Subgroup.zpowers b₂) ≤ centralizerBTwo b₂ :=
    sup_le (Subgroup.zpowers_le.mpr hb0) (Subgroup.zpowers_le.mpr hb2)
  rw [Subgroup.subgroupOf_sup hS hA, Subgroup.map_sup,
    map_subgroupOf_zpowers_sup_eq hb0 hb2]

theorem b_two_mem_and_span_le_centralizer {G : Type} [Group G] {b₀ : G} {K E : Subgroup G}
    {B : Basis3 G (5 + 1)} (hB : Adapted B b₀ K E) (hE : IsElemAbelian 3 E) :
    B.b 2 ∈ E ∧ E ≤ centralizerBTwo (B.b 2) := by
  have hb2E : B.b 2 ∈ E := by
    rw [← hB.1]
    exact Subgroup.subset_closure (Set.mem_range_self 2)
  refine ⟨hb2E, ?_⟩
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hc : (⟨x, hx⟩ : ↥E) * ⟨B.b 2, hb2E⟩ = ⟨B.b 2, hb2E⟩ * ⟨x, hx⟩ :=
    hE.1.is_comm.comm _ _
  exact Subtype.ext_iff.mp hc

theorem mem_sup_primeCore_of_mem_sup_barA {G : Type} [Group G] [Finite G]
    {b₀ : G} {K E : Subgroup G} {B : Basis3 G (5 + 1)} (hstd : StdTwD5 b₀ K E)
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD5 B b₀)
    (hb0 : b₀ ∈ centralizerBTwo (B.b 2)) {y : ↥(centralizerBTwo (B.b 2))}
    (h : (twD5BarMap (B.b 2) y) * twD5BarBZero (B.b 2) b₀ hb0 * (twD5BarMap (B.b 2) y)⁻¹ ∈
      Subgroup.zpowers (twD5BarBZero (B.b 2) b₀ hb0) ⊔
        Subgroup.zpowers (twD5BarBTwo (B.b 2)) ⊔
        twD5BarSub (B.b 2) ((E ⊓ nineJ K (B.b 2)).subgroupOf (centralizerBTwo (B.b 2)))) :
    (y : G) * b₀ * (y : G)⁻¹ ∈
      (Subgroup.zpowers b₀ ⊔ Subgroup.zpowers (B.b 2)) ⊔
        primeCoreCentralizerBTwo (B.b 2) := by
  obtain ⟨-, -, -, -, -, -, -, -, hEmax, hb0E, hEcard, -⟩ := hstd.2.1
  have hE : IsElemAbelian 3 E := hEmax.2.1
  obtain ⟨hb2E, hEH⟩ := b_two_mem_and_span_le_centralizer hB hE
  let H : Subgroup G := centralizerBTwo (B.b 2)
  let O : Subgroup G := primeCoreCentralizerBTwo (B.b 2)
  let S : Subgroup G := Subgroup.zpowers b₀ ⊔ Subgroup.zpowers (B.b 2)
  let A : Subgroup G := E ⊓ nineJ K (B.b 2)
  have hb0H : b₀ ∈ H := hb0
  have hb2H : B.b 2 ∈ H := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hOH : O ≤ H := Subgroup.map_subtype_le _
  have hSH : S ≤ H := sup_le (Subgroup.zpowers_le.mpr hb0H) (Subgroup.zpowers_le.mpr hb2H)
  have hAH : A ≤ H := inf_le_left.trans hEH
  have hSA : S ⊔ A ≤ E := sup_le (sup_le (Subgroup.zpowers_le.mpr hb0E)
    (Subgroup.zpowers_le.mpr hb2E)) inf_le_left
  have hmapS : ((S ⊔ A).subgroupOf H).map (twD5BarMap (B.b 2)) =
      Subgroup.zpowers (twD5BarBZero (B.b 2) b₀ hb0) ⊔
        Subgroup.zpowers (twD5BarBTwo (B.b 2)) ⊔ (A.subgroupOf H).map (twD5BarMap (B.b 2)) :=
    map_subgroupOf_sup_zpowers_sup_eq hb0H hb2H hAH
  have h' : (twD5BarMap (B.b 2) y) * twD5BarBZero (B.b 2) b₀ hb0 * (twD5BarMap (B.b 2) y)⁻¹ ∈
      ((S ⊔ A).subgroupOf H).map (twD5BarMap (B.b 2)) := by
    rw [hmapS]
    exact h
  have hx : y * ⟨b₀, hb0H⟩ * y⁻¹ ∈ (S ⊔ A).subgroupOf H ⊔ O.subgroupOf H := by
    have h1 : y * ⟨b₀, hb0H⟩ * y⁻¹ ∈
        (((S ⊔ A).subgroupOf H).map (twD5BarMap (B.b 2))).comap (twD5BarMap (B.b 2)) :=
      Subgroup.mem_comap.mpr h'
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h1
  have hxG : (y : G) * b₀ * (y : G)⁻¹ ∈ S ⊔ A ⊔ O := by
    have hle : (S ⊔ A).subgroupOf H ⊔ O.subgroupOf H ≤ (S ⊔ A ⊔ O).subgroupOf H := by
      rw [Subgroup.subgroupOf_sup (sup_le hSH hAH) hOH]
    exact Subgroup.mem_subgroupOf.mp (hle hx)
  have hxEO : (y : G) * b₀ * (y : G)⁻¹ ∈ E ⊔ O := by
    have hle : S ⊔ A ⊔ O ≤ E ⊔ O :=
      sup_le (hSA.trans le_sup_left) (le_sup_right : O ≤ E ⊔ O)
    exact hle hxG
  exact mem_sup_zpowers_sup_primeCore_of_mem_sup hstd hB hrec y.2 hxEO

theorem twD5BarMap_conj_mem_zpowers_of_mem_sup {G : Type} [Group G] [Finite G]
    {b₀ : G} {B : Basis3 G (5 + 1)}
    (hb0 : b₀ ∈ centralizerBTwo (B.b 2)) {y : ↥(centralizerBTwo (B.b 2))}
    (hres : (y : G) * b₀ * (y : G)⁻¹ ∈
      (Subgroup.zpowers b₀ ⊔ Subgroup.zpowers (B.b 2)) ⊔
        primeCoreCentralizerBTwo (B.b 2)) :
    (twD5BarMap (B.b 2) y) * twD5BarBZero (B.b 2) b₀ hb0 * (twD5BarMap (B.b 2) y)⁻¹ ∈
      Subgroup.zpowers (twD5BarBZero (B.b 2) b₀ hb0) ⊔
        Subgroup.zpowers (twD5BarBTwo (B.b 2)) := by
  let H : Subgroup G := centralizerBTwo (B.b 2)
  let O : Subgroup G := primeCoreCentralizerBTwo (B.b 2)
  let S : Subgroup G := Subgroup.zpowers b₀ ⊔ Subgroup.zpowers (B.b 2)
  have hb0H : b₀ ∈ H := hb0
  have hb2H : B.b 2 ∈ H := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hOH : O ≤ H := Subgroup.map_subtype_le _
  have hSH : S ≤ H := sup_le (Subgroup.zpowers_le.mpr hb0H) (Subgroup.zpowers_le.mpr hb2H)
  have hxH : (y : G) * b₀ * (y : G)⁻¹ ∈ H :=
    H.mul_mem (H.mul_mem y.2 hb0H) (H.inv_mem y.2)
  have hfin : twD5BarMap (B.b 2) ⟨(y : G) * b₀ * (y : G)⁻¹, hxH⟩ ∈
      Subgroup.zpowers (twD5BarBZero (B.b 2) b₀ hb0) ⊔
        Subgroup.zpowers (twD5BarBTwo (B.b 2)) := by
    have hxS : (⟨(y : G) * b₀ * (y : G)⁻¹, hxH⟩ : ↥H) ∈
        S.subgroupOf H ⊔ O.subgroupOf H := by
      rw [← Subgroup.subgroupOf_sup hSH hOH]
      exact Subgroup.mem_subgroupOf.mpr hres
    have hmem := Subgroup.mem_map_of_mem (twD5BarMap (B.b 2)) hxS
    rw [Subgroup.map_sup, map_subgroupOf_zpowers_sup_eq hb0H hb2H] at hmem
    have hOmap : (O.subgroupOf H).map (twD5BarMap (B.b 2)) = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨z, hz, rfl⟩
      exact (QuotientGroup.eq_one_iff _).mpr hz
    rwa [hOmap, sup_bot_eq] at hmem
  have heq : twD5BarMap (B.b 2) ⟨(y : G) * b₀ * (y : G)⁻¹, hxH⟩ =
      (twD5BarMap (B.b 2) y) * twD5BarBZero (B.b 2) b₀ hb0 * (twD5BarMap (B.b 2) y)⁻¹ := by
    have hxsub : (⟨(y : G) * b₀ * (y : G)⁻¹, hxH⟩ : ↥H) =
        y * ⟨b₀, hb0H⟩ * y⁻¹ := rfl
    rw [hxsub]
    change twD5BarMap (B.b 2) (y * ⟨b₀, hb0H⟩ * y⁻¹) =
      (twD5BarMap (B.b 2) y) * (twD5BarMap (B.b 2) ⟨b₀, hb0H⟩) * (twD5BarMap (B.b 2) y)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
  rw [heq] at hfin
  exact hfin

theorem conj_mem_zpowers_sup_zpowers_of_mem_sup_barA {G : Type} [Group G] [Finite G]
    {b₀ : G} {K E : Subgroup G} {B : Basis3 G (5 + 1)} (hstd : StdTwD5 b₀ K E)
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD5 B b₀)
    (hb0 : b₀ ∈ centralizerBTwo (B.b 2)) {ybar : barCentralizerBTwo (B.b 2)}
    (h : ybar * twD5BarBZero (B.b 2) b₀ hb0 * ybar⁻¹ ∈
      Subgroup.zpowers (twD5BarBZero (B.b 2) b₀ hb0) ⊔
        Subgroup.zpowers (twD5BarBTwo (B.b 2)) ⊔
        twD5BarSub (B.b 2) ((E ⊓ nineJ K (B.b 2)).subgroupOf (centralizerBTwo (B.b 2)))) :
    ybar * twD5BarBZero (B.b 2) b₀ hb0 * ybar⁻¹ ∈
      Subgroup.zpowers (twD5BarBZero (B.b 2) b₀ hb0) ⊔
        Subgroup.zpowers (twD5BarBTwo (B.b 2)) := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective
    ((primeCoreCentralizerBTwo (B.b 2)).subgroupOf (centralizerBTwo (B.b 2))) ybar
  exact twD5BarMap_conj_mem_zpowers_of_mem_sup hb0
    (mem_sup_primeCore_of_mem_sup_barA hstd hB hrec hb0 h)

theorem inf_primeCore_centralizer_le_primeCore {G : Type} [Group G] [Finite G] {b₂ : G}
    {L : Subgroup G} (hLH : L ≤ centralizerBTwo b₂) :
    L ⊓ primeCoreCentralizerBTwo b₂ ≤ GLAPPrimeCoreOf 3 L := by
  have hOnorm : centralizerBTwo b₂ ≤
      Subgroup.normalizer (primeCoreCentralizerBTwo b₂ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp
      (gLAPPrimeCoreOf_normal 3 (centralizerBTwo b₂))
  have hLn : L ≤ Subgroup.normalizer ((L ⊓ primeCoreCentralizerBTwo b₂) : Set G) := by
    intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_inf (H := L)
      (K := primeCoreCentralizerBTwo b₂)
      (Subgroup.mem_inf.mpr ⟨Subgroup.le_normalizer hx, hOnorm (hLH hx)⟩)
  have hnormal : ((L ⊓ primeCoreCentralizerBTwo b₂).subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hLn
  have hcopO : Nat.Coprime 3 (Nat.card (primeCoreCentralizerBTwo b₂)) := by
    change Nat.Coprime 3 (Nat.card ↥((pPrimeCore 3 ↥(centralizerBTwo b₂)).map
      (centralizerBTwo b₂).subtype))
    rw [Subgroup.card_map_of_injective (centralizerBTwo b₂).subtype_injective]
    exact coprime_card_pPrimeCore 3 ↥(centralizerBTwo b₂)
  have hcop : Nat.Coprime 3
      (Nat.card ↥((L ⊓ primeCoreCentralizerBTwo b₂).subgroupOf L)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
    exact hcopO.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
  have hle : (L ⊓ primeCoreCentralizerBTwo b₂).subgroupOf L ≤ pPrimeCore 3 ↥L :=
    le_sSup ⟨hnormal, hcop⟩
  intro z hz
  exact Subgroup.mem_map.mpr ⟨⟨z, hz.1⟩, hle (Subgroup.mem_subgroupOf.mpr hz), rfl⟩

theorem exists_bar_mem_not_commute_of_not_mem_dQ {G : Type} [Group G] [Finite G]
    {b₀ b₂ : G} {L : Subgroup G} (hLH : L ≤ centralizerBTwo b₂)
    (hb0 : b₀ ∈ centralizerBTwo b₂) (hb0N : b₀ ∈ Subgroup.normalizer (L : Set G))
    (hnot : b₀ ∉ dQ L) :
    ∃ y ∈ (L.subgroupOf (centralizerBTwo b₂)).map (twD5BarMap b₂),
      y * twD5BarBZero b₂ b₀ hb0 ≠ twD5BarBZero b₂ b₀ hb0 * y := by
  by_contra h
  push Not at h
  apply hnot
  rw [mem_dQ]
  refine ⟨hb0N, ?_, ?_⟩
  · have hmapL : L.map (MulAut.conj b₀).toMonoidHom = L :=
      (Subgroup.mem_normalizer_iff_map_conj_eq).mp hb0N
    have hmapO := gLAPPrimeCoreOf_map_mulEquiv 3 (MulAut.conj b₀) L
    change GLAPPrimeCoreOf 3 (L.map (MulAut.conj b₀).toMonoidHom) =
      (GLAPPrimeCoreOf 3 L).map (MulAut.conj b₀).toMonoidHom at hmapO
    rw [hmapL] at hmapO
    exact (Subgroup.mem_normalizer_iff_map_conj_eq).mpr hmapO.symm
  · intro x hx
    have hxbar : twD5BarMap b₂ ⟨x, hLH hx⟩ ∈
        (L.subgroupOf (centralizerBTwo b₂)).map (twD5BarMap b₂) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)
    have hcomm := h _ hxbar
    have hvL : b₀ * x * b₀⁻¹ * x⁻¹ ∈ L := by
      have h1 : b₀ * x * b₀⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hb0N x).mp hx
      exact L.mul_mem h1 (L.inv_mem hx)
    have hvH : b₀ * x * b₀⁻¹ * x⁻¹ ∈ centralizerBTwo b₂ :=
      (centralizerBTwo b₂).mul_mem ((centralizerBTwo b₂).mul_mem
        ((centralizerBTwo b₂).mul_mem hb0 (hLH hx)) ((centralizerBTwo b₂).inv_mem hb0))
        ((centralizerBTwo b₂).inv_mem (hLH hx))
    have hvq : twD5BarMap b₂ ⟨b₀ * x * b₀⁻¹ * x⁻¹, hvH⟩ = 1 := by
      have hsub : (⟨b₀ * x * b₀⁻¹ * x⁻¹, hvH⟩ : ↥(centralizerBTwo b₂)) =
          ⟨b₀, hb0⟩ * ⟨x, hLH hx⟩ * ⟨b₀, hb0⟩⁻¹ * ⟨x, hLH hx⟩⁻¹ := rfl
      rw [hsub]
      simp only [map_mul, map_inv]
      rw [show twD5BarBZero b₂ b₀ hb0 = twD5BarMap b₂ ⟨b₀, hb0⟩ from rfl] at hcomm
      rw [← hcomm]
      group
    have hvO : b₀ * x * b₀⁻¹ * x⁻¹ ∈ primeCoreCentralizerBTwo b₂ :=
      Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hvq)
    have hvU : b₀ * x * b₀⁻¹ * x⁻¹ ∈ GLAPPrimeCoreOf 3 L :=
      inf_primeCore_centralizer_le_primeCore hLH ⟨hvL, hvO⟩
    have hinv : (b₀ * x * b₀⁻¹ * x⁻¹)⁻¹ = x * b₀ * x⁻¹ * b₀⁻¹ := by group
    have := (GLAPPrimeCoreOf 3 L).inv_mem hvU
    rw [hinv] at this
    exact this

theorem twD5BarSub_inf_le {G : Type} [Group G] {b₂ : G} {E J : Subgroup G} :
    twD5BarSub b₂ ((E ⊓ J).subgroupOf (centralizerBTwo b₂)) ≤
      twD5BarSub b₂ (J.subgroupOf (centralizerBTwo b₂)) := by
  apply Subgroup.map_mono
  intro x hx
  exact Subgroup.mem_subgroupOf.mpr
    (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)).2

theorem isElemAbelian_twD5BarSub_inf {G : Type} [Group G] {b₂ : G} {E J : Subgroup G}
    (hE : IsElemAbelian 3 E) :
    IsElemAbelian 3
      (twD5BarSub b₂ ((E ⊓ J).subgroupOf (centralizerBTwo b₂))) :=
  CFSG.Open.IsElemAbelian.map
    (CFSG.Open.IsElemAbelian.subgroupOf (CFSG.Open.IsElemAbelian.mono hE inf_le_left)
      (centralizerBTwo b₂)) (twD5BarMap b₂)
