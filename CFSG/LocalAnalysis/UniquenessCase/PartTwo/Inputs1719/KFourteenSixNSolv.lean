module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFourteenSixNRank
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ChiefFactors.Core
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
public import CFSG.GroupTheory.LocalLift.NormalizerQuotient
public import CFSG.LocalAnalysis.UniquenessCase.UC1K327Core
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
public import CFSG.LieType.BorelTits.Basic
public import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.Fischer.Classification.Unitary.Model
public import CFSG.GH74.GLS.Basic
public import CFSG.Fischer.Classification.Unitary.Coords
public import CFSG.LargeExtraspecial.AS35QThModel
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.Open.GeneralizedFittingSelfCentralizingMilestoneDefs
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Matrix.Basis
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.GroupTheory.RegularWreathProduct
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.Transvection
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.LinearAlgebra.Projectivization.Cardinality
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Free
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.Transvection.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.RingTheory.TensorProduct.Finite

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFourteenSixN

open Subgroup

theorem exists_isPGroup_map_eq_of_two {Γ : Type} [Group Γ] [Finite Γ] (K : Subgroup Γ) [K.Normal]
    (hK : IsPGroup 2 K) {s : ℕ} [Fact s.Prime] (hs2 : s ≠ 2) {Y : Subgroup Γ} (hKY : K ≤ Y)
    {P : Subgroup (Γ ⧸ K)} (hP : IsPGroup s P) (hPY : P ≤ Y.map (QuotientGroup.mk' K)) :
    ∃ S : Subgroup Γ, S ≤ Y ∧ IsPGroup s S ∧ S.map (QuotientGroup.mk' K) = P ∧
      CFSG.Open.pRank s P = CFSG.Open.pRank s S := by
  have hker : (QuotientGroup.mk' K).ker ≤ Y := by
    rw [QuotientGroup.ker_mk']
    exact hKY
  obtain ⟨S, hS, hSY, hSmap⟩ :=
    CFSG.LocalLift.exists_isPGroup_map_eq (QuotientGroup.mk' K)
      (QuotientGroup.mk'_surjective K) hker hP hPY
  have hdisj : Disjoint S K :=
    IsPGroup.disjoint_of_ne s 2 hs2 S K hS hK
  have hSK : S ⊓ K = ⊥ := hdisj.eq_bot
  have hinj : Set.InjOn (QuotientGroup.mk' K) (S : Set Γ) := by
    intro x hx y hy hxy
    have h1 : QuotientGroup.mk' K (x⁻¹ * y) = 1 := by
      rw [map_mul, map_inv, hxy, inv_mul_cancel]
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h2 : x⁻¹ * y ∈ S := S.mul_mem (S.inv_mem hx) hy
    have h3 : x⁻¹ * y = 1 := by
      have : x⁻¹ * y ∈ S ⊓ K := ⟨h2, h1⟩
      simpa [hSK] using this
    have hyx : y = x := by
      calc y = x * (x⁻¹ * y) := by group
        _ = x := by rw [h3, mul_one]
    exact hyx.symm
  have hpr := CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC327.pRank_map_of_injOn
    (p := s) (QuotientGroup.mk' K) S hinj
  exact ⟨S, hSY, hS, hSmap, by rw [← hSmap]; exact hpr⟩

theorem commutator_le_centralizer_fittingSubgroupOf {Γ : Type} [Group Γ] [Finite Γ]
    {Y Q A : Subgroup Γ} {r : ℕ} (hr : r.Prime) (hr4 : 4 < r) (hA : IsPGroup r A)
    (hQ : IsPGroup 2 Q) (hY : Group.IsSolvable Y) (hY2 : CFSG.Open.pCoreOf 2 Y = ⊥)
    (hQY : Q ≤ normalizer (Y : Set Γ)) (hAY : A ≤ normalizer (Y : Set Γ))
    (hAQ : A ≤ normalizer (Q : Set Γ))
    (hrank : ∀ s : ℕ, s.Prime → s ≠ 2 → ∀ P : Subgroup Γ, P ≤ Y → IsPGroup s P →
      CFSG.Open.pRank s P ≤ 2) :
    ⁅Q, A⁆ ≤ centralizer (CFSG.fittingSubgroupOf Y : Set Γ) := by
  have _ : Group.IsSolvable Y := hY
  rw [show CFSG.fittingSubgroupOf Y = GorensteinWalter.fittingSubgroupOf Y from rfl,
    GorensteinWalter.fittingSubgroupOf_eq_iSup_qCoreOf Y]
  refine CFSG.subgroup_le_centralizer_iSup_of_le_centralizer
    (S := fun q : (Nat.card ↥Y).primeFactors.attach => GorensteinWalter.qCoreOf Y q.1.1) ?_
  intro q
  have hq : q.1.1.Prime := Nat.prime_of_mem_primeFactors q.1.2
  by_cases hq2 : q.1.1 = 2
  · have hbot : GorensteinWalter.qCoreOf Y q.1.1 = ⊥ := by
      rw [hq2]
      simpa [GorensteinWalter.qCoreOf, CFSG.Open.pCoreOf] using hY2
    rw [hbot, show centralizer ((⊥ : Subgroup Γ) : Set Γ) = ⊤ by
      rw [Subgroup.centralizer_eq_top_iff_subset]
      simp]
    exact le_top
  · have : Fact q.1.1.Prime := ⟨hq⟩
    refine commutator_le_centralizer_of_pRank_le_two (s := q.1.1) (r := r) hq2 hr hr4
      (GorensteinWalter.qCoreOf_isPGroup Y q.1.1)
      (hrank q.1.1 hq hq2 (GorensteinWalter.qCoreOf Y q.1.1)
        (GorensteinWalter.qCoreOf_le Y q.1.1)
        (GorensteinWalter.qCoreOf_isPGroup Y q.1.1)) hQ hA ?_ ?_ hAQ
    · exact hQY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := q.1.1) Y)
    · exact hAY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := q.1.1) Y)

variable {G : Type} [Group G] [Finite G]

theorem commutator_le_pCoreOf_of_sup_eq_top {Γ : Type} [Group Γ] [Finite Γ]
    {Y S A : Subgroup Γ} {r : ℕ} (hr : r.Prime) (hr4 : 4 < r) (hA : IsPGroup r A)
    (hY : Group.IsSolvable Y) (hS : IsPGroup 2 S) (hAY : A ≤ normalizer (Y : Set Γ))
    (hSY : S ≤ Y) (hAS : A ≤ normalizer (S : Set Γ)) (hgen : Y ⊔ A = ⊤)
    (hrank : ∀ s : ℕ, s.Prime → s ≠ 2 → ∀ P : Subgroup Γ, P ≤ Y → IsPGroup s P →
      CFSG.Open.pRank s P ≤ 2) :
    ⁅S, A⁆ ≤ CFSG.Open.pCoreOf 2 Y := by
  let K : Subgroup Γ := CFSG.Open.pCoreOf 2 Y
  have hKY : K ≤ Y := CFSG.LieType.BorelTits.pCoreOf_le 2 Y
  have hK2 : IsPGroup 2 K := by
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y
  have hKnormal : K.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hgen]
    refine sup_le ?_ ?_
    · exact Subgroup.le_normalizer.trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) Y)
    · exact hAY.trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) Y)
  let q : Γ →* Γ ⧸ K := QuotientGroup.mk' K
  let Yb : Subgroup (Γ ⧸ K) := Y.map q
  let Sb : Subgroup (Γ ⧸ K) := S.map q
  let Ab : Subgroup (Γ ⧸ K) := A.map q
  have hSb : IsPGroup 2 Sb := hS.map q
  have hAb : IsPGroup r Ab := hA.map q
  have hSbYb : Sb ≤ Yb := Subgroup.map_mono hSY
  have hYb_solv : Group.IsSolvable ↥Yb :=
    Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective q Y)
  let φ : ↥Y →* Γ ⧸ K := q.comp Y.subtype
  have hrange : φ.range = Yb := by
    rw [MonoidHom.range_eq_map]
    change (⊤ : Subgroup ↥Y).map (q.comp Y.subtype) = Yb
    rw [← Subgroup.map_map, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hKsub : K.subgroupOf Y = CFSG.pCore 2 ↥Y := by
    change K.comap Y.subtype = CFSG.pCore 2 ↥Y
    rw [show K = (CFSG.pCore 2 ↥Y).map Y.subtype from rfl,
      Subgroup.comap_map_eq_self_of_injective Y.subtype_injective]
  have hker : φ.ker = CFSG.pCore 2 ↥Y := by
    ext x
    rw [MonoidHom.mem_ker]
    change q (x : Γ) = 1 ↔ x ∈ CFSG.pCore 2 ↥Y
    constructor
    · intro hx
      have hxK : (x : Γ) ∈ K := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
        exact hx
      have hx' : x ∈ K.subgroupOf Y := Subgroup.mem_subgroupOf.mpr hxK
      rwa [hKsub] at hx'
    · intro hx
      have hx' : x ∈ K.subgroupOf Y := by rwa [hKsub]
      have hxK : (x : Γ) ∈ K := Subgroup.mem_subgroupOf.mp hx'
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hxK
  have hYb_pcore : CFSG.pCore 2 ↥Yb = ⊥ := by
    let e : (↥Y ⧸ CFSG.pCore 2 ↥Y) ≃* Yb :=
      (QuotientGroup.quotientMulEquivOfEq hker).symm.trans
        ((QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hrange))
    have h0 : CFSG.pCore 2 (↥Y ⧸ CFSG.pCore 2 ↥Y) = ⊥ :=
      CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot
    simpa [h0, Subgroup.map_bot] using (CFSG.pCore_map_iso 2 e).symm
  have hYb2 : CFSG.Open.pCoreOf 2 Yb = ⊥ := by
    rw [CFSG.Open.pCoreOf, hYb_pcore, Subgroup.map_bot]
  have hrankYb : ∀ s : ℕ, s.Prime → s ≠ 2 → ∀ P : Subgroup (Γ ⧸ K), P ≤ Yb →
      IsPGroup s P → CFSG.Open.pRank s P ≤ 2 := by
    intro s hs hs2 P hPY hP
    have : Fact s.Prime := ⟨hs⟩
    obtain ⟨T, hTY, hT, hTmap, hpT⟩ :=
      exists_isPGroup_map_eq_of_two (Γ := Γ) K hK2 hs2 (Y := Y) hKY hP hPY
    rw [hpT]
    exact hrank s hs hs2 T hTY hT
  have hAbYb : Ab ≤ normalizer (Yb : Set (Γ ⧸ K)) :=
    (Subgroup.map_mono hAY).trans (Subgroup.le_normalizer_map q)
  have hAbSb : Ab ≤ normalizer (Sb : Set (Γ ⧸ K)) :=
    (Subgroup.map_mono hAS).trans (Subgroup.le_normalizer_map q)
  have hcomm_le_Sb : ⁅Sb, Ab⁆ ≤ Sb :=
    (Subgroup.le_normalizer_iff_commutator_le_left).mp hAbSb
  have hmain : ⁅Sb, Ab⁆ ≤
      Subgroup.centralizer (CFSG.fittingSubgroupOf Yb : Set (Γ ⧸ K)) :=
    commutator_le_centralizer_fittingSubgroupOf hr hr4 hAb hSb hYb_solv hYb2
      (hSbYb.trans Subgroup.le_normalizer) hAbYb hAbSb hrankYb
  have hfit : ⁅Sb, Ab⁆ ≤ CFSG.fittingSubgroupOf Yb :=
    (le_inf (hcomm_le_Sb.trans hSbYb) hmain).trans
      (GorensteinWalter.fact_1_2_centralizer_fitting_le_fitting Yb hYb_solv)
  have hOddF : Odd (Nat.card (CFSG.fittingSubgroupOf Yb)) := by
    have hpc : CFSG.pCore 2 ↥Yb = ⊥ := by
      rw [CFSG.Open.pCoreOf] at hYb2
      exact (Subgroup.map_eq_bot_iff_of_injective _ Yb.subtype_injective).mp hYb2
    set F : Subgroup ↥Yb := CFSG.fittingSubgroup ↥Yb
    obtain ⟨Q⟩ : Nonempty (Sylow 2 ↥F) := inferInstance
    have hQle : (Q : Subgroup ↥F).map F.subtype ≤ CFSG.pCore 2 ↥Yb :=
      Sylow.map_le_pCore CFSG.fittingSubgroup_normal CFSG.fittingSubgroup_nilpotent 2 Q
    rw [hpc, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ F.subtype_injective] at hQle
    have hc := Sylow.card_eq_multiplicity Q
    rw [hQle, Subgroup.card_bot] at hc
    have hF0 : Nat.card ↥F ≠ 0 := Nat.card_pos.ne'
    have hv : (Nat.card ↥F).factorization 2 = 0 :=
      Nat.pow_right_injective (le_refl 2) (hc.symm.trans (pow_zero 2).symm)
    have hnd : ¬ 2 ∣ Nat.card ↥F := by
      intro h2
      have := (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hF0).1 h2
      omega
    have hodd : Odd (Nat.card ↥F) := Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hnd)
    have hcard : Nat.card (CFSG.fittingSubgroupOf Yb) = Nat.card ↥F := by
      rw [CFSG.fittingSubgroupOf]
      exact Subgroup.card_map_of_injective Yb.subtype_injective
    rw [hcard]
    exact hodd
  have hOddComm : Odd (Nat.card (⁅Sb, Ab⁆ : Subgroup (Γ ⧸ K))) :=
    hOddF.of_dvd_nat (Subgroup.card_dvd_of_le hfit)
  have h2comm : IsPGroup 2 (⁅Sb, Ab⁆ : Subgroup (Γ ⧸ K)) := hSb.to_le hcomm_le_Sb
  have hcomm_bot : ⁅Sb, Ab⁆ = ⊥ := by
    have hcard1 : Nat.card (⁅Sb, Ab⁆ : Subgroup (Γ ⧸ K)) = 1 := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h2comm
      have hoddpow : Odd (2 ^ n) := hn ▸ hOddComm
      have hn0 : n = 0 := by
        cases n with
        | zero => rfl
        | succ n =>
            exact absurd (by
              rw [pow_succ]
              exact dvd_mul_left 2 (2 ^ n)) hoddpow.not_two_dvd_nat
      rw [hn, hn0, pow_zero]
    exact Subgroup.eq_bot_of_card_eq _ hcard1
  have hmapbot : (⁅S, A⁆).map q = ⊥ := by
    rw [Subgroup.map_commutator]
    exact hcomm_bot
  have hle : ⁅S, A⁆ ≤ q.ker :=
    (Subgroup.map_eq_bot_iff (f := q) (H := ⁅S, A⁆)).mp hmapbot
  simpa [q, QuotientGroup.ker_mk'] using hle

variable {G : Type} [Group G] [Finite G]

theorem commutator_le_pCoreOf_of_isSolvable {N Y S A : Subgroup G} {r : ℕ} (hr : r.Prime)
    (hr4 : 4 < r) (hA : IsPGroup r A) (hYN : Y ≤ N) (hY : Group.IsSolvable Y)
    (hAY : A ≤ normalizer (Y : Set G)) (hSY : S ≤ Y) (hS : IsPGroup 2 S)
    (hAS : A ≤ normalizer (S : Set G)) (h3 : CFSG.Open.pRank 3 N ≤ 1)
    (hsN : ∀ s : ℕ, s.Prime → 3 < s → CFSG.Open.pRank s N ≤ 2) :
    ⁅S, A⁆ ≤ CFSG.Open.pCoreOf 2 Y := by
  let Γ : Subgroup G := Y ⊔ A
  let Y' : Subgroup ↥Γ := Y.subgroupOf Γ
  let S' : Subgroup ↥Γ := S.subgroupOf Γ
  let A' : Subgroup ↥Γ := A.subgroupOf Γ
  have hYinst : Group.IsSolvable ↥Y := hY
  have hgen : Y' ⊔ A' = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (le_sup_left : Y ≤ Γ) (le_sup_right : A ≤ Γ),
      Subgroup.subgroupOf_self]
  have hS' : IsPGroup 2 S' := hS.comap_subtype (K := Γ)
  have hA' : IsPGroup r A' := hA.comap_subtype (K := Γ)
  have hY' : Group.IsSolvable ↥Y' :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe (le_sup_left : Y ≤ Γ)).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe (le_sup_left : Y ≤ Γ)).injective
  have hSY' : S' ≤ Y' := Subgroup.subgroupOf_mono Γ hSY
  have hAY' : A' ≤ normalizer (Y' : Set ↥Γ) := by
    have h : A' ≤ (normalizer (Y : Set G)).subgroupOf Γ := Subgroup.subgroupOf_mono Γ hAY
    rwa [Subgroup.subgroupOf_normalizer_eq (le_sup_left : Y ≤ Γ)] at h
  have hAS' : A' ≤ normalizer (S' : Set ↥Γ) := by
    have h : A' ≤ (normalizer (S : Set G)).subgroupOf Γ := Subgroup.subgroupOf_mono Γ hAS
    rwa [Subgroup.subgroupOf_normalizer_eq (hSY.trans le_sup_left)] at h
  have hrank' : ∀ s : ℕ, s.Prime → s ≠ 2 → ∀ P : Subgroup ↥Γ, P ≤ Y' → IsPGroup s P →
      CFSG.Open.pRank s P ≤ 2 := by
    intro s hs hs2 P hPY hP
    have hPG : CFSG.Open.pRank s (P.map Γ.subtype) = CFSG.Open.pRank s P :=
      CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC327.pRank_map_of_injOn
        (p := s) Γ.subtype P Γ.subtype_injective.injOn
    rw [← hPG]
    have hPYG : P.map Γ.subtype ≤ Y := by
      rintro _ ⟨x, hxP, rfl⟩
      exact Subgroup.mem_subgroupOf.mp (hPY hxP)
    have hPN : P.map Γ.subtype ≤ N := hPYG.trans hYN
    have hle := CFSG.SectionRank.pRank_mono hs.one_lt hPN
    by_cases hs3 : s = 3
    · rw [hs3] at hle ⊢
      exact hle.trans (h3.trans (by norm_num))
    · have hsgt : 3 < s := by
        have h2s : 2 ≤ s := hs.two_le
        omega
      exact hle.trans (hsN s hs hsgt)
  have hcomm' : ⁅S', A'⁆ ≤ CFSG.Open.pCoreOf 2 Y' :=
    commutator_le_pCoreOf_of_sup_eq_top hr hr4 hA' hY' hS' hAY' hSY' hAS' hgen hrank'
  have hSmap : S'.map Γ.subtype = S := by
    rw [show S'.map Γ.subtype = S ⊓ Γ from Subgroup.subgroupOf_map_subtype S Γ,
      inf_eq_left.mpr (hSY.trans le_sup_left)]
  have hAmap : A'.map Γ.subtype = A := by
    rw [show A'.map Γ.subtype = A ⊓ Γ from Subgroup.subgroupOf_map_subtype A Γ,
      inf_eq_left.mpr le_sup_right]
  have hKmap : (CFSG.Open.pCoreOf 2 Y').map Γ.subtype = CFSG.Open.pCoreOf 2 Y := by
    rw [CFSG.Open.pCoreOf]
    exact CFSG.ABGLocalTools.map_pCore_subgroupOf (le_sup_left : Y ≤ Γ)
  calc ⁅S, A⁆ = ⁅S', A'⁆.map Γ.subtype := by
        rw [Subgroup.map_commutator, hSmap, hAmap]
    _ ≤ (CFSG.Open.pCoreOf 2 Y').map Γ.subtype := Subgroup.map_mono hcomm'
    _ = CFSG.Open.pCoreOf 2 Y := hKmap

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFourteenSixN
