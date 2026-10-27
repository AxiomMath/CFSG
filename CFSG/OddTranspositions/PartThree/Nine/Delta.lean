module

public import CFSG.OddTranspositions.PartThree.Nine.Setup
public import CFSG.OddTranspositions.PartThree.CardWidth
public import CFSG.OddTranspositions.WidthSylowSetup
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CosetNormalizerSingerAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CosetNormalizerSolvableOrSevenSinger
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CosetNormalizerSolvableOrSevenLocal
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CosetNormalizerSolvableOrSevenAffine
public import CFSG.LocalAnalysis.QuasithinUnique.CompNormSylow
public import CFSG.Timmesfeld.Bridge.Asc72Bender
public import CFSG.StronglyEmbedded.MatrixGroups.SzModel
public import CFSG.GH74.Uniqueness.Bender.Models
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.Models
public import CFSG.Assembly.OrderReductions.CharacterInflation
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexNormalizer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorOrbit
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.OddTranspositions.O4PairTenWidth
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Walter.Defs
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

namespace CFSG.OddTranspositions.PartThree.Nine

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem d_mem_sylow_map (hC : HypothesisC D) (h3 : Conclusion9_3 D hC)
    (T : Sylow 2 (Halpha D hC.alpha)) :
    hC.d ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype := by
  have hu : hC.d ∈ (CFSG.pCore 2 (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype := by
    rw [h3.2.1]
    exact Subgroup.mem_zpowers _
  exact Subgroup.map_mono (CFSG.pCore_isPGroup.le_sylow_of_normal T) hu

theorem eq_one_of_mem_pResidualOf_of_commute (hC : HypothesisC D) (h3 : Conclusion9_3 D hC)
    {z : G} (hzL : z ∈ CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha))
    (hzc : ∀ h ∈ Halpha D hC.alpha, Commute z h) (hz2 : z * z = 1) : z = 1 := by
  set H := Halpha D hC.alpha
  have hzH : z ∈ H := Subgroup.map_subtype_le _ hzL
  let z' : H := ⟨z, hzH⟩
  have hz'c : z' ∈ Subgroup.center H :=
    Subgroup.mem_center_iff.mpr fun h => Subtype.ext (hzc h h.2).eq.symm
  have hz'2 : z' * z' = 1 := Subtype.ext hz2
  have hKn : (Subgroup.zpowers z').Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hz'c)
  have hKp : IsPGroup 2 (Subgroup.zpowers z') := by
    rintro ⟨g, k, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    change (z' ^ k) ^ 2 ^ 1 = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_two, hz'2,
      one_zpow]
  have hle : Subgroup.zpowers z' ≤ CFSG.pCore 2 H := le_sSup ⟨hKn, hKp⟩
  have hzu : z ∈ Subgroup.zpowers hC.d := by
    rw [← h3.2.1]
    exact ⟨z', hle (Subgroup.mem_zpowers z'), rfl⟩
  exact Subgroup.disjoint_def.mp h3.2.2.2 hzu hzL

omit [Finite G] in
private theorem conj_mem_pResidualOf {α : Set G} {h l : G} (hh : h ∈ Halpha D α)
    (hl : l ∈ CFSG.Quasithin.pResidualOf 2 (Halpha D α)) :
    h * l * h⁻¹ ∈ CFSG.Quasithin.pResidualOf 2 (Halpha D α) :=
  (Subgroup.mem_normalizer_iff.mp (CFSG.Quasithin.normalizer_le_normalizer_pResidualOf 2 _
    (Subgroup.le_normalizer hh)) l).mp hl

theorem exists_conj_of_mem_pResidualOf (hC : HypothesisC D) (hH : Th91Hyp D hC)
    (h3 : Conclusion9_3 D hC) {t₁ t₂ : G}
    (h₁L : t₁ ∈ CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) (h₁ : orderOf t₁ = 2)
    (h₂L : t₂ ∈ CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) (h₂ : orderOf t₂ = 2) :
    ∃ h ∈ Halpha D hC.alpha, h * t₁ * h⁻¹ = t₂ := by
  set H := Halpha D hC.alpha
  set L := CFSG.Quasithin.pResidualOf 2 H
  have hLH : L ≤ H := Subgroup.map_subtype_le _
  have hsq : ∀ t : G, orderOf t = 2 → t * t = 1 := fun t ht => by
    rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have himg : ∀ t (htL : t ∈ L), orderOf t = 2 →
      orderOf (QuotientGroup.mk (s := Subgroup.center H) (⟨t, hLH htL⟩ : H)) = 2 := by
    intro t htL ht
    refine orderOf_eq_prime ?_ fun h1 => ?_
    · rw [← QuotientGroup.mk_pow, pow_two]
      exact (QuotientGroup.eq_one_iff _).mpr (by
        rw [show (⟨t, hLH htL⟩ : H) * ⟨t, hLH htL⟩ = 1 from Subtype.ext (hsq t ht)]
        exact Subgroup.one_mem _)
    · have hc := Subgroup.mem_center_iff.mp ((QuotientGroup.eq_one_iff _).mp h1)
      have ht1 := eq_one_of_mem_pResidualOf_of_commute hC h3 htL
        (fun h hh => (congrArg Subtype.val (hc ⟨h, hh⟩)).symm) (hsq t ht)
      rw [ht1, orderOf_one] at ht
      exact absurd ht (by decide)
  obtain ⟨c, hc⟩ := isConj_iff.mp
    (CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isConj_of_orderOf_eq_two hH.bender
      (himg t₁ h₁L h₁) (himg t₂ h₂L h₂))
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective c
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    QuotientGroup.eq] at hc
  set a : G := (h : G) * t₁ * (h : G)⁻¹ with ha
  have haL : a ∈ L := conj_mem_pResidualOf h.2 h₁L
  have haH : a ∈ H := hLH haL
  have hzc : ∀ g ∈ H, Commute (a⁻¹ * t₂) g := fun g hg =>
    (congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨g, hg⟩)).symm
  have hzL : a⁻¹ * t₂ ∈ L := L.mul_mem (L.inv_mem haL) h₂L
  have ha2 : a * a = 1 := by
    rw [ha]
    calc (h : G) * t₁ * (h : G)⁻¹ * ((h : G) * t₁ * (h : G)⁻¹) =
        (h : G) * (t₁ * t₁) * (h : G)⁻¹ := by group
      _ = 1 := by rw [hsq t₁ h₁, mul_one, mul_inv_cancel]
  have hz2 : (a⁻¹ * t₂) * (a⁻¹ * t₂) = 1 := by
    obtain ⟨z, hz⟩ : ∃ z, z = a⁻¹ * t₂ := ⟨_, rfl⟩
    have ht₂ : t₂ = a * z := by rw [hz, mul_inv_cancel_left]
    have hcomm : z * a = a * z := hz ▸ (hzc a haH).eq
    rw [← hz]
    calc z * z = (a * a) * (z * z) := by rw [ha2, one_mul]
      _ = a * (a * z) * z := by group
      _ = a * (z * a) * z := by rw [hcomm]
      _ = t₂ * t₂ := by rw [ht₂]; group
      _ = 1 := hsq t₂ h₂
  have hz := eq_one_of_mem_pResidualOf_of_commute hC h3 hzL hzc hz2
  exact ⟨h, h.2, (inv_mul_eq_one.mp hz)⟩

theorem mul_mem_commSet_of_orderOf_eq_two (hC : HypothesisC D) (hH : Th91Hyp D hC)
    (h3 : Conclusion9_3 D hC) {t : G}
    (htL : t ∈ CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) (ht : orderOf t = 2) :
    hC.d * t ∈ commSet D hC.d := by
  set H := Halpha D hC.alpha
  set u := hC.d
  obtain ⟨x₀, hx₀, -⟩ := hC.hE
  have hu2 : u * u = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
  have hx₀2 : x₀ * x₀ = 1 := hC.setup.oddT.mul_self_eq_one hx₀.1
  have ht₀L : u * x₀ ∈ CFSG.Quasithin.pResidualOf 2 H := mul_mem_of_mem_commSet hC h3 hx₀
  have ht₀ : orderOf (u * x₀) = 2 := by
    refine orderOf_eq_prime ?_ fun h1 => hx₀.2.2 ?_
    · rw [pow_two, mul_assoc, ← mul_assoc x₀ u x₀, hx₀.2.1.eq, mul_assoc, hx₀2, mul_one, hu2]
    · rw [← hC.setup.oddT.inv_eq hC.hd]
      exact eq_inv_of_mul_eq_one_right h1
  obtain ⟨h, hh, rfl⟩ := exists_conj_of_mem_pResidualOf hC hH h3 ht₀L ht₀ htL ht
  have hhu : h * u = u * h :=
    Subgroup.mem_centralizer_singleton_iff.mp (PartThree.Halpha_le_centralizer_d hC hh)
  have hconj : u * (h * (u * x₀) * h⁻¹) = h * x₀ * h⁻¹ := by
    calc u * (h * (u * x₀) * h⁻¹) = u * ((h * u) * x₀ * h⁻¹) := by group
      _ = u * ((u * h) * x₀ * h⁻¹) := by rw [hhu]
      _ = (u * u) * (h * x₀ * h⁻¹) := by group
      _ = h * x₀ * h⁻¹ := by rw [hu2, one_mul]
  rw [hconj]
  refine ⟨hC.setup.conj_mem h hx₀.1, ?_, ?_⟩
  · have hc : Commute (h * x₀ * h⁻¹) (h * u * h⁻¹) := (Commute.conj_iff h).mpr hx₀.2.1
    rwa [hhu, mul_inv_cancel_right] at hc
  · intro heq
    apply hx₀.2.2
    have : x₀ = h⁻¹ * (h * x₀ * h⁻¹) * h := by group
    rw [this, heq, mul_assoc, ← hhu, ← mul_assoc, inv_mul_cancel, one_mul]

theorem mem_commSet_iff (hC : HypothesisC D) (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC)
    {x : G} :
    x ∈ commSet D hC.d ↔
      hC.d * x ∈ CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) ∧ orderOf (hC.d * x) = 2 := by
  have hu2 : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
  constructor
  · intro hx
    have hx2 : x * x = 1 := hC.setup.oddT.mul_self_eq_one hx.1
    refine ⟨mul_mem_of_mem_commSet hC h3 hx, orderOf_eq_prime ?_ fun h1 => hx.2.2 ?_⟩
    · rw [pow_two, mul_assoc, ← mul_assoc x hC.d x, hx.2.1.eq, mul_assoc, hx2, mul_one, hu2]
    · rw [← hC.setup.oddT.inv_eq hC.hd]
      exact eq_inv_of_mul_eq_one_right h1
  · rintro ⟨hxL, hx⟩
    have h := mul_mem_commSet_of_orderOf_eq_two hC hH h3 hxL hx
    rwa [← mul_assoc, hu2, one_mul] at h

theorem exists_sylow_pResidualOf {H : Subgroup G} (T : Sylow 2 H) :
    ∃ R : Sylow 2 (CFSG.Quasithin.pResidualOf 2 H),
      (R : Subgroup _).map (CFSG.Quasithin.pResidualOf 2 H).subtype =
        (T : Subgroup H).map H.subtype ⊓ CFSG.Quasithin.pResidualOf 2 H := by
  have := CFSG.Quasithin.pResidual_characteristic 2 H
  let e : CFSG.Quasithin.pResidual 2 H ≃* CFSG.Quasithin.pResidualOf 2 H :=
    (CFSG.Quasithin.pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
  obtain ⟨R, hR⟩ :=
    CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_normal T (CFSG.Quasithin.pResidual 2 H)
  have hcomp : (CFSG.Quasithin.pResidualOf 2 H).subtype.comp e.toMonoidHom =
      H.subtype.comp (CFSG.Quasithin.pResidual 2 H).subtype := by
    ext a
    rfl
  have he : Function.Surjective e.toMonoidHom := e.surjective
  refine ⟨R.mapSurjective (f := e.toMonoidHom) he, ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, hcomp, ← Subgroup.map_map, hR,
    Subgroup.map_inf _ _ _ H.subtype_injective]
  rfl

theorem sylow_map_eq_sup (hC : HypothesisC D) (h3 : Conclusion9_3 D hC)
    (T : Sylow 2 (Halpha D hC.alpha)) :
    (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype =
      Subgroup.zpowers hC.d ⊔
        ((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
          CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) := by
  have huT : hC.d ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype :=
    d_mem_sylow_map hC h3 T
  refine le_antisymm (fun t ht => ?_) (sup_le (Subgroup.zpowers_le.mpr huT) inf_le_left)
  rcases mem_or_mul_mem_of_conclusion9_3 hC h3 (Subgroup.map_subtype_le _ ht) with htL | htL
  · exact Subgroup.mem_sup_right ⟨ht, htL⟩
  · have ht' : t = hC.d * (hC.d * t) := by
      rw [← mul_assoc, hC.setup.oddT.mul_self_eq_one hC.hd, one_mul]
    rw [ht']
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
      (Subgroup.mem_sup_right ⟨Subgroup.mul_mem _ huT ht, htL⟩)

theorem sylow_inter_subset_sylow_map (hC : HypothesisC D) (h3 : Conclusion9_3 D hC)
    (T : Sylow 2 (Halpha D hC.alpha)) (S : Sylow 2 G)
    (hTS : (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ≤ S) :
    (S : Set G) ∩ D ⊆ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype := by
  have huT := d_mem_sylow_map hC h3 T
  rintro x ⟨hxS, hxD⟩
  have hxH : x ∈ Halpha D hC.alpha := by
    by_cases hxu : x = hC.d
    · rw [hxu]
      exact d_mem_Halpha hC h3
    · have hc := sylow_inter_commute_of_setup hC.setup S hxS (hTS huT) hxD hC.hd hxu
      have hx : x ∈ DalphaStar D hC.alpha := by
        rw [DalphaStar_eq_commSet hC h3.1]
        exact ⟨hxD, hc, hxu⟩
      exact Subgroup.subset_closure hx
  have hP : IsPGroup 2 ((S : Subgroup G).subgroupOf (Halpha D hC.alpha)) :=
    S.isPGroup'.comap_subtype
  have hTP : (T : Subgroup (Halpha D hC.alpha)) ≤ (S : Subgroup G).subgroupOf (Halpha D hC.alpha) :=
    fun t ht => hTS ⟨t, ht, rfl⟩
  have hx' : (⟨x, hxH⟩ : Halpha D hC.alpha) ∈ (S : Subgroup G).subgroupOf (Halpha D hC.alpha) :=
    hxS
  rw [T.is_maximal' hP hTP] at hx'
  exact ⟨⟨x, hxH⟩, hx', rfl⟩

theorem exists_quotient_mulEquiv_pResidualOf (hC : HypothesisC D) (h3 : Conclusion9_3 D hC) :
    ∃ (C : Subgroup (CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha))) (_ : C.Normal),
      C ≤ Subgroup.center _ ∧ Odd (Nat.card C) ∧
      Nonempty (CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) ⧸ C ≃*
        Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha)) := by
  have hLH : CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) ≤ Halpha D hC.alpha :=
    Subgroup.map_subtype_le _
  let f : CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) →*
      Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) :=
    (QuotientGroup.mk' (Subgroup.center (Halpha D hC.alpha))).comp (Subgroup.inclusion hLH)
  have hf1 : ∀ x, f x = 1 ↔ Subgroup.inclusion hLH x ∈ Subgroup.center (Halpha D hC.alpha) :=
    fun x => QuotientGroup.eq_one_iff _
  have hu : (⟨hC.d, d_mem_Halpha hC h3⟩ : Halpha D hC.alpha) ∈
      Subgroup.center (Halpha D hC.alpha) :=
    Subgroup.mem_center_iff.mpr fun h => Subtype.ext
      (Subgroup.mem_centralizer_singleton_iff.mp (PartThree.Halpha_le_centralizer_d hC h.2))
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (Halpha D hC.alpha)) y
    rcases mem_or_mul_mem_of_conclusion9_3 hC h3 h.2 with hL | hL
    · exact ⟨⟨h, hL⟩, rfl⟩
    · refine ⟨⟨hC.d * h, hL⟩, ?_⟩
      have hu1 : QuotientGroup.mk' (Subgroup.center (Halpha D hC.alpha))
          ⟨hC.d, d_mem_Halpha hC h3⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr hu
      change QuotientGroup.mk' _ (⟨hC.d, d_mem_Halpha hC h3⟩ * h) = QuotientGroup.mk' _ h
      rw [map_mul, hu1, one_mul]
  have hker : ∀ x ∈ f.ker, ∀ h ∈ Halpha D hC.alpha, Commute ((x : _) : G) h := by
    intro x hx h hh
    have hc := Subgroup.mem_center_iff.mp ((hf1 x).mp hx) ⟨h, hh⟩
    exact (congrArg Subtype.val hc).symm
  refine ⟨f.ker, inferInstance, fun x hx => ?_, ?_,
    ⟨QuotientGroup.quotientKerEquivOfSurjective f hf⟩⟩
  · exact Subgroup.mem_center_iff.mpr fun l => Subtype.ext (hker x hx l (hLH l.2)).eq.symm
  · by_contra hodd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := f.ker) 2
      (even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd))
    have hx' : orderOf (((x : CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) : G)) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
    have hx2 := pow_orderOf_eq_one ((x : CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) : G)
    rw [hx', pow_two] at hx2
    have hx1 := eq_one_of_mem_pResidualOf_of_commute hC h3
      (x : CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)).2 (hker x x.2) hx2
    rw [hx1, orderOf_one] at hx'
    exact absurd hx' (by decide)

private theorem exists_singer_model {L : Type} [Group L] (C : Subgroup L) [C.Normal]
    {K : Type} [Group K] (hK : CFSG.BenderSuzuki.IsBenderGroup K) (ψ : L ⧸ C ≃* K) :
    ∃ q : ℕ, ((∃ f : ℕ, 2 ≤ f ∧ q = 2 ^ f ∧
        Nonempty (L ⧸ C ≃* CFSG.BenderSuzuki.MatrixGroups.PSL2BinaryMatrixGroup f)) ∨
      (∃ m : ℕ, 1 ≤ m ∧ q = 2 ^ (2 * m + 1) ∧
        Nonempty (L ⧸ C ≃* CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) ∨
      (∃ f : ℕ, 2 ≤ f ∧ q = 2 ^ f ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F)
        (A : CFSG.BenderSuzuki.MatrixGroups.HermitianForm 3 F),
          A.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] ∧ Nat.card F = q ^ 2 ∧
          Nat.card {x : F // A.conj x = x} = q ∧
          Nonempty (L ⧸ C ≃*
            CFSG.BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup A))) ∧
      ((∃ f : ℕ, 2 ≤ f ∧ q = 2 ^ f ∧ Nonempty (K ≃* CFSG.Theory.Comparator.PSL2Model f)) ∨
        (∃ m : ℕ, 1 ≤ m ∧ q = 2 ^ (2 * m + 1) ∧ Nonempty (K ≃* CFSG.Theory.Comparator.SzModel m)) ∨
        (∃ f : ℕ, 2 ≤ f ∧ q = 2 ^ f ∧ Nonempty (K ≃* CFSG.Theory.Comparator.PSU3Model f))) := by
  rcases hK with ⟨n, hn, e⟩ | ⟨n, hn, e⟩ | ⟨n, hn, e⟩
  · exact ⟨2 ^ n, Or.inl ⟨n, hn, rfl, ⟨ψ.trans e⟩⟩, Or.inl ⟨n, hn, rfl, ⟨e⟩⟩⟩
  · exact ⟨2 ^ (2 * n + 1), Or.inr (Or.inl ⟨n, hn, rfl, ⟨(ψ.trans e).trans
      (MulEquiv.subgroupCongr (CFSG.BenderSuzuki.szModel_eq_suzukiMatrixGroup n))⟩⟩),
      Or.inr (Or.inl ⟨n, hn, rfl, ⟨e⟩⟩)⟩
  · obtain ⟨F, hF, hFfin, A, hA, hFcard, hfixed, ⟨e'⟩⟩ :=
      CFSG.GH74.Uniqueness.Bender.exists_psu3_concrete hn
    exact ⟨2 ^ n, Or.inr (Or.inr ⟨n, hn, rfl, F, hF, hFfin, A, hA, hFcard, hfixed,
      ⟨(ψ.trans e).trans e'⟩⟩), Or.inr (Or.inr ⟨n, hn, rfl, ⟨e⟩⟩)⟩

open CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex (cosetNormalizerPerm) in
structure DeltaSetup (hC : HypothesisC D) (T : Sylow 2 (Halpha D hC.alpha)) (S : Sylow 2 G)
    (U : Subgroup G) : Prop where
  eq_closure : U = Subgroup.closure {x : G | x ∈ (T : Subgroup (Halpha D hC.alpha)).map
    (Halpha D hC.alpha).subtype ⊓ CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) ∧
      orderOf x = 2}
  isElementaryAbelian : IsElementaryAbelian 2 U
  model : (∃ f : ℕ, 2 ≤ f ∧ Nat.card U = 2 ^ f ∧
      Nonempty (Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃*
        CFSG.Theory.Comparator.PSL2Model f)) ∨
    (∃ m : ℕ, 1 ≤ m ∧ Nat.card U = 2 ^ (2 * m + 1) ∧
      Nonempty (Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃*
        CFSG.Theory.Comparator.SzModel m)) ∨
    (∃ f : ℕ, 2 ≤ f ∧ Nat.card U = 2 ^ f ∧
      Nonempty (Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃*
        CFSG.Theory.Comparator.PSU3Model f))
  le_pResidualOf : U ≤ CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)
  le_sylow_map : U ≤ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype
  sylow_inter : (S : Set G) ∩ D = (fun v : G => hC.d * v) '' (U : Set G)
  sylow_map_inter : ((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype :
    Set G) ∩ D = (fun v : G => hC.d * v) '' (U : Set G)
  singer_isCyclic : IsCyclic (((CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) ⊓
      Subgroup.normalizer (U : Set G)).subgroupOf
        (Subgroup.normalizer ((fun v : G => hC.d * v) '' (U : Set G)))).map
      (cosetNormalizerPerm ((fun v : G => hC.d * v) '' (U : Set G))))
  singer_card : Nat.card (((CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) ⊓
      Subgroup.normalizer (U : Set G)).subgroupOf
        (Subgroup.normalizer ((fun v : G => hC.d * v) '' (U : Set G)))).map
      (cosetNormalizerPerm ((fun v : G => hC.d * v) '' (U : Set G)))) = Nat.card U - 1
  singer_regular : ∀ x y : (fun v : G => hC.d * v) '' (U : Set G), (x : G) ≠ hC.d →
    (y : G) ≠ hC.d → ∃! σ : ((CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) ⊓
      Subgroup.normalizer (U : Set G)).subgroupOf
        (Subgroup.normalizer ((fun v : G => hC.d * v) '' (U : Set G)))).map
      (cosetNormalizerPerm ((fun v : G => hC.d * v) '' (U : Set G))),
        (σ : Equiv.Perm ((fun v : G => hC.d * v) '' (U : Set G))) x = y

open CFSG.ProperTwoGeneratedCore.CosetNormalizerSinger in
theorem exists_deltaSetup (hC : HypothesisC D)
    (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC) (T : Sylow 2 (Halpha D hC.alpha))
    (S : Sylow 2 G)
    (hTS : (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ≤ S) :
    ∃ U : Subgroup G, DeltaSetup hC T S U := by
  classical
  have hLH : CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) ≤ Halpha D hC.alpha :=
    Subgroup.map_subtype_le _
  have huL : ∀ l ∈ CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha), Commute hC.d l :=
    fun l hl => (Subgroup.mem_centralizer_singleton_iff.mp
      (PartThree.Halpha_le_centralizer_d hC (hLH hl))).symm
  have huT := d_mem_sylow_map hC h3 T
  have hu2 : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
  obtain ⟨R, hR⟩ := exists_sylow_pResidualOf T
  obtain ⟨C, hCn, hCc, hCodd, ⟨ψ⟩⟩ := exists_quotient_mulEquiv_pResidualOf hC h3
  obtain ⟨q, hmodelL, hmodelH⟩ := exists_singer_model C hH.bender ψ
  obtain ⟨hel, hcard, hcyc, hcardS, hreg, -⟩ :=
    even_rank_one_central_odd_cover_involution_normalizer_singer_action C hCc hCodd R q hmodelL
  obtain ⟨U, hUmap⟩ : ∃ U : Subgroup G, (Subgroup.closure
      {x : CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) | x ∈ (R : Subgroup _) ∧
        orderOf x = 2}).map (CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)).subtype = U :=
    ⟨_, rfl⟩
  have hUeq : U = Subgroup.closure {x : G | x ∈ (T : Subgroup (Halpha D hC.alpha)).map
      (Halpha D hC.alpha).subtype ⊓ CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) ∧
        orderOf x = 2} := by
    rw [← hUmap, CFSG.ProperTwoGeneratedCore.RankOnePair.map_closure_involutions, hR]
  have hU' : Subgroup.closure
      {x : CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) | x ∈ (R : Subgroup _) ∧
        orderOf x = 2} = U.subgroupOf (CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) := by
    rw [← hUmap]
    exact (Subgroup.comap_map_eq_self_of_injective
      (CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)).subtype_injective _).symm
  have hUel : IsElementaryAbelian 2 U := by
    rw [← hUmap]
    exact IsElementaryAbelian.map_subtype
  have hcardU : Nat.card U = q := by
    rw [← hUmap, Subgroup.card_map_of_injective
      (CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)).subtype_injective]
    exact hcard
  have hUL : U ≤ CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) := by
    rw [← hUmap]
    exact Subgroup.map_subtype_le _
  have hUT : U ≤ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype := by
    rw [hUeq, Subgroup.closure_le]
    exact fun x hx => hx.1.1
  rw [hU'] at hcyc hcardS hreg
  obtain ⟨hCcyc, hCcard, hCreg⟩ :=
    CFSG.ProperTwoGeneratedCore.RankOnePair.coset_conjugation_image_of_singer hUL huL hcyc
      hcardS hreg
  have hΔT : ((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype : Set G) ∩ D =
      (fun v : G => hC.d * v) '' (U : Set G) := by
    ext x
    constructor
    · rintro ⟨hxT, hxD⟩
      by_cases hxu : x = hC.d
      · exact ⟨1, U.one_mem, show hC.d * 1 = x by rw [mul_one, hxu]⟩
      · have hc : Commute x hC.d := hC.setup.oddT.commute_of_isPGroup
          (T.isPGroup'.map (Halpha D hC.alpha).subtype) hxD hC.hd hxT huT
        have hxL := mul_mem_of_mem_commSet hC h3 ⟨hxD, hc, hxu⟩
        have hx2 : x * x = 1 := hC.setup.oddT.mul_self_eq_one hxD
        have hord : orderOf (hC.d * x) = 2 := by
          refine orderOf_eq_prime ?_ fun h1 => hxu ?_
          · rw [pow_two, mul_assoc, ← mul_assoc x hC.d x, hc.eq, mul_assoc, hx2, mul_one, hu2]
          · rw [← hC.setup.oddT.inv_eq hC.hd]
            exact eq_inv_of_mul_eq_one_right h1
        refine ⟨hC.d * x, ?_, show hC.d * (hC.d * x) = x by rw [← mul_assoc, hu2, one_mul]⟩
        rw [hUeq]
        exact Subgroup.subset_closure ⟨⟨Subgroup.mul_mem _ huT hxT, hxL⟩, hord⟩
    · rintro ⟨v, hv, rfl⟩
      refine ⟨Subgroup.mul_mem _ huT (hUT hv), show hC.d * v ∈ D from ?_⟩
      by_cases hv1 : v = 1
      · rw [hv1, mul_one]
        exact hC.hd
      · exact (mul_mem_commSet_of_orderOf_eq_two hC hH h3 (hUL hv)
          (orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian v hv) hv1)).1
  have hΔS : (S : Set G) ∩ D = (fun v : G => hC.d * v) '' (U : Set G) := by
    rw [← hΔT]
    refine Set.Subset.antisymm (fun x hx => ⟨sylow_inter_subset_sylow_map hC h3 T S hTS hx,
      hx.2⟩) ?_
    rintro x ⟨hxT, hxD⟩
    exact ⟨hTS hxT, hxD⟩
  refine ⟨U, hUeq, hUel, ?_, hUL, hUT, hΔS, hΔT, hCcyc, ?_, hCreg⟩
  · rw [hcardU]
    exact hmodelH
  · rw [hCcard, hcardU]

namespace DeltaSetup

open CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex (cosetNormalizerPerm)

variable {hC : HypothesisC D} {T : Sylow 2 (Halpha D hC.alpha)} {S : Sylow 2 G}
  {U : Subgroup G}

omit [Finite G] in
theorem exists_card (hU : DeltaSetup hC T S U) : ∃ e : ℕ, 2 ≤ e ∧ Nat.card U = 2 ^ e := by
  rcases hU.model with ⟨f, hf, hq, -⟩ | ⟨m, hm, hq, -⟩ | ⟨f, hf, hq, -⟩
  · exact ⟨f, hf, hq⟩
  · exact ⟨2 * m + 1, by omega, hq⟩
  · exact ⟨f, hf, hq⟩

omit [Finite G] in
theorem ne_bot (hU : DeltaSetup hC T S U) : U ≠ ⊥ := by
  rintro rfl
  obtain ⟨e, he, hcard⟩ := hU.exists_card
  rw [Subgroup.card_bot] at hcard
  have : 2 ^ 2 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  omega

theorem d_mem_centralizer (hU : DeltaSetup hC T S U) :
    hC.d ∈ Subgroup.centralizer (U : Set G) :=
  Subgroup.mem_centralizer_iff.mpr fun _ hx => Subgroup.mem_centralizer_singleton_iff.mp
    (PartThree.Halpha_le_centralizer_d hC (Subgroup.map_subtype_le _ (hU.le_pResidualOf hx)))

theorem d_not_mem (h3 : Conclusion9_3 D hC) (hU : DeltaSetup hC T S U) : hC.d ∉ U := fun h =>
  hC.setup.oddT.ne_one hC.hd
    (Subgroup.disjoint_def.mp h3.2.2.2 (Subgroup.mem_zpowers _) (hU.le_pResidualOf h))

theorem transitive (hU : DeltaSetup hC T S U) :
    ∀ x ∈ (fun v : G => hC.d * v) '' (U : Set G), ∀ y ∈ (fun v : G => hC.d * v) '' (U : Set G),
      ∃ n ∈ Subgroup.normalizer ((fun v : G => hC.d * v) '' (U : Set G)), n * x * n⁻¹ = y := by
  rw [← hU.sylow_inter]
  intro x hx y hy
  exact sylow_inter_D_transitive hC.setup.isClass hC.setup.oddT S hx hy

theorem two_transitive (hU : DeltaSetup hC T S U) :
    ∀ a ∈ (fun v : G => hC.d * v) '' (U : Set G), ∀ b ∈ (fun v : G => hC.d * v) '' (U : Set G),
    ∀ c ∈ (fun v : G => hC.d * v) '' (U : Set G), ∀ e ∈ (fun v : G => hC.d * v) '' (U : Set G),
      a ≠ b → c ≠ e → ∃ g ∈ Subgroup.normalizer ((fun v : G => hC.d * v) '' (U : Set G)),
        g * a * g⁻¹ = c ∧ g * b * g⁻¹ = e := by
  intro a ha b hb c hc e he hab hce
  have hu : hC.d ∈ (fun v : G => hC.d * v) '' (U : Set G) := ⟨1, U.one_mem, mul_one _⟩
  obtain ⟨n₁, hn₁, hn₁a⟩ := hU.transitive a ha _ hu
  obtain ⟨n₂, hn₂, hn₂c⟩ := hU.transitive c hc _ hu
  have hb' := (Subgroup.mem_set_normalizer_iff.mp hn₁ b).mp hb
  have he' := (Subgroup.mem_set_normalizer_iff.mp hn₂ e).mp he
  have hb'u : n₁ * b * n₁⁻¹ ≠ hC.d := fun h =>
    hab (mul_left_cancel (mul_right_cancel (h.trans hn₁a.symm))).symm
  have he'u : n₂ * e * n₂⁻¹ ≠ hC.d := fun h =>
    hce (mul_left_cancel (mul_right_cancel (h.trans hn₂c.symm))).symm
  obtain ⟨⟨_, m, hm, rfl⟩, hσ, -⟩ := hU.singer_regular ⟨_, hb'⟩ ⟨_, he'⟩ hb'u he'u
  have hmL := (Subgroup.mem_subgroupOf.mp hm).1
  have hmu : (m : G) * hC.d = hC.d * m := Subgroup.mem_centralizer_singleton_iff.mp
    (PartThree.Halpha_le_centralizer_d hC (Subgroup.map_subtype_le _ hmL))
  have hσ' : (m : G) * (n₁ * b * n₁⁻¹) * (m : G)⁻¹ = n₂ * e * n₂⁻¹ := congrArg Subtype.val hσ
  refine ⟨n₂⁻¹ * m * n₁, Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hn₂) m.2)
    hn₁, ?_, ?_⟩
  · calc n₂⁻¹ * m * n₁ * a * (n₂⁻¹ * m * n₁)⁻¹ =
          n₂⁻¹ * ((m : G) * (n₁ * a * n₁⁻¹) * (m : G)⁻¹) * n₂ := by group
      _ = n₂⁻¹ * hC.d * n₂ := by rw [hn₁a, hmu, mul_inv_cancel_right]
      _ = c := by rw [← hn₂c]; group
  · calc n₂⁻¹ * m * n₁ * b * (n₂⁻¹ * m * n₁)⁻¹ =
          n₂⁻¹ * ((m : G) * (n₁ * b * n₁⁻¹) * (m : G)⁻¹) * n₂ := by group
      _ = e := by rw [hσ']; group

theorem affine [IsElementaryAbelian 2 U] (h3 : Conclusion9_3 D hC) (hU : DeltaSetup hC T S U) :
    Subgroup.normalizer ((fun v : G => hC.d * v) '' (U : Set G)) ≤
        Subgroup.normalizer (U : Set G) ∧
      (∀ n : G, (n ∈ Subgroup.normalizer ((fun v : G => hC.d * v) '' (U : Set G)) ∧
          ∀ x ∈ (fun v : G => hC.d * v) '' (U : Set G), n * x * n⁻¹ = x) ↔
        n ∈ Subgroup.centralizer
          ((Subgroup.closure ({hC.d} : Set G) ⊔ U : Subgroup G) : Set G)) ∧
      (∃ φ : Subgroup.normalizer ((fun v : G => hC.d * v) '' (U : Set G)) →*
          (Additive U ≃ᵃ[ZMod 2] Additive U),
        φ.ker = (Subgroup.centralizer
            ((Subgroup.closure ({hC.d} : Set G) ⊔ U : Subgroup G) : Set G)).subgroupOf
          (Subgroup.normalizer ((fun v : G => hC.d * v) '' (U : Set G))) ∧
        ∀ (n : Subgroup.normalizer ((fun v : G => hC.d * v) '' (U : Set G))) (v : U),
          (n : G) * (hC.d * v) * (n : G)⁻¹ =
            hC.d * ((Additive.toMul (φ n (Additive.ofMul v)) : U) : G)) ∧
      Subgroup.normalizer ((fun v : G => hC.d * v) '' (U : Set G)) ⊓
          Subgroup.centralizer ({hC.d} : Set G) =
        Subgroup.centralizer ({hC.d} : Set G) ⊓ Subgroup.normalizer (U : Set G) := by
  obtain ⟨-, hNU, hker, ⟨φ, hφker, -, hφ⟩, hNu⟩ :=
    CFSG.ProperTwoGeneratedCore.CosetNormalizer.involution_coset_normalizer_affine_action U
      hU.ne_bot hU.d_mem_centralizer (hU.d_not_mem h3) (hC.setup.oddT.orderOf_eq_two hC.hd)
  exact ⟨hNU, hker, ⟨φ, hφker, hφ⟩, hNu⟩

end DeltaSetup

omit [Finite G] in
open CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex in
theorem affine_eq_one_iff {U : Subgroup G} [IsElementaryAbelian 2 U] {u : G}
    (φ : Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G)) →*
      (Additive U ≃ᵃ[ZMod 2] Additive U))
    (hφ : ∀ (n : Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G))) (v : U),
      (n : G) * (u * v) * (n : G)⁻¹ = u * ((Additive.toMul (φ n (Additive.ofMul v)) : U) : G))
    (n : Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G))) :
    φ n = 1 ↔ (n : G) ∈ Subgroup.centralizer ((fun v : G => u * v) '' (U : Set G)) := by
  calc φ n = 1 ↔ CFSG.ProperTwoGeneratedCore.RankOnePair.cosetAffinePerm U u (φ n) =
        CFSG.ProperTwoGeneratedCore.RankOnePair.cosetAffinePerm U u 1 :=
      (CFSG.ProperTwoGeneratedCore.RankOnePair.cosetAffinePerm_injective U u).eq_iff.symm
    _ ↔ cosetNormalizerPerm ((fun v : G => u * v) '' (U : Set G)) n = 1 := by
      rw [map_one, ← MonoidHom.comp_apply,
        CFSG.ProperTwoGeneratedCore.RankOnePair.cosetAffinePerm_comp_eq φ hφ]
    _ ↔ _ := by
      rw [← MonoidHom.mem_ker, cosetNormalizerPerm_ker_eq_entire_centralizer,
        Subgroup.mem_subgroupOf]

open CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex (cosetNormalizerPerm)
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open scoped MatrixGroups

local instance factPrimeSevenDelta : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩

omit [Finite G] in
private theorem nonempty_range_mulEquiv_psl {Δ : Set G} (b : Δ ≃ Omega (ZMod 7))
    (hb : (fun σ : Equiv.Perm Δ => b.permCongr σ) '' ((cosetNormalizerPerm Δ).range :
      Set (Equiv.Perm Δ)) = (coordinateG (ZMod 7) : Set (Equiv.Perm (Omega (ZMod 7)))))
    (hPSL : (coordinatePSLAction (ZMod 7)).range = coordinateG (ZMod 7)) :
    Nonempty ((cosetNormalizerPerm Δ).range ≃* PSL(2, ZMod 7)) := by
  have hmap : (cosetNormalizerPerm Δ).range.map b.permCongrHom.toMonoidHom =
      coordinateG (ZMod 7) := by
    apply SetLike.coe_injective
    rw [Subgroup.coe_map]
    exact hb
  let e₁ : (cosetNormalizerPerm Δ).range ≃* coordinateG (ZMod 7) :=
    ((cosetNormalizerPerm Δ).range.equivMapOfInjective _ b.permCongrHom.injective).trans
      (MulEquiv.subgroupCongr hmap)
  let e₂ : PSL(2, ZMod 7) ≃* coordinateG (ZMod 7) :=
    (MonoidHom.ofInjective (coordinatePSLAction_injective (ZMod 7))).trans
      (MulEquiv.subgroupCongr hPSL)
  exact ⟨e₁.trans e₂.symm⟩

namespace DeltaSetup

variable {hC : HypothesisC D} {T : Sylow 2 (Halpha D hC.alpha)} {S : Sylow 2 G}
  {U : Subgroup G}

theorem solvable_or_projective_seven [IsElementaryAbelian 2 U] (h3 : Conclusion9_3 D hC)
    (hU : DeltaSetup hC T S U) :
    (Group.IsSolvable (cosetNormalizerPerm ((fun v : G => hC.d * v) '' (U : Set G))).range ∧
        ∀ g ∈ CFSG.ProperTwoGeneratedCore.CosetNormalizerSinger.translationGroup (Additive U),
          (CFSG.ProperTwoGeneratedCore.RankOnePair.cosetCoordinates U hC.d).permCongr
              g.toEquiv ∈
            (cosetNormalizerPerm ((fun v : G => hC.d * v) '' (U : Set G))).range) ∨
      (Nat.card U = 8 ∧
        Nonempty ((cosetNormalizerPerm ((fun v : G => hC.d * v) '' (U : Set G))).range ≃*
          PSL(2, ZMod 7))) := by
  obtain ⟨e, he, hcard⟩ := hU.exists_card
  obtain ⟨hNU, -, ⟨φ, -, hφ⟩, -⟩ := hU.affine h3
  let X := (CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) ⊓
    Subgroup.normalizer (U : Set G)).subgroupOf
      (Subgroup.normalizer ((fun v : G => hC.d * v) '' (U : Set G)))
  have hXu : ∀ x ∈ X, (x : G) ∈ Subgroup.centralizer ({hC.d} : Set G) := fun x hx =>
    PartThree.Halpha_le_centralizer_d hC
      (Subgroup.map_subtype_le _ (Subgroup.mem_subgroupOf.mp hx).1)
  have hXn : ∀ m : Subgroup.normalizer ((fun v : G => hC.d * v) '' (U : Set G)),
      (m : G) ∈ Subgroup.centralizer ({hC.d} : Set G) → ∀ x ∈ X, m * x * m⁻¹ ∈ X := by
    intro m hm x hx
    obtain ⟨hxL, hxU⟩ := Subgroup.mem_subgroupOf.mp hx
    have hmα : (m : G) ∈ Subgroup.normalizer hC.alpha := by
      rw [h3.1]
      exact Subgroup.centralizer_le_normalizer _ hm
    have hmL := CFSG.Quasithin.normalizer_le_normalizer_pResidualOf 2 _
      (CFSG.OddTranspositions.normalizer_le_normalizer_Halpha hC.setup.normal hmα)
    refine Subgroup.mem_subgroupOf.mpr ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp hmL _).mp hxL
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hNU m.2) hxU) (Subgroup.inv_mem _ (hNU m.2))
  rcases CFSG.ProperTwoGeneratedCore.RankOnePair.coset_normalizer_perm_solvable_or_projective_seven
      (by omega) hcard φ hφ hU.transitive X hXu hXn hU.singer_isCyclic hU.singer_regular with
    h | ⟨h8, ⟨b, hb⟩, hPSL⟩
  · exact Or.inl h
  · exact Or.inr ⟨h8, nonempty_range_mulEquiv_psl b hb hPSL⟩

end DeltaSetup

end CFSG.OddTranspositions.PartThree.Nine
