module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXCentralizerPushing
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.H13.NQRigidFitting4

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup CFSG.Open
open CFSG.QuasithinUnique.Setup.Campbell (NoPQuotient)
open CFSG.ABGLocalTools (IsSylowOf)

theorem characteristic_map_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    {D : Subgroup A} [hD : D.Characteristic] : (D.map e.toMonoidHom).Characteristic := by
  rw [characteristic_iff_map_le]
  intro φ
  have h1 := (characteristic_iff_map_le.mp hD) ((e.trans φ).trans e.symm)
  rw [map_map]
  calc D.map (φ.toMonoidHom.comp e.toMonoidHom) =
        (D.map ((e.trans φ).trans e.symm).toMonoidHom).map e.toMonoidHom := by
        rw [map_map]
        congr 1
        ext x
        simp
    _ ≤ D.map e.toMonoidHom := map_mono h1

section Simple

variable {G : Type} [Group G] [Finite G]

theorem centralizer_ne_top_of_simple [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    {v : G} (hv : v ≠ 1) : centralizer ({v} : Set G) ≠ ⊤ := by
  intro htop
  have hvc : v ∈ center G := by
    rw [mem_center_iff]
    intro g
    have : g ∈ centralizer ({v} : Set G) := htop ▸ mem_top g
    exact mem_centralizer_singleton_iff.mp this
  rcases (center G).normal_of_characteristic.eq_bot_or_eq_top with hc | hc
  · rw [hc, mem_bot] at hvc
    exact hv hvc
  · obtain ⟨a, b, hab⟩ := hnab
    have ha : a ∈ center G := hc ▸ mem_top a
    exact hab (mem_center_iff.mp ha b).symm

variable {T L M : Subgroup G}

theorem isKGroupCat_centralizer (h : QTNQ T L M) {v : G} (hv : v ≠ 1) :
    CFSG.SectionRank.IsKGroupCat (centralizer ({v} : Set G)) := by
  have := h.simple
  exact QuasithinUnique.isKGroupCat_of_kProper h.qtke.1
    (centralizer_ne_top_of_simple h.nonabelian hv)

theorem isSQTKCat_centralizer (h : QTNQ T L M) {v : G} (hv : v ∈ qtnqU L M) (hv1 : v ≠ 1) :
    CFSG.SectionRank.IsSQTKCat (centralizer ({v} : Set G)) :=
  ⟨isStronglyQuasithin_centralizer h hv hv1, isKGroupCat_centralizer h hv1⟩

theorem conj_mem_qtnqU (h : QTNQ T L M) {m u : G} (hm : m ∈ M) (hu : u ∈ qtnqU L M) :
    m⁻¹ * u * m ∈ qtnqU L M := by
  have := (mem_normalizer_iff.mp (le_normalizer_qtnqU h (M.inv_mem hm)) u).mp hu
  simpa using this

theorem centralizer_le_of_conj {m u : G} (hm : m ∈ M)
    (hle : centralizer ({m⁻¹ * u * m} : Set G) ≤ M) : centralizer ({u} : Set G) ≤ M := by
  intro g hg
  have hg' : m⁻¹ * g * m ∈ centralizer ({m⁻¹ * u * m} : Set G) := by
    rw [mem_centralizer_singleton_iff] at hg ⊢
    calc m⁻¹ * g * m * (m⁻¹ * u * m) = m⁻¹ * (g * u) * m := by group
      _ = m⁻¹ * (u * g) * m := by rw [hg]
      _ = m⁻¹ * u * m * (m⁻¹ * g * m) := by group
  have h1 := hle hg'
  have h2 : g = m * (m⁻¹ * g * m) * m⁻¹ := by group
  rw [h2]
  exact M.mul_mem (M.mul_mem hm h1) (M.inv_mem hm)

end Simple

theorem isSQTKCat_quotient_pCore {H : Type} [Group H] [Finite H]
    (hH : CFSG.SectionRank.IsSQTKCat H) : CFSG.SectionRank.IsSQTKCat (H ⧸ CFSG.pCore 2 H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨(CFSG.SectionRank.isStronglyQuasithin_quotient_two_group_iff _
    CFSG.pCore_isPGroup).mpr hH.1, hH.2.quotient _⟩

theorem isSQTKCat_subgroup_quotient_pCore {H : Type} [Group H] [Finite H]
    (hH : CFSG.SectionRank.IsSQTKCat H) (K : Subgroup H) :
    CFSG.SectionRank.IsSQTKCat (K ⧸ CFSG.pCore 2 K) :=
  isSQTKCat_quotient_pCore (hH.subgroup K)

section Control

variable {G : Type} [Group G] [Finite G]

theorem normalizer_le_of_characteristic_of_singleton {Y M R : Subgroup G}
    (hMG : CFSG.maximalTwoLocalsContaining (Y : Set G) = {M}) (hR2 : IsPGroup 2 R)
    (hYR : Y ≤ normalizer (R : Set G)) (D : Subgroup R) [D.Characteristic] (hD1 : D ≠ ⊥) :
    normalizer ((D.map R.subtype : Subgroup G) : Set G) ≤ M := by
  classical
  set Dg := D.map R.subtype with hDg
  have hDg1 : Dg ≠ ⊥ := by
    rw [hDg, Ne, map_eq_bot_iff_of_injective _ R.subtype_injective]
    exact hD1
  have hDg2 : IsPGroup 2 Dg := (hR2.to_subgroup D).map R.subtype
  have hYD : Y ≤ normalizer (Dg : Set G) := fun g hg =>
    CFSG.LocalAnalysis.GorensteinLyons.mem_normalizer_map_of_characteristic D (hYR hg)
  obtain ⟨B, ⟨hBloc, hNB⟩, hBmax⟩ := (Set.toFinite
    {Z : Subgroup G | CFSG.IsPLocal 2 Z ∧ normalizer (Dg : Set G) ≤ Z}).exists_maximal
      ⟨_, ⟨Dg, hDg1, hDg2, rfl⟩, le_rfl⟩
  have hBM : B ∈ CFSG.maximalTwoLocalsContaining (Y : Set G) := by
    refine ⟨⟨hBloc, fun Z hBZ hZ => ?_⟩, fun g hg => hNB (hYD hg)⟩
    exact absurd (hBmax ⟨hZ, hNB.trans hBZ.le⟩ hBZ.le) (not_le_of_gt hBZ)
  rw [hMG, Set.mem_singleton_iff] at hBM
  exact hBM ▸ hNB

theorem normalizer_le_subgroupOf_of_characteristic {H M R : Subgroup G} (hRH : R ≤ H)
    (hND : ∀ D : Subgroup R, D.Characteristic → D ≠ ⊥ →
      normalizer ((D.map R.subtype : Subgroup G) : Set G) ≤ M) :
    ∀ D : Subgroup (R.subgroupOf H), D.Characteristic → D ≠ ⊥ →
      normalizer ((D.map (R.subgroupOf H).subtype : Subgroup H) : Set H) ≤
        (M ⊓ H).subgroupOf H := by
  intro D hD hD1
  set e : R.subgroupOf H ≃* R := subgroupOfEquivOfLe hRH with he
  have hD' : (D.map e.toMonoidHom).Characteristic := characteristic_map_mulEquiv e
  have hD'1 : D.map e.toMonoidHom ≠ ⊥ := by
    rw [Ne, map_eq_bot_iff_of_injective _ e.injective]
    exact hD1
  have h1 := hND _ hD' hD'1
  set DH := D.map (R.subgroupOf H).subtype with hDH
  have heq : ((D.map e.toMonoidHom).map R.subtype : Subgroup G) = DH.map H.subtype := by
    rw [hDH, map_map, map_map]
    rfl
  have hDHH : DH.map H.subtype ≤ H := map_subtype_le _
  have hsub : (DH.map H.subtype).subgroupOf H = DH :=
    comap_map_eq_self_of_injective H.subtype_injective DH
  intro y hy
  rw [mem_subgroupOf]
  refine ⟨h1 ?_, y.2⟩
  rw [heq]
  have h2 : y ∈ (normalizer ((DH.map H.subtype : Subgroup G) : Set G)).subgroupOf H := by
    rw [subgroupOf_normalizer_eq hDHH, hsub]
    exact hy
  exact mem_subgroupOf.mp h2

theorem eq_pCore_normalizer_subgroupOf {H R : Subgroup G} (hRH : R ≤ H)
    (hR : R = (CFSG.pCore 2 (H ⊓ normalizer (R : Set G) : Subgroup G)).map
      (H ⊓ normalizer (R : Set G)).subtype) :
    R.subgroupOf H = (CFSG.pCore 2 (normalizer ((R.subgroupOf H : Subgroup H) : Set H))).map
      (normalizer ((R.subgroupOf H : Subgroup H) : Set H)).subtype := by
  apply map_injective H.subtype_injective
  have hNR : (normalizer ((R.subgroupOf H : Subgroup H) : Set H)).map H.subtype =
      H ⊓ normalizer (R : Set G) := by
    rw [← subgroupOf_normalizer_eq hRH, subgroupOf_map_subtype, inf_comm]
  rw [subgroupOf_map_subtype, inf_of_le_left hRH,
    CFSG.LocalAnalysis.GorensteinLyons.map_subtype_pCore_map, hNR]
  exact hR

end Control

theorem isSolvable_of_isPGroup_quotient_pCore {X : Type*} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] (hX : IsPGroup p (X ⧸ CFSG.pCore 2 X)) : Group.IsSolvable X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA2 : IsPGroup 2 (CFSG.pCore 2 X) := CFSG.pCore_isPGroup
  have : Group.IsSolvable (CFSG.pCore 2 X) := by
    have : Group.IsNilpotent (CFSG.pCore 2 X) := hA2.isNilpotent
    infer_instance
  have : Group.IsSolvable (X ⧸ CFSG.pCore 2 X) := by
    have : Group.IsNilpotent (X ⧸ CFSG.pCore 2 X) := hX.isNilpotent
    infer_instance
  exact Group.isSolvable_of_ker_le_range (CFSG.pCore 2 X).subtype
    (QuotientGroup.mk' (CFSG.pCore 2 X)) (by rw [QuotientGroup.ker_mk', range_subtype])

theorem index_ne_two_of_noPQuotient {X : Type*} [Group X] (hX : NoPQuotient 2 X)
    (D : Subgroup X) (hD : D.Normal) : D.index ≠ 2 := by
  haveI := hD
  intro h2
  have hq : IsPGroup 2 (X ⧸ D) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine IsPGroup.of_card (n := 1) ?_
    rw [pow_one]
    exact h2
  have htop := hX D hq
  rw [htop, index_top] at h2
  omega

end CFSG.Quasithin.H13.NQRigid
