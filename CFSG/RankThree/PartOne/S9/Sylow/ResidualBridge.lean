module

public import CFSG.RankThree.PartOne.S9.Defs
public import CFSG.Quasithin.Background.B6Defs
public import CFSG.RankThree.GroupTheory.SteinbergBYRelativeCores
public import CFSG.RankThree.GroupTheory.SubnormalCores
public import CFSG.RankThree.LocalRank.ThetaPlaneAlpha

public section

namespace CFSG.RankThree.PartOne.Sec9A

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory

theorem map_inSubgroup_theta_of_injective {X Y : Type*} [Group X] [Group Y] [Finite X] {p : ℕ}
    (hp : p.Prime) (f : X →* Y) (hf : Function.Injective f) (L : Subgroup X) :
    (inSubgroup (aschbacherSolvableCore p) L).map f =
      inSubgroup (aschbacherSolvableCore p) (L.map f) := by
  rw [inSubgroup, inSubgroup,
    ← CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv hp (L.equivMapOfInjective f hf),
    Subgroup.map_map, Subgroup.map_map]
  rfl

theorem twoPrimeResidual_map_le_of_injective {X Y : Type*} [Group X] [Group Y]
    (f : X →* Y) (hf : Function.Injective f) (W : Subgroup X) :
    CFSG.Quasithin.twoPrimeResidual (W.map f) ≤ (CFSG.Quasithin.twoPrimeResidual W).map f := by
  intro x hx
  unfold CFSG.Quasithin.twoPrimeResidual at hx
  simp only [Subgroup.mem_iInf] at hx
  have hW : x ∈ W.map f := hx (W.map f) ⟨le_rfl, Subgroup.le_normalizer, by
    rw [Subgroup.relIndex_self]; simp⟩
  obtain ⟨y, hyW, rfl⟩ := hW
  refine Subgroup.mem_map.mpr ⟨y, ?_, rfl⟩
  unfold CFSG.Quasithin.twoPrimeResidual
  simp only [Subgroup.mem_iInf]
  intro N hN
  have hN' : f y ∈ N.map f := by
    refine hx (N.map f) ⟨Subgroup.map_mono hN.1,
      (Subgroup.map_mono hN.2.1).trans (Subgroup.le_normalizer_map f), ?_⟩
    rw [Subgroup.relIndex_map_map_of_injective _ _ hf]
    exact hN.2.2
  obtain ⟨y', hy', hy'f⟩ := hN'
  have : y' = y := hf hy'f
  rwa [← this]

theorem evenRank_subgroup_le {G : Type*} [Group G] [Finite G] (K : Subgroup G) :
    evenRank K ≤ evenRank G := by
  apply csSup_le'
  rintro _ ⟨p, X, hp, hp2, ⟨P, hP, hP2, rfl⟩, rfl⟩
  refine ((CFSG.RankThreeEvenClassification.Helpers.pRank_le_map_of_injective p hp K.subtype
    K.subtype_injective (Subgroup.normalizer (P : Set K))).trans
      (CFSG.RankThreeEvenClassification.Helpers.pRank_mono p hp
        (Subgroup.le_normalizer_map K.subtype))).trans
    (CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank p hp hp2 _
      ⟨P.map K.subtype, fun h => hP ((Subgroup.map_eq_bot_iff_of_injective P
        K.subtype_injective).mp h), hP2.map _, rfl⟩)

theorem map_thetaT_subgroupOf {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {K D : Subgroup G} (hDK : D ≤ K) {t : G} (htD : t ∈ D) (ht1 : t ≠ 1) :
    (thetaT p (D.subgroupOf K)).map K.subtype =
      ⨅ d ∈ D, ⨅ (_ : d ≠ 1),
        inSubgroup (aschbacherSolvableCore p) (K ⊓ Subgroup.centralizer ({d} : Set G)) := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_iInf, thetaT, Subgroup.coe_subtype]
  constructor
  · rintro ⟨y, hy, rfl⟩ d hd hd1
    have hdK : d ∈ K := hDK hd
    have hy' := hy ⟨d, hdK⟩ hd (fun h => hd1 (congrArg Subtype.val h))
    have := Subgroup.mem_map_of_mem K.subtype hy'
    rwa [map_inSubgroup_theta_of_injective hp K.subtype K.subtype_injective,
      CFSG.RankThree.GroupTheory.SteinbergBY.map_subtype_centralizer_singleton] at this
  · intro hx
    have hxt := hx t htD ht1
    have hxK : x ∈ K := (inf_le_left : K ⊓ _ ≤ K) (Subgroup.map_subtype_le _ hxt)
    refine ⟨⟨x, hxK⟩, ?_, rfl⟩
    intro b' hb' hb'1
    have hb1 : (b' : G) ≠ 1 := fun h => hb'1 (Subtype.ext h)
    have hxb := hx b' hb' hb1
    rw [← CFSG.RankThree.GroupTheory.SteinbergBY.map_subtype_centralizer_singleton,
      ← map_inSubgroup_theta_of_injective hp K.subtype K.subtype_injective] at hxb
    obtain ⟨z, hz, hzx⟩ := hxb
    have : z = ⟨x, hxK⟩ := Subtype.ext hzx
    rwa [← this]

theorem residualGroup_eq_map {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {K D : Subgroup G} (hDK : D ≤ K) {t : G} (htD : t ∈ D) (ht1 : t ≠ 1) :
    residualGroup p K D t =
      (⁅inSubgroup (aschbacherSolvableCore p)
          (Subgroup.centralizer ({(⟨t, hDK htD⟩ : K)} : Set K)), D.subgroupOf K⁆ ⊔
        thetaT p (D.subgroupOf K)).map K.subtype := by
  unfold residualGroup
  rw [Subgroup.map_sup, Subgroup.map_commutator,
    map_inSubgroup_theta_of_injective hp K.subtype K.subtype_injective,
    CFSG.RankThree.GroupTheory.SteinbergBY.map_subtype_centralizer_singleton,
    Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hDK,
    map_thetaT_subgroupOf hp hDK htD ht1]

end CFSG.RankThree.PartOne.Sec9A
