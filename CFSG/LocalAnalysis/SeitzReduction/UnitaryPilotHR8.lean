module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotHR8
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatCovers
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotPositionB
import CFSG.LocalAnalysis.SeitzReduction.CentralizerComponents
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourStandard
public import CFSG.LocalAnalysis.SeitzReduction.Inheritance
import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup CFSG.Blueprint CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section Center

theorem nonempty_quotient_center_mulEquiv_map_oddCore {G : Type} [Group G] [Finite G]
    {H D : Subgroup G} (hDH : D ≤ H) (hDq : CFSG.IsQuasisimple D)
    (hne : (D.subgroupOf H).map (QuotientGroup.mk' (oddCore H)) ≠ ⊥) :
    Nonempty (D ⧸ center D ≃* ((D.subgroupOf H).map (QuotientGroup.mk' (oddCore H))) ⧸
      center ((D.subgroupOf H).map (QuotientGroup.mk' (oddCore H)))) ∧
      Nat.card (center ((D.subgroupOf H).map (QuotientGroup.mk' (oddCore H)))) ∣
        Nat.card (center D) := by
  have hD₁ : CFSG.IsQuasisimple (D.subgroupOf H) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hDH).symm hDq
  have hnt : ∃ k, (QuotientGroup.mk' (oddCore H)).subgroupMap (D.subgroupOf H) k ≠ 1 := by
    by_contra h
    push Not at h
    apply hne
    rw [eq_bot_iff]
    rintro _ ⟨d, hd, rfl⟩
    exact (mem_bot).mpr (congrArg Subtype.val (h ⟨d, hd⟩))
  obtain ⟨e₂⟩ := LocalAnalysis.ComponentInitial.center_quotient_equiv_of_surjective hD₁
    ((QuotientGroup.mk' (oddCore H)).subgroupMap (D.subgroupOf H))
    ((QuotientGroup.mk' (oddCore H)).subgroupMap_surjective _)
    (LieType.CurtisTits.ker_le_center_of_isQuasisimple hD₁ hnt)
  have e₁ : D ⧸ center D ≃* (D.subgroupOf H) ⧸ center (D.subgroupOf H) :=
    QuotientGroup.congr _ _ (subgroupOfEquivOfLe hDH).symm
      (map_center_eq (subgroupOfEquivOfLe hDH).symm)
  refine ⟨⟨e₁.trans e₂⟩, ?_⟩
  rw [← Nat.card_congr (centerCongr (subgroupOfEquivOfLe hDH)).toEquiv]
  exact card_center_dvd_of_surjective _ ((QuotientGroup.mk' (oddCore H)).subgroupMap_surjective _)
    e₂

theorem lieModel_quotient_center_map_oddCore_of_isQuasisimple {G : Type} [Group G] [Finite G]
    {H D : Subgroup G} (hDH : D ≤ H) (hDq : CFSG.IsQuasisimple D)
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {m p f : ℕ} (hDm : LieModel (D ⧸ center D) t m p f)
    (hne : (D.subgroupOf H).map (QuotientGroup.mk' (oddCore H)) ≠ ⊥) :
    LieModel (((D.subgroupOf H).map (QuotientGroup.mk' (oddCore H))) ⧸
      center ((D.subgroupOf H).map (QuotientGroup.mk' (oddCore H)))) t m p f := by
  obtain ⟨⟨e⟩, -⟩ := nonempty_quotient_center_mulEquiv_map_oddCore hDH hDq hne
  exact LieType.CurtisTits.lieModel_of_mulEquiv e hDm

theorem odd_card_center_map_subgroupOf_oddCore {G : Type} [Group G] [Finite G] {H D : Subgroup G}
    (hDH : D ≤ H) (hDq : CFSG.IsQuasisimple D) (hZD : Odd (Nat.card (center D)))
    (hne : (D.subgroupOf H).map (QuotientGroup.mk' (oddCore H)) ≠ ⊥) :
    Odd (Nat.card (center ((D.subgroupOf H).map (QuotientGroup.mk' (oddCore H))))) :=
  hZD.of_dvd_nat (nonempty_quotient_center_mulEquiv_map_oddCore hDH hDq hne).2

theorem isComponent_fixedSubgroup_of_le_of_lieModel_quotient {Y : Type} [Group Y] {s : Y}
    {Kc D : Subgroup Y} (hsN : s ∈ normalizer (Kc : Set Y)) (hDK : D ≤ Kc)
    (hDs : D ≤ centralizer ({s} : Set Y))
    (hDcomp : IsComponent (D.subgroupOf (Kc ⊓ centralizer ({s} : Set Y))))
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {m p f : ℕ}
    (hDm : LieModel (D ⧸ center D) t m p f) :
    IsComponent
        ((D.subgroupOf Kc).subgroupOf (fixedSubgroup (Kc.normalizerMonoidHom ⟨s, hsN⟩))) ∧
      LieModel
        (((D.subgroupOf Kc).subgroupOf (fixedSubgroup (Kc.normalizerMonoidHom ⟨s, hsN⟩))) ⧸
          center ((D.subgroupOf Kc).subgroupOf
            (fixedSubgroup (Kc.normalizerMonoidHom ⟨s, hsN⟩)))) t m p f ∧
      ((D.subgroupOf Kc).subgroupOf (fixedSubgroup (Kc.normalizerMonoidHom ⟨s, hsN⟩))).map
        (fixedSubgroup (Kc.normalizerMonoidHom ⟨s, hsN⟩)).subtype = D.subgroupOf Kc ∧
      Nat.card (center ((D.subgroupOf Kc).subgroupOf
        (fixedSubgroup (Kc.normalizerMonoidHom ⟨s, hsN⟩)))) = Nat.card (center D) := by
  have hDfix : D.subgroupOf Kc ≤ fixedSubgroup (Kc.normalizerMonoidHom ⟨s, hsN⟩) := by
    rw [F4Pilot.fixedSubgroup_normalizerMonoidHom]
    intro x hx
    exact mem_subgroupOf.mpr (hDs (mem_subgroupOf.mp hx))
  exact ⟨F4Pilot.isComponent_subgroupOf_subgroupOf
      (F4Pilot.map_fixedSubgroup_normalizerMonoidHom Kc hsN) hDcomp,
    LinearPilot.lieModel_quotient_center_congr (F4Pilot.subgroupOfSubgroupOfEquiv hDK hDfix).symm
      hDm,
    by rw [subgroupOf_map_subtype, inf_eq_left.mpr hDfix],
    Nat.card_congr (centerCongr (F4Pilot.subgroupOfSubgroupOfEquiv hDK hDfix)).toEquiv⟩

theorem lieModel_PSU_of_mulEquiv_unitaryPSU {X : Type} [Group X] {p f m : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) (hm : 3 ≤ m) (hmq : (m, p ^ f) ≠ (3, 2))
    (e : X ≃* unitaryPSU h m) : LieModel X .PSU m p f :=
  Or.inl ⟨by decide, ⟨h.prime, h.one_le, hm, hmq⟩, K, inferInstance, h.finite, h.card_eq_sq,
    ⟨e.trans (unitaryPSUEquiv h (by omega))⟩⟩

end Center

@[expose] def SUmNeighbourAlternative {Y : Type} [Group Y] (s : Y) (D Kc : Subgroup Y)
    (m f : ℕ) : Prop :=
  D ≤ Kc ⊔ Kc.map (MulAut.conj s).toMonoidHom ∧
    ((Kc.map (MulAut.conj s).toMonoidHom = Kc ∧ D < Kc ∧ s ∉ Kc ∧
        ∃ hsN : s ∈ normalizer (Kc : Set Y),
          SUmOvergroup Kc (Kc.normalizerMonoidHom ⟨s, hsN⟩) m f) ∨
      (Kc.map (MulAut.conj s).toMonoidHom ≠ Kc ∧
        ⁅Kc, Kc.map (MulAut.conj s).toMonoidHom⁆ = ⊥ ∧ center Kc = ⊥ ∧ Nonempty (Kc ≃* D)))

@[expose] def NeighbourOvergroupSUm {Y : Type} [Group Y] (s : Y) (D : Subgroup Y) (m f : ℕ) :
    Prop :=
  ∃ Kc : Subgroup Y, IsComponent Kc ∧ SUmNeighbourAlternative s D Kc m f

theorem SUmNeighbourAlternative.map_conj_of_swap {Y : Type} [Group Y] {s : Y} (hs2 : s ^ 2 = 1)
    {D Kc : Subgroup Y} {m f : ℕ} (hDKK : D ≤ Kc ⊔ Kc.map (MulAut.conj s).toMonoidHom)
    (hKt : Kc.map (MulAut.conj s).toMonoidHom ≠ Kc)
    (hcomm : ⁅Kc, Kc.map (MulAut.conj s).toMonoidHom⁆ = ⊥) (hZ : center Kc = ⊥)
    (hφ : Nonempty (Kc ≃* D)) :
    SUmNeighbourAlternative s D (Kc.map (MulAut.conj s).toMonoidHom) m f := by
  obtain ⟨φ⟩ := hφ
  have hKK := CentralizerComponents.map_conj_map_conj hs2 Kc
  set ψ : Kc ≃* Kc.map (MulAut.conj s).toMonoidHom :=
    Kc.equivMapOfInjective (MulAut.conj s).toMonoidHom (MulAut.conj s).injective
  refine ⟨by rw [hKK, sup_comm]; exact hDKK, Or.inr ⟨by rw [hKK]; exact fun h => hKt h.symm, ?_,
    ?_, ⟨ψ.symm.trans φ⟩⟩⟩
  · rw [hKK, commutator_comm]
    exact hcomm
  · rw [← map_center_eq ψ, hZ, Subgroup.map_bot]

theorem neighbour_overgroup_sum_of_pPrimeCore_eq_bot {m f : ℕ} (hm : 4 ≤ m)
    (hmf : (m, f) ≠ (4, 1)) (hcat : SUmCatalogueClausesAt m) {Y : Type} [Group Y] [Finite Y]
    (hO : pPrimeCore 2 Y = ⊥)
    (hsec : ∀ Kc : Subgroup Y, IsComponent Kc → Catalog (Kc ⧸ center Kc))
    {s : Y} (hs : orderOf s = 2) {D : Subgroup Y}
    (hD : CFSG.Open.IsComponentOf D (centralizer ({s} : Set Y)))
    (hsyl : ∀ U : Subgroup Y, IsPGroup 2 U → U ≤ centralizer (D : Set Y) → Nat.card U ≤ 2)
    (hstd : CFSG.Open.standardComponentIsStandard D) (hnn : ¬ D.Normal)
    (hDm : LieModel (D ⧸ center D) .PSU m 2 f) (hZD : Odd (Nat.card (center D))) :
    NeighbourOvergroupSUm s D m f ∧
      ∀ Lc : Subgroup Y, IsComponent Lc → ⁅D, Lc⁆ ≠ ⊥ → SUmNeighbourAlternative s D Lc m f := by
  have hs2 : s ^ 2 = 1 := hs ▸ pow_orderOf_eq_one s
  have hDs : D ≤ centralizer ({s} : Set Y) := hD.1
  have hDc : IsComponent (D.subgroupOf (centralizer ({s} : Set Y))) :=
    (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hDs).1
      ((ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open _ _).2 hD)
  obtain ⟨-, Kc, hKc, -, hDKK, -, hiff, hfix, hswap⟩ :=
    exists_isComponent_orbit_of_isComponent_centralizer hO hs2 hDs hDc
  have hK : SUmNeighbourAlternative s D Kc m f := by
    refine ⟨hDKK, ?_⟩
    by_cases hKt : Kc.map (MulAut.conj s).toMonoidHom = Kc
    · left
      obtain ⟨hDK, hDcomp⟩ := hfix hKt
      have hDne : D ≠ Kc := by
        rintro rfl
        exact hnn (F4Pilot.normal_of_isComponent_of_standard hKc hstd)
      have hsN : s ∈ normalizer (Kc : Set Y) := mem_normalizer_iff_map_conj_eq.2 hKt
      have hKs : ¬ Kc ≤ centralizer ({s} : Set Y) := by
        intro hKs
        rw [inf_eq_left.mpr hKs] at hDcomp
        exact hDne (F4Pilot.eq_of_isComponent_subgroupOf hKc.1 hDK hDcomp)
      have hτ2 := F4Pilot.orderOf_normalizerMonoidHom_eq_two Kc hsN hs2 hKs
      obtain ⟨hD'c, hD'm, hD'map, hD'Z⟩ :=
        isComponent_fixedSubgroup_of_le_of_lieModel_quotient hsN hDK hDs hDcomp hDm
      have hcatK := hsec Kc hKc
      have hsK : s ∉ Kc := fun hsK =>
        sum_not_inner_of_clauses hcat hKc.1 hcatK _ hτ2 hm hmf _ hD'c hD'm (hD'Z ▸ hZD)
          (E6Pilot.fixedCentralizerTwoSmall_of_card_le_two _ hDK hsyl _ hD'map)
          (F4Pilot.normalizerMonoidHom_mem_range_conj Kc hsN hsK)
      exact ⟨hKt, lt_of_le_of_ne hDK hDne, hsK, hsN, sum_overgroup_catalogue hcat
        hKc.1 hcatK _ hτ2 hm _ hD'c hD'm
        (F4Pilot.fixedCentralizerTwoFree_of_card_le_two hsN hs hsK hDs hDK hsyl _ hD'map)⟩
    · right
      obtain ⟨hcomm, -, hdiag, -⟩ := hswap hKt
      exact ⟨hKt, hcomm,
        LinearPilot.center_eq_bot_and_nonempty_mulEquiv_of_swap hO hs hKc hKt hcomm hdiag hDs
          hsyl⟩
  refine ⟨⟨Kc, hKc, hK⟩, fun Lc hLc hDLc => ?_⟩
  rcases (hiff Lc hLc).1 hDLc with rfl | rfl
  · exact hK
  · by_cases hKt : Kc.map (MulAut.conj s).toMonoidHom = Kc
    · rw [hKt]
      exact hK
    · obtain ⟨-, ⟨hKt', -⟩ | ⟨-, hcomm, hZ, hφ⟩⟩ := hK
      · exact absurd hKt' hKt
      · exact SUmNeighbourAlternative.map_conj_of_swap hs2 hDKK hKt hcomm hZ hφ

theorem SUmNeighbourAlternative.exact {Y : Type} [Group Y] [Finite Y] (hO : pPrimeCore 2 Y = ⊥)
    {s : Y} {D Kc : Subgroup Y} (hKc : IsComponent Kc) {m f : ℕ} (hmf : (m, f) ≠ (4, 1))
    (h : SUmNeighbourAlternative s D Kc m f) :
    D ≤ Kc ⊔ Kc.map (MulAut.conj s).toMonoidHom ∧
      ((Kc.map (MulAut.conj s).toMonoidHom = Kc ∧ D < Kc ∧ s ∉ Kc ∧
          (∃ hsN : s ∈ normalizer (Kc : Set Y),
            Kc.normalizerMonoidHom ⟨s, hsN⟩ ∉ (MulAut.conj : Kc →* MulAut Kc).range) ∧
          center Kc = ⊥ ∧ LieModel Kc .PSL m 2 (2 * f)) ∨
        (Kc.map (MulAut.conj s).toMonoidHom ≠ Kc ∧
          ⁅Kc, Kc.map (MulAut.conj s).toMonoidHom⁆ = ⊥ ∧ center Kc = ⊥ ∧
            Nonempty (Kc ≃* D))) := by
  obtain ⟨hDKK, ⟨hKt, hDK, hsK, hsN, hout, hZodd, hlist⟩ | hswap⟩ := h
  · have hZ := E6Pilot.center_eq_bot_of_isComponent_of_odd hO hKc hZodd
    have hmodel : LieModel (Kc ⧸ center Kc) .PSL m 2 (2 * f) :=
      hlist.resolve_right (not_sumSmall_of_ne hmf)
    exact ⟨hDKK, .inl ⟨hKt, hDK, hsK, ⟨hsN, hout⟩, hZ, LieType.CurtisTits.lieModel_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) hmodel⟩⟩
  · exact ⟨hDKK, .inr hswap⟩

theorem neighbour_overgroup_sum {m f : ℕ} (hm : 4 ≤ m) (hmf : (m, f) ≠ (4, 1))
    (hcat : SUmCatalogueClausesAt m) {G : Type} [Group G] [Finite G]
    (hKP : CFSG.Assembly.KProper Catalog G) {X : Subgroup G}
    (hXG : centralizer (X : Set G) ≠ ⊤) {t : G} (htX : t ∈ centralizer (X : Set G))
    (ht : orderOf t = 2) {D : Subgroup G} (hDX : D ≤ centralizer (X : Set G))
    (hDq : CFSG.IsQuasisimple D) (hDm : LieModel (D ⧸ center D) .PSU m 2 f)
    (hZD : Odd (Nat.card (center D)))
    (hcomp : CFSG.Open.IsComponentOf
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
        (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))))
    (hsyl : ∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
      IsPGroup 2 U →
      U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
        Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
      Nat.card U ≤ 2)
    (hstd : CFSG.Open.standardComponentIsStandard ((D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))))
    (hnn : ¬ ((D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal) :
    NeighbourOvergroupSUm (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) m f ∧
      ∀ Lc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        IsComponent Lc →
        ⁅(D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))), Lc⁆ ≠ ⊥ →
        SUmNeighbourAlternative (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
          ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) Lc m f := by
  have hsec : ∀ Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
      IsComponent Kc → Catalog (Kc ⧸ center Kc) :=
    fun Kc hKc => F4Pilot.catalog_center_quotient_of_kProper hKP hXG hKc.1
  have ht' : orderOf (⟨t, htX⟩ : centralizer (X : Set G)) = 2 := by
    rw [orderOf_mk]
    exact ht
  have hne := ne_bot_of_isQuasisimple hcomp.2.2
  exact neighbour_overgroup_sum_of_pPrimeCore_eq_bot hm hmf hcat
    (F4Pilot.pPrimeCore_two_quotient_oddCore_eq_bot _) hsec (orderOf_mk_oddCore ht') hcomp hsyl
    hstd hnn (lieModel_quotient_center_map_oddCore_of_isQuasisimple hDX hDq hDm hne)
    (odd_card_center_map_subgroupOf_oddCore hDX hDq hZD hne)

section Seitz

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
private theorem centralizer_ne_top_of_ne_bot'' (hG : IsSimpleGroup G)
    (hnonab : ∃ a b : G, a * b ≠ b * a) {X : Subgroup G} (hX : X ≠ ⊥) :
    centralizer (X : Set G) ≠ ⊤ := by
  intro htop
  obtain ⟨a, b, hab⟩ := hnonab
  apply hX
  rcases hG.eq_bot_or_eq_top_of_normal (center G) with hZ | hZ
  · rw [eq_bot_iff, ← hZ]
    intro x hx
    rw [mem_center_iff]
    intro g
    exact (mem_centralizer_iff.mp (htop ▸ mem_top g) x hx).symm
  · exact absurd (mem_center_iff.mp (hZ ▸ mem_top b) a) hab

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {n : ℕ}

omit [Finite G] in
theorem lieModel_quotient_center_map_blockSU_compl_pair (e : L ≃* unitaryPSU h n) (hn : 6 ≤ n)
    {a b : Fin n} (hab : a ≠ b) :
    LieModel ((((blockSU h ({a, b}ᶜ : Finset (Fin n))).map e.symm.toMonoidHom).map L.subtype :
      Subgroup G) ⧸ center (((blockSU h ({a, b}ᶜ : Finset (Fin n))).map e.symm.toMonoidHom).map
        L.subtype : Subgroup G)) .PSU (n - 2) 2 f := by
  have hcard : (({a, b} : Finset (Fin n))ᶜ).card = n - 2 := card_compl_pair hab
  set ψ := LinearPilot.mapSymmMulEquiv e (blockSU h ({a, b}ᶜ : Finset (Fin n)))
  have h1 := lieModel_PSU_of_mulEquiv_unitaryPSU h (m := (({a, b} : Finset (Fin n))ᶜ).card)
    (by omega) (fun h3 => by have := congrArg Prod.fst h3; simp only at this; omega)
    ((QuotientGroup.congr _ _ ψ (map_center_eq ψ)).trans
      (blockSUQuotientCenterEquiv h (by omega)))
  rwa [hcard] at h1

theorem neighbour_overgroup_unitaryRootTorus (hset : SeitzSetting G L)
    (hcat : SUmCatalogueClausesAt (n - 2)) (e : L ≃* unitaryPSU h n) (hn : 6 ≤ n)
    (hnf : (n, f) ≠ (6, 1)) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {a b : Fin n} (hab : a ≠ b) {X : Subgroup G}
    (hX : X = ((unitaryRootTorus h hab).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((blockSU h ({a, b}ᶜ : Finset (Fin n))).map e.symm.toMonoidHom).map L.subtype) :
    NeighbourOvergroupSUm (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) (n - 2) f ∧
      ∀ Lc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        IsComponent Lc →
        ⁅(D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))), Lc⁆ ≠ ⊥ →
        SUmNeighbourAlternative (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
          ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) Lc (n - 2) f := by
  have hcard : (({a, b} : Finset (Fin n))ᶜ).card = n - 2 := card_compl_pair hab
  obtain ⟨hcomp, hsyl, hstd⟩ :=
    neighbour_standard_unitaryRootTorus_of_seitzSetting h hset e hn htC ht hab hX htX hDe
  have hnn := not_normal_neighbour_unitaryRootTorus h hset e hn htC ht hab hX hDe
  obtain ⟨-, -, -, -, -, -, hDC, -, -, hZ, -⟩ :=
    neighbour_data_unitaryRootTorus h e hn hab htC hX hDe
  have hDq : CFSG.IsQuasisimple D := hDe ▸ isQuasisimple_map_blockSU h e (by omega) (by omega)
  have hDm : LieModel (D ⧸ center D) .PSU (n - 2) 2 f :=
    hDe ▸ lieModel_quotient_center_map_blockSU_compl_pair h e hn hab
  have hXne : X ≠ ⊥ := by
    rw [hX, Ne, map_eq_bot_iff_of_injective _ L.subtype_injective,
      map_eq_bot_iff_of_injective _ e.symm.injective]
    exact unitaryRootTorus_ne_bot h (by omega) hab
  have hmf : (n - 2, f) ≠ (4, 1) := by
    intro h'
    apply hnf
    rw [Prod.mk.injEq] at h' ⊢
    omega
  exact neighbour_overgroup_sum (by omega) hmf hcat hset.standardSetting.kProper
    (centralizer_ne_top_of_ne_bot'' hset.standardSetting.simple hset.standardSetting.nonab hXne)
    htX ht (hDC.trans inf_le_left) hDq hDm hZ hcomp hsyl hstd hnn

end Seitz

end CFSG.SeitzReduction.UnitaryPilot
