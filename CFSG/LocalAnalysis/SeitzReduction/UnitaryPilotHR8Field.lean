module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotHR8
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatEvenOuterPSL
import CFSG.LocalAnalysis.SeitzReduction.CentralizerComponents

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem forall_isPComponent_lieModel_PSU_of_not_inner {m : ℕ} (hm : 4 ≤ m)
    (hdet : SUmEvenTypeDetAt m) {S : Type} [Group S] [Finite S] {f : ℕ}
    (hS : LieModel S .PSL m 2 (2 * f)) {σ : MulAut S} (hσ : orderOf σ = 2)
    (hout : σ ∉ (MulAut.conj : S →* MulAut S).range) {D : Subgroup (fixedSubgroup σ)}
    (hD : IsComponent D) (hDm : LieModel (D ⧸ center D) .PSU m 2 f) :
    ∀ P : Subgroup (fixedSubgroup σ), IsPComponent 2 P → LieModel P .PSU m 2 f := by
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL m 2 (2 * f) :=
    (ComponentClassification.CatLeaf.statedClassicalModel_of_lieModel_psl hS).1
  have hDp : IsPComponent 2 D := isPComponent_two_of_isComponent hD
  rcases psl_outer_fixed_even hadm hS σ hσ hout with h | ⟨-, h⟩ | ⟨k, _, _, r, hk, hr, ⟨Φ⟩⟩ | h
  · obtain ⟨hadm', hmD, -⟩ := h D hDp
    obtain ⟨htt, -, -⟩ := sumTypeDet_of_simple hdet hD.1
      (LinearPilot.isSimpleGroup_of_lieModel_PSL hmD) hDm hadm' hmD
    exact absurd htt (by decide)
  · intro P hP
    obtain ⟨-, hmP⟩ := h P hP
    rwa [Nat.mul_div_cancel_left f (by norm_num : 0 < 2)] at hmP
  · exact (no_sum_component_statedSp hdet hm hk hr Φ hD hDm).elim
  · exact (h D hDp).elim

@[expose] def SUmNeighbourAlternativeField {Y : Type} [Group Y] (s : Y) (D Kc : Subgroup Y)
    (m f : ℕ) : Prop :=
  D ≤ Kc ⊔ Kc.map (MulAut.conj s).toMonoidHom ∧
    ((Kc.map (MulAut.conj s).toMonoidHom = Kc ∧ D < Kc ∧ s ∉ Kc ∧
        ∃ hsN : s ∈ normalizer (Kc : Set Y),
          Kc.normalizerMonoidHom ⟨s, hsN⟩ ∉ (MulAut.conj : Kc →* MulAut Kc).range ∧
          center Kc = ⊥ ∧ LieModel Kc .PSL m 2 (2 * f) ∧
          ∀ P : Subgroup (fixedSubgroup (Kc.normalizerMonoidHom ⟨s, hsN⟩)), IsPComponent 2 P →
            LieModel P .PSU m 2 f) ∨
      (Kc.map (MulAut.conj s).toMonoidHom ≠ Kc ∧
        ⁅Kc, Kc.map (MulAut.conj s).toMonoidHom⁆ = ⊥ ∧ center Kc = ⊥ ∧ Nonempty (Kc ≃* D)))

theorem SUmNeighbourAlternative.field {Y : Type} [Group Y] [Finite Y] (hO : pPrimeCore 2 Y = ⊥)
    {s : Y} (hs : orderOf s = 2) {D : Subgroup Y}
    (hD : CFSG.Open.IsComponentOf D (centralizer ({s} : Set Y))) {m f : ℕ} (hm : 4 ≤ m)
    (hmf : (m, f) ≠ (4, 1)) (hdet : SUmEvenTypeDetAt m)
    (hDm : LieModel (D ⧸ center D) .PSU m 2 f) {Kc : Subgroup Y} (hKc : IsComponent Kc)
    (h : SUmNeighbourAlternative s D Kc m f) :
    SUmNeighbourAlternativeField s D Kc m f ∧ center D = ⊥ := by
  obtain ⟨hDKK, ⟨hKt, hDK, hsK, ⟨hsN, hout⟩, hZ, hmodel⟩ | ⟨hKt, hcomm, hZ, ⟨φ⟩⟩⟩ :=
    h.exact hO hKc hmf
  · have hs2 : s ^ 2 = 1 := hs ▸ pow_orderOf_eq_one s
    have hDs : D ≤ centralizer ({s} : Set Y) := hD.1
    have hDc : IsComponent (D.subgroupOf (centralizer ({s} : Set Y))) :=
      (isComponentOf_iff_isComponent_subgroupOf hDs).1
        ((ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open _ _).2 hD)
    have hDcomp := CentralizerComponents.isComponent_subgroupOf_inf_centralizer hDs hDc hDK.le
    obtain ⟨hD'c, hD'm, -, -⟩ :=
      isComponent_fixedSubgroup_of_le_of_lieModel_quotient hsN hDK.le hDs hDcomp hDm
    have hτ2 : orderOf (Kc.normalizerMonoidHom ⟨s, hsN⟩) = 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      refine orderOf_eq_prime (F4Pilot.normalizerMonoidHom_sq_eq_one Kc hsN hs2) fun h1 => ?_
      apply hout
      rw [h1]
      exact one_mem _
    have hall := forall_isPComponent_lieModel_PSU_of_not_inner hm hdet hmodel hτ2 hout hD'c hD'm
    have hD'Z : center ((D.subgroupOf Kc).subgroupOf
        (fixedSubgroup (Kc.normalizerMonoidHom ⟨s, hsN⟩))) = ⊥ :=
      F4Pilot.center_eq_bot_of_isQuasisimple hD'c.1
        (LinearPilot.isSimpleGroup_of_lieModel_PSU
          (hall _ (isPComponent_two_of_isComponent hD'c)))
    have hDfix : D.subgroupOf Kc ≤ fixedSubgroup (Kc.normalizerMonoidHom ⟨s, hsN⟩) := by
      rw [F4Pilot.fixedSubgroup_normalizerMonoidHom]
      intro x hx
      exact mem_subgroupOf.mpr (hDs (mem_subgroupOf.mp hx))
    refine ⟨⟨hDKK, .inl ⟨hKt, hDK, hsK, hsN, hout, hZ, hmodel, hall⟩⟩, ?_⟩
    rw [← map_center_eq (F4Pilot.subgroupOfSubgroupOfEquiv hDK.le hDfix), hD'Z,
      Subgroup.map_bot]
  · refine ⟨⟨hDKK, .inr ⟨hKt, hcomm, hZ, ⟨φ⟩⟩⟩, ?_⟩
    rw [← map_center_eq φ, hZ, Subgroup.map_bot]

section Seitz


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {K : Type} [Field K]
  (h : UnitaryFieldData 2 f K) {n : ℕ}

theorem forall_neighbour_unitaryRootTorus_field (hset : SeitzSetting G L)
    (hcat : SUmCatalogueClausesAt (n - 2)) (e : L ≃* unitaryPSU h n) (hn : 6 ≤ n)
    (hnf : (n, f) ≠ (6, 1)) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {a b : Fin n} (hab : a ≠ b) {X : Subgroup G}
    (hX : X = ((unitaryRootTorus h hab).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((blockSU h ({a, b}ᶜ : Finset (Fin n))).map e.symm.toMonoidHom).map L.subtype) :
    (∃ Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        IsComponent Kc ∧
        SUmNeighbourAlternativeField
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
          ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) Kc (n - 2) f) ∧
      (∀ Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        IsComponent Kc →
        ⁅(D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))), Kc⁆ ≠ ⊥ →
        SUmNeighbourAlternativeField
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
          ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) Kc (n - 2) f) ∧
      center ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) = ⊥ := by
  have hcard : (({a, b} : Finset (Fin n))ᶜ).card = n - 2 := card_compl_pair hab
  have hmf : (n - 2, f) ≠ (4, 1) := by
    intro h'
    apply hnf
    rw [Prod.mk.injEq] at h' ⊢
    omega
  obtain ⟨⟨Kc, hKc, hK⟩, hall⟩ :=
    neighbour_overgroup_unitaryRootTorus h hset hcat e hn hnf htC ht hab hX htX hDe
  obtain ⟨hcomp, -, -⟩ :=
    neighbour_standard_unitaryRootTorus_of_seitzSetting h hset e hn htC ht hab hX htX hDe
  obtain ⟨-, -, -, -, -, -, hDC, -, -, -, -⟩ :=
    neighbour_data_unitaryRootTorus h e hn hab htC hX hDe
  have hDq : CFSG.IsQuasisimple D := hDe ▸ isQuasisimple_map_blockSU h e (by omega) (by omega)
  have hDm : LieModel (D ⧸ center D) .PSU (n - 2) 2 f :=
    hDe ▸ lieModel_quotient_center_map_blockSU_compl_pair h e hn hab
  have hDm' := lieModel_quotient_center_map_oddCore_of_isQuasisimple (hDC.trans inf_le_left) hDq
    hDm (ne_bot_of_isQuasisimple hcomp.2.2)
  have ht' : orderOf (⟨t, htX⟩ : centralizer (X : Set G)) = 2 := by
    rw [orderOf_mk]
    exact ht
  have hO := F4Pilot.pPrimeCore_two_quotient_oddCore_eq_bot (centralizer (X : Set G))
  have hdet : SUmEvenTypeDetAt (n - 2) := sumEvenTypeDetAt (by omega)
  refine ⟨⟨Kc, hKc, (hK.field hO (orderOf_mk_oddCore ht') hcomp (by omega) hmf hdet hDm'
      hKc).1⟩, fun Lc hLc hDL => (( hall Lc hLc hDL).field hO (orderOf_mk_oddCore ht') hcomp
      (by omega) hmf hdet hDm' hLc).1,
    (hK.field hO (orderOf_mk_oddCore ht') hcomp (by omega) hmf hdet hDm' hKc).2⟩

end Seitz

end CFSG.SeitzReduction.UnitaryPilot
