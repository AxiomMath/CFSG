module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseComponentData
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreASevenNormalizerLayerEquality
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ComponentLayerCentralizesSolvableNormalized
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.GorensteinWalter

universe u

private abbrev A7 := alternatingGroup (Fin 7)

/-- In the `A₇` component branch, the ambient D-group quotient is also the
`A₇` quotient.  The two-group and rank-one alternatives force the perfect
component image into a solvable or rank-one subgroup, contradicting its
`A₇` central quotient. -/
public theorem secondCase_a7_ambient_quotient_model
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (_hmodel : d.model = ComponentQuotientModel.alternating hA7) :
    Nonempty ((w.M ⧸ pPrimeCore 2 w.M) ≃*
      alternatingGroup (Fin 7)) := by
  classical
  let M : Subgroup G := w.M
  let E : Subgroup G := d.E
  let : (pPrimeCore 2 M).Normal := inferInstance
  have hOodd : Odd (Nat.card (pPrimeCore 2 M)) := by
    exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := M))
  have hEne : E ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot E).mp d.E_component.2.2.1
  have hEperf : Group.IsPerfect (E.subgroupOf M) := by
    let : Group.IsPerfect E :=
      (Group.isPerfect_def).2 d.E_component.2.2.2.1
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe d.E_component.1).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe d.E_component.1).symm.surjective
  have hEi_ne : E.subgroupOf M ≠ ⊥ := by
    intro hbot
    apply hEne
    have hm : (E.subgroupOf M).map M.subtype = E :=
      Subgroup.map_subgroupOf_eq_of_le d.E_component.1
    rw [hbot, Subgroup.map_bot] at hm
    exact hm.symm
  have hEsn : (E.subgroupOf M).IsSubnormal := d.E_component.2.1
  have hEO : E ≤
      Subgroup.centralizer ((pPrimeCore 2 M).map M.subtype : Set G) := by
    have hnorm : IsNormalIn ((pPrimeCore 2 M).map M.subtype) M := by
      refine ⟨Subgroup.map_subtype_le (pPrimeCore 2 M), ?_⟩
      intro m hm o ho
      rcases Subgroup.mem_map.mp ho with ⟨o0, ho0, rfl⟩
      exact Subgroup.mem_map.mpr ⟨(⟨m, hm⟩ : M) * o0 * (⟨m, hm⟩ : M)⁻¹,
        (pPrimeCore_normal (p := 2) (G := M)).conj_mem o0 ho0 ⟨m, hm⟩, rfl⟩
    have hsolv : Group.IsSolvable ((pPrimeCore 2 M).map M.subtype) := by
      have hcard : Nat.card ((pPrimeCore 2 M).map M.subtype) =
          Nat.card (pPrimeCore 2 M) :=
        Subgroup.card_map_of_injective M.subtype_injective
      have hoddmap : Odd (Nat.card ((pPrimeCore 2 M).map M.subtype)) :=
        hcard ▸ hOodd
      exact odd_order_theorem ((pPrimeCore 2 M).map M.subtype) hoddmap
    have hnormLayer : componentLayerOf M ≤
        Subgroup.normalizer ((pPrimeCore 2 M).map M.subtype : Set G) :=
      (componentLayerOf_isNormalIn M).1.trans (le_normalizer_of_isNormalIn hnorm)
    have hcommLayer := componentLayerOf_centralizes_solvable_of_le_normalizer
      M ((pPrimeCore 2 M).map M.subtype)
        (Subgroup.map_subtype_le (pPrimeCore 2 M)) hsolv hnormLayer
    have hcentLayer : componentLayerOf M ≤
        Subgroup.centralizer ((pPrimeCore 2 M).map M.subtype : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer
        (H₁ := componentLayerOf M)
        (H₂ := (pPrimeCore 2 M).map M.subtype)).mp hcommLayer
    have hEleLayer : E ≤ componentLayerOf M :=
      le_sSup (s := {E : Subgroup G | IsComponentOf E M}) d.E_component
    exact hEleLayer.trans hcentLayer
  let q : M →* M ⧸ pPrimeCore 2 M :=
    QuotientGroup.mk' (pPrimeCore 2 M)
  let Ebar : Subgroup (M ⧸ pPrimeCore 2 M) :=
    (E.subgroupOf M).map q
  let eEi : E.subgroupOf M ≃* E := Subgroup.subgroupOfEquivOfLe d.E_component.1
  have hA7Ei : Nonempty ((E.subgroupOf M) ⧸
      Subgroup.center (E.subgroupOf M) ≃* A7) := by
    exact ⟨(QuotientGroup.congr (Subgroup.center (E.subgroupOf M))
      (Subgroup.center E) eEi
      (map_center_eq_center_of_mulEquiv eEi)).trans hA7.some⟩
  have hEOi : E.subgroupOf M ≤
      Subgroup.centralizer (pPrimeCore 2 M : Set M) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro o ho
    have hxEi := Subgroup.mem_subgroupOf.mp hx
    have hxG : (x : G) ∈ E := hxEi
    have hoG : (o : G) ∈ (pPrimeCore 2 M).map M.subtype :=
      Subgroup.mem_map.mpr ⟨o, ho, rfl⟩
    have hcommG : (o : G) * (x : G) = (x : G) * (o : G) :=
      (Subgroup.mem_centralizer_iff.mp (hEO hxG)) (o : G) hoG
    exact Subtype.ext hcommG
  have hEbarA7 : Nonempty (Ebar ⧸ Subgroup.center Ebar ≃* A7) := by
    simpa [Ebar, q] using
      (a7_central_quotient_of_image_of_central_kernel
        (E.subgroupOf M)
        (isQuasisimple_mulEquiv_local
          (Subgroup.subgroupOfEquivOfLe d.E_component.1).symm
          d.E_component.2.2)
        (pPrimeCore 2 M)
        (odd_order_theorem (pPrimeCore 2 M) hOodd) hEOi hA7Ei)
  have hEbarData : Ebar ≠ ⊥ ∧ Group.IsPerfect Ebar ∧ Ebar.IsSubnormal := by
    have h := perfect_subnormal_image_le_normal_odd_index
      (E.subgroupOf M) hEperf hEi_ne hEsn (pPrimeCore 2 M)
        (odd_order_theorem (pPrimeCore 2 M) hOodd)
      (⊤ : Subgroup (M ⧸ pPrimeCore 2 M)) (by infer_instance) (by simp)
    exact ⟨h.1, h.2.1, h.2.2.1⟩
  have hD : IsDGroup M := properSubgroups_areDGroups hmin M w.M_maximal.ne_top
  rcases hD with ⟨_hSylow, h2⟩ | ⟨_hSylow, hA7M⟩ |
      ⟨_hSylow, K, hKprime, L, hLnormal, hLindex, hLmodel⟩
  · let : Group.IsPerfect Ebar := hEbarData.2.1
    let : Nontrivial Ebar :=
      (Subgroup.nontrivial_iff_ne_bot Ebar).mpr hEbarData.1
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let : Group.IsNilpotent (M ⧸ pPrimeCore 2 M) := IsPGroup.isNilpotent h2
    have hEbarsolv : Group.IsSolvable Ebar := inferInstance
    exact False.elim (Group.IsPerfect.not_isSolvable Ebar hEbarsolv)
  · exact hA7M
  · have hEbar_le_L : Ebar ≤ L := by
      have h := perfect_subnormal_image_le_normal_odd_index
        (E.subgroupOf M) hEperf hEi_ne hEsn (pPrimeCore 2 M)
          (odd_order_theorem (pPrimeCore 2 M) hOodd)
        L hLnormal hLindex
      exact h.2.2.2
    rcases hLmodel with hPSL | hPGL
    · rcases hPSL with ⟨eL⟩
      let EL : Subgroup L := Ebar.subgroupOf L
      let J : Subgroup (PSL2 K) := EL.map eL.toMonoidHom
      have hEL_A7 : Nonempty (EL ⧸ Subgroup.center EL ≃* A7) := by
        let eEL : EL ≃* Ebar := Subgroup.subgroupOfEquivOfLe hEbar_le_L
        exact central_quotient_of_mulEquiv eEL.symm hEbarA7
      have hJ_A7 : Nonempty (J ⧸ Subgroup.center J ≃* A7) := by
        let eMap : EL ≃* J :=
          Subgroup.equivMapOfInjective EL eL.toMonoidHom eL.injective
        exact central_quotient_of_mulEquiv eMap hEL_A7
      exact False.elim (no_a7_quotient_subgroup_of_psl2_odd hKprime J hJ_A7)
    · rcases hPGL with ⟨eL⟩
      let EL : Subgroup L := Ebar.subgroupOf L
      let J : Subgroup (PGL2 K) := EL.map eL.toMonoidHom
      have hEL_A7 : Nonempty (EL ⧸ Subgroup.center EL ≃* A7) := by
        let eEL : EL ≃* Ebar := Subgroup.subgroupOfEquivOfLe hEbar_le_L
        exact central_quotient_of_mulEquiv eEL.symm hEbarA7
      have hJ_A7 : Nonempty (J ⧸ Subgroup.center J ≃* A7) := by
        let eMap : EL ≃* J :=
          Subgroup.equivMapOfInjective EL eL.toMonoidHom eL.injective
        exact central_quotient_of_mulEquiv eMap hEL_A7
      have hELne : EL ≠ ⊥ := by
        intro hbot
        apply hEbarData.1
        have hmap : EL.map L.subtype = Ebar :=
          Subgroup.map_subgroupOf_eq_of_le hEbar_le_L
        rw [hbot, Subgroup.map_bot] at hmap
        exact hmap.symm
      have hJne : J ≠ ⊥ := by
        intro hbot
        apply hELne
        exact (Subgroup.map_eq_bot_iff_of_injective
          (H := EL) (f := eL.toMonoidHom) eL.injective).mp hbot
      have hELperf : Group.IsPerfect EL := by
        let : Group.IsPerfect Ebar := hEbarData.2.1
        let eEL : EL ≃* Ebar := Subgroup.subgroupOfEquivOfLe hEbar_le_L
        exact Group.IsPerfect.ofSurjective
          (f := eEL.symm.toMonoidHom) eEL.symm.surjective
      have hJperf : Group.IsPerfect J :=
        perfect_map_subgroup EL eL.toMonoidHom hELperf
      have hJsn : J.IsSubnormal := hEbarData.2.2.subgroupOf.map eL.surjective
      let : Finite (PGL2 K) :=
        Finite.of_surjective Matrix.ProjGenLinGroup.mk
          Matrix.ProjGenLinGroup.mk_surjective
      have hPGLcore := pgl2_perfect_subnormal_eq_commutator
        K hKprime J hJne hJperf hJsn
      have hcardgt : 3 < Nat.card K := hPGLcore.1
      let eD : commutator (PGL2 K) ≃* PSL2 K :=
        (commutator_mulEquiv_psl2_of_mulEquiv_pgl2_card_gt_three
          K hKprime hcardgt (MulEquiv.refl (PGL2 K))).some
      let eJ : J ≃* PSL2 K :=
        (MulEquiv.subgroupCongr hPGLcore.2).trans eD
      have hPSLA7 : Nonempty ((PSL2 K) ⧸ Subgroup.center (PSL2 K) ≃* A7) :=
        central_quotient_of_mulEquiv eJ hJ_A7
      have hcenter : Subgroup.center (PSL2 K) = ⊥ := psl2_center_eq_bot K
      let eBot : (PSL2 K) ⧸ Subgroup.center (PSL2 K) ≃* PSL2 K :=
        (QuotientGroup.quotientMulEquivOfEq (G := PSL2 K)
          (M := Subgroup.center (PSL2 K)) (N := ⊥) hcenter).trans
          (QuotientGroup.quotientBot (G := PSL2 K))
      exact False.elim (psl2_ne_a7 hKprime
        ⟨eBot.symm.trans hPSLA7.some⟩)

end CFSG.GorensteinWalter
