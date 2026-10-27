module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreBInterM
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The maximal-overgroup factorization `M = (B ∩ M) E(M)`

After the A₇ layer model is reached, the source derives
`B ∩ M = O(M)` and `M = (B ∩ M) E(M)` (p. 223).  The first equality is
landed as `firstCase_cyclic_B_inter_M_eq_oddCore_of_a7_layer`.  Here we
show that the component layer covers `M / O(M)`: its image is a
nontrivial normal subgroup of the simple quotient `A₇`, hence is the
whole quotient.  The correspondence theorem then gives
`M = O(M) E(M)`, and the odd-core equality turns `O(M)` back into
`B ∩ M`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- In the A₇ layer model, the component layer maps onto the whole
quotient `M / O₂'(M)`. -/
private theorem firstCase_cyclic_componentLayer_image_top_of_layer_a7
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (M : Subgroup G) (hMmax : IsCoatom M)
    (hSM : (c.S : Subgroup G) ≤ M)
    (fd : FirstCaseFourData c od.d)
    (hV2 : fd.V2 ≤ componentLayerOf M)
    (hA7 : Nonempty ((componentLayerOf M) ⧸
      pPrimeCore 2 (componentLayerOf M) ≃* alternatingGroup (Fin 7))) :
    ((componentLayerOf M).subgroupOf M).map
      (QuotientGroup.mk' (pPrimeCore 2 M)) = ⊤ := by
  classical
  let O0 : Subgroup M := pPrimeCore 2 M
  let E : Subgroup G := componentLayerOf M
  let E0 : Subgroup M := E.subgroupOf M
  let q : M →* M ⧸ O0 := QuotientGroup.mk' O0
  let Ebar : Subgroup (M ⧸ O0) := E0.map q
  let : O0.Normal := pPrimeCore_normal
  have hE_le_M : E ≤ M := (componentLayerOf_isNormalIn M).1
  have hE0_normal : E0.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (H := M) (N := E)
      (le_normalizer_of_isNormalIn (componentLayerOf_isNormalIn M))
  have : E0.Normal := hE0_normal
  have hEbar_normal : Ebar.Normal := QuotientGroup.map_normal (G := M) O0 E0
  have hEbar_ne : Ebar ≠ ⊥ := by
    intro hbot
    have hE0_le_ker : E0 ≤ q.ker := (Subgroup.map_eq_bot_iff E0).mp hbot
    have htM : c.t ∈ M := hSM (fd.V2_le_S fd.t_mem_V2)
    let tM : M := ⟨c.t, htM⟩
    have htE0 : tM ∈ E0 := Subgroup.mem_subgroupOf.mpr (hV2 fd.t_mem_V2)
    have htO0 : tM ∈ O0 := by
      have htker : tM ∈ q.ker := hE0_le_ker htE0
      simpa [q, QuotientGroup.ker_mk'] using htker
    have hdvd2 : 2 ∣ Nat.card O0 := by
      have hdvd : orderOf tM ∣ Nat.card O0 :=
        Subgroup.orderOf_dvd_natCard O0 htO0
      have hord2 : orderOf tM = 2 := by
        apply orderOf_eq_prime
        · apply Subtype.ext
          exact c.t_involution.2
        · intro h1
          exact c.t_involution.1 (congrArg Subtype.val h1)
      rwa [hord2] at hdvd
    have hodd : Odd (Nat.card O0) :=
      Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥M))
    exact hodd.not_two_dvd_nat hdvd2
  obtain ⟨eM⟩ := firstCase_cyclic_m_quotient_a7_of_layer_a7
    hmin M hMmax hA7
  let EA : Subgroup (alternatingGroup (Fin 7)) := Ebar.map eM.toMonoidHom
  have hEA_normal : EA.Normal :=
    hEbar_normal.map eM.toMonoidHom eM.surjective
  have hEA_ne : EA ≠ ⊥ := by
    intro hbot
    exact hEbar_ne ((Subgroup.map_eq_bot_iff_of_injective
      (H := Ebar) (f := eM.toMonoidHom) eM.injective).mp hbot)
  let : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by norm_num : 5 ≤ Nat.card (Fin 7))
  have hEA_top : EA = ⊤ :=
    (@IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ _ EA hEA_normal).resolve_left hEA_ne
  have hEbar_top : Ebar = ⊤ := by
    apply (Subgroup.map_injective (f := eM.toMonoidHom) eM.injective)
    simpa [EA] using hEA_top
  simpa [O0, E, E0, q, Ebar] using hEbar_top

/-- In the A₇ layer model, the odd core of the maximal overgroup and the
component layer generate the whole maximal overgroup. -/
private theorem firstCase_cyclic_oddCore_sup_componentLayer_eq_top_of_layer_a7
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (M : Subgroup G) (hMmax : IsCoatom M)
    (hSM : (c.S : Subgroup G) ≤ M)
    (fd : FirstCaseFourData c od.d)
    (hV2 : fd.V2 ≤ componentLayerOf M)
    (hA7 : Nonempty ((componentLayerOf M) ⧸
      pPrimeCore 2 (componentLayerOf M) ≃* alternatingGroup (Fin 7))) :
    pPrimeCore 2 M ⊔ (componentLayerOf M).subgroupOf M = ⊤ := by
  classical
  let O0 : Subgroup M := pPrimeCore 2 M
  let E0 : Subgroup M := (componentLayerOf M).subgroupOf M
  let q : M →* M ⧸ O0 := QuotientGroup.mk' O0
  let : O0.Normal := pPrimeCore_normal
  have hEbar_top : E0.map q = ⊤ :=
    firstCase_cyclic_componentLayer_image_top_of_layer_a7
      hmin c od M hMmax hSM fd hV2 hA7
  have hcomap : (E0.map q).comap q = O0 ⊔ E0 := by
    simp [q, O0]
  rw [hEbar_top, Subgroup.comap_top] at hcomap
  exact hcomap.symm

/-- In the cyclic first-case A₇ layer model, the maximal overgroup is the
join of `B ∩ M` and its component layer. -/
public theorem firstCase_cyclic_M_eq_B_inter_sup_componentLayerOf_a7
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (M : Subgroup G) (hMmax : IsCoatom M)
    (hSM : (c.S : Subgroup G) ≤ M)
    (fd : FirstCaseFourData c od.d)
    (hV2 : fd.V2 ≤ componentLayerOf M)
    (hA7 : Nonempty ((componentLayerOf M) ⧸
      pPrimeCore 2 (componentLayerOf M) ≃* alternatingGroup (Fin 7)))
    (hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B) :
    M = (od.d.bg.B ⊓ M) ⊔ componentLayerOf M := by
  classical
  have hBMeqO : od.d.bg.B ⊓ M = (pPrimeCore 2 M).map M.subtype :=
    firstCase_cyclic_B_inter_M_eq_oddCore_of_a7_layer
      hmin c od M hMmax hSM fd hV2 hA7 hU
  have hsupM : pPrimeCore 2 M ⊔ (componentLayerOf M).subgroupOf M = ⊤ :=
    firstCase_cyclic_oddCore_sup_componentLayer_eq_top_of_layer_a7
      hmin c od M hMmax hSM fd hV2 hA7
  have htopmap : (⊤ : Subgroup M).map M.subtype = M := by
    rw [← MonoidHom.range_eq_map M.subtype, Subgroup.range_subtype]
  have hEmap : ((componentLayerOf M).subgroupOf M).map M.subtype =
      componentLayerOf M := by
    exact Subgroup.map_subgroupOf_eq_of_le (componentLayerOf_isNormalIn M).1
  have hmap_eq : (pPrimeCore 2 M).map M.subtype ⊔
      ((componentLayerOf M).subgroupOf M).map M.subtype =
        (⊤ : Subgroup M).map M.subtype := by
    rw [← Subgroup.map_sup, hsupM]
  have hOamb : (pPrimeCore 2 M).map M.subtype ⊔ componentLayerOf M = M := by
    simpa [hEmap, htopmap] using hmap_eq
  rw [hBMeqO]
  exact hOamb.symm

end CFSG.GorensteinWalter
