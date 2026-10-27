module

public import CFSG.LocalAnalysis.StandardType.FS81.E7FrameNativeRoots
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2Neighbour
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCores
public import CFSG.LieType.Universal.SpinOmega.CommutatorEquiv
public import CFSG.RankThree.Chevalley.EvenPinnedRootSL2
public import CFSG.LocalAnalysis.StandardType.FS81.LocalOrthModels
public import CFSG.LocalAnalysis.StandardType.FS81.E7FrameSeven
public import CFSG.RankThree.Literature.FSmithOrthogonal

public noncomputable section

namespace CFSG.StandardType.FrameRoute.FS81.E7Frame

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.Generic
open CFSG.SeitzReduction.EPilot CFSG.SeitzReduction.E7Pilot
open CFSG.Blueprint
open CFSG.LieType.Universal.Spin

theorem isInnerAut_inv_mul_of_omegaAutIsometric {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] (Q : QuadraticForm (ZMod 2) V)
    (hind : OmegaAutIsometric Q)
    (hidx : (⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆).relIndex
        (TauCeti.QuadraticMap.orthogonalGroup Q) = 2)
    (α₁ α₂ : MulAut ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    (hn₁ : ¬ IsInnerAut α₁) (hn₂ : ¬ IsInnerAut α₂) :
    IsInnerAut (α₁⁻¹ * α₂) := by
  let O := TauCeti.QuadraticMap.orthogonalGroup Q
  let D := ⁅O, O⁆
  obtain ⟨u₁, hu₁O, h₁⟩ := hind α₁
  obtain ⟨u₂, hu₂O, h₂⟩ := hind α₂
  have not_mem : ∀ (α : MulAut D) (u : V ≃ₗ[ZMod 2] V),
      (∀ x : D, ((α x : D) : V ≃ₗ[ZMod 2] V) = u * (x : V ≃ₗ[ZMod 2] V) * u⁻¹) →
      ¬ IsInnerAut α → u ∉ D := by
    intro α u h hn hu
    apply hn
    refine ⟨⟨u, hu⟩, ?_⟩
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    exact h x
  have hn₁D := not_mem α₁ u₁ h₁ hn₁
  have hn₂D := not_mem α₂ u₂ h₂ hn₂
  have hprod : u₁⁻¹ * u₂ ∈ D := by
    have hi : (D.subgroupOf O).index = 2 := hidx
    have h : (⟨u₁, hu₁O⟩⁻¹ * ⟨u₂, hu₂O⟩ : O) ∈ D.subgroupOf O := by
      apply (Subgroup.mul_mem_iff_of_index_two hi).2
      change u₁⁻¹ ∈ D ↔ u₂ ∈ D
      simpa only [Subgroup.inv_mem_iff] using iff_of_false hn₁D hn₂D
    exact h
  refine ⟨⟨u₁⁻¹ * u₂, hprod⟩, ?_⟩
  have hInv : ∀ x : D,
      (((α₁⁻¹) x : D) : V ≃ₗ[ZMod 2] V) =
        u₁⁻¹ * (x : V ≃ₗ[ZMod 2] V) * u₁ := by
    intro x
    apply (MulAut.conj u₁).injective
    simpa [MulAut.conj_apply, mul_assoc] using (h₁ ((α₁⁻¹) x)).symm
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  change (((α₁⁻¹) (α₂ x) : D) : V ≃ₗ[ZMod 2] V) =
    (u₁⁻¹ * u₂) * (x : V ≃ₗ[ZMod 2] V) * (u₁⁻¹ * u₂)⁻¹
  rw [hInv, h₂]
  simp [mul_assoc]

theorem exists_perpLevi_map_eq_m0 :
    ∃ φ : L7 →* ModGL .E7 (ZMod 2), Function.Injective φ ∧
      (perpLevi .E7 (ZMod 2)).map φ = M0 := by
  obtain ⟨w, hw, hwθ⟩ := e7NatWeyl_holds.1
  refine ⟨(MulAut.conj w).toMonoidHom.comp L7.subtype,
    (MulAut.conj w).injective.comp Subtype.val_injective, ?_⟩
  have hC : L7 ⊓ Subgroup.centralizer (J theta : Set (ModGL .E7 (ZMod 2))) =
      rootSpan .E7 (ZMod 2) (perpRoots .E7) := by
    have h := adjointGroup_inf_centralizer_highRootSL2_eq_of_charTwo
      (K := ZMod 2) (Or.inr (Or.inl rfl))
    have hJ : J theta = highRootSL2 .E7 (ZMod 2) := rootRankOneGroup_eq_sup isRoot_theta
    simpa only [hJ] using h
  have hD : rootSpan .E7 (ZMod 2) (perpRoots .E7) ≤ L7 := by
    rw [← hC]
    exact inf_le_left
  have hL : L7.map (MulAut.conj w).toMonoidHom = L7 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hw)
  change ((rootSpan .E7 (ZMod 2) (perpRoots .E7)).subgroupOf L7).map
    ((MulAut.conj w).toMonoidHom.comp L7.subtype) = M0
  rw [← Subgroup.map_map, Subgroup.subgroupOf_map_subtype, inf_of_le_left hD, ← hC,
    Subgroup.map_inf_eq _ _ _ (MulAut.conj w).injective,
    hL, CFSG.SeitzReduction.F4Pilot.map_centralizer_mulEquiv, hwθ]

theorem exists_mulEquiv_perpLevi_m0 :
    Nonempty ((perpLevi .E7 (ZMod 2)) ≃* M0) := by
  obtain ⟨φ, hφ, hmap⟩ := exists_perpLevi_map_eq_m0
  exact ⟨((perpLevi .E7 (ZMod 2)).equivMapOfInjective φ hφ).trans
    (MulEquiv.subgroupCongr hmap)⟩

theorem isSimpleGroup_m0 : IsSimpleGroup M0 := by
  obtain ⟨e⟩ := exists_mulEquiv_perpLevi_m0
  let : IsSimpleGroup (perpLevi .E7 (ZMod 2)) := isSimpleGroup_perpLevi_E7
  exact e.symm.isSimpleGroup

theorem exists_mulEquiv_m0_omega :
    Nonempty (M0 ≃* ↥⁅TauCeti.QuadraticMap.orthogonalGroup
      (CFSG.LieType.Universal.Spin.quadPlus 6 (ZMod 2)),
      TauCeti.QuadraticMap.orthogonalGroup (CFSG.LieType.Universal.Spin.quadPlus 6 (ZMod 2))⁆) := by
  obtain ⟨e⟩ := exists_mulEquiv_perpLevi_m0
  exact ⟨e.symm.trans ((spinEquivPerpLevi (ZMod 2)).symm.trans
    (CFSG.LieType.Universal.Spin.spinEquivCommutatorQuadPlus
      (n := 6) (K := ZMod 2) (by decide) (by decide +kernel)))⟩

open scoped MatrixGroups
open CFSG.LocalAnalysis.ComponentInitial

theorem exists_order_three_j {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β) :
    ∃ z ∈ J β, orderOf z = 3 := by
  let A : SL(2, ZMod 2) := uSL 1 * vSL 1
  have hA : orderOf A = 3 := orderOf_eq_prime (by decide +kernel) (by decide +kernel)
  have hinj := (CFSG.RankThree.Chevalley.even_Chevalley_pinned_root_SL2_maps .E7 (ZMod 2) hβ).1
  refine ⟨rootSL2 .E7 (ZMod 2) β A, ⟨A, rfl⟩, ?_⟩
  rw [orderOf_injective _ hinj, hA]

theorem exists_order_three_jn_zero : ∃ z ∈ Jn 0, orderOf z = 3 :=
  exists_order_three_j (isRoot_single .E7 (⟨0, by decide⟩ : Fin (Tag.rank .E7)))

theorem three_dvd_natCard_m0 : 3 ∣ Nat.card M0 := by
  obtain ⟨z, hz, h3⟩ := exists_order_three_j
    (isRoot_single .E7 (⟨1, by decide⟩ : Fin (Tag.rank .E7)))
  have hzM : z ∈ M0 := jn_le_m0 (1 : Fin 7) (by decide) (by decide) hz
  simpa only [h3] using Subgroup.orderOf_dvd_natCard M0 hzM

theorem out_le_two_m0 (φ₁ φ₂ : MulAut M0)
    (hn₁ : ¬ IsInnerAut φ₁) (hn₂ : ¬ IsInnerAut φ₂) : IsInnerAut (φ₁⁻¹ * φ₂) := by
  obtain ⟨e⟩ := exists_mulEquiv_m0_omega
  have hnd := nondegenerate_polarBilin_quadPlus 6 (ZMod 2)
  have hdim : 6 ≤ Module.finrank (ZMod 2) (Fin 6 ⊕ Fin 6 → ZMod 2) := by
    simp [Module.finrank_fintype_fun_eq_card]
  have hi : (⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus 6 (ZMod 2)),
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus 6 (ZMod 2))⁆).relIndex
        (TauCeti.QuadraticMap.orthogonalGroup (quadPlus 6 (ZMod 2))) = 2 := by
    rw [CFSG.RankThree.Literature.FSmith.commutator_orthogonalGroup_eq_omegaGroup hnd hdim]
    exact CFSG.RankThree.OrthogonalInvolutions.relIndex_omegaGroup _ hnd
  exact out_le_two_congr e.symm
    (isInnerAut_inv_mul_of_omegaAutIsometric _ omegaAutIsometric_quadPlus_six hi)
    φ₁ φ₂ hn₁ hn₂

theorem inf_centralizer_zpowers_highRoot_of_order_three {a : ModGL .E7 (ZMod 2)}
    (ha : a ∈ J theta) (h3 : orderOf a = 3) :
    L7 ⊓ Subgroup.centralizer (Subgroup.zpowers a : Set (ModGL .E7 (ZMod 2))) =
      Subgroup.zpowers a ⊔ rootSpan .E7 (ZMod 2) (perpRoots .E7) := by
  have haL : a ∈ L7 := e7NatHigh_holds.2.2.2.1 ha
  let aL : L7 := ⟨a, haL⟩
  let X : Subgroup L7 := Subgroup.zpowers aL
  have hXJ : X ≤ (highRootSL2 .E7 (ZMod 2)).subgroupOf L7 := by
    apply Subgroup.zpowers_le.mpr
    exact (rootRankOneGroup_eq_sup isRoot_theta).le ha
  have hcard : Nat.card X = Nat.card (ZMod 2) + 1 := by
    rw [Nat.card_zpowers, ← Subgroup.orderOf_coe]
    simp [aL, h3]
  have h := inf_centralizer_nonsplit_E7_of_finite (MulEquiv.refl L7) hXJ hcard
    (inferInstance : IsCyclic X)
  have hXraw : (X.map (MulEquiv.refl L7).symm.toMonoidHom).map L7.subtype =
      Subgroup.zpowers a := by
    rw [Subgroup.map_map]
    change (Subgroup.zpowers aL).map _ = _
    rw [MonoidHom.map_zpowers]
    rfl
  have hD : L7 ⊓ Subgroup.centralizer (J theta : Set (ModGL .E7 (ZMod 2))) =
      rootSpan .E7 (ZMod 2) (perpRoots .E7) := by
    have hJ : J theta = highRootSL2 .E7 (ZMod 2) := rootRankOneGroup_eq_sup isRoot_theta
    simpa only [hJ] using
      adjointGroup_inf_centralizer_highRootSL2_eq_of_charTwo
        (K := ZMod 2) (Or.inr (Or.inl rfl))
  have hDle : rootSpan .E7 (ZMod 2) (perpRoots .E7) ≤ L7 := by
    rw [← hD]
    exact inf_le_left
  have hDraw : ((perpLevi .E7 (ZMod 2)).map
      (MulEquiv.refl L7).symm.toMonoidHom).map L7.subtype =
      rootSpan .E7 (ZMod 2) (perpRoots .E7) := by
    rw [Subgroup.map_map]
    change ((rootSpan .E7 (ZMod 2) (perpRoots .E7)).subgroupOf L7).map
      L7.subtype = _
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hDle]
  simpa only [hXraw, hDraw] using h

theorem inf_centralizer_order_three_jn_zero {z : ModGL .E7 (ZMod 2)}
    (hz : z ∈ Jn 0) (h3 : orderOf z = 3) :
    L7 ⊓ Subgroup.centralizer ({z} : Set (ModGL .E7 (ZMod 2))) =
      Subgroup.zpowers z ⊔ M0 := by
  obtain ⟨w, hw, hwθ⟩ := e7NatWeyl_holds.1
  obtain ⟨a, ha, haeq⟩ := (show z ∈ (J theta).map (MulAut.conj w).toMonoidHom from
    hwθ.symm ▸ hz)
  have h3a : orderOf a = 3 := by
    rw [← (MulAut.conj w).orderOf_eq, ← MulEquiv.coe_toMonoidHom, haeq, h3]
  have h := inf_centralizer_zpowers_highRoot_of_order_three ha h3a
  have hD : L7 ⊓ Subgroup.centralizer (J theta : Set (ModGL .E7 (ZMod 2))) =
      rootSpan .E7 (ZMod 2) (perpRoots .E7) := by
    have hJ : J theta = highRootSL2 .E7 (ZMod 2) := rootRankOneGroup_eq_sup isRoot_theta
    simpa only [hJ] using
      adjointGroup_inf_centralizer_highRootSL2_eq_of_charTwo
        (K := ZMod 2) (Or.inr (Or.inl rfl))
  have hL : L7.map (MulAut.conj w).toMonoidHom = L7 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hw)
  have hDimage : (rootSpan .E7 (ZMod 2) (perpRoots .E7)).map
      (MulAut.conj w).toMonoidHom = M0 := by
    rw [← hD, Subgroup.map_inf_eq _ _ _ (MulAut.conj w).injective, hL,
      CFSG.SeitzReduction.F4Pilot.map_centralizer_mulEquiv, hwθ]
  have hf := congrArg (fun H : Subgroup (ModGL .E7 (ZMod 2)) =>
    H.map (MulAut.conj w).toMonoidHom) h
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj w).injective, hL,
    CFSG.SeitzReduction.F4Pilot.map_centralizer_mulEquiv, Subgroup.map_sup,
    MonoidHom.map_zpowers, haeq, hDimage] at hf
  simpa only [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] using hf

theorem e7NatCent_of_doubleCentralizer
    (hC : L7 ⊓ Subgroup.centralizer (M0 : Set (ModGL .E7 (ZMod 2))) = Jn 0) :
    E7NatCent :=
  ⟨hC, fun _ hz h3 => inf_centralizer_order_three_jn_zero hz h3,
    isSimpleGroup_m0, three_dvd_natCard_m0, exists_order_three_jn_zero, out_le_two_m0⟩

end CFSG.StandardType.FrameRoute.FS81.E7Frame
