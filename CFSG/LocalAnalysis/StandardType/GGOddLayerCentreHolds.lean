module

public import CFSG.LocalAnalysis.StandardType.GGExcAdjOddLayerCentreHolds
public import CFSG.LocalAnalysis.StandardType.GGOddLayerInndiagGlue
public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalExcTwCore

public section

namespace CFSG.StandardType.OddLayerCentre

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem twE6OddLayerCentre_of_ringEquiv
    (K : Type) [Field K] [Finite K] [CharP K 2]
    (σ : K →+* K) (σe : K ≃+* K) (hσe : σe.toRingHom = σ) (hσ2 : σe ^ TwistTag.E6.order = 1)
    (A : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ))) (hA : Odd (Nat.card A))
    (hAI : A ≤ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 K σ) →*
      MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ)).range ⊔ (RootCentExc.compatParamAut σ).range)
    (z : ↥(graphFixedRootGroup TwistTag.E6 K σ)) (hz : z ∈ GLALayer (LayerSixE.autFix A))
    (hzc : ∀ y ∈ GLALayer (LayerSixE.autFix A), z * y = y * z) (hz2 : z ^ 2 = 1) : z = 1 := by
  classical
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  obtain ⟨Â, hÂH, hÂodd, hfix⟩ :=
    exists_odd_lift_twInndiag K σ (by rw [← hσe]; exact σe.surjective) A hA hAI
  have hD4 : ∀ J, graphFixedParabolicRadical TwistTag.E6 K σ J ⊓
      (graphFixedParabolicLevi TwistTag.E6 K σ J ⊔
        (TableB.TwE6.compat σ).map (rootDiagUnitHom TwistTag.E6.tag K)) = ⊥ := fun J => by
    have h := (graphFixedParabolic_inndiag_Levi K σe J).2.2.2.1
    rw [hσe] at h; exact h
  have hD5 : ∀ J, (graphFixedRootGroup TwistTag.E6 K σ ⊔
      (TableB.TwE6.compat σ).map (rootDiagUnitHom TwistTag.E6.tag K)) ⊓
        normalizer (graphFixedParabolicRadical TwistTag.E6 K σ J : Set (ModGL TwistTag.E6.tag K)) =
      graphFixedParabolic TwistTag.E6 K σ J ⊔
        (TableB.TwE6.compat σ).map (rootDiagUnitHom TwistTag.E6.tag K) := fun J => by
    have h := (graphFixedParabolic_inndiag_Levi K σe J).2.2.2.2.1
    rw [hσe] at h; exact h
  have hD6 : ∀ J, ∀ y ∈ graphFixedParabolic TwistTag.E6 K σ J ⊔
      (TableB.TwE6.compat σ).map (rootDiagUnitHom TwistTag.E6.tag K),
      ∃ u ∈ graphFixedParabolicRadical TwistTag.E6 K σ J,
        ∃ m ∈ graphFixedParabolicLevi TwistTag.E6 K σ J ⊔
          (TableB.TwE6.compat σ).map (rootDiagUnitHom TwistTag.E6.tag K), y = u * m := fun J => by
    have h := (graphFixedParabolic_inndiag_Levi K σe J).2.2.2.2.2
    rw [hσe] at h; exact h
  have hDS : (TableB.TwE6.compat σ).map (rootDiagUnitHom TwistTag.E6.tag K) ≤
      normalizer (graphFixedRootGroup TwistTag.E6 K σ : Set (ModGL TwistTag.E6.tag K)) := by
    rintro _ ⟨b, hb, rfl⟩
    exact rootDiagUnit_mem_normalizer_graphFixedRootGroup hb
  set X : Subgroup (graphFixedRootGroup TwistTag.E6 K σ) := LayerSixE.autFix A with hXdef
  set E : Subgroup (graphFixedRootGroup TwistTag.E6 K σ) := GLALayer X with hEdef
  have hinj : Function.Injective (graphFixedRootGroup TwistTag.E6 K σ).subtype :=
    (graphFixedRootGroup TwistTag.E6 K σ).subtype_injective
  have hperfS : ⁅E, E⁆ = E :=
    Subgroup.isPerfect_iff.mp (CFSG.LocalAnalysis.GLTheoremA.glaLayer_perfect X)
  have hEXS : E ≤ X := CFSG.LocalAnalysis.GLTheoremA.I142N.GLALayer_le X
  have hEnS : ∀ x ∈ X, ∀ e ∈ E, x * e * x⁻¹ ∈ E := by
    intro x hx e he
    exact CFSG.LocalAnalysis.GLTheoremA.glaLayer_conj_le X hx ⟨e, he, rfl⟩
  have hXS : X.map (graphFixedRootGroup TwistTag.E6 K σ).subtype ≤
      (graphFixedRootGroup TwistTag.E6 K σ) := by
    rintro _ ⟨x, -, rfl⟩; exact x.2
  have key := central_involution_trivial_of_split (G := ModGL TwistTag.E6.tag K)
    (X := X.map (graphFixedRootGroup TwistTag.E6 K σ).subtype)
    (E := E.map (graphFixedRootGroup TwistTag.E6 K σ).subtype)
    (Subgroup.map_mono hEXS)
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [mem_normalizer_iff]
      intro y
      constructor
      · rintro ⟨e, he, rfl⟩
        exact ⟨x * e * x⁻¹, hEnS x hx e he, by simp⟩
      · intro hy
        obtain ⟨e, he, hey⟩ := hy
        refine ⟨x⁻¹ * e * x⁻¹⁻¹, hEnS x⁻¹ (X.inv_mem hx) e he, ?_⟩
        have : ((graphFixedRootGroup TwistTag.E6 K σ).subtype e) =
            (graphFixedRootGroup TwistTag.E6 K σ).subtype x * y *
              ((graphFixedRootGroup TwistTag.E6 K σ).subtype x)⁻¹ := hey
        simp only [map_mul, map_inv, inv_inv]
        rw [this]; group)
    (by rw [← Subgroup.map_commutator, hperfS])
    (by
      intro V hV2 hVX hXV
      set W : Subgroup (graphFixedRootGroup TwistTag.E6 K σ) :=
        V.comap (graphFixedRootGroup TwistTag.E6 K σ).subtype
      have hVW : V = W.map (graphFixedRootGroup TwistTag.E6 K σ).subtype := by
        rw [Subgroup.map_comap_eq, Subgroup.range_subtype]
        exact (inf_eq_right.mpr (hVX.trans hXS)).symm
      have hW2 : IsPGroup 2 W := by
        intro w
        obtain ⟨k, hk⟩ := hV2 ⟨(graphFixedRootGroup TwistTag.E6 K σ).subtype w, w.2⟩
        refine ⟨k, ?_⟩
        apply Subtype.ext; apply hinj
        have := congrArg Subtype.val hk
        simpa using this
      have hWX : W ≤ X := by
        intro w hw
        obtain ⟨x, hx, hxw⟩ := hVX hw
        rw [show w = x from hinj hxw.symm]; exact hx
      have hXW : X ≤ normalizer (W : Set (graphFixedRootGroup TwistTag.E6 K σ)) := by
        intro x hx
        rw [mem_normalizer_iff]
        intro w
        have h := (mem_normalizer_iff.mp (hXV ⟨x, hx, rfl⟩))
          ((graphFixedRootGroup TwistTag.E6 K σ).subtype w)
        simpa [W, Subgroup.mem_comap, Subgroup.mem_subgroupOf] using h
      have hEW := glaLayer_le_centralizer_of_pGroup hW2 hWX hXW
      rintro _ ⟨e, he, rfl⟩
      rw [mem_centralizer_iff]
      intro v hv
      rw [hVW] at hv
      obtain ⟨w, hw, rfl⟩ := hv
      have := (mem_centralizer_iff.mp (hEW he)) w hw
      simpa using congrArg Subtype.val this)
    (by
      intro U₀ hU₀ne hU₀2 hU₀X hXU₀
      have hU₀S : U₀ ≤ (graphFixedRootGroup TwistTag.E6 K σ) := hU₀X.trans hXS
      have hXÂ : X.map (graphFixedRootGroup TwistTag.E6 K σ).subtype ≤
          centralizer (Â : Set (ModGL TwistTag.E6.tag K)) := by
        rw [hfix]; exact inf_le_right
      have hÂU₀ : Â ≤ normalizer (U₀ : Set (ModGL TwistTag.E6.tag K)) := by
        intro a ha
        rw [mem_normalizer_iff]
        have hcomm : ∀ u ∈ U₀, a * u * a⁻¹ = u := by
          intro u hu
          have := (mem_centralizer_iff.mp (hXÂ (hU₀X hu))) a ha
          rw [this]; group
        intro u
        constructor
        · intro hu; rw [hcomm u hu]; exact hu
        · intro hu
          have h := hcomm _ hu
          have h' : a * u * a⁻¹ = u := by
            have := congrArg (fun y => a⁻¹ * y * a) h
            simpa [mul_assoc] using this
          rw [← h']; exact hu
      have hEN : X.map (graphFixedRootGroup TwistTag.E6 K σ).subtype ⊔ Â ≤
          normalizer ((graphFixedRootGroup TwistTag.E6 K σ) : Set (ModGL TwistTag.E6.tag K)) :=
        sup_le (hXS.trans Subgroup.le_normalizer) (hÂH.trans (sup_le Subgroup.le_normalizer hDS))
      obtain ⟨R, hU₀R, hRad, hER⟩ := GGTwoSig.exists_radicalTwo
        (G₀ := (graphFixedRootGroup TwistTag.E6 K σ)) hEN U₀ hU₀S hU₀2 (sup_le hXU₀ hÂU₀)
      have hRne : R ≠ ⊥ := by
        intro h; apply hU₀ne; rw [eq_bot_iff, ← h]; exact hU₀R
      obtain ⟨g, hgS, J, hRJ⟩ :=
        GGOppRadExc.exists_eq_map_conj_graphFixedParabolicRadical σe hσ2 hRne
          (by rw [hσe]; exact hRad)
      rw [hσe] at hgS hRJ
      set φ := (MulAut.conj g).toMonoidHom with hφ
      obtain ⟨-, -, -, -, -, -, -, -, hQP0, -, hMP0, -⟩ :=
        diagram_fixed_parabolic_root_radical_Levi_factors TwistTag.E6 K σe J
      rw [hσe] at hQP0 hMP0
      set D := (TableB.TwE6.compat σ).map (rootDiagUnitHom TwistTag.E6.tag K) with hD
      set P : Subgroup (ModGL TwistTag.E6.tag K) :=
        (graphFixedParabolic TwistTag.E6 K σ J ⊔ D).map φ with hP
      set M : Subgroup (ModGL TwistTag.E6.tag K) :=
        (graphFixedParabolicLevi TwistTag.E6 K σ J ⊔ D).map φ with hM
      have hgH : g ∈ normalizer ((graphFixedRootGroup TwistTag.E6 K σ ⊔ D :
          Subgroup (ModGL TwistTag.E6.tag K)) : Set (ModGL TwistTag.E6.tag K)) :=
        Subgroup.le_normalizer (Subgroup.mem_sup_left hgS)
      have hHφ : (graphFixedRootGroup TwistTag.E6 K σ ⊔ D).map φ =
          graphFixedRootGroup TwistTag.E6 K σ ⊔ D :=
        GGTwoSig.map_conj_eq hgH
      have hPeq : (graphFixedRootGroup TwistTag.E6 K σ ⊔ D) ⊓
          normalizer (R : Set (ModGL TwistTag.E6.tag K)) = P := by
        rw [hP, ← (hD5 J), GGTwoSig.map_conj_inf, hHφ, GGTwoSig.map_conj_normalizer, ← hRJ]
      have hAP : Â ≤ P := by
        rw [← hPeq]
        intro a ha
        exact ⟨hÂH ha, hER (Subgroup.mem_sup_right ha)⟩
      have hXP : X.map (graphFixedRootGroup TwistTag.E6 K σ).subtype ≤ P := by
        rw [← hPeq]
        intro x hx
        exact ⟨Subgroup.mem_sup_left (hXS hx), hER (Subgroup.mem_sup_left hx)⟩
      have hQP : R ≤ P := by
        rw [hRJ, hP]; exact Subgroup.map_mono (hQP0.trans le_sup_left)
      have hPQ : P ≤ normalizer (R : Set (ModGL TwistTag.E6.tag K)) := by
        rw [← hPeq]; exact inf_le_right
      have hMP : M ≤ P := Subgroup.map_mono (sup_le_sup_right hMP0 _)
      have hQM : R ⊓ M = ⊥ := by
        rw [hRJ, hM, ← GGTwoSig.map_conj_inf, hD4 J, Subgroup.map_bot]
      have hdecP : ∀ x ∈ P, ∃ u ∈ R, ∃ m ∈ M, x = u * m := by
        rintro _ ⟨p, hp, rfl⟩
        obtain ⟨q, hq, m, hm, hpqm⟩ := hD6 J p hp
        refine ⟨φ q, ?_, φ m, ⟨m, hm, rfl⟩, ?_⟩
        · rw [hRJ]; exact ⟨q, hq, rfl⟩
        · rw [hpqm, map_mul]
      obtain ⟨C, hRC, hdecX⟩ := exists_fixed_complement_split hRad.isPGroup hÂodd hAP hQP hPQ
        hMP hQM hdecP
      refine ⟨R, C, hU₀R, hRad.isPGroup, fun x hx => hPQ (hXP hx), hRC, ?_⟩
      intro x hx
      obtain ⟨u, hu, c, ⟨hcC, hcA⟩, hxuc⟩ := hdecX x (hXP hx) (hXÂ hx)
      refine ⟨u, hu, c, ⟨hcC, ?_⟩, hxuc⟩
      have hcS : c ∈ (graphFixedRootGroup TwistTag.E6 K σ) := by
        have : c = u⁻¹ * x := by rw [hxuc]; group
        rw [this]
        exact (graphFixedRootGroup TwistTag.E6 K σ).mul_mem
          ((graphFixedRootGroup TwistTag.E6 K σ).inv_mem (hRad.le hu)) (hXS hx)
      rw [hfix]; exact ⟨hcS, hcA⟩)
    (z := (graphFixedRootGroup TwistTag.E6 K σ).subtype z) ⟨z, hz, rfl⟩
    (by
      rintro _ ⟨e, he, rfl⟩
      have := hzc e he
      simpa using congrArg Subtype.val this)
    (by simpa using congrArg Subtype.val hz2)
  exact hinj (by simpa using key)

end CFSG.StandardType.OddLayerCentre

namespace CFSG.StandardType

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley OddLayerCentre

theorem ggE6InndiagOddLayerCentre_holds
    : GGE6InndiagOddLayerCentre := by
  intro K _ _ _ A hA _ hAI z hz hzc hz2
  classical
  haveI : Finite (ModGL Tag.E6 K) := finite_modGL
  obtain ⟨Â, hÂH, hÂodd, hfix⟩ := exists_odd_lift_inndiag Tag.E6 K A hA hAI
  have hL := fun J => parabolic_inndiag_Levi Tag.E6 K J
  have hD4 := fun J => (hL J).2.2.2.1
  have hD5 := fun J => (hL J).2.2.2.2.1
  have hD6 := fun J => (hL J).2.2.2.2.2
  have hDS : (rootDiagUnitHom Tag.E6 K).range ≤
      normalizer (adjointGroup Tag.E6 K : Set (ModGL Tag.E6 K)) := by
    rintro _ ⟨a, rfl⟩
    exact (root_diagonal_conjugation Tag.E6 K a).2.2
  set X : Subgroup (adjointGroup Tag.E6 K) := LayerSixE.autFix A with hXdef
  set E : Subgroup (adjointGroup Tag.E6 K) := GLALayer X with hEdef
  have hinj : Function.Injective (adjointGroup Tag.E6 K).subtype :=
    (adjointGroup Tag.E6 K).subtype_injective
  have hperfS : ⁅E, E⁆ = E :=
    Subgroup.isPerfect_iff.mp (CFSG.LocalAnalysis.GLTheoremA.glaLayer_perfect X)
  have hEXS : E ≤ X := CFSG.LocalAnalysis.GLTheoremA.I142N.GLALayer_le X
  have hEnS : ∀ x ∈ X, ∀ e ∈ E, x * e * x⁻¹ ∈ E := by
    intro x hx e he
    exact CFSG.LocalAnalysis.GLTheoremA.glaLayer_conj_le X hx ⟨e, he, rfl⟩
  have hXS : X.map (adjointGroup Tag.E6 K).subtype ≤ (adjointGroup Tag.E6 K) := by
    rintro _ ⟨x, -, rfl⟩; exact x.2
  have key := central_involution_trivial_of_split (G := ModGL Tag.E6 K)
    (X := X.map (adjointGroup Tag.E6 K).subtype) (E := E.map (adjointGroup Tag.E6 K).subtype)
    (Subgroup.map_mono hEXS)
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [mem_normalizer_iff]
      intro y
      constructor
      · rintro ⟨e, he, rfl⟩
        exact ⟨x * e * x⁻¹, hEnS x hx e he, by simp⟩
      · intro hy
        obtain ⟨e, he, hey⟩ := hy
        refine ⟨x⁻¹ * e * x⁻¹⁻¹, hEnS x⁻¹ (X.inv_mem hx) e he, ?_⟩
        have : ((adjointGroup Tag.E6 K).subtype e) = (adjointGroup Tag.E6 K).subtype x * y *
            ((adjointGroup Tag.E6 K).subtype x)⁻¹ := hey
        simp only [map_mul, map_inv, inv_inv]
        rw [this]; group)
    (by rw [← Subgroup.map_commutator, hperfS])
    (by
      intro V hV2 hVX hXV
      set W : Subgroup (adjointGroup Tag.E6 K) := V.comap (adjointGroup Tag.E6 K).subtype
      have hVW : V = W.map (adjointGroup Tag.E6 K).subtype := by
        rw [Subgroup.map_comap_eq, Subgroup.range_subtype]
        exact (inf_eq_right.mpr (hVX.trans hXS)).symm
      have hW2 : IsPGroup 2 W := by
        intro w
        obtain ⟨k, hk⟩ := hV2 ⟨(adjointGroup Tag.E6 K).subtype w, w.2⟩
        refine ⟨k, ?_⟩
        apply Subtype.ext; apply hinj
        have := congrArg Subtype.val hk
        simpa using this
      have hWX : W ≤ X := by
        intro w hw
        obtain ⟨x, hx, hxw⟩ := hVX hw
        rw [show w = x from hinj hxw.symm]; exact hx
      have hXW : X ≤ normalizer (W : Set (adjointGroup Tag.E6 K)) := by
        intro x hx
        rw [mem_normalizer_iff]
        intro w
        have h := (mem_normalizer_iff.mp (hXV ⟨x, hx, rfl⟩)) ((adjointGroup Tag.E6 K).subtype w)
        simpa [W, Subgroup.mem_comap, Subgroup.mem_subgroupOf] using h
      have hEW := glaLayer_le_centralizer_of_pGroup hW2 hWX hXW
      rintro _ ⟨e, he, rfl⟩
      rw [mem_centralizer_iff]
      intro v hv
      rw [hVW] at hv
      obtain ⟨w, hw, rfl⟩ := hv
      have := (mem_centralizer_iff.mp (hEW he)) w hw
      simpa using congrArg Subtype.val this)
    (by
      intro U₀ hU₀ne hU₀2 hU₀X hXU₀
      have hU₀S : U₀ ≤ (adjointGroup Tag.E6 K) := hU₀X.trans hXS
      have hXÂ : X.map (adjointGroup Tag.E6 K).subtype ≤
          centralizer (Â : Set (ModGL Tag.E6 K)) := by
        rw [hfix]; exact inf_le_right
      have hÂU₀ : Â ≤ normalizer (U₀ : Set (ModGL Tag.E6 K)) := by
        intro a ha
        rw [mem_normalizer_iff]
        have hcomm : ∀ u ∈ U₀, a * u * a⁻¹ = u := by
          intro u hu
          have := (mem_centralizer_iff.mp (hXÂ (hU₀X hu))) a ha
          rw [this]; group
        intro u
        constructor
        · intro hu; rw [hcomm u hu]; exact hu
        · intro hu
          have h := hcomm _ hu
          have h' : a * u * a⁻¹ = u := by
            have := congrArg (fun y => a⁻¹ * y * a) h
            simpa [mul_assoc] using this
          rw [← h']; exact hu
      have hEN : X.map (adjointGroup Tag.E6 K).subtype ⊔ Â ≤
          normalizer ((adjointGroup Tag.E6 K) : Set (ModGL Tag.E6 K)) :=
        sup_le (hXS.trans Subgroup.le_normalizer) (hÂH.trans (sup_le Subgroup.le_normalizer hDS))
      obtain ⟨R, hU₀R, hRad, hER⟩ := GGTwoSig.exists_radicalTwo (G₀ := (adjointGroup Tag.E6 K)) hEN
        U₀ hU₀S hU₀2 (sup_le hXU₀ hÂU₀)
      have hRne : R ≠ ⊥ := by
        intro h; apply hU₀ne; rw [eq_bot_iff, ← h]; exact hU₀R
      obtain ⟨g, hgS, J, hRJ⟩ := GGOppRadExc.exists_eq_map_conj_parabolicRadical hRne hRad
      set φ := (MulAut.conj g).toMonoidHom with hφ
      obtain ⟨hQP0, -, -, hMP0, -, -, -, -⟩ := parabolic_root_radical_Levi_factors Tag.E6 K J
      set D := (rootDiagUnitHom Tag.E6 K).range with hD
      set P : Subgroup (ModGL Tag.E6 K) := (parabolicSubgroup Tag.E6 K J ⊔ D).map φ with hP
      set M : Subgroup (ModGL Tag.E6 K) := (parabolicLevi Tag.E6 K J ⊔ D).map φ with hM
      have hgH : g ∈ normalizer ((adjointGroup Tag.E6 K ⊔ D : Subgroup (ModGL Tag.E6 K)) :
          Set (ModGL Tag.E6 K)) := Subgroup.le_normalizer (Subgroup.mem_sup_left hgS)
      have hHφ : (adjointGroup Tag.E6 K ⊔ D).map φ = adjointGroup Tag.E6 K ⊔ D :=
        GGTwoSig.map_conj_eq hgH
      have hPeq : (adjointGroup Tag.E6 K ⊔ D) ⊓ normalizer (R : Set (ModGL Tag.E6 K)) = P := by
        rw [hP, ← (hD5 J), GGTwoSig.map_conj_inf, hHφ, GGTwoSig.map_conj_normalizer, ← hRJ]
      have hAP : Â ≤ P := by
        rw [← hPeq]
        intro a ha
        exact ⟨hÂH ha, hER (Subgroup.mem_sup_right ha)⟩
      have hXP : X.map (adjointGroup Tag.E6 K).subtype ≤ P := by
        rw [← hPeq]
        intro x hx
        exact ⟨Subgroup.mem_sup_left (hXS hx), hER (Subgroup.mem_sup_left hx)⟩
      have hQP : R ≤ P := by
        rw [hRJ, hP]; exact Subgroup.map_mono (hQP0.trans le_sup_left)
      have hPQ : P ≤ normalizer (R : Set (ModGL Tag.E6 K)) := by
        rw [← hPeq]; exact inf_le_right
      have hMP : M ≤ P := Subgroup.map_mono (sup_le_sup_right hMP0 _)
      have hQM : R ⊓ M = ⊥ := by
        rw [hRJ, hM, ← GGTwoSig.map_conj_inf, hD4 J, Subgroup.map_bot]
      have hdecP : ∀ x ∈ P, ∃ u ∈ R, ∃ m ∈ M, x = u * m := by
        rintro _ ⟨p, hp, rfl⟩
        obtain ⟨q, hq, m, hm, hpqm⟩ := hD6 J p hp
        refine ⟨φ q, ?_, φ m, ⟨m, hm, rfl⟩, ?_⟩
        · rw [hRJ]; exact ⟨q, hq, rfl⟩
        · rw [hpqm, map_mul]
      obtain ⟨C, hRC, hdecX⟩ := exists_fixed_complement_split hRad.isPGroup hÂodd hAP hQP hPQ
        hMP hQM hdecP
      refine ⟨R, C, hU₀R, hRad.isPGroup, fun x hx => hPQ (hXP hx), hRC, ?_⟩
      intro x hx
      obtain ⟨u, hu, c, ⟨hcC, hcA⟩, hxuc⟩ := hdecX x (hXP hx) (hXÂ hx)
      refine ⟨u, hu, c, ⟨hcC, ?_⟩, hxuc⟩
      have hcS : c ∈ (adjointGroup Tag.E6 K) := by
        have : c = u⁻¹ * x := by rw [hxuc]; group
        rw [this]
        exact (adjointGroup Tag.E6 K).mul_mem ((adjointGroup Tag.E6 K).inv_mem (hRad.le hu))
          (hXS hx)
      rw [hfix]; exact ⟨hcS, hcA⟩)
    (z := (adjointGroup Tag.E6 K).subtype z) ⟨z, hz, rfl⟩
    (by
      rintro _ ⟨e, he, rfl⟩
      have := hzc e he
      simpa using congrArg Subtype.val this)
    (by simpa using congrArg Subtype.val hz2)
  exact hinj (by simpa using key)

theorem ggTwE6OddLayerCentre_holds
    : GGTwE6OddLayerCentre := by
  intro f hf A hA _ hAI z hz hzc hz2
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ TwistTag.E6.order := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]; rfl
  set σe : GaloisField 2 (2 * f) ≃+* GaloisField 2 (2 * f) :=
    iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f with hσedef
  have hσapp : ∀ c, σe c = c ^ (2 ^ f) := fun c => iterateFrobeniusEquiv_def _ 2 f c
  have hσe : σe.toRingHom = CFSG.LieType.Steinberg.Exceptional.frobQ 2 f :=
    RingHom.ext fun c => by
      change σe c = iterateFrobenius (GaloisField 2 (2 * f)) 2 f c
      rw [hσapp, iterateFrobenius_def]
  exact twE6OddLayerCentre_of_ringEquiv (GaloisField 2 (2 * f)) _ σe hσe
    (pow_eq_one_of_apply_eq_pow σe hK hσapp) A hA hAI z hz hzc hz2


theorem ggOddLayerCentre_holds
    : GGOddLayerCentre :=
  ⟨ggExcAdjOddLayerCentre_holds _, ggExcAdjOddLayerCentre_holds _, ggExcAdjOddLayerCentre_holds _,
    ggE6InndiagOddLayerCentre_holds, ggTwE6OddLayerCentre_holds⟩

end CFSG.StandardType
