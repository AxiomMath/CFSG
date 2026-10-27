module

public import CFSG.LocalAnalysis.StandardType.GGSporKLieZReduce
public import CFSG.LocalAnalysis.StandardType.GGExcAdjOddLayerCentreHolds
public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalExcTwCore

public section

namespace CFSG.StandardType.SporadicShape

open Subgroup CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

private theorem l937z_d4_layerCentre
    {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)
    (hσ : σ ^ TwistTag.D4.order = 1)
    (A : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hA : Odd (Nat.card A)) :
    ∀ z ∈ GLALayer (Subgroup.centralizer
      (A : Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))),
      (∀ y ∈ GLALayer (Subgroup.centralizer
        (A : Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))),
        z * y = y * z) → z ^ 2 = 1 → z = 1 := by
  intro z hz hzc hz2
  classical
  haveI : Finite (ModGL TwistTag.D4.tag K) := finite_modGL (τ := TwistTag.D4.tag) (K := K)
  let C₀ : Subgroup (ModGL TwistTag.D4.tag K) := graphFixedRootGroup TwistTag.D4 K σ.toRingHom
  set X : Subgroup ↥C₀ := Subgroup.centralizer (A : Set ↥C₀) with hXdef
  set E : Subgroup ↥C₀ := GLALayer X with hEdef
  have hinj : Function.Injective C₀.subtype := C₀.subtype_injective
  have hperfS : ⁅E, E⁆ = E :=
    Subgroup.isPerfect_iff.mp (CFSG.LocalAnalysis.GLTheoremA.glaLayer_perfect X)
  have hEXS : E ≤ X := CFSG.LocalAnalysis.GLTheoremA.I142N.GLALayer_le X
  have hEnS : ∀ x ∈ X, ∀ e ∈ E, x * e * x⁻¹ ∈ E := by
    intro x hx e he
    exact CFSG.LocalAnalysis.GLTheoremA.glaLayer_conj_le X hx ⟨e, he, rfl⟩
  have hXS : X.map C₀.subtype ≤ C₀ := by rintro _ ⟨x, -, rfl⟩; exact x.2
  have mem_map_iff : ∀ (H : Subgroup ↥C₀) (y : ModGL TwistTag.D4.tag K) (hy : y ∈ C₀),
      y ∈ H.map C₀.subtype ↔ (⟨y, hy⟩ : ↥C₀) ∈ H := by
    intro H y hy
    constructor
    · rintro ⟨h, hh, rfl⟩; exact hh
    · intro h; exact ⟨_, h, rfl⟩
  have key := CFSG.StandardType.OddLayerCentre.central_involution_trivial_of_split
    (G := ModGL TwistTag.D4.tag K) (X := X.map C₀.subtype) (E := E.map C₀.subtype)
    (Subgroup.map_mono hEXS)
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [mem_normalizer_iff]
      intro y
      constructor
      · rintro ⟨e, he, rfl⟩
        exact ⟨x * e * x⁻¹, hEnS x hx e he, by simp⟩
      · intro hy
        have hyS : y ∈ C₀ := by
          have h1 : C₀.subtype x * y * (C₀.subtype x)⁻¹ ∈ C₀ :=
            hXS (Subgroup.map_mono hEXS hy)
          have h2 : (C₀.subtype x)⁻¹ * (C₀.subtype x * y * (C₀.subtype x)⁻¹) *
              C₀.subtype x ∈ C₀ :=
            C₀.mul_mem (C₀.mul_mem (C₀.inv_mem x.2) h1) x.2
          simpa [mul_assoc] using h2
        obtain ⟨e, he, hey⟩ := hy
        refine ⟨x⁻¹ * e * x⁻¹⁻¹, hEnS x⁻¹ (X.inv_mem hx) e he, ?_⟩
        have : C₀.subtype e = C₀.subtype x * y * (C₀.subtype x)⁻¹ := hey
        simp only [map_mul, map_inv, inv_inv]
        rw [this]; group)
    (by rw [← Subgroup.map_commutator, hperfS])
    (by
      intro V hV2 hVX hXV
      set W : Subgroup ↥C₀ := V.comap C₀.subtype
      have hVW : V = W.map C₀.subtype := by
        rw [Subgroup.map_comap_eq, Subgroup.range_subtype]
        exact (inf_eq_right.mpr (hVX.trans hXS)).symm
      have hW2 : IsPGroup 2 W := by
        intro w
        obtain ⟨k, hk⟩ := hV2 ⟨C₀.subtype w, w.2⟩
        refine ⟨k, ?_⟩
        apply Subtype.ext; apply hinj
        have := congrArg Subtype.val hk
        simpa using this
      have hWX : W ≤ X := by
        intro w hw
        obtain ⟨x, hx, hxw⟩ := hVX hw
        rw [show w = x from hinj hxw.symm]; exact hx
      have hXW : X ≤ normalizer (W : Set ↥C₀) := by
        intro x hx
        rw [mem_normalizer_iff]
        intro w
        have h := (mem_normalizer_iff.mp (hXV ⟨x, hx, rfl⟩)) (C₀.subtype w)
        simpa [W, Subgroup.mem_comap, Subgroup.mem_subgroupOf] using h
      have hEW := CFSG.StandardType.OddLayerCentre.glaLayer_le_centralizer_of_pGroup
        hW2 hWX hXW
      rintro _ ⟨e, he, rfl⟩
      rw [mem_centralizer_iff]
      intro v hv
      rw [hVW] at hv
      obtain ⟨w, hw, rfl⟩ := hv
      have := (mem_centralizer_iff.mp (hEW he)) w hw
      simpa using congrArg Subtype.val this)
    (by
      intro U₀ hU₀ne hU₀2 hU₀X hXU₀
      have hU₀S : U₀ ≤ C₀ := hU₀X.trans hXS
      have hAU₀ : A.map C₀.subtype ≤ normalizer (U₀ : Set (ModGL TwistTag.D4.tag K)) := by
        rintro _ ⟨a, ha, rfl⟩
        rw [mem_normalizer_iff]
        intro u
        have hcomm : ∀ u ∈ U₀, C₀.subtype a * u * (C₀.subtype a)⁻¹ = u := by
          intro u hu
          obtain ⟨x, hx, rfl⟩ := hU₀X hu
          have := (mem_centralizer_iff.mp hx) a ha
          have h2 : C₀.subtype a * C₀.subtype x = C₀.subtype x * C₀.subtype a := by
            simpa using congrArg Subtype.val this
          rw [h2]; group
        constructor
        · intro hu; rw [hcomm u hu]; exact hu
        · intro hu
          have hu' := hcomm _ hu
          have : u = C₀.subtype a * u * (C₀.subtype a)⁻¹ := by
            have h3 : C₀.subtype a * (C₀.subtype a * u * (C₀.subtype a)⁻¹) *
                (C₀.subtype a)⁻¹ = C₀.subtype a * u * (C₀.subtype a)⁻¹ := by rw [hu']
            have h4 : C₀.subtype a * u * (C₀.subtype a)⁻¹ = u := by
              have := congrArg (fun y => (C₀.subtype a)⁻¹ * y * C₀.subtype a) h3
              simpa [mul_assoc] using this
            exact h4.symm
          rw [this]; exact hu
      have hEN : X.map C₀.subtype ⊔ A.map C₀.subtype ≤
          normalizer (C₀ : Set (ModGL TwistTag.D4.tag K)) := by
        refine sup_le (hXS.trans (Subgroup.le_normalizer)) ?_
        rintro _ ⟨a, -, rfl⟩; exact Subgroup.le_normalizer a.2
      obtain ⟨R, hU₀R, hRad, hER⟩ := GGTwoSig.exists_radicalTwo (G₀ := C₀) hEN U₀ hU₀S hU₀2
        (sup_le hXU₀ hAU₀)
      have hRne : R ≠ ⊥ := by
        intro h; apply hU₀ne; rw [eq_bot_iff, ← h]; exact hU₀R
      obtain ⟨g, hgS, J, hRJ⟩ :=
        GGOppRadExc.exists_eq_map_conj_graphFixedParabolicRadical (t := TwistTag.D4) σ hσ hRne hRad
      set φ := (MulAut.conj g).toMonoidHom with hφ
      obtain ⟨-, -, -, -, -, -, -, -, hQP0, -, hMP0, huniq0, -⟩ :=
        diagram_fixed_parabolic_root_radical_Levi_factors TwistTag.D4 K σ J
      have hQM0 : graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom J ⊓
          graphFixedParabolicLevi TwistTag.D4 K σ.toRingHom J = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        obtain ⟨hxQ, hxL⟩ := Subgroup.mem_inf.mp hx
        obtain ⟨qm, -, huniq⟩ := huniq0 x (hQP0 hxQ)
        have e1 : (x, 1) = qm := huniq (x, 1)
          ⟨hxQ, (graphFixedParabolicLevi TwistTag.D4 K σ.toRingHom J).one_mem, by simp⟩
        have e2 : (1, x) = qm := huniq (1, x)
          ⟨(graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom J).one_mem, hxL, by simp⟩
        have hxe : x = 1 := by
          have hpair : (x, 1) = (1, x) := e1.trans e2.symm
          simpa using congrArg Prod.fst hpair
        simpa using hxe
      have hN0 : C₀ ⊓ Subgroup.normalizer
          (graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom J :
            Set (ModGL TwistTag.D4.tag K)) =
          graphFixedParabolic TwistTag.D4 K σ.toRingHom J :=
        diagram_fixed_parabolic_root_radical_normalizers TwistTag.D4 K σ J
      set P : Subgroup (ModGL TwistTag.D4.tag K) :=
        (graphFixedParabolic TwistTag.D4 K σ.toRingHom J).map φ with hP
      set M : Subgroup (ModGL TwistTag.D4.tag K) :=
        (graphFixedParabolicLevi TwistTag.D4 K σ.toRingHom J).map φ with hM
      have hSφ : C₀.map φ = C₀ := GGTwoSig.map_conj_eq (Subgroup.le_normalizer hgS)
      have hPeq : C₀ ⊓ normalizer (R : Set (ModGL TwistTag.D4.tag K)) = P := by
        rw [hP, ← hN0, GGTwoSig.map_conj_inf, hSφ, GGTwoSig.map_conj_normalizer, ← hRJ]
      have hAP : A.map C₀.subtype ≤ P := by
        rw [← hPeq]
        rintro _ ⟨a, ha, rfl⟩
        exact ⟨a.2, hER (Subgroup.mem_sup_right ⟨a, ha, rfl⟩)⟩
      have hXP : X.map C₀.subtype ≤ P := by
        rw [← hPeq]
        intro x hx
        exact ⟨hXS hx, hER (Subgroup.mem_sup_left hx)⟩
      have hQP : R ≤ P := by rw [hRJ, hP]; exact Subgroup.map_mono hQP0
      have hPQ : P ≤ normalizer (R : Set (ModGL TwistTag.D4.tag K)) := by
        rw [← hPeq]; exact inf_le_right
      have hMP : M ≤ P := Subgroup.map_mono hMP0
      have hQM : R ⊓ M = ⊥ := by
        rw [hRJ, hM, ← GGTwoSig.map_conj_inf, hQM0, Subgroup.map_bot]
      have hdecP : ∀ x ∈ P, ∃ u ∈ R, ∃ m ∈ M, x = u * m := by
        rintro _ ⟨p, hp, rfl⟩
        obtain ⟨⟨q, m⟩, ⟨hq, hm, hpqm⟩, -⟩ := huniq0 p hp
        refine ⟨φ q, ?_, φ m, ⟨m, hm, rfl⟩, ?_⟩
        · rw [hRJ]; exact ⟨q, hq, rfl⟩
        · rw [hpqm, map_mul]
      have hAodd : Odd (Nat.card (A.map C₀.subtype)) := by
        rwa [Subgroup.card_map_of_injective hinj]
      obtain ⟨C, hRC, hdecX⟩ :=
        CFSG.StandardType.OddLayerCentre.exists_fixed_complement_split hRad.isPGroup hAodd hAP
          hQP hPQ hMP hQM hdecP
      refine ⟨R, C, hU₀R, hRad.isPGroup, fun x hx => hPQ (hXP hx), hRC, ?_⟩
      intro x hx
      have hxA : x ∈ centralizer
          ((A.map C₀.subtype : Subgroup (ModGL TwistTag.D4.tag K)) :
            Set (ModGL TwistTag.D4.tag K)) := by
        obtain ⟨x₀, hx₀, rfl⟩ := hx
        rw [mem_centralizer_iff]
        rintro _ ⟨a, ha, rfl⟩
        have := (mem_centralizer_iff.mp hx₀) a ha
        simpa using congrArg Subtype.val this
      obtain ⟨u, hu, c, ⟨hcC, hcA⟩, hxuc⟩ := hdecX x (hXP hx) hxA
      refine ⟨u, hu, c, ⟨hcC, ?_⟩, hxuc⟩
      have hcS : c ∈ C₀ := by
        have : c = u⁻¹ * x := by rw [hxuc]; group
        rw [this]; exact C₀.mul_mem (C₀.inv_mem (hRad.le hu)) (hXS hx)
      refine (mem_map_iff X c hcS).mpr ?_
      rw [mem_centralizer_iff]
      intro a ha
      apply Subtype.ext
      have := (mem_centralizer_iff.mp hcA) (C₀.subtype a) ⟨a, ha, rfl⟩
      simpa using this)
    (z := C₀.subtype z) ⟨z, hz, rfl⟩
    (by
      rintro _ ⟨e, he, rfl⟩
      simpa only [map_mul] using congrArg C₀.subtype (hzc e he))
    (by simpa only [map_pow, map_one] using congrArg C₀.subtype hz2)
  exact hinj (by rw [key, map_one])

theorem layerCentreSeven_graphFixedD4
    {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)
    (hσ : σ ^ TwistTag.D4.order = 1) :
    LayerCentreSeven ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  intro x hx z hz hzc hz2
  have hcent : Subgroup.centralizer
      (Subgroup.zpowers x : Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) =
      Subgroup.centralizer ({x} : Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hAodd : Odd (Nat.card (Subgroup.zpowers x)) := by
    rw [Nat.card_zpowers, hx]
    decide
  refine l937z_d4_layerCentre (K := K) (σ := σ) hσ (Subgroup.zpowers x) hAodd z ?_ ?_ hz2
  · rwa [hcent]
  · intro y hy
    exact hzc y (by rwa [hcent] at hy)

end CFSG.StandardType.SporadicShape
