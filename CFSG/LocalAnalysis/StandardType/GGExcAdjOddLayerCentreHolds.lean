module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NBase
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KU6L2
public import CFSG.LocalAnalysis.StandardType.GGLayerAbelianOdd
public import CFSG.LocalAnalysis.StandardType.GGOddLayerTheoremF
public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalExcCore
public import CFSG.LocalAnalysis.StandardType.GGStructSOnePrimeCent
public import CFSG.LocalAnalysis.StandardType.GGTwoSignalizerRadical
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.StandardType.GGStructSOneHolds

public section

namespace CFSG.StandardType.OddLayerCentre

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem glaLayer_le_centralizer_of_pGroup {X V : Subgroup G} (hV2 : IsPGroup 2 V) (hVX : V ≤ X)
    (hXV : X ≤ normalizer (V : Set G)) : GLALayer X ≤ centralizer (V : Set G) := by
  rw [CFSG.LocalAnalysis.GLTheoremA.I142N.GLALayer_eq_sSup]
  refine sSup_le fun L hL => ?_
  have hsub : CFSG.Open.IsSubnormal V X := by
    refine CFSG.Open.IsSubnormal.step hVX ?_ (CFSG.Open.IsSubnormal.refl X)
    rw [Subgroup.normal_subgroupOf_iff hVX]
    intro h k hh hk
    exact (mem_normalizer_iff.mp (hXV hk) h).mp hh
  rcases CFSG.StandardType.isComponentOf_le_or_commutator_eq_bot_of_isSubnormal hL hsub with
    hLV | hLV
  · exfalso
    obtain ⟨-, -, hperf, hsimp⟩ := hL
    haveI : Group.IsNilpotent L := (hV2.to_le hLV).isNilpotent
    haveI : Group.IsPerfect L := ⟨hperf⟩
    haveI : Nontrivial (L ⧸ center L) := hsimp.toNontrivial
    haveI : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
    exact Group.IsPerfect.not_isSolvable (G := L) inferInstance
  · exact (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hLV

end CFSG.StandardType.OddLayerCentre

namespace CFSG.StandardType

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  OddLayerCentre

theorem ggExcAdjOddLayerCentre_holds
    (τ : Tag) : GGExcAdjOddLayerCentre τ := by
  intro K _ _ _ A hA _ z hz hzc hz2
  classical
  haveI : Finite (ModGL τ K) := finite_modGL
  set X : Subgroup (adjointGroup τ K) := centralizer (A : Set (adjointGroup τ K)) with hXdef
  set E : Subgroup (adjointGroup τ K) := GLALayer X with hEdef
  have hinj : Function.Injective (adjointGroup τ K).subtype := (adjointGroup τ K).subtype_injective
  have hperfS : ⁅E, E⁆ = E :=
    Subgroup.isPerfect_iff.mp (CFSG.LocalAnalysis.GLTheoremA.glaLayer_perfect X)
  have hEXS : E ≤ X := CFSG.LocalAnalysis.GLTheoremA.I142N.GLALayer_le X
  have hEnS : ∀ x ∈ X, ∀ e ∈ E, x * e * x⁻¹ ∈ E := by
    intro x hx e he
    exact CFSG.LocalAnalysis.GLTheoremA.glaLayer_conj_le X hx ⟨e, he, rfl⟩
  have hXS : X.map (adjointGroup τ K).subtype ≤ (adjointGroup τ K) := by rintro _ ⟨x, -, rfl⟩; exact x.2
  have mem_map_iff : ∀ (H : Subgroup (adjointGroup τ K)) (y : ModGL τ K) (hy : y ∈ (adjointGroup τ K)),
      y ∈ H.map (adjointGroup τ K).subtype ↔ (⟨y, hy⟩ : (adjointGroup τ K)) ∈ H := by
    intro H y hy
    constructor
    · rintro ⟨h, hh, rfl⟩; exact hh
    · intro h; exact ⟨_, h, rfl⟩
  have key := central_involution_trivial_of_split (G := ModGL τ K) (X := X.map (adjointGroup τ K).subtype) (E := E.map (adjointGroup τ K).subtype)
    (Subgroup.map_mono hEXS)
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [mem_normalizer_iff]
      intro y
      constructor
      · rintro ⟨e, he, rfl⟩
        exact ⟨x * e * x⁻¹, hEnS x hx e he, by simp⟩
      · intro hy
        have hyS : y ∈ (adjointGroup τ K) := by
          have h1 : (adjointGroup τ K).subtype x * y * ((adjointGroup τ K).subtype x)⁻¹ ∈ (adjointGroup τ K) := hXS (Subgroup.map_mono hEXS hy)
          have h2 : ((adjointGroup τ K).subtype x)⁻¹ * ((adjointGroup τ K).subtype x * y * ((adjointGroup τ K).subtype x)⁻¹) * (adjointGroup τ K).subtype x ∈ (adjointGroup τ K) :=
            (adjointGroup τ K).mul_mem ((adjointGroup τ K).mul_mem ((adjointGroup τ K).inv_mem x.2) h1) x.2
          simpa [mul_assoc] using h2
        obtain ⟨e, he, hey⟩ := hy
        refine ⟨x⁻¹ * e * x⁻¹⁻¹, hEnS x⁻¹ (X.inv_mem hx) e he, ?_⟩
        have : ((adjointGroup τ K).subtype e) = (adjointGroup τ K).subtype x * y * ((adjointGroup τ K).subtype x)⁻¹ := hey
        simp only [map_mul, map_inv, inv_inv]
        rw [this]; group)
    (by rw [← Subgroup.map_commutator, hperfS])
    (by
      intro V hV2 hVX hXV
      set W : Subgroup (adjointGroup τ K) := V.comap (adjointGroup τ K).subtype
      have hVW : V = W.map (adjointGroup τ K).subtype := by
        rw [Subgroup.map_comap_eq, Subgroup.range_subtype]
        exact (inf_eq_right.mpr (hVX.trans hXS)).symm
      have hW2 : IsPGroup 2 W := by
        intro w
        obtain ⟨k, hk⟩ := hV2 ⟨(adjointGroup τ K).subtype w, w.2⟩
        refine ⟨k, ?_⟩
        apply Subtype.ext; apply hinj
        have := congrArg Subtype.val hk
        simpa using this
      have hWX : W ≤ X := by
        intro w hw
        obtain ⟨x, hx, hxw⟩ := hVX hw
        rw [show w = x from hinj hxw.symm]; exact hx
      have hXW : X ≤ normalizer (W : Set (adjointGroup τ K)) := by
        intro x hx
        rw [mem_normalizer_iff]
        intro w
        have h := (mem_normalizer_iff.mp (hXV ⟨x, hx, rfl⟩)) ((adjointGroup τ K).subtype w)
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
      have hU₀S : U₀ ≤ (adjointGroup τ K) := hU₀X.trans hXS
      have hAU₀ : A.map (adjointGroup τ K).subtype ≤ normalizer (U₀ : Set (ModGL τ K)) := by
        rintro _ ⟨a, ha, rfl⟩
        rw [mem_normalizer_iff]
        intro u
        have hcomm : ∀ u ∈ U₀, (adjointGroup τ K).subtype a * u * ((adjointGroup τ K).subtype a)⁻¹ = u := by
          intro u hu
          obtain ⟨x, hx, rfl⟩ := hU₀X hu
          have := (mem_centralizer_iff.mp hx) a ha
          have h2 : (adjointGroup τ K).subtype a * (adjointGroup τ K).subtype x = (adjointGroup τ K).subtype x * (adjointGroup τ K).subtype a := by
            simpa using congrArg Subtype.val this
          rw [h2]; group
        constructor
        · intro hu; rw [hcomm u hu]; exact hu
        · intro hu
          have hu' := hcomm _ hu
          have : u = (adjointGroup τ K).subtype a * u * ((adjointGroup τ K).subtype a)⁻¹ := by
            have h3 : (adjointGroup τ K).subtype a * ((adjointGroup τ K).subtype a * u * ((adjointGroup τ K).subtype a)⁻¹) * ((adjointGroup τ K).subtype a)⁻¹ = (adjointGroup τ K).subtype a * u * ((adjointGroup τ K).subtype a)⁻¹ := by rw [hu']
            have h4 : (adjointGroup τ K).subtype a * u * ((adjointGroup τ K).subtype a)⁻¹ = u := by
              have := congrArg (fun y => ((adjointGroup τ K).subtype a)⁻¹ * y * (adjointGroup τ K).subtype a) h3
              simpa [mul_assoc] using this
            exact h4.symm
          rw [this]; exact hu
      have hEN : X.map (adjointGroup τ K).subtype ⊔ A.map (adjointGroup τ K).subtype ≤ normalizer ((adjointGroup τ K) : Set (ModGL τ K)) := by
        refine sup_le (hXS.trans (Subgroup.le_normalizer)) ?_
        rintro _ ⟨a, -, rfl⟩; exact Subgroup.le_normalizer a.2
      obtain ⟨R, hU₀R, hRad, hER⟩ := GGTwoSig.exists_radicalTwo (G₀ := (adjointGroup τ K)) hEN U₀ hU₀S hU₀2
        (sup_le hXU₀ hAU₀)
      have hRne : R ≠ ⊥ := by
        intro h; apply hU₀ne; rw [eq_bot_iff, ← h]; exact hU₀R
      obtain ⟨g, hgS, J, hRJ⟩ := GGOppRadExc.exists_eq_map_conj_parabolicRadical hRne hRad
      set φ := (MulAut.conj g).toMonoidHom with hφ
      obtain ⟨hQP0, -, -, hMP0, hQM0, -, huniq0, -⟩ := parabolic_root_radical_Levi_factors τ K J
      have hN0 := adjointGroup_inf_normalizer_parabolicRadical (τ := τ) (K := K) J
      set P : Subgroup (ModGL τ K) := (parabolicSubgroup τ K J).map φ with hP
      set M : Subgroup (ModGL τ K) := (parabolicLevi τ K J).map φ with hM
      have hSφ : (adjointGroup τ K).map φ = (adjointGroup τ K) := GGTwoSig.map_conj_eq (Subgroup.le_normalizer hgS)
      have hPeq : (adjointGroup τ K) ⊓ normalizer (R : Set (ModGL τ K)) = P := by
        rw [hP, ← hN0, GGTwoSig.map_conj_inf, hSφ, GGTwoSig.map_conj_normalizer, ← hRJ]
      have hAP : A.map (adjointGroup τ K).subtype ≤ P := by
        rw [← hPeq]
        rintro _ ⟨a, ha, rfl⟩
        exact ⟨a.2, hER (Subgroup.mem_sup_right ⟨a, ha, rfl⟩)⟩
      have hXP : X.map (adjointGroup τ K).subtype ≤ P := by
        rw [← hPeq]
        intro x hx
        exact ⟨hXS hx, hER (Subgroup.mem_sup_left hx)⟩
      have hQP : R ≤ P := by rw [hRJ, hP]; exact Subgroup.map_mono hQP0
      have hPQ : P ≤ normalizer (R : Set (ModGL τ K)) := by
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
      have hAodd : Odd (Nat.card (A.map (adjointGroup τ K).subtype)) := by
        rwa [Subgroup.card_map_of_injective hinj]
      obtain ⟨C, hRC, hdecX⟩ := exists_fixed_complement_split hRad.isPGroup hAodd hAP hQP hPQ
        hMP hQM hdecP
      refine ⟨R, C, hU₀R, hRad.isPGroup, fun x hx => hPQ (hXP hx), hRC, ?_⟩
      intro x hx
      have hxA : x ∈ centralizer ((A.map (adjointGroup τ K).subtype : Subgroup (ModGL τ K)) : Set (ModGL τ K)) := by
        obtain ⟨x₀, hx₀, rfl⟩ := hx
        rw [mem_centralizer_iff]
        rintro _ ⟨a, ha, rfl⟩
        have := (mem_centralizer_iff.mp hx₀) a ha
        simpa using congrArg Subtype.val this
      obtain ⟨u, hu, c, ⟨hcC, hcA⟩, hxuc⟩ := hdecX x (hXP hx) hxA
      refine ⟨u, hu, c, ⟨hcC, ?_⟩, hxuc⟩
      have hcS : c ∈ (adjointGroup τ K) := by
        have : c = u⁻¹ * x := by rw [hxuc]; group
        rw [this]; exact (adjointGroup τ K).mul_mem ((adjointGroup τ K).inv_mem (hRad.le hu)) (hXS hx)
      refine (mem_map_iff X c hcS).mpr ?_
      rw [mem_centralizer_iff]
      intro a ha
      apply Subtype.ext
      have := (mem_centralizer_iff.mp hcA) ((adjointGroup τ K).subtype a) ⟨a, ha, rfl⟩
      simpa using this)
    (z := (adjointGroup τ K).subtype z) ⟨z, hz, rfl⟩
    (by
      rintro _ ⟨e, he, rfl⟩
      have := hzc e he
      simpa using congrArg Subtype.val this)
    (by simpa using congrArg Subtype.val hz2)
  exact hinj (by simpa using key)

end CFSG.StandardType
