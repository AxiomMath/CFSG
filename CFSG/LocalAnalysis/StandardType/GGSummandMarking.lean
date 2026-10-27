module

public import CFSG.LocalAnalysis.StandardType.GGSummandCentralSurj
public import CFSG.LocalAnalysis.StandardType.GGSummandMarkingCentralSurj

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Config

variable {X : Type} [Group X] [Finite X] (V E K : Subgroup X)
  [hN : ((ggRCSU V E K).subgroupOf (E ⊔ K)).Normal]

private lemma ggSumRho_mk'_eq {a : ↥(E ⊔ K)} (haE : (a : X) ∈ E)
    (hmem : QuotientGroup.mk' ((ggRCSU V E K).subgroupOf (E ⊔ K)) a ∈ ggSumT V E K) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥(ggSumT V E K))
        ⟨QuotientGroup.mk' ((ggRCSU V E K).subgroupOf (E ⊔ K)) a, hmem⟩ =
      ggSumRho V E K ⟨(a : X), Subgroup.mem_sup_left haE⟩ := by
  have h : (⟨QuotientGroup.mk' ((ggRCSU V E K).subgroupOf (E ⊔ K)) a, hmem⟩ :
      ↥(ggSumT V E K)) = ggSumSigma V E K ⟨(a : X), Subgroup.mem_sup_left haE⟩ := by
    apply Subtype.ext
    simp only [ggSumSigma, MonoidHom.codRestrict_apply, MonoidHom.comp_apply]
    apply congrArg (QuotientGroup.mk' ((ggRCSU V E K).subgroupOf (E ⊔ K)))
    apply Subtype.ext
    rfl
  rw [ggSumRho, MonoidHom.comp_apply, h]

private lemma mem_ggHypImage_iff {e' : GGHypQuot (ggSumT V E K)} :
    e' ∈ ggHypImage (ggSumT V E K)
        ((E.subgroupOf (E ⊔ K)).map
          (QuotientGroup.mk' ((ggRCSU V E K).subgroupOf (E ⊔ K)))) ↔
      ∃ ε ∈ E, ∃ hε : ε ∈ E ⊔ (K ⊓ V), e' = ggSumRho V E K ⟨ε, hε⟩ := by
  constructor
  · intro he'
    rw [ggHypImage, Subgroup.mem_map] at he'
    obtain ⟨z, hz, hz'⟩ := he'
    rw [Subgroup.mem_subgroupOf] at hz
    rw [Subgroup.mem_map] at hz
    obtain ⟨a, ha, haeq⟩ := hz
    rw [Subgroup.mem_subgroupOf] at ha
    refine ⟨(a : X), ha, Subgroup.mem_sup_left ha, ?_⟩
    rw [← hz']
    have hmem : QuotientGroup.mk' ((ggRCSU V E K).subgroupOf (E ⊔ K)) a ∈ ggSumT V E K := by
      rw [haeq]
      exact z.2
    have hzval : z = ⟨QuotientGroup.mk' ((ggRCSU V E K).subgroupOf (E ⊔ K)) a, hmem⟩ :=
      Subtype.ext haeq.symm
    rw [hzval]
    exact ggSumRho_mk'_eq V E K ha hmem
  · rintro ⟨ε, hεE, hε, rfl⟩
    rw [ggHypImage, Subgroup.mem_map]
    refine ⟨ggSumSigma V E K ⟨ε, hε⟩, Subgroup.mem_subgroupOf.mpr ?_, rfl⟩
    rw [Subgroup.mem_map]
    refine ⟨⟨ε, Subgroup.mem_sup_left hεE⟩, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.mpr hεE
    · simp only [ggSumSigma, MonoidHom.codRestrict_apply, MonoidHom.comp_apply]
      apply congrArg (QuotientGroup.mk' ((ggRCSU V E K).subgroupOf (E ⊔ K)))
      apply Subtype.ext
      rfl

theorem ggSum_marking {p : ℕ} {Q : Subgroup X} {𝒞 : Set (Subgroup X)}
    (hp : p.Prime) (hp2 : p ≠ 2) (hE : IsElemAbelian p E) (hEV : E ≤ V)
    (hEK : E ≤ Subgroup.normalizer (K : Set X)) (hS : GGSummandStruct E K V Q 𝒞)
    {S : Subgroup X} (hS𝒞 : S ∈ 𝒞) :
    ggHypImage (ggSumT V E K) ((E.subgroupOf (E ⊔ K)).map
        (QuotientGroup.mk' ((ggRCSU V E K).subgroupOf (E ⊔ K)))) ≤
      Subgroup.normalizer (ggSumImg V E K S : Set (GGHypQuot (ggSumT V E K))) ∧
    LargeEvenMarking ↥(ggSumImg V E K S) (fun lab _ _ I _ θ => GGChevStTag lab ∧
      ∀ e ∈ ggHypImage (ggSumT V E K) ((E.subgroupOf (E ⊔ K)).map
        (QuotientGroup.mk' ((ggRCSU V E K).subgroupOf (E ⊔ K)))), ∃ φ ∈ I,
        LargeEvenInduces θ (fun l l' => (l' : GGHypQuot (ggSumT V E K)) = e⁻¹ * l * e) φ) := by
  obtain ⟨hSKV, hQS, hsub, hperf, hES, hq⟩ := hS.2.2 S hS𝒞
  haveI : (Q.subgroupOf S).Normal := ggSum_normal_subgroupOf_Q hS hS𝒞
  refine ⟨?_, ?_⟩
  · intro e' he'
    obtain ⟨ε, hεE, hε, rfl⟩ := (mem_ggHypImage_iff V E K).mp he'
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [ggSumImg, Subgroup.mem_map] at hx
      obtain ⟨a, ha, rfl⟩ := hx
      rw [Subgroup.mem_subgroupOf] at ha
      let y : ↥(E ⊔ (K ⊓ V)) := ⟨ε, hε⟩ * a * ⟨ε, hε⟩⁻¹
      have hyS : (y : X) ∈ S := by
        have h := (Subgroup.mem_normalizer_iff.mp (hES hεE) (a : X)).mp ha
        simpa [y] using h
      refine Subgroup.mem_map.mpr ⟨y, Subgroup.mem_subgroupOf.mpr hyS, ?_⟩
      simp only [y, map_mul, map_inv]
    · intro hx
      rw [ggSumImg, Subgroup.mem_map] at hx
      obtain ⟨a, ha, hρa⟩ := hx
      rw [Subgroup.mem_subgroupOf] at ha
      let y : ↥(E ⊔ (K ⊓ V)) := ⟨ε, hε⟩⁻¹ * a * ⟨ε, hε⟩
      have hyS : (y : X) ∈ S := by
        have h := (Subgroup.mem_normalizer_iff.mp (hES (E.inv_mem hεE)) (a : X)).mp ha
        simpa [y] using h
      refine Subgroup.mem_map.mpr ⟨y, Subgroup.mem_subgroupOf.mpr hyS, ?_⟩
      have hxeq : x = (ggSumRho V E K ⟨ε, hε⟩)⁻¹ * ggSumRho V E K a *
          ggSumRho V E K ⟨ε, hε⟩ := by
        rw [hρa]
        group
      rw [hxeq]
      simp only [y, map_mul, map_inv]
  · have hq' : CFSG.Assembly.IsQuasisimple (↥S ⧸ Q.subgroupOf S) ∧
        LargeEvenMarking (↥S ⧸ Q.subgroupOf S) (fun lab _ _ I _ θ => GGChevStTag lab ∧
          ∀ ε ∈ E, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => ∃ s s' : ↥S,
            QuotientGroup.mk s = l ∧ QuotientGroup.mk s' = l' ∧
              (s' : X) = ε⁻¹ * s * ε) φ) := hq
    obtain ⟨hqQ, hmark⟩ := hq'
    obtain ⟨g, hg, hker, hgformula⟩ :=
      ggSum_exists_central_surj V E K hp hp2 hE hEV hEK hS hS𝒞
    refine largeEvenMarking_of_central_surj g hg hker hqQ.1
      (fun ε : X => ε ∈ E)
      (fun e' => e' ∈ ggHypImage (ggSumT V E K)
        ((E.subgroupOf (E ⊔ K)).map
          (QuotientGroup.mk' ((ggRCSU V E K).subgroupOf (E ⊔ K)))))
      GGChevStTag
      (fun ε l l' => ∃ s s' : ↥S, QuotientGroup.mk s = l ∧ QuotientGroup.mk s' = l' ∧
        (s' : X) = ε⁻¹ * s * ε)
      (fun e' l l' => (l' : GGHypQuot (ggSumT V E K)) = e'⁻¹ * l * e')
      ?_ hmark
    intro e' he'
    obtain ⟨ε, hεE, hε, he'eq⟩ := (mem_ggHypImage_iff V E K).mp he'
    refine ⟨ε, hεE, ?_⟩
    intro b b' hbb'
    obtain ⟨a, ha⟩ := hg b
    obtain ⟨s₀, rfl⟩ := QuotientGroup.mk_surjective a
    let s₀' : ↥S := ⟨ε⁻¹ * (s₀ : X) * ε, by
      have h := (Subgroup.mem_normalizer_iff.mp (hES (E.inv_mem hεE)) (s₀ : X)).mp s₀.2
      simpa using h⟩
    let a' : ↥S ⧸ Q.subgroupOf S := QuotientGroup.mk s₀'
    have hs₀H : (s₀ : X) ∈ E ⊔ (K ⊓ V) := Subgroup.mem_sup_right (hSKV s₀.2)
    have hs₀'H : (s₀' : X) ∈ E ⊔ (K ⊓ V) := Subgroup.mem_sup_right (hSKV s₀'.2)
    have hbval : (b : GGHypQuot (ggSumT V E K)) = ggSumRho V E K ⟨(s₀ : X), hs₀H⟩ := by
      rw [← ha]
      exact hgformula (s₀ : X) s₀.2 hs₀H
    have ha'val : (g a' : GGHypQuot (ggSumT V E K)) =
        ggSumRho V E K ⟨(s₀' : X), hs₀'H⟩ :=
      hgformula (s₀' : X) s₀'.2 hs₀'H
    have hga' : g a' = b' := by
      apply Subtype.ext
      rw [ha'val, hbb', hbval, he'eq]
      have hx : (⟨(s₀' : X), hs₀'H⟩ : ↥(E ⊔ (K ⊓ V))) =
          ⟨ε, hε⟩⁻¹ * ⟨(s₀ : X), hs₀H⟩ * ⟨ε, hε⟩ := by
        apply Subtype.ext
        rfl
      rw [hx]
      simp only [map_mul, map_inv]
    exact ⟨QuotientGroup.mk s₀, a', ha, hga', s₀, s₀', rfl, rfl, rfl⟩

end Config

end CFSG.StandardType
