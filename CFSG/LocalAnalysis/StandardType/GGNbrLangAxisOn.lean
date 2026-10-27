module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangTypeAFrame
public import CFSG.LocalAnalysis.StandardType.GGNbrLangWeylRestLabels

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

open NbrLangTypeA

@[expose] def GGNbrLangAxisOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ∀ hN : Bs ≤ Subgroup.normalizer (K : Set G),
        GGMarkingAll (K := ↥K) fun lab _ _ I F θ => S p lab →
          (∀ (b : G) (hb : b ∈ Bs), ∃ u ∈ I, ∃ f ∈ Subgroup.closure F,
            ggLAut K θ ⟨b, hN hb⟩ = u * f) →
          ∀ (b₀ : G) (hb₀ : b₀ ∈ Bs), ggLAut K θ ⟨b₀, hN hb₀⟩ ∉ I →
            ∃ B₀ : Subgroup G, B₀ ≤ Bs ∧ Nat.card B₀ * p = Nat.card Bs ∧ b₀ ∉ B₀ ∧
              (∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈ I → b ∈ B₀) ∧
              ∃ k ∈ Subgroup.centralizer (B₀ : Set G), ∃ e ∈ B₀, e ≠ 1 ∧
                k * b₀ * k⁻¹ = e * b₀

theorem GGNbrLangAxisOn.mono {S S' : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, S' p lab → S p lab) (h : GGNbrLangAxisOn S) : GGNbrLangAxisOn S' := by
  intro G _ _ p B Bs x L D J hC y K hK hN
  exact ggMarkingAll_mono (fun lab R _ I F θ hQ hS' => hQ (hS p lab hS'))
    (h G p B Bs x L D J hC y K hK hN)

theorem GGNbrLangAxisOn.or {S S' : ℕ → LargeEvenLabel → Prop} (h : GGNbrLangAxisOn S)
    (h' : GGNbrLangAxisOn S') : GGNbrLangAxisOn fun p lab => S p lab ∨ S' p lab := by
  intro G _ _ p B Bs x L D J hC y K hK hN
  refine ggMarkingAll_of_and (h G p B Bs x L D J hC y K hK hN)
    (h' G p B Bs x L D J hC y K hK hN) ?_
  rintro lab R _ I F θ hQ hQ' (hS | hS)
  · exact hQ hS
  · exact hQ' hS

theorem ggNbrLangAxisOn_true_of {S : ℕ → LargeEvenLabel → Prop} (h : GGNbrLangAxisOn S)
    (h' : GGNbrLangAxisOn fun p lab => ¬ S p lab) : GGNbrLangAxisOn fun _ _ => True :=
  (h.or h').mono fun p lab _ => em (S p lab)

theorem ggNbrLangAxisInput_of_on (h : GGNbrLangAxisOn fun _ _ => True) : GGNbrLangAxisInput := by
  intro G _ _ p B Bs x L D J hC y K hK hN
  exact ggMarkingAll_mono (fun lab R _ I F θ hQ => hQ trivial) (h G p B Bs x L D J hC y K hK hN)

theorem ggNbrLangAxisOn_of_torusOn {S : ℕ → LargeEvenLabel → Prop}
    (h : GGNbrLangTorusAxisOn S) : GGNbrLangAxisOn S := by
  intro G _ _ p B Bs x L D J hcfg y K hK hN
  refine ggMarkingAll_mono ?_ (h G p B Bs x L D J hcfg y K hK hN)
  intro lab R _ I F θ hQ hS hall b₀ hb₀ hb₀I
  obtain ⟨B₀, hB₀, hcard, hb₀', hax, T, hTC, hTab, hb₀T, hnorm, e, ⟨heB₀, heT⟩, he1⟩ :=
    hQ hS hall b₀ hb₀ hb₀I
  have hBs : IsElemAbelian p Bs := hcfg.2.1.2.1
  have hbp : b₀ ^ p = 1 := hBs.2 b₀ hb₀
  have heb : b₀ * e * b₀⁻¹ = e := by
    rw [TableB.IsElemAbelian.comm hBs hb₀ (hB₀ heB₀), mul_inv_cancel_right]
  have hep : e ^ p = 1 := hBs.2 e (hB₀ heB₀)
  obtain ⟨k, hkT, hk⟩ := NbrLang.exists_conj_eq_mul_of_norm hTab hb₀T hbp hnorm heT heb hep
  exact ⟨B₀, hB₀, hcard, hb₀', hax, k, hTC hkT, e, heB₀, he1, hk⟩

theorem ggNbrLangAxisOn_rest_of_rest12
    (h : GGNbrLangAxisOn GGNbrLangRest12Label) :
    GGNbrLangAxisOn GGNbrLangRestLabel := by
  refine ((h.or (ggNbrLangAxisOn_of_torusOn ggNbrLangTorusAxisOn_e6Coprime)).or
    (ggNbrLangAxisOn_of_torusOn ggNbrLangTorusAxisOn_twB2)).mono ?_
  intro p lab hS
  by_cases h1 : GGNbrLangE6CoprimeLabel p lab
  · exact Or.inl (Or.inr h1)
  by_cases h2 : lab.tag = .twB2
  · exact Or.inr h2
  exact Or.inl (Or.inl ⟨hS, h1, h2⟩)

theorem ggNbrLangAxisOn_notTypeASplit_of_rest
    (h : GGNbrLangAxisOn GGNbrLangRestLabel) :
    GGNbrLangAxisOn fun p lab => ¬ GGTypeASplitCoprimeLabel p lab := by
  refine ((((((h.or (ggNbrLangAxisOn_of_torusOn ggNbrLangTorusAxisOn_linearTwo)).or
    (ggNbrLangAxisOn_of_torusOn ggNbrLangTorusAxisOn_openVac)).or
    (ggNbrLangAxisOn_of_torusOn ggNbrLangTorusAxisOn_fieldTwo)).or
    (ggNbrLangAxisOn_of_torusOn ggNbrLangTorusAxisOn_linearCoprimeDeg)).or
    (ggNbrLangAxisOn_of_torusOn ggNbrLangTorusAxisOn_spOmegaCoprimeDeg)).or
    (ggNbrLangAxisOn_of_torusOn ggNbrLangTorusAxisOn_excCoprimeDeg)).mono ?_
  intro p lab hS
  by_cases h1 : GGLinearTwoLabel lab
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h1)))))
  by_cases h2 : GGCorFourTwoOpenVacLabel p lab
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h2))))
  by_cases h3 : GGNbrLangFieldTwoLabel lab
  · exact Or.inl (Or.inl (Or.inl (Or.inr h3)))
  by_cases h4 : GGLinearCoprimeDegLabel p lab
  · exact Or.inl (Or.inl (Or.inr h4))
  by_cases h5 : GGSpOmegaCoprimeDegLabel p lab
  · exact Or.inl (Or.inr h5)
  by_cases h6 : GGExcCoprimeDegLabel p lab
  · exact Or.inr h6
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨hS, h1, h2, h3, h4, h5, h6⟩)))))

theorem ggNbrLangAxisInput_of_typeASplit_rest'
    (hrest : GGNbrLangAxisOn fun p lab => ¬ GGTypeASplitCoprimeLabel p lab) :
    GGNbrLangAxisInput :=
  ggNbrLangAxisInput_of_on
    (ggNbrLangAxisOn_true_of (ggNbrLangAxisOn_of_torusOn ggNbrLangTorusAxisOn_typeASplit_holds)
      hrest)

theorem ggXNotNormalInput_of_typeASplit_rest_axis (hnorm : GGBstarNbrNormalInput)
    (hgraph : GGNbrGraphInput) (hI3 : GGNbrSubcomponentInput)
    (hlang : GGNbrLangAxisOn fun p lab => ¬ GGTypeASplitCoprimeLabel p lab)
    (hweyl : GGNbrInnerWeylOn fun p lab => ¬ GGTypeASplitCoprimeLabel p lab) :
    GGXNotNormalInput :=
  ggXNotNormalInput_of_lang hnorm hgraph
    (ggNbrLangInput_of_axis (ggNbrLangAxisInput_of_typeASplit_rest' hlang))
    (ggNbrInnerXNotNormalInput_of_weyl
      (ggNbrInnerWeylInput_of_on
        (ggNbrInnerWeylOn_true_of (ggNbrInnerWeylOn_typeASplit_of_subcomponent hI3) hweyl)))

theorem ggNbrFieldTransvectionInput_of_typeASplit_rest_axis
    (hlang : GGNbrLangAxisOn fun p lab => ¬ GGTypeASplitCoprimeLabel p lab) :
    GGNbrFieldTransvectionInput :=
  ggNbrFieldTransvectionInput_of_lang
    (ggNbrLangInput_of_axis (ggNbrLangAxisInput_of_typeASplit_rest' hlang))

end CFSG.StandardType

end
