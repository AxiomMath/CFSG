module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangAxisCases
public import CFSG.LocalAnalysis.StandardType.GGNbrLangTypeASixNonSplit
public import CFSG.LocalAnalysis.StandardType.GGNbrLangS1ExcX

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGNbrLangS1LinLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGNbrLangTypeASixLabel p lab ∧ GGTypeASplitPrime p lab ∧ p ∣ lab.n ∧ lab.tag = .A

@[expose] def GGNbrLangS1UniLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGNbrLangTypeASixLabel p lab ∧ GGTypeASplitPrime p lab ∧ p ∣ lab.n ∧ lab.tag = .twA

@[expose] def GGNbrLangS1ExcELabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7) ∧ p = 3 ∧ 3 ∣ lab.n

@[expose] def GGNbrLangS1Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGNbrLangS1LinLabel p lab ∨ GGNbrLangS1UniLabel p lab ∨ GGNbrLangS1ExcELabel p lab ∨
    GGNbrLangS1ExcXLabel p lab

theorem GGNbrLangAxisOuterOn.mono_of_lambda {S S' : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, p.Prime → p ≠ 2 → LargeEvenInLambda2 lab → S' p lab → S p lab)
    (h : GGNbrLangAxisOuterOn S) : GGNbrLangAxisOuterOn S' := by
  intro G _ _ p B Bs x L D J hC y K hK hN Q hQ
  have hp : p.Prime := hC.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hC.1.2.2.2.2.2.1.2.1
  obtain ⟨hKt, lab, hlab, hraw⟩ := h G p B Bs x L D J hC y K hK hN Q hQ
  refine ⟨hKt, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, hPθ, hQ'⟩
  exact ⟨hs, hna, θ, hPθ, fun hS' => hQ' (hS p lab hp hp2 hlab hS')⟩

theorem ggNbrLangS1Label_of_open {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime) (hp2 : p ≠ 2)
    (hlab : LargeEvenInLambda2 lab) (h : GGNbrLangRest12NonRegOpenLabel p lab)
    (hT : ¬ GGNbrLangT3Label p lab) : GGNbrLangS1Label p lab := by
  obtain ⟨⟨⟨hR12, hnReg⟩, hnRank⟩, hSix⟩ := h
  have hsplit := ggNbrLangRest12Label_split hlab hR12
  obtain ⟨⟨-, -, hOV, -, hLC, -, hEC⟩, hE6, -⟩ := hR12
  rcases hsplit with hReg | hTor | hT3
  · exact absurd hReg hnReg
  · rcases hTor with hA | hE
    · have h6 : GGNbrLangTypeASixLabel p lab := by
        by_contra h6
        exact hnRank ⟨hA, h6⟩
      have hsp := hSix h6
      rcases hA.1 with htag | htag
      · refine Or.inl ⟨h6, hsp, ?_, htag⟩
        by_contra hn
        exact hLC ⟨Or.inl htag, hn⟩
      · refine Or.inr (Or.inl ⟨h6, hsp, ?_, htag⟩)
        by_contra hn
        exact hOV ⟨hp2, Or.inr (Or.inr ⟨Or.inl htag, hn⟩)⟩
    · have hpn : p ∣ lab.n := by
        by_contra hn
        rcases hE with ⟨htag, -⟩ | ⟨htag, -⟩
        · rcases htag with htag | htag | htag | htag | htag
          · exact hEC ⟨Or.inr (Or.inl htag), hn⟩
          · exact hEC ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl htag))))), hn⟩
          · exact hE6 ⟨Or.inl htag, hn⟩
          · exact hE6 ⟨Or.inr htag, hn⟩
          · exact hEC ⟨Or.inr (Or.inr (Or.inl htag)), hn⟩
        · exact hEC ⟨Or.inr (Or.inr (Or.inr (Or.inl htag))), hn⟩
      rcases hE with ⟨htag, hp3⟩ | ⟨htag, hp35⟩
      · rcases htag with htag | htag | htag | htag | htag
        · exact Or.inr (Or.inr (Or.inr ⟨Or.inl ⟨Or.inl htag, hp3⟩, hpn⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨Or.inl ⟨Or.inr htag, hp3⟩, hpn⟩))
        · exact Or.inr (Or.inr (Or.inl ⟨Or.inl htag, hp3, hp3 ▸ hpn⟩))
        · exact Or.inr (Or.inr (Or.inl ⟨Or.inr (Or.inl htag), hp3, hp3 ▸ hpn⟩))
        · exact Or.inr (Or.inr (Or.inl ⟨Or.inr (Or.inr htag), hp3, hp3 ▸ hpn⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨Or.inr ⟨htag, hp35⟩, hpn⟩))
  · exact absurd hT3 hT

end CFSG.StandardType
