module

public import CFSG.LocalAnalysis.StandardType.GGExcTwoCompList
public import CFSG.LocalAnalysis.StandardType.GGKacK0V2

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGK0CompMult (Gen : LargeEvenLabel → ℕ → Prop)
    (Valid : LargeEvenLabel → ℕ → GGKacDatum → Prop) : Prop :=
  ∀ p : ℕ, ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → Gen lab p →
    LargeEvenLabelAll lab fun R _ I _ =>
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
        ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
        ∀ e : MulAut L', e ^ p = 1 → (∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (e l)) →
          ∃ D : GGKacDatum, Valid lab p D ∧
            (∀ J : Subgroup L', IsComponentOf J (ggFixSub e) →
              ∃ o ∈ D.orbits, o.qs = true ∧ lab.n ∣ o.lab.n ∧ LargeEvenInLambda2 o.lab ∧
                GGHasLabel o.lab (↥J ⧸ Subgroup.center ↥J)) ∧
            (∀ o ∈ D.orbits, o.qs = true → ∃ J : Subgroup L',
              IsComponentOf J (ggFixSub e) ∧ GGHasLabel o.lab (↥J ⧸ Subgroup.center ↥J)) ∧
            (∀ J : Subgroup L', IsComponentOf J (ggFixSub e) → p ∣ Nat.card J) ∧
            ∃ f : {J : Subgroup L' // IsComponentOf J (ggFixSub e)} ≃
                {i : Fin D.orbits.length // D.orbits[i].qs = true},
              ∀ J, GGHasLabel D.orbits[(f J).1].lab (↥J.1 ⧸ Subgroup.center ↥J.1)

@[expose] def GGK0CompREMult : Prop := GGK0CompMult GGKacRE GGKacValid

theorem GGK0CompMult.toComp {Gen : LargeEvenLabel → ℕ → Prop}
    {Valid : LargeEvenLabel → ℕ → GGKacDatum → Prop} (h : GGK0CompMult Gen Valid) :
    GGK0Comp Gen Valid := fun p lab hΛ hG Q hQ =>
  largeEvenRawDatum_mono
    (fun _ _ _ _ hR => ⟨hR.1, fun L' _ _ ψ hψ hk hc e he hφ => by
      obtain ⟨D, hD, ha, hb, hc', -⟩ := hR.2 L' ψ hψ hk hc e he hφ
      exact ⟨D, hD, ha, hb, hc'⟩⟩) (h p lab hΛ hG Q hQ)

theorem ggK0CompRE_of_mult (h : GGK0CompREMult) : GGK0CompRE :=
  GGK0CompMult.toComp h

theorem GGKacRE.toExcPair {lab : LargeEvenLabel} {p : ℕ} (h : GGKacRE lab p) : GGKacExcPair lab p := by
  obtain ⟨hp, hp2, hd, ht⟩ := h
  refine ⟨hp, hp2, hd, ?_⟩
  rcases ht with ⟨ht, -⟩ | ⟨ht | ht, -⟩ | ⟨ht | ht, -⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr ht)))
  · exact Or.inl ht
  · exact Or.inr (Or.inl ht)
  · exact Or.inr (Or.inr (Or.inl ht))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ht)))

theorem ggK0CompREMult_of_excB (h : GGK0ExcB) : GGK0CompREMult := by
  intro p lab hlab hRE Q hQ
  refine largeEvenRawDatum_mono ?_ (h p lab hlab hRE.toExcPair Q hQ)
  rintro R _ I F ⟨hQ, hP⟩
  refine ⟨hQ, ?_⟩
  intro L' _ _ ψ hψ hker hcomm e hep hind
  obtain ⟨D, hV, ha, hb, hc, -, he⟩ := hP L' ψ hψ hker hcomm e hep hind
  exact ⟨D, hV, ha, hb, hc, he⟩

end CFSG.StandardType

end
