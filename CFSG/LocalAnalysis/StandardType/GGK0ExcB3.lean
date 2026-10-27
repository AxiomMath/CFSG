module

public import CFSG.LocalAnalysis.StandardType.GGKacExcB2

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGKacCentred (lab : LargeEvenLabel) (p : ℕ) : Prop :=
  ¬ ((lab.tag = .E6 ∨ lab.tag = .twE6) ∧ p = 3)

theorem GGKacGeneric.centred {lab : LargeEvenLabel} {p : ℕ} (h : GGKacGeneric lab p) :
    GGKacCentred lab p := by
  rintro ⟨htag, hp3⟩
  exact h.2.2.2.2.2.1 ⟨htag, Or.inl hp3⟩

@[expose] def GGK0ExcB3 : Prop :=
  ∀ p : ℕ, ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → GGKacExcPair lab p →
    LargeEvenLabelAll lab fun R _ I _ =>
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
        ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
        ∀ e : MulAut L', e ^ p = 1 → (∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (e l)) →
          ∃ D : GGKacDatum, GGKacValid lab p D ∧
            (∀ J : Subgroup L', CFSG.Assembly.IsComponentOf J (ggFixSub e) →
              ∃ o ∈ D.orbits, o.qs = true ∧ lab.n ∣ o.lab.n ∧ LargeEvenInLambda2 o.lab ∧
                GGHasLabel o.lab (J ⧸ Subgroup.center J)) ∧
            (∀ o ∈ D.orbits, o.qs = true → ∃ J : Subgroup L',
              CFSG.Assembly.IsComponentOf J (ggFixSub e) ∧
                GGHasLabel o.lab (J ⧸ Subgroup.center J)) ∧
            (∀ J : Subgroup L', CFSG.Assembly.IsComponentOf J (ggFixSub e) → p ∣ Nat.card J) ∧
            (GGKacCentred lab p → 2 ≤ D.rZ → ∃ E : Subgroup L', IsElemAbelian p E ∧
              Nat.card E = p ^ D.rZ ∧ E ≤ ggFixSub e ∧
              (∀ z ∈ E, ∀ g ∈ ggFixSub e, g * z = z * g) ∧
              ∀ A : Subgroup (MulAut L'), e ∈ A → IsElemAbelian p A →
                (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) → ∀ z ∈ E, ∀ a ∈ A, a z = z) ∧
            GGKacCompBij D L' e ∧ GGKacA12Comp D L' e

theorem GGK0ExcB3.toB2 (h : GGK0ExcB3) : GGK0ExcB2 := by
  intro p lab hlab hpair Q hQ
  refine largeEvenRawDatum_mono ?_ (h p lab hlab hpair Q hQ)
  rintro R _ I F ⟨hQ, hP⟩
  refine ⟨hQ, ?_⟩
  intro L' _ _ ψ hψ hker hcomm e hep hind
  obtain ⟨D, hV, ha, hb, hc, hd, he, hA12⟩ := hP L' ψ hψ hker hcomm e hep hind
  exact ⟨D, hV, ha, hb, hc, fun hgen => hd hgen.centred, he, hA12⟩

theorem ggK0ExcBS_of_B3 (h : GGK0ExcB3) : GGK0ExcBS :=
  ggK0ExcBS_of_B2 h.toB2

end CFSG.StandardType

end
