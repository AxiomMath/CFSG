module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGFixSub

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

deriving instance DecidableEq for LargeEvenLabel

structure GGKacOrbit where
  lab : LargeEvenLabel
  qs : Bool
  deriving DecidableEq

structure GGKacDatum where
  orbits : List GGKacOrbit
  rZ : ℕ
  stabΩ : ℕ
  deriving DecidableEq

@[expose] def GGKacGeneric (lab : LargeEvenLabel) (p : ℕ) : Prop :=
  p.Prime ∧ p ≠ 2 ∧ (p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1) ∧
    (lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .F4) ∧
    ¬ (lab.tag = .F4 ∧ p = 3) ∧
    ¬ ((lab.tag = .E6 ∨ lab.tag = .twE6) ∧ (p = 3 ∨ p = 5)) ∧
    ¬ ((lab.tag = .E7 ∨ lab.tag = .E8) ∧ (p = 3 ∨ p = 5 ∨ p = 7))

@[expose] def GGK0Main (Gen : LargeEvenLabel → ℕ → Prop)
    (Valid : LargeEvenLabel → ℕ → GGKacDatum → Prop) : Prop :=
  ∀ p : ℕ, ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → Gen lab p →
    LargeEvenLabelAll lab fun R _ I _ =>
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
        ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
        ∀ e : MulAut L', e ^ p = 1 → (∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (e l)) →
          ∃ D : GGKacDatum, Valid lab p D ∧
            (∀ J : Subgroup L', CFSG.Assembly.IsComponentOf J (ggFixSub e) →
              ∃ o ∈ D.orbits, o.qs = true ∧ lab.n ∣ o.lab.n ∧ LargeEvenInLambda2 o.lab ∧
                GGHasLabel o.lab (J ⧸ Subgroup.center J)) ∧
            (∀ o ∈ D.orbits, o.qs = true → ∃ J : Subgroup L',
              CFSG.Assembly.IsComponentOf J (ggFixSub e) ∧
                GGHasLabel o.lab (J ⧸ Subgroup.center J)) ∧
            (∀ J : Subgroup L', CFSG.Assembly.IsComponentOf J (ggFixSub e) → p ∣ Nat.card J) ∧
            (2 ≤ D.rZ → ∃ E : Subgroup L', IsElemAbelian p E ∧ Nat.card E = p ^ D.rZ ∧
              E ≤ ggFixSub e ∧ (∀ z ∈ E, ∀ g ∈ ggFixSub e, g * z = z * g) ∧
              ∀ A : Subgroup (MulAut L'), e ∈ A → IsElemAbelian p A →
                (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) → ∀ z ∈ E, ∀ a ∈ A, a z = z)

@[expose] def GGK0Schur (Gen : LargeEvenLabel → ℕ → Prop) : Prop :=
  ∀ p : ℕ, ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → Gen lab p →
    LargeEvenLabelAll lab fun R _ _ _ =>
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
        ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
        (Nat.card (Subgroup.center L')).Coprime p

@[expose] def GGTCJKac (Gen : LargeEvenLabel → ℕ → Prop)
    (Valid : LargeEvenLabel → ℕ → GGKacDatum → Prop) : Prop :=
  GGK0Main Gen Valid ∧ GGK0Schur Gen

def GGTCJKnownGeneric : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    GGKacGeneric lab p →
    LargeEvenLabelAll lab fun R _ I _ =>
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
        ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
        ∀ e : MulAut L', e ^ p = 1 → (∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (e l)) →
          ∀ J : Subgroup L', CFSG.Assembly.IsComponentOf J (ggFixSub e) →
            ∃ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ ∧ lab.n ∣ labJ.n ∧
              GGHasLabel labJ (J ⧸ Subgroup.center J)

theorem GGK0Main.toTCJGeneric {Valid : LargeEvenLabel → ℕ → GGKacDatum → Prop}
    (h : GGK0Main GGKacGeneric Valid) : GGTCJKnownGeneric := by
  intro p hp hp2 lab hlab hgen Q hQ
  refine largeEvenRawDatum_mono ?_ (h p lab hlab hgen Q hQ)
  intro R _ I F ⟨hq, hP⟩
  refine ⟨hq, ?_⟩
  intro L' _ _ ψ hψ hker hcomm e hep hind J hJ
  obtain ⟨D, -, hcomp, -⟩ := hP L' ψ hψ hker hcomm e hep hind
  obtain ⟨o, -, -, hn, hΛ, hlabJ⟩ := hcomp J hJ
  exact ⟨o.lab, hΛ, hn, hlabJ⟩

end CFSG.StandardType

end
