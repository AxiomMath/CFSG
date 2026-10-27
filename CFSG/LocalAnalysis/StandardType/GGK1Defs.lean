module

public import CFSG.LocalAnalysis.StandardType.GGKacK0V2
public import CFSG.LocalAnalysis.StandardType.GGKacK1
public import CFSG.LocalAnalysis.StandardType.GGMultTableCl
public import CFSG.LocalAnalysis.StandardType.GGTPNDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

@[expose] def GGK1Comps (nf : ℕ) (D : GGKacDatum) (R : Type) [Group R] (φ : MulAut R) : Prop :=
  (∀ J : Subgroup R, CFSG.Assembly.IsComponentOf J (ggFixSub φ) →
      ∃ o ∈ D.orbits, o.qs = true ∧ nf ∣ o.lab.n ∧ LargeEvenInLambda2 o.lab ∧
        GGHasLabel o.lab (J ⧸ Subgroup.center J)) ∧
    (∀ o ∈ D.orbits, o.qs = true → ∃ J : Subgroup R,
      CFSG.Assembly.IsComponentOf J (ggFixSub φ) ∧ GGHasLabel o.lab (J ⧸ Subgroup.center J))

@[expose] def GGK1Dvd (p : ℕ) (R : Type) [Group R] (φ : MulAut R) : Prop :=
  ∀ J : Subgroup R, CFSG.Assembly.IsComponentOf J (ggFixSub φ) → p ∣ Nat.card J

@[expose] def GGK1Center (p : ℕ) (D : GGKacDatum) (R : Type) [Group R] (I : Set (MulAut R))
    (φ : MulAut R) : Prop :=
  2 ≤ D.rZ → ∃ E : Subgroup R, IsElemAbelian p E ∧ Nat.card E = p ^ D.rZ ∧
    E ≤ ggFixSub φ ∧ (∀ z ∈ E, ∀ g ∈ ggFixSub φ, g * z = z * g) ∧
    ∀ ψ ∈ I, ψ ^ p = 1 → Commute ψ φ → ∀ z ∈ E, ψ z = z

@[expose] def GGK1Core (Valid : LargeEvenLabel → ℕ → GGKacDatum → Prop) (p : ℕ)
    (lab : LargeEvenLabel) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ φ ∈ I, φ ^ p = 1 → ∃ D : GGKacDatum, Valid lab p D ∧ GGK1Comps lab.n D R φ ∧
    GGK1Dvd p R φ ∧ GGK1Center p D R I φ ∧ GGKacCompBij D R φ ∧
    GGKacSigmaClause p I D R (MonoidHom.id R) φ

@[expose] def GGK1Cont (Valid : LargeEvenLabel → ℕ → GGKacDatum → Prop) (p : ℕ)
    (lab : LargeEvenLabel) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
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
            (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) → ∀ z ∈ E, ∀ a ∈ A, a z = z) ∧
        GGKacCompBij D L' e ∧ GGKacSigmaClause p I D L' ψ e

theorem ggK0MainBS_of_cont {Gen : LargeEvenLabel → ℕ → Prop}
    {Valid : LargeEvenLabel → ℕ → GGKacDatum → Prop}
    (h : ∀ p : ℕ, ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → Gen lab p →
      LargeEvenLabelAll lab fun R _ I _ => GGK1Cont Valid p lab R I) : GGK0MainBS Gen Valid :=
  fun p lab hlab hgen => h p lab hlab hgen

end CFSG.StandardType

end
