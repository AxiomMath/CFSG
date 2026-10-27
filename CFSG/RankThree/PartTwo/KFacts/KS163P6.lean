module

public import CFSG.RankThree.PartTwo.Sec4.Statements

public section

namespace CFSG.RankThree.PartTwo.KFacts

@[expose] def IsType163P6 (L : Type) [Group L] : Prop :=
  Nonempty (L ≃* alternatingGroup (Fin 7)) ∨ Nonempty (L ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
    Nonempty (L ≃* CFSG.Blueprint.NativeSporadic.J2) ∨
    ∃ (p e : ℕ) (_ : Fact p.Prime), p ≠ 2 ∧ 1 ≤ e ∧ Sec4.IsoLThreePi L p e ∧
      ¬ (p ^ e % 9 = 1 ∨ p ^ e % 9 = 8)

@[expose] def IsMaxInvTwo {L : Type} [Group L] (E D : Subgroup L) : Prop :=
  Maximal (fun T : Subgroup L => IsPGroup 2 T ∧ E ≤ Subgroup.normalizer (T : Set L)) D

@[expose] def KS163P6Norm : Prop :=
  ∀ (L : Type) [Group L] [Finite L], IsType163P6 L →
    ∀ E : Subgroup L, CFSG.Open.IsElemAbelian 3 E → Nat.card E = 9 →
    ∀ D : Subgroup L, IsMaxInvTwo E D →
    ∀ σ : MulAut L, (∀ e ∈ E, σ e = e) → Nat.Coprime (orderOf σ) 3 →
      D.map σ.toMonoidHom = D

@[expose] def KS163P6Cent : Prop :=
  ∀ (L : Type) [Group L] [Finite L], IsType163P6 L →
    ∀ E : Subgroup L, CFSG.Open.IsElemAbelian 3 E → Nat.card E = 9 →
    ∀ D : Subgroup L, IsMaxInvTwo E D →
    ∀ T : Subgroup (MulAut L), IsPGroup 2 T →
      D.map (MulAut.conj : L →* MulAut L) ≤ T →
      T ≤ D.map (MulAut.conj : L →* MulAut L) ⊔
        Subgroup.centralizer ((D.map (MulAut.conj : L →* MulAut L) : Subgroup (MulAut L)) :
          Set (MulAut L)) →
      E.map (MulAut.conj : L →* MulAut L) ≤ Subgroup.normalizer (T : Set (MulAut L)) →
        T = D.map (MulAut.conj : L →* MulAut L)

@[expose] def KS163P6NormL3 : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (p f : ℕ) [Fact p.Prime], p ≠ 2 → 1 ≤ f →
    Sec4.IsoLThreePi L p f → ¬ (p ^ f % 9 = 1 ∨ p ^ f % 9 = 8) →
    ∀ E : Subgroup L, CFSG.Open.IsElemAbelian 3 E → Nat.card E = 9 →
    ∀ D : Subgroup L, IsMaxInvTwo E D →
    ∀ σ : MulAut L, (∀ e ∈ E, σ e = e) → Nat.Coprime (orderOf σ) 3 →
      D.map σ.toMonoidHom = D

@[expose] def KS163P6CentL3 : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (p f : ℕ) [Fact p.Prime], p ≠ 2 → 1 ≤ f →
    Sec4.IsoLThreePi L p f → ¬ (p ^ f % 9 = 1 ∨ p ^ f % 9 = 8) →
    ∀ E : Subgroup L, CFSG.Open.IsElemAbelian 3 E → Nat.card E = 9 →
    ∀ D : Subgroup L, IsMaxInvTwo E D →
    ∀ T : Subgroup (MulAut L), IsPGroup 2 T →
      D.map (MulAut.conj : L →* MulAut L) ≤ T →
      T ≤ D.map (MulAut.conj : L →* MulAut L) ⊔
        Subgroup.centralizer ((D.map (MulAut.conj : L →* MulAut L) : Subgroup (MulAut L)) :
          Set (MulAut L)) →
      E.map (MulAut.conj : L →* MulAut L) ≤ Subgroup.normalizer (T : Set (MulAut L)) →
        T = D.map (MulAut.conj : L →* MulAut L)

@[expose] def KS163P6A10 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Nonempty (K ≃* alternatingGroup (Fin 10)) →
    ∀ B : Subgroup (MulAut K), CFSG.Open.IsElemAbelian 3 B → Nat.card B = 27 →
    ∀ T : Subgroup (MulAut K), IsPGroup 2 T →
      B ≤ Subgroup.normalizer (T : Set (MulAut K)) → Nat.card T = 1 ∨ Nat.card T = 4

end CFSG.RankThree.PartTwo.KFacts
