module

public import CFSG.RankThree.PartOne.Census3.Interface
public import CFSG.RankThree.PartOne.S9.Defs
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.RankThree.PartOne

open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)

@[expose] def IsStronglyPEmbedded {H : Type*} [Group H] (p : ℕ) (Y : Subgroup H) : Prop :=
  Y ≠ ⊤ ∧ p ∣ Nat.card Y ∧
    ∀ g : H, g ∉ Y → ¬ p ∣ Nat.card (Y ⊓ Y.map (MulAut.conj g).toMonoidHom : Subgroup H)

@[expose] def ExtSeitz : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (t : StatedLieTag) (n r f : ℕ),
    StatedLieAdmissible t n r f → CFSG.Blueprint.LieModel K t n r f →
    ∀ p : ℕ, p.Prime → 5 ≤ p → p ≠ r →
      ∀ E : Subgroup (MulAut K), IsElementaryAbelian p E → ¬ IsCyclic E →
        Subgroup.closure {k : K | ∃ F : Subgroup (MulAut K), F ≤ E ∧ F ≠ ⊥ ∧
          ∀ φ ∈ F, φ k = k} = ⊤ ∨
        (Nat.card E = 25 ∧ ((t = .Tits ∧ n = 0 ∧ r = 2 ∧ f = 1) ∨
          (t = .twistedB2 ∧ n = 0 ∧ r = 2 ∧ f = 5)))

@[expose] def ExtSPE : Prop :=
  ∀ p : ℕ, p.Prime → 5 ≤ p →
    ∀ (H : Type) [Group H] [Finite H] (S : Subgroup H), S.Normal → Census3.TheoremThreeHyp ↥S →
      Subgroup.centralizer (S : Set H) = ⊥ →
      ∀ Y : Subgroup H, IsStronglyPEmbedded p Y →
        ∀ P : Subgroup H, IsSylowOf p P ⊤ → IsElementaryAbelian p (omegaOne p P) →
          (Nat.card (omegaOne p P) = p ^ 2 ∨ Nat.card (omegaOne p P) = p ^ 3) →
          (∃ q : TauCeti.PrimePower, q.p = p ∧ (q.exponent = 2 ∨ q.exponent = 3) ∧
            Census3.IsoLie ↥S (.A 1 q)) ∨
          (p = 5 ∧ (Nonempty (↥S ≃* alternatingGroup (Fin 10)) ∨ Census3.IsoLie ↥S .tits ∨
            Census3.IsoLie ↥S (.suzuki 2)))

end CFSG.RankThree.PartOne
