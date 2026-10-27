module

public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFInputs

public section

namespace CFSG.RankThree.PartTwo.Sec15.F153L3C2

open CFSG CFSG.Quasithin CFSG.GH74.GLS CFSG.RankThree.PartTwo.Sec14
open CFSG.HardMathSupport.Cooperstein.Coordinator (FFHyp)

@[expose] def NoOuterFFOffender (T : Type) [Group T] : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ H L : Subgroup (MulAut V), FFHyp H L → Nonempty (↥L ⧸ Subgroup.center ↥L ≃* T) →
      ∀ A : Subgroup (MulAut V), A ≤ H → A ≠ ⊥ → IsElemAbelian2 A → A ⊓ L = ⊥ →
        Nat.card A * Nat.card (fixV A) < Nat.card V

@[expose] def KFactL3NoOuterOffender : Prop :=
  ∀ (T : Type) [Group T] (f : ℕ), 1 ≤ f →
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    IsLThreeEpsAt T 2 f → NoOuterFFOffender T

@[expose] def KFactL3CentOdd : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (f : ℕ), 1 ≤ f → CFSG.IsQuasisimple Q →
    Odd (Nat.card (Subgroup.center Q)) →
    (letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
     IsLThreeEpsAt (Q ⧸ Subgroup.center Q) 2 f) →
    ∀ D : Subgroup (MulAut Q), CFSG.Assembly.IsElemAbelian 3 D →
      Odd (Nat.card ↥(pPrimeCoreOf 3 (FixedPoints.subgroup D Q)))

@[expose] def KL3Char2NotList148 : Prop :=
  ∀ (T : Type) [Group T] (f : ℕ), 1 ≤ f →
    (letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩ ; IsLThreeEpsAt T 2 f) →
    IsEmpty (T ≃* alternatingGroup (Fin 5)) ∧ IsEmpty (T ≃* alternatingGroup (Fin 6)) ∧
    IsEmpty (T ≃* alternatingGroup (Fin 7)) ∧ IsEmpty (T ≃* alternatingGroup (Fin 10)) ∧
    IsEmpty (T ≃* CFSG.Blueprint.NativeSporadic.ON) ∧
    IsEmpty (T ≃* CFSG.Blueprint.NativeSporadic.J2) ∧
    (∀ _ : Fact (Nat.Prime 7),
      IsEmpty (T ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)))

end CFSG.RankThree.PartTwo.Sec15.F153L3C2
