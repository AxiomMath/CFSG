module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
public import CFSG.LocalAnalysis.StandardType.GGTableBRank
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBPosition
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBRkDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

@[expose] def GGE6ThreeStrongWitness {L' : Type} [Group L'] (Z : Subgroup L')
    (A : Subgroup (MulAut L')) (T : Subgroup L') (w : Fin 6 → L') : Prop :=
  (∀ s ∈ T, ∀ t ∈ T, s * t = t * s) ∧
  (∀ z ∈ Z, Odd (orderOf z) → z ∈ T) ∧
  (∀ a ∈ A, ∀ t ∈ T, a t = t) ∧
  (∀ i, ∀ a ∈ A, w i * (a (w i))⁻¹ ∈ T ∧ (w i * (a (w i))⁻¹) ^ 3 = 1) ∧
  (∀ c : L', (∀ a ∈ A, a c = c) → Odd (orderOf c) → c ∈ T) ∧
  (∀ a ∈ A, a ≠ 1 → ∀ J : Subgroup L', IsComponentOf J (ggFix a) →
    ∀ c ∈ T, (∃ k : ℕ, c ^ 3 ^ k = 1) →
      c ∈ Subgroup.closure (⋃ n ∈ (Subgroup.closure (Set.range w) : Set L'),
        (fun s => n * s * n⁻¹) '' {s : L' | s ∈ J ∧ s ∈ T ∧ ∃ k : ℕ, s ^ 3 ^ k = 1}))

@[expose] def GGE6ThreeStrongData {L' : Type} [Group L'] (Z : Subgroup L')
    (A : Subgroup (MulAut L')) : Prop :=
  ∃ (T : Subgroup L') (w : Fin 6 → L'), GGE6ThreeStrongWitness Z A T w

@[expose] def GGE6ThreeStrongSCr (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), CFSG.Open.IsElemAbelian 3 A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      3 ^ 5 ≤ Nat.card A → GGTorusSelfCent 3 A → GGE6ThreeStrongData ψ.ker A

end CFSG.StandardType
