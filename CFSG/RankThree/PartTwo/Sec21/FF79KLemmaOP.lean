module

public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21

@[expose] def HasAbelianSylow3 (L : Type) [Group L] : Prop :=
  ∃ S : Sylow 3 L, ∀ a ∈ (S : Subgroup L), ∀ b ∈ (S : Subgroup L), a * b = b * a

@[expose] def ThreeRankLeOneInv (L : Type) [Group L] : Prop :=
  ∀ t u v : L, orderOf t = 2 → t * u = u * t → t * v = v * t → u * v = v * u →
    orderOf u = 3 → orderOf v = 3 → v ∈ Subgroup.zpowers u

@[expose] def FF79KLemmaOP : Prop :=
  ∀ (L : Type) [Group L] [Finite L], IsSimpleGroup L → (∃ a b : L, a * b ≠ b * a) →
    CFSG.Assembly.InCatalog L → HasAbelianSylow3 L → ThreeRankLeOneInv L →
    ∀ x : MulAut L, orderOf x = 3 → (∀ c : L, x ≠ MulAut.conj c) →
    ∀ K : Subgroup L, K ≤ x.toMonoidHom.eqLocus (MonoidHom.id L) →
      Nonempty (K ≃* alternatingGroup (Fin 5)) →
      IsComponent (K.subgroupOf (x.toMonoidHom.eqLocus (MonoidHom.id L))) →
      (∀ K' : Subgroup L, K' ≤ x.toMonoidHom.eqLocus (MonoidHom.id L) →
        IsComponent (K'.subgroupOf (x.toMonoidHom.eqLocus (MonoidHom.id L))) → K' ≠ K →
        Nat.Coprime 3 (Nat.card K')) →
      IsLnq 2 2 6 (⊤ : Subgroup L) ∨ IsLnq 2 5 3 (⊤ : Subgroup L) ∨ IsLnq 3 2 2 (⊤ : Subgroup L)

@[expose] def IsExcLieIndex : TauCeti.LieTypeIndex → Prop
  | .B r q => 3 ≤ r ∧ q.p ≠ 2
  | .D 4 q => q.p ≠ 2 ∨ q.card < 8
  | .E6 q | .E7 q | .E8 q | .F4 q | .G2 q | .twistedE6 q | .trialityD4 q => q.p ≠ 2 ∨ q.card < 8
  | .reeF4 _ | .tits => True
  | _ => False

@[expose] def FF79KLemmaOExc : Prop :=
  ∀ (L : Type) [Group L] [Finite L], IsSimpleGroup L → (∃ a b : L, a * b ≠ b * a) →
    ∀ d : TauCeti.ValidLieTypeIndex, IsExcLieIndex d.1 →
    Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group) → HasAbelianSylow3 L → ThreeRankLeOneInv L →
    ∀ x : MulAut L, x ^ 3 = 1 → (∀ c : L, x ≠ MulAut.conj c) →
    ∀ K : Subgroup L,
      CFSG.Open.IsComponentOf K (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup x) →
      ¬ Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* alternatingGroup (Fin 5))

end CFSG.RankThree.PartTwo.Sec21.FF79
