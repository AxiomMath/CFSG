module

public import CFSG.Quasithin.H13.A5S136ab1

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank

@[expose] def Elim1366Sp4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : A5.Setting G T L V),
    CFSG.Open.IsElemAbelian 2 (conjClosure V S.G1) →
    ∀ K : Subgroup G, IsComponentIn K (Subgroup.centralizer ({S.v12} : Set G)) →
      (K.subgroupOf (Subgroup.centralizer ({S.v12} : Set G))).Normal → IsSimpleGroup ↥K →
      (∃ f : ℕ, 2 ≤ f ∧ StatedClassicalModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSp 2 2 f) →
      Ch1.InducesInner S.z K →
      (∀ y ∈ S.Lv, ∀ hyN : y ∈ Subgroup.normalizer (K : Set G),
        ∃ k : ↥K ⧸ CFSG.pCore 2 ↥K, ConfAB.indHom K (MulEquiv.refl _) ⟨y, hyN⟩ = MulAut.conj k) →
      False

@[expose] def Elim1366SzPair : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : A5.Setting G T L V),
    CFSG.Open.IsElemAbelian 2 (conjClosure V S.G1) →
    ∀ K : Subgroup G, IsComponentIn K (Subgroup.centralizer ({S.v12} : Set G)) →
      ¬ (K.subgroupOf (Subgroup.centralizer ({S.v12} : Set G))).Normal →
      (∃ n : ℕ, IsSz n ↥K) → Ch1.InducesInner S.z K → False

end CFSG.Quasithin.H13.A5
