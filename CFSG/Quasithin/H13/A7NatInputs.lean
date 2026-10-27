module

public import CFSG.Quasithin.EmptyFaithful.S153DC27
public import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.Quasithin.H13.A7

open CFSG.Open CFSG.Quasithin Subgroup
open scoped IsMulCommutative

@[expose] def AsI16AltSevenCover : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V : Subgroup G) [IsMulCommutative ↥V],
    (∀ v ∈ V, v ^ 2 = 1) → L ≤ normalizer (V : Set G) → ⁅V, L⁆ = V →
    AlternatingNatural (V := ↥V) (autOn L V) ⊤ ((centralizer (L : Set G)).subgroupOf V) 7 →
    V ⊓ centralizer (L : Set G) = ⊥

@[expose] def Insp1236 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H R M K V T X : Subgroup G), HypC23 H R M →
    K ∈ cComp H → CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) → QuasithinUnique.CharTwo K →
    ¬ K ≤ M → R ≤ normalizer (K : Set G) → V = omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) →
    C27Concl H R M K V → QuasithinUnique.IsSylowTwoOf T H → R ≤ T →
    T ≤ normalizer (K : Set G) → X ≤ K ⊓ M → T ≤ normalizer (X : Set G) →
    CFSG.IsQuasisimple (↥X ⧸ CFSG.pCore 2 ↥X) →
    ¬ Nonempty ((↥X ⧸ CFSG.pCore 2 ↥X) ⧸ center (↥X ⧸ CFSG.pCore 2 ↥X) ≃*
      alternatingGroup (Fin 6))

@[expose] def InspSL2NoA6 : Prop :=
  ∀ (r : ℕ), r.Prime → 5 ≤ r → ∀ (Y : Type) [Group Y] [Finite Y]
    (f : Y →* Matrix.SpecialLinearGroup (Fin 2) (ZMod r)) (g : Y →* alternatingGroup (Fin 6)),
    Function.Surjective g → f.ker ≤ g.ker → False

end CFSG.Quasithin.H13.A7
