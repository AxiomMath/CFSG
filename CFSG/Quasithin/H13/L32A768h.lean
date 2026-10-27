module

public import CFSG.Quasithin.H13.L32A5Props

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def Lemma14_7_68_quasi : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp147 G T L V →
    ∀ u ∈ L32A.u0 T V, u ≠ 1 → (∀ t ∈ T, t * u * t⁻¹ * u⁻¹ ∈ fsuV1 T V) →
      QuasithinUnique.IsSylowTwoOf (T ⊓ Subgroup.centralizer ({u} : Set G))
        (Subgroup.centralizer ({u} : Set G)) →
      ∀ I ∈ cComp (Subgroup.centralizer ({u} : Set G)),
        (I.subgroupOf (Subgroup.centralizer ({u} : Set G))).Normal → L32A.kz T V ≤ I →
          I ≠ L32A.kz T V → CFSG.IsQuasisimple (↥I ⧸ CFSG.pCore 2 ↥I)

end CFSG.Quasithin.H13
