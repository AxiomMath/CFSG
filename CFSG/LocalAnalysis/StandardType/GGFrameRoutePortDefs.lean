module

public import CFSG.Assembly.LargeEvenDefs
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Assembly CFSG.Open

@[expose] def Elem3Disjoint (G : Type*) [Group G] (r : ℕ) : Prop :=
  ∃ E : Subgroup G, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ r ∧ E ⊓ Subgroup.center G = ⊥

@[expose] def Rank3Witness (G : Type*) [Group G] (r : ℕ) : Prop :=
  ∃ (E : Subgroup G) (t : G), IsElemAbelian 3 E ∧ Nat.card E = 3 ^ r ∧
    E ⊓ Subgroup.center G = ⊥ ∧ (∃ k : ℕ, t ^ 2 ^ k = 1) ∧ t ∉ Subgroup.center G ∧
    E ≤ Subgroup.centralizer ({t} : Set G)

section Centralizer

variable {G : Type} [Group G] [Finite G]

@[expose] def barImage (z : G) (K : Subgroup G) :
    Subgroup (↥(Subgroup.centralizer ({z} : Set G)) ⧸
      LargeEvenPPrimeCore 3 ↥(Subgroup.centralizer ({z} : Set G))) :=
  (K.subgroupOf (Subgroup.centralizer ({z} : Set G))).map
    (QuotientGroup.mk' (LargeEvenPPrimeCore 3 ↥(Subgroup.centralizer ({z} : Set G))))

structure P5Out (B Bs : Subgroup G) (x z : G) (L D₁ J₁ : Subgroup G) : Prop where
  cfg : GGConfig 3 B Bs x L D₁ J₁
  plane : D₁ = Subgroup.closure {x, z}
  normL : Bs ≤ Subgroup.normalizer (L : Set G)
  three_dvd : 3 ∣ Nat.card J₁
  A1 : ¬ Bs ≤ Subgroup.centralizer (J₁ : Set G)
  usable : ∃ r, LargeEvenTwoLocalRank 3 G < 2 * r + 1 ∧ Rank3Witness ↥J₁ r

end Centralizer

end CFSG.StandardType.FrameRoute

end
