module

public import CFSG.Quasithin.Vol2.Ch8Sec3Statements
public import CFSG.Quasithin.Background.C2Defs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G]

@[expose] def ch83Yz (T L : Subgroup G) (z : G) : Subgroup G :=
  centralizerSection (Subgroup.centralizer ({z} : Set G)) (ch83X T L z)
    (pCoreOf 2 (ch83X T L z))

@[expose] def KGRankOneOvergroups : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T K : Subgroup G), IsSQTKIn H → pCoreOf 2 H ≠ ⊥ →
    IsSylowTwoOf T H → K ∈ cComp H → conjClosure K T ⊔ T = H →
    (∃ n : ℕ, (2 ≤ n ∧ IsPSL 2 2 n (↥K ⧸ CFSG.pCore 2 ↥K)) ∨
      (3 ≤ n ∧ IsSz n (↥K ⧸ CFSG.pCore 2 ↥K))) →
      Group.IsSolvable
          ↥(H ⊓ Subgroup.normalizer ((T ⊓ conjClosure K T : Subgroup G) : Set G)) ∧
        ∀ Y : Subgroup G, T ≤ Y → Y ≤ H →
          Y = H ∨ Y ≤ Subgroup.normalizer ((T ⊓ conjClosure K T : Subgroup G) : Set G)

@[expose] def Claim837L2N : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    ∀ _ : IsMulCommutative ↥(fsuV T I), Row711L3Wreath T L I →
    ∀ z : G, orderOf z = 2 →
      fsuV T I ⊓ Subgroup.centralizer (T : Set G) = Subgroup.zpowers z →
      ∀ (K : Subgroup G) (s : G) (n : ℕ), s ∈ T → s ∉ Subgroup.normalizer (K : Set G) →
        K ∈ cComp (Subgroup.centralizer ({z} : Set G)) →
        ch83Kz T L z = K ⊔ CFSG.conjugate K s → Even n → 4 ≤ n →
        IsPSL 2 2 n (↥K ⧸ CFSG.pCore 2 ↥K) → (3 : ℕ∞) ≤ E1.nParam (ch83Kz T L z ⊔ T)

@[expose] def Claim837YNonsolv : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    ∀ _ : IsMulCommutative ↥(fsuV T I), Row711L3Wreath T L I →
    ∀ z : G, orderOf z = 2 →
      fsuV T I ⊓ Subgroup.centralizer (T : Set G) = Subgroup.zpowers z →
      ¬ Group.IsSolvable ↥(ch83Yz T L z) → ch83Yz T L z ≤ fsuM T L

end CFSG.Quasithin.H13
