module

public import CFSG.Quasithin.Background.B6Sections
public import CFSG.Quasithin.Vol2.Ch8Sec2Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative

variable {G : Type} [Group G]

@[expose] def ch8Kstar (K : Subgroup G) (z : G) :
    Subgroup (↥(Subgroup.centralizer ({z} : Set G)) ⧸
      CFSG.pCore 2 ↥(Subgroup.centralizer ({z} : Set G))) :=
  (K.subgroupOf (Subgroup.centralizer ({z} : Set G))).map (QuotientGroup.mk' _)

@[expose] def Step8_2_13_insp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    Hyp8_2_1 T L I → ∀ _ : IsMulCommutative ↥(fsuV T I), Case8_2 T L I →
    ¬ Row711M24Code T L I → ∀ z : G, orderOf z = 2 →
      fsuV T I ⊓ Subgroup.centralizer (T : Set G) = Subgroup.zpowers z →
      Row711M24Cocode T L I ∧
      ∃ K : Subgroup G, K ≤ Subgroup.centralizer ({z} : Set G) ∧
        Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (K : Set G) ∧
        quasithinIsCComponent K (Subgroup.centralizer ({z} : Set G)) ∧ ch8Lz L z ≤ K ∧
        CFSG.Open.IsQuasisimple ↥(ch8Kstar K z) ∧
        Nat.card ↥(Subgroup.center ↥(ch8Kstar K z)) = 3 ∧
        IsSporadic .M22 (↥(ch8Kstar K z) ⧸ Subgroup.center ↥(ch8Kstar K z))

end CFSG.Quasithin.H13
