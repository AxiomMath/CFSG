module

public import CFSG.RankThree.GF2n.Parrott.CentralizerV
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.GF2n.Parrott.Setup

@[expose] public section

namespace CFSG.RankThree.GF2n.Parrott

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal]

variable (D : QuotientData (z := z) hN)

theorem card_centralizer_inf_J_subgroupOf (x : H z) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set ↥(H z)) ⊓
      (J z).subgroupOf (H z)) =
    Nat.card (centralizerJ x) := by
  let A : Subgroup ↥(H z) :=
    Subgroup.centralizer ({x} : Set ↥(H z)) ⊓ (J z).subgroupOf (H z)
  let C : Subgroup G := Subgroup.centralizer ({(x : G)} : Set G) ⊓ J z
  have hmap : A.map (H z).subtype = C := by
    ext y
    constructor
    · intro hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨a, ha, rfl⟩ := hy
      rw [Subgroup.mem_inf] at ha ⊢
      constructor
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact congrArg Subtype.val
          ((Subgroup.mem_centralizer_singleton_iff (g := x) (k := a)).mp ha.1)
      · exact ha.2
    · intro hy
      rw [Subgroup.mem_inf] at hy
      rw [Subgroup.mem_map]
      refine ⟨⟨y, J_le_H (z := z) hy.2⟩, ?_, rfl⟩
      rw [Subgroup.mem_inf]
      constructor
      · rw [Subgroup.mem_centralizer_singleton_iff]
        apply Subtype.ext
        exact (Subgroup.mem_centralizer_singleton_iff (g := (x : G)) (k := y)).mp hy.1
      · exact hy.2
  have hcardA : Nat.card ↥A = Nat.card ↥C := by
    rw [← hmap]
    exact Nat.card_congr
      (Subgroup.equivMapOfInjective A (H z).subtype (H z).subtype_injective).toEquiv
  have hcardC : Nat.card ↥C = Nat.card (centralizerJ x) := by
    have hCJ : centralizerJ x = C.subgroupOf (J z) := rfl
    rw [hCJ]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : C ≤ J z)).toEquiv).symm
  change Nat.card ↥A = Nat.card (centralizerJ x)
  exact hcardA.trans hcardC

end CFSG.RankThree.GF2n.Parrott
