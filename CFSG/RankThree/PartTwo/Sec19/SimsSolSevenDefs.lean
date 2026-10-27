module

public import CFSG.RankThree.PartTwo.Sec19.F194Item316Leaves
public import CFSG.CGT.PushingUpLit.SolK.QStruct

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolSeven

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo

structure Setting (G : Type) [Group G] [Finite G] (M X : Subgroup G) : Prop where
  simple : IsSimpleGroup G
  nonab : ∃ a b : G, a * b ≠ b * a
  kProper : CFSG.Assembly.KProper CFSG.Assembly.InCatalog G
  charTwo : CFSG.Assembly.IsCharTwoType G
  maxLocal : CFSG.IsMaximalTwoLocal M
  block : IsBlock M X
  elemU : CFSG.Open.IsElemAbelian 2 (blockU X)
  normalizer_eq : Subgroup.normalizer (X : Set G) = M
  uniq : CFSG.maximalTwoLocalsContaining (X : Set G) = {M}
  type : IsA7FourType X
  cent : ∀ x ∈ CFSG.Open.pCoreOf 2 M, x ≠ 1 →
    CFSG.generalizedFitting ↥(Subgroup.centralizer ({x} : Set G)) =
      CFSG.pCore 2 ↥(Subgroup.centralizer ({x} : Set G))

theorem lit316SolomonSeven_of_setting
    (h : ∀ (G : Type) [Group G] [Finite G] (M X : Subgroup G), Setting G M X →
      CFSG.Assembly.InCatalog G) :
    Lit316SolomonSeven := fun G _ _ hs hn hK hc M X hM hB hab hN hu ht hcent =>
  h G M X ⟨hs, hn, hK, hc, hM, hB, hab, hN, hu, ht, hcent⟩

namespace Setting

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} (S : Setting G M X)
include S

theorem le : X ≤ M := S.block.2.1

theorem normal {m : G} (hm : m ∈ M) {x : G} (hx : x ∈ X) : m * x * m⁻¹ ∈ X := by
  rw [← S.normalizer_eq] at hm
  exact (Subgroup.mem_normalizer_iff.mp hm x).mp hx

theorem xnorm : CFSG.CGT.PushingUpLit.SolK.XNorm M X where
  le := S.le
  normal := fun _ hm _ hx => S.normal hm hx

theorem centralizer_le : Subgroup.centralizer (X : Set G) ≤ M := by
  rw [← S.normalizer_eq]
  exact Subgroup.centralizer_le_normalizer (X : Set G)

end Setting

end CFSG.RankThree.PartTwo.Sec19.SolSeven
