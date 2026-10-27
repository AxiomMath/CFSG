module

public import CFSG.RankThree.PartTwo.Sec8.Steps
public import CFSG.RankThree.PartTwo.KFacts.K71Sp48Gamma

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSp)


@[expose] def Pair810Center : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
    Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* projSp 2 (GaloisField 2 3)) →
    A ⊓ Sec4.thetaQuotCentralizer X ≤ Subgroup.zpowers b

theorem mem_gammaSet_of_mem_sec8B {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G}
    {L : Subgroup G} {a b : G} {X : Subgroup G} {n : ℕ} (h : Sec8Pair G A c L a b X n)
    (hX : Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* projSp 2 (GaloisField 2 3)))
    (hC : A ⊓ Sec4.thetaQuotCentralizer X ≤ Subgroup.zpowers b) {e : G} (he : e ∈ sec8B A X)
    (heb : e ∉ Subgroup.zpowers b) : e ∈ gammaSet A X := by
  obtain ⟨heA, heB⟩ := Subgroup.mem_inf.mp he
  have he3 : e ^ 3 = 1 := h.mem_partTwoF.1.2 e heA
  have heC : e ∉ Sec4.thetaQuotCentralizer X := fun hc => heb (hC ⟨heA, hc⟩)
  have hX' : Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* projSp 2 (GaloisField 2 (3 * 1))) := by
    simpa using hX
  exact KFacts.mem_gammaSet_of_mem_sup_of_projSp le_rfl hX' heA he3 heB heC

theorem item810_of (h87 : Item87) (h89 : Item89) (hC : Pair810Center) : Item810 := by
  intro G _ _ A c L a b X n h e he heb
  obtain ⟨Y, hY, hIJ⟩ := h87 G A c L a b X n h
  have hX := (h89 G A c L a b X n h Y hY hIJ).1
  exact mem_gammaSet_of_mem_sec8B h hX (hC G A c L a b X n h hX) he heb

end CFSG.RankThree.PartTwo.Sec8
