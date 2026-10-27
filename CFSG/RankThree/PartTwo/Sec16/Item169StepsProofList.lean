module

public import CFSG.RankThree.PartTwo.Sec16.Item169GeneralDefs
public import CFSG.RankThree.PartTwo.Sec16.Item169HJ
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
public import CFSG.RankThree.PartTwo.Sec13.Item13Prod
public import CFSG.RankThree.PartTwo.Sec15.HypS

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

@[expose] def KS1611A7NotTrans : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L →
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) →
      ∀ (hAab : IsMulCommutative A) (hcA : c ∈ A), Item142 A (lB A) c L hAab hcA →
        ¬ TransOn A (lB A) (xA A) (Subgroup.normalizer (Subgroup.zpowers c : Set G))

@[expose] def KS1611M22NotTrans : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L →
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22) →
      ∀ (hAab : IsMulCommutative A) (hcA : c ∈ A), Item142 A (lB A) c L hAab hcA →
        ¬ TransOn A (lB A) (xA A) (Subgroup.normalizer (Subgroup.zpowers c : Set G))

@[expose] def KS1611M12NotTrans : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L →
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M12) →
      ∀ (hAab : IsMulCommutative A) (hcA : c ∈ A), Item142 A (lB A) c L hAab hcA →
        ¬ TransOn A (lB A) (xA A) (Subgroup.normalizer (Subgroup.zpowers c : Set G))

@[expose] def KS1611OddNotTrans : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ (p e : ℕ) [Fact p.Prime], p ≠ 2 → 1 ≤ e →
      Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e →
      Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L) →
      ∀ (hAab : IsMulCommutative A) (hcA : c ∈ A), Item142 A (lB A) c L hAab hcA →
        ¬ TransOn A (lB A) (xA A) (Subgroup.normalizer (Subgroup.zpowers c : Set G))

theorem step1611List_of
    (h131 : Item131) (hHJ : KS169HJNotTrans)
    (hA7 : KS1611A7NotTrans) (hM22 : KS1611M22NotTrans) (hM12 : KS1611M12NotTrans)
    (hOdd : KS1611OddNotTrans) : Step1611List := by
  intro G _ _ A c L h h142 hn
  have hD := h.toSec13Data
  have hcL : c ∉ L := h.hypS.2.2 c h.zpowers_mem_omegaA L h.mem_lA
  have hspor := sporadicModels131
  have hM12p := hspor.2.1.1
  have hJ2p := hspor.2.2.1
  rcases cases131 h131 hspor slTwoCenter hD with
    ⟨-, -, hprod, ⟨hL3, -⟩ | ⟨hA, -⟩ | ⟨hM, -⟩⟩ | ⟨-, -, hS, -⟩ | ⟨-, hPGL, -⟩ | ⟨hcL', -⟩
  · obtain ⟨p, e, hp, he, hiso⟩ := hL3
    by_cases hp2 : p = 2
    · subst hp2
      exact absurd (Or.inr ⟨e, he, hiso, hprod⟩) hn
    · exact hOdd G A c L h p e hp2 he hiso hprod h.isElemAbelian.1 h.mem_A h142
  · exact hA7 G A c L h hA h.isElemAbelian.1 h.mem_A h142
  · exact hM22 G A c L h hM h.isElemAbelian.1 h.mem_A h142
  · rcases hS with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
    · exact hM12 G A c L h (nonempty_thetaQuot_equiv hD hM12p φ) h.isElemAbelian.1 h.mem_A
        h142
    · exact hHJ G A c L h (nonempty_thetaQuot_equiv hD hJ2p φ) h.isElemAbelian.1 h.mem_A h142
  · exact absurd (Or.inl hPGL) hn
  · exact absurd hcL' hcL

end CFSG.RankThree.PartTwo.Sec16
