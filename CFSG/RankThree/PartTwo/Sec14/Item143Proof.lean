module

public import CFSG.RankThree.PartTwo.Sec14.Concl143Std
public import CFSG.RankThree.PartTwo.Sec14.Concl143HJ
import CFSG.RankThree.PartTwo.Sec14.Item148ProofNHJ
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
public import CFSG.Sporadic.J2

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

section Point

variable {A L : Subgroup G} {c : G}

theorem item143NAt_of_lB_eq_bot (hbal : Step143Balance) (h : Sec14Std G A c L) {a : G}
    (ha : a ∈ A) (ha1 : a ≠ 1) (hΩ : Subgroup.zpowers a ∉ omegaA A)
    (hLB : ∀ B : Subgroup G, IsHyperplane A B → a ∈ B → lB A B = ⊥) :
    Item143NAt A (lB A) a :=
  fun Q hQ => ⟨concl143_at_of_lB_eq_bot hbal h ha ha1 hΩ hLB Q hQ,
    Or.inl (delta_eq_sup_of_lB_eq_bot hbal h ha ha1 hΩ hLB)⟩

theorem forall_lB_eq_bot_or_exists_isLBConfig (A : Subgroup G) (a : G) :
    (∀ B : Subgroup G, IsHyperplane A B → a ∈ B → lB A B = ⊥) ∨
      ∃ (B : Subgroup G) (b d : G) (Lb : Subgroup G), IsHyperplane A B ∧ a ∈ B ∧
        IsLBConfig A B b d Lb := by
  by_cases hall : ∀ B : Subgroup G, IsHyperplane A B → a ∈ B → lB A B = ⊥
  · exact Or.inl hall
  · push Not at hall
    obtain ⟨B, hB, haB, hne⟩ := hall
    obtain ⟨b, d, Lb, hc⟩ := exists_isLBConfig_of_lB_ne_bot hne
    exact Or.inr ⟨B, b, d, Lb, hB, haB, hc⟩

end Point

section Std

variable {A L : Subgroup G} {c : G}

theorem item143N_of_steps (hbal : Step143Balance) (hHJ : Step143HJ) (h : Sec14Std G A c L) :
    Item143N A (lB A) := by
  refine item143N_iff_forall_at.mpr fun a ha ha1 hΩ => ?_
  rcases forall_lB_eq_bot_or_exists_isLBConfig A a with hLB | ⟨B, b, d, Lb, hB, haB, hc⟩
  · exact item143NAt_of_lB_eq_bot hbal h ha ha1 hΩ hLB
  · exact hHJ G A c L h a ha ha1 hΩ B b d Lb hB haB hc

theorem concl143_of_steps (hbal : Step143Balance) (hmem : Step143HJMem) (h : Sec14Std G A c L) :
    Concl143 A (lB A) := by
  intro a ha ha1 hΩ
  rcases forall_lB_eq_bot_or_exists_isLBConfig A a with hLB | ⟨B, b, d, Lb, hB, haB, hc⟩
  · exact concl143_at_of_lB_eq_bot hbal h ha ha1 hΩ hLB
  · exact hmem G A c L h a ha ha1 hΩ B b d Lb hB haB hc

section Certificates


theorem lB_eq_bot_of_not_allPointsHJ' (h134 : Item134) (h48 : Sec4.Item4_8)
    (h : Sec14Std G A c L) (hNHJ : ¬ AllPointsHJ A) {B : Subgroup G} (hB : IsHyperplane A B) :
    lB A B = ⊥ :=
  lB_eq_bot_of_not_allPointsHJ h134 CFSG.Sporadic.J2.isSimpleGroup_J2 h48
    Sec4.Sporadic.rank3II_4_15 (KFacts.KS14.center_nativeJ2_eq_bot Sec4.Sporadic.rank3II_4_15) h
    hNHJ hB

theorem concl143_of_not_allPointsHJ (hbal : Step143Balance) (h134 : Item134)
    (h48 : Sec4.Item4_8) (h : Sec14Std G A c L) (hNHJ : ¬ AllPointsHJ A) : Concl143 A (lB A) :=
  concl143_of_lB_eq_bot hbal h fun _ hB => lB_eq_bot_of_not_allPointsHJ' h134 h48 h hNHJ hB

theorem item143N_of_not_allPointsHJ (hbal : Step143Balance) (h134 : Item134)
    (h48 : Sec4.Item4_8) (h : Sec14Std G A c L) (hNHJ : ¬ AllPointsHJ A) :
    Item143N A (lB A) :=
  item143N_iff_forall_at.mpr fun _ ha ha1 hΩ => item143NAt_of_lB_eq_bot hbal h ha ha1 hΩ
    fun _ hB _ => lB_eq_bot_of_not_allPointsHJ' h134 h48 h hNHJ hB

end Certificates

end Std

theorem concl143NHJS14_of
    (hbal : Step143Balance)
    (h134 : Item134) (h48 : Sec4.Item4_8) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec14Std G A c L → ¬ AllPointsHJ A → Concl143 A (lB A) :=
  fun _ _ _ _ _ _ h hNHJ => concl143_of_not_allPointsHJ hbal h134 h48 h hNHJ

theorem item143NNHJS14_of
    (hbal : Step143Balance)
    (h134 : Item134) (h48 : Sec4.Item4_8) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec14Std G A c L → ¬ AllPointsHJ A → Item143N A (lB A) :=
  fun _ _ _ _ _ _ h hNHJ => item143N_of_not_allPointsHJ hbal h134 h48 h hNHJ

end CFSG.RankThree.PartTwo.Sec14
