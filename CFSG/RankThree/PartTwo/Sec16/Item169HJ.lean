module

public import CFSG.RankThree.PartTwo.Sec16.Item16Statements
public import CFSG.RankThree.PartTwo.Sec14.Item1411Strong
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements
public import CFSG.RankThree.PartTwo.Sec15.HypR

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def Item169HJ (A : Subgroup G) (LB : Subgroup G → Subgroup G)
    (L : Subgroup G) : Prop :=
  Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
    Item169 A LB L

@[expose] def Item1610 (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  scriptY0 A LB = ∅ → scriptY3 A LB = scriptY1 A LB

@[expose] def KS169HJNotTrans : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L →
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
      ∀ (hAab : IsMulCommutative A) (hcA : c ∈ A), Item142 A (lB A) c L hAab hcA →
        ¬ TransOn A (lB A) (xA A) (Subgroup.normalizer (Subgroup.zpowers c : Set G))

theorem normalizer_pCoreOf_mem_scriptY2 {A Y : Subgroup G} (hsimp : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hY : Y ∈ scriptY2 A) :
    Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) ∈ scriptY2 A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := CFSG.Open.pCoreOf 2 Y with hP
  have hP2 : IsPGroup 2 P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y
  have hPN : P ≤ Subgroup.normalizer (P : Set G) := Subgroup.le_normalizer
  refine ⟨⟨fun htop => normalizer_ne_top_of_isPGroup hsimp hnab hY.2 hP2 htop,
    (hY.1.2.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)).trans
      Subgroup.le_normalizer⟩, fun h0 => ?_⟩
  have hPO : P ≤ CFSG.Open.pCoreOf 2 (Subgroup.normalizer (P : Set G)) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hPN le_rfl hP2
  rw [h0] at hPO
  exact hY.2 (le_bot_iff.mp hPO)

theorem isEmpty_mulEquiv_l34_of_j2 {X : Type*} [Group X]
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    IsEmpty (X ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)) := by
  obtain ⟨e⟩ := hX
  refine ⟨fun f => ?_⟩
  exact (KFacts.KS14.isEmpty_mulEquiv_projSL_three_of_card KFacts.KS14.card_nativeJ2
    (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) KFacts.KS14.checkSL_j2)
    (GaloisField 2 2)).false (e.symm.trans f)

omit [Finite G] in
theorem xA_le_normalizer_zpowers {A : Subgroup G} {c : G} (hcA : c ∈ A) :
    xA A ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
  (pPrimeCoreOf_le 3 _).trans ((Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hcA)).trans
    (centralizer_singleton_le_normalizer_zpowers c))

omit [Finite G] in
theorem le_normalizer_normalizer_zpowers {A : Subgroup G} {c : G} (hAab : IsMulCommutative A)
    (hcA : c ∈ A) :
    A ≤ Subgroup.normalizer
      ((Subgroup.normalizer (Subgroup.zpowers c : Set G) : Subgroup G) : Set G) := by
  have hAC : A ≤ Subgroup.centralizer ({c} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hAab.is_comm.comm ⟨a, ha⟩ ⟨c, hcA⟩))
  exact (hAC.trans (centralizer_singleton_le_normalizer_zpowers c)).trans Subgroup.le_normalizer

theorem rank3II_16_9_1_of_not_transOn {A : Subgroup G} {LB : Subgroup G → Subgroup G} {c : G}
    (hAab : IsMulCommutative A) (hcA : c ∈ A) (h1610 : Item1610 A LB)
    (h1411 : Item1411_3Strong A LB)
    (hNT : ¬ TransOn A LB (xA A) (Subgroup.normalizer (Subgroup.zpowers c : Set G))) :
    (scriptY0 A LB).Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have hG : ¬ TransOn A LB (xA A) ⊤ := fun htr =>
    hNT (transOn_of_transOn_top (xA_le_normalizer_zpowers hcA)
      (le_normalizer_normalizer_zpowers hAab hcA) htr)
  obtain ⟨Y, hYΔ, hY, hO2, -, hO3, -⟩ := h1411 hG
  have hY3 : Y ∈ scriptY3 A LB := ⟨⟨hY, hO2⟩, hYΔ⟩
  rw [h1610 hne] at hY3
  exact hO3 hY3.2

end CFSG.RankThree.PartTwo.Sec16
