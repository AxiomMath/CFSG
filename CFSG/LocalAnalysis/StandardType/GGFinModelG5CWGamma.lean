module

public import CFSG.LocalAnalysis.StandardType.GGFinModelG5Defs

public section

namespace CFSG.StandardType.GGFinModel.G5

open CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.Open CFSG.Assembly CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Assembly.LowTwoRank

section CWGamma

private instance g5_f4RankNeZero : NeZero (Tag.rank .F4) := ⟨by decide⟩

private lemma g5_e6_orbitWord_zero :
    TwistTag.E6.orbitWord (0 : Fin TwistTag.E6.foldedTag.rank) = [0, 5] := by decide

private lemma g5_e6_orbitWord_one :
    TwistTag.E6.orbitWord (1 : Fin TwistTag.E6.foldedTag.rank) = [2, 4] := by decide

private lemma g5_e6_orbitWord_two :
    TwistTag.E6.orbitWord (2 : Fin TwistTag.E6.foldedTag.rank) = [3] := by decide

private lemma g5_e6_orbitWord_three :
    TwistTag.E6.orbitWord (3 : Fin TwistTag.E6.foldedTag.rank) = [1] := by decide

private lemma g5_e6_orbitReflection_zero :
    TwistTag.E6.orbitReflection (0 : Fin TwistTag.E6.foldedTag.rank) =
      (coxeterSystem TwistTag.E6.tag).simple (0 : Fin 6) *
        (coxeterSystem TwistTag.E6.tag).simple (5 : Fin 6) := by
  unfold TwistTag.orbitReflection
  rw [g5_e6_orbitWord_zero, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_cons,
    CoxeterSystem.wordProd_nil, mul_one]
  rfl

private lemma g5_e6_orbitReflection_one :
    TwistTag.E6.orbitReflection (1 : Fin TwistTag.E6.foldedTag.rank) =
      (coxeterSystem TwistTag.E6.tag).simple (2 : Fin 6) *
        (coxeterSystem TwistTag.E6.tag).simple (4 : Fin 6) := by
  unfold TwistTag.orbitReflection
  rw [g5_e6_orbitWord_one, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_cons,
    CoxeterSystem.wordProd_nil, mul_one]
  rfl

private lemma g5_e6_orbitReflection_two :
    TwistTag.E6.orbitReflection (2 : Fin TwistTag.E6.foldedTag.rank) =
      (coxeterSystem TwistTag.E6.tag).simple (3 : Fin 6) := by
  unfold TwistTag.orbitReflection
  rw [g5_e6_orbitWord_two, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil, mul_one]
  rfl

private lemma g5_e6_orbitReflection_three :
    TwistTag.E6.orbitReflection (3 : Fin TwistTag.E6.foldedTag.rank) =
      (coxeterSystem TwistTag.E6.tag).simple (1 : Fin 6) := by
  unfold TwistTag.orbitReflection
  rw [g5_e6_orbitWord_three, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil, mul_one]
  rfl

private lemma g5_e6_orbitReflection_subset :
    Set.range TwistTag.E6.orbitReflection ⊆
      ({(coxeterSystem TwistTag.E6.tag).simple (1 : Fin 6),
        (coxeterSystem TwistTag.E6.tag).simple (3 : Fin 6),
        (coxeterSystem TwistTag.E6.tag).simple (2 : Fin 6) *
          (coxeterSystem TwistTag.E6.tag).simple (4 : Fin 6),
        (coxeterSystem TwistTag.E6.tag).simple (0 : Fin 6) *
          (coxeterSystem TwistTag.E6.tag).simple (5 : Fin 6)} : Set (WeylGroup TwistTag.E6.tag)) := by
  rintro x ⟨a, rfl⟩
  have ha : a = (0 : Fin TwistTag.E6.foldedTag.rank) ∨
      a = (1 : Fin TwistTag.E6.foldedTag.rank) ∨
      a = (2 : Fin TwistTag.E6.foldedTag.rank) ∨
      a = (3 : Fin TwistTag.E6.foldedTag.rank) := by
    fin_cases a <;> decide
  rcases ha with rfl | rfl | rfl | rfl
  · rw [g5_e6_orbitReflection_zero]; simp
  · rw [g5_e6_orbitReflection_one]; simp
  · rw [g5_e6_orbitReflection_two]; simp
  · rw [g5_e6_orbitReflection_three]; simp

theorem ggG5_cwgamma_gen
    (u : WeylGroup TwistTag.E6.tag) (hu : weylTwist TwistTag.E6 u = u) :
    u ∈ Subgroup.closure
      ({(coxeterSystem TwistTag.E6.tag).simple (1 : Fin 6),
        (coxeterSystem TwistTag.E6.tag).simple (3 : Fin 6),
        (coxeterSystem TwistTag.E6.tag).simple (2 : Fin 6) *
          (coxeterSystem TwistTag.E6.tag).simple (4 : Fin 6),
        (coxeterSystem TwistTag.E6.tag).simple (0 : Fin 6) *
          (coxeterSystem TwistTag.E6.tag).simple (5 : Fin 6)} : Set (WeylGroup TwistTag.E6.tag)) := by
  have hu' : u ∈ Subgroup.closure (Set.range TwistTag.E6.orbitReflection) := by
    rw [← relWeylTwist_eq_closure]
    exact (mem_relWeylTwist TwistTag.E6).2 hu
  exact Subgroup.closure_mono g5_e6_orbitReflection_subset hu'

end CWGamma

end CFSG.StandardType.GGFinModel.G5
