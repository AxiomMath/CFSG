module

public import CFSG.RankThree.PartTwo.Sec21.Hering233iExt
public import CFSG.RankThree.PartTwo.Sec21.Hering233iSL2
public import CFSG.RankThree.PartTwo.Sec21.Item21Early2ProofCenter
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44End
import CFSG.RankThree.PartTwo.Sec4.Census.Item44PartOne
import CFSG.RankThree.PartTwo.Sec4.T444.Step452

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering233i

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)
open scoped MatrixGroups

theorem isSimpleGroup_SL3_three : IsSimpleGroup SL(3, ZMod 3) := by
  have h : IsSimpleGroup (SL(3, ZMod 3) ⧸ Subgroup.center SL(3, ZMod 3)) :=
    Sec4.Census.isQuasisimple_SL3_three.2.1
  exact ((QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq Sec4.Census.center_SL3_three.symm))).isSimpleGroup

theorem exists_not_commute_SL3_three : ∃ a b : SL(3, ZMod 3), a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := Sec4.Census.isQuasisimple_SL3_three.2.2
  let eq : SL(3, ZMod 3) ⧸ Subgroup.center SL(3, ZMod 3) ≃* SL(3, ZMod 3) :=
    (QuotientGroup.quotientMulEquivOfEq Sec4.Census.center_SL3_three).trans
      QuotientGroup.quotientBot
  exact ⟨eq a, eq b, fun h => hab (eq.injective (by rw [map_mul, map_mul]; exact h))⟩

theorem isQuasisimple_of_quotient_SL3 {X : Type*} [Group X] [Group.IsPerfect X]
    {N : Subgroup X} [N.Normal] (hN : N ≤ Subgroup.center X)
    (e : X ⧸ N ≃* SL(3, ZMod 3)) : IsQuasisimple X := by
  haveI : IsSimpleGroup (X ⧸ N) := by
    haveI := isSimpleGroup_SL3_three
    exact e.isSimpleGroup
  obtain ⟨a, b, hab⟩ := exists_not_commute_SL3_three
  exact Item21EarlyProof.isQuasisimple_of_le_center
    ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩ hN

open Item21EarlyProof Item21Early2Proof in
theorem isQuasisimple_of_item44 (h44 : Sec4.Item4_4)
    {X : Type} [Group X] [Finite X] [hXp : Group.IsPerfect X] (hX4 : SectionFourHyp X)
    (hq : IsQuasisimple (X ⧸ aschbacherSolvableCore 3 X))
    (hO2 : CFSG.pCore 2 X ≤ Subgroup.center X) {S : Subgroup X} [IsSimpleGroup S]
    (hSnc : ∃ x ∈ S, ∃ y ∈ S, x * y ≠ y * x) {u v : X} (hu : u ∈ S) (hv : v ∈ S) (hu1 : u ≠ 1)
    (hv1 : v ≠ 1) (huv : u ≠ v) (hu2 : u * u = 1) (hv2 : v * v = 1)
    (hlin : CFSG.pCore 2 X = ⊥ → ¬ IsQuasisimple X → ∀ p : ℕ, p.Prime →
      Subgroup.centralizer (CFSG.pCore p X : Set X) ≤ centerPre (aschbacherSolvableCore 3 X) →
        ∃ (N : Subgroup X) (_ : N.Normal), Sec4.Census.LinearOutcome X p N) :
    IsQuasisimple X := by
  obtain ⟨hTs, -, hT3, -⟩ := solvable_prime_complement_core_characterization (H := X)
    Nat.prime_three
  set T := aschbacherSolvableCore 3 X with hTdef
  set K₀ := centerPre T with hK₀
  have hK₀s : Group.IsSolvable K₀ := isSolvable_centerPre T hTs
  have : IsSimpleGroup ((X ⧸ T) ⧸ Subgroup.center (X ⧸ T)) := hq.2.1
  have : IsSimpleGroup (X ⧸ K₀) := (centerPreEquiv T).isSimpleGroup
  have hO3 : CFSG.pCore 3 X ≤ Subgroup.center X := pCore_three_le_center T hT3
  by_contra hQ
  have hSN : ∀ N : Subgroup X, N.Normal → Group.IsSolvable N → S ⊓ N = ⊥ := fun N hN hNs =>
    inf_eq_bot_of_simple hSnc (by rw [Subgroup.normalizer_eq_top]; exact le_top) hNs
  rcases h44 X hX4 hXp K₀ hK₀s inferInstance with
    h1 | he2 | ⟨p, hp, hp3, he3⟩ | (he4 | h4b) | ⟨hO2', h5⟩
  ·
    exact hQ (isQuasisimple_of_quotient_pCore_two hq h1 hO2)
  ·
    obtain ⟨e⟩ := he2
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    exact false_of_sl2_quotient (p := 5) (by norm_num) e
      (hSN _ inferInstance Sec4.isSolvable_oTwoFitting) hu hv hu1 hv1 huv hu2 hv2
  ·
    obtain ⟨e⟩ := he3
    haveI : Fact p.Prime := ⟨hp⟩
    exact false_of_sl2_quotient (p := p) (by omega) e
      (hSN _ inferInstance (Sec4.isSolvable_oTwoP p)) hu hv hu1 hv1 huv hu2 hv2
  ·
    obtain ⟨e⟩ := he4
    have hR : Sec4.oTwoP 3 X ≤ Subgroup.center X := oTwoP_le_center hO2 hO3
    exact hQ (isQuasisimple_of_quotient_SL3 hR (e.trans Sec4.Census.sl3EquivProjSL.symm))
  ·
    exact false_of_isExtOf_oTwoP hO2 hO3 h4b
  ·
    obtain ⟨p₀, hp₀, hS₀⟩ := Sec4.Census.exists_centralizer_pCore_le hK₀s hQ
    rcases Sec4.Census.linear_endgame hK₀s hO2' hp₀ hS₀ (hlin hO2' hQ) with ⟨⟨e⟩⟩ |
        ⟨p, hp, hp3, ⟨e⟩⟩ | ⟨⟨e⟩⟩
    ·
      haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      haveI : Group.IsNilpotent (fittingSubgroup X) := CFSG.fittingSubgroup_nilpotent
      haveI := CFSG.fittingSubgroup_normal (G := X)
      exact false_of_sl2_quotient (p := 5) (by norm_num) e (hSN _ inferInstance inferInstance)
        hu hv hu1 hv1 huv hu2 hv2
    ·
      haveI : Fact p.Prime := ⟨hp⟩
      haveI : Group.IsNilpotent (CFSG.pCore p X) := CFSG.pCore_isNilpotent
      exact false_of_sl2_quotient (p := p) (by omega) e (hSN _ inferInstance inferInstance)
        hu hv hu1 hv1 huv hu2 hv2
    ·
      exact hQ (isQuasisimple_of_quotient_SL3 hO3 e)

end CFSG.RankThree.PartTwo.Sec21.Hering233i
