module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69S7L34Basic
import CFSG.GH74.KGroups.PSL2
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactDihedralType

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Blueprint (LieModel)

theorem not_hasL34Section_mulAut_of_lieModel_psl_two {X : Type} [Group X] [Finite X] {p m : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (h : LieModel X .PSL 2 p m) :
    ¬ HasL34Section (⊤ : Subgroup (MulAut X)) := by
  have hm1 : 1 ≤ m := h.admissible.2.1
  have hm0 : m ≠ 0 := by omega
  have hpFact : Fact p.Prime := ⟨hp⟩
  obtain ⟨e⟩ := CFSG.GH74.KGroups.PSL2.psl2_equiv_of_lieModel (F := GaloisField p m) p m
    (by omega) (GaloisField.card p m hm0) h
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField p m)) :=
    ⟨p, m, hp, hp.odd_of_ne_two (by omega), hm1, GaloisField.card p m hm0⟩
  have hsol : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.outer_solvable_of_equiv
      (GaloisField p m) e
  have hdih : GorensteinWalter.HasDihedralSylowTwo X :=
    GorensteinWalter.hasDihedralSylowTwo_of_mulEquiv e
      (GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model (GaloisField p m) hodd)
  obtain ⟨S⟩ := Sylow.nonempty (p := 2) (G := X)
  refine not_hasL34Section_mulAut_of_isSolvable_outer hsol ?_
  refine not_hasL34Section_of_card_frattini_le_eight S ?_
  intro R hRS
  obtain ⟨n, hn, ⟨eD⟩⟩ := hdih S
  have hnNe : NeZero (2 ^ n) := ⟨by positivity⟩
  have hTG : CFSG.GF2Type.Aschbacher1976Common.TwoGenSubgroups ↥(S : Subgroup X) :=
    CFSG.GF2Type.Aschbacher1976Common.twoGen_of_mulEquiv eD
      (CFSG.GF2Type.Aschbacher1976Common.twoGen_dihedral (2 ^ n))
  have hR2 : IsPGroup 2 ↥R := S.isPGroup'.to_le hRS
  have h4 :=
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.card_frattini_le_four_of_twoGen hTG hRS hR2
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

end
