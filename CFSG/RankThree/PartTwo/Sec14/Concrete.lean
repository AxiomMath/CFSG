module

public import CFSG.RankThree.PartTwo.Sec14.LBNatural
public import CFSG.RankThree.PartTwo.Sec14.Item1411
public import CFSG.RankThree.PartTwo.Sec15.Item151

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

theorem Sec14Std.isE27 {c : G} {L : Subgroup G} (h : Sec14Std G A c L) : IsE27 A :=
  isE27_of_mem_partTwoE h.toSec13Data.mem_partTwoE

theorem rank3II_14_4_5_lB {w : G} (hw : w ∈ Subgroup.normalizer (A : Set G)) {Q : Subgroup G}
    (hQ : Q ∈ scriptQ A (lB A)) : Q.map (MulAut.conj w).toMonoidHom ∈ scriptQ A (lB A) :=
  rank3II_14_4_5 (isNaturalFamily_lB A) hw hQ

theorem rank3II_14_4_5_zero_lB {w : G} (hw : w ∈ Subgroup.normalizer (A : Set G))
    {Q : Subgroup G} (hQ : Q ∈ scriptQZero A (lB A)) :
    Q.map (MulAut.conj w).toMonoidHom ∈ scriptQZero A (lB A) :=
  rank3II_14_4_5_zero (isNaturalFamily_lB A) hw hQ

theorem rank3II_14_5_lB (hA : IsE27 A) (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    {Y : Subgroup G} (hY : A ≤ Subgroup.normalizer (Y : Set G)) :
    delta A (lB A) Y =
        deltaZero A (lB A) Y ⊔ (pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊓ Y) ∧
      deltaZero A (lB A) Y = ⁅delta A (lB A) Y, A⁆ ∧
      delta A (lB A) Y ≤ Subgroup.normalizer (deltaZero A (lB A) Y : Set G) :=
  rank3II_14_5 hA (isNaturalFamily_lB A) hbot hY

theorem rank3II_15_1_lB (hA : IsE27 A) (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    {Y : Subgroup G} (hY : Y ∈ Sec15.scriptY4 A (lB A)) : Y = deltaZero A (lB A) Y :=
  Sec15.rank3II_15_1 hA (isNaturalFamily_lB A) hbot hY

section Standing

variable {c : G} {L : Subgroup G}

theorem rank3II_14_11_1_lB (h : Sec14Std G A c L)
    (hloc : ∀ Y ∈ scriptY A, ∀ S ∈ scriptQPiStar A (lB A) Y (piOf 2),
      ∀ T ∈ scriptQPiStar A (lB A) Y (piOf 2),
        IsConjIn (Subgroup.normalizer (A : Set G) ⊓ Y) S T)
    {S T : Subgroup G} (hS : S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2))
    (hT : T ∈ scriptQPiStar A (lB A) ⊤ (piOf 2)) :
    IsConjIn (Subgroup.normalizer (A : Set G)) S T :=
  rank3II_14_11_1_reduction h.isSimpleGroup h.nonabelian h.isE27 (isNaturalFamily_lB A) hloc hS hT

theorem rank3II_14_11_2_lB (h : Sec14Std G A c L)
    (hloc : ∀ Y ∈ scriptY A, ∀ S ∈ scriptQPiStar A (lB A) Y (piOf 2),
      ∀ T ∈ scriptQPiStar A (lB A) Y (piOf 2),
        IsConjIn (pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊓ Y) S T)
    {S T : Subgroup G} (hS : S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2))
    (hT : T ∈ scriptQPiStar A (lB A) ⊤ (piOf 2)) :
    IsConjIn (pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))) S T :=
  rank3II_14_11_2_reduction h.isSimpleGroup h.nonabelian h.isE27 (isNaturalFamily_lB A) hloc hS hT

theorem rank3II_14_15_lB {X : Subgroup G} (hXA : X ≤ Subgroup.normalizer (A : Set G))
    (hloc : ∀ U ∈ scriptQPi A (lB A) ⊤ (piOf 2), U ≠ ⊥ →
      ∀ S ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (U : Set G)) (piOf 2),
      ∀ T ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (U : Set G)) (piOf 2),
        IsConjIn (X ⊓ Subgroup.normalizer (U : Set G)) S T)
    {S T : Subgroup G} (hS : S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2))
    (hT : T ∈ scriptQPiStar A (lB A) ⊤ (piOf 2)) (hST : ¬ IsConjIn X S T) : S ⊓ T = ⊥ :=
  rank3II_14_15_reduction (isNaturalFamily_lB A) hXA hloc hS hT hST

theorem rank3II_17_24_2_lB (h : Sec14Std G A c L) {p : ℕ} [Fact p.Prime] (hp3 : p ≠ 3)
    (hloc : ∀ Y ∈ scriptY A, ∀ S ∈ scriptQPiStar A (lB A) Y (piOf p),
      ∀ T ∈ scriptQPiStar A (lB A) Y (piOf p),
        IsConjIn (pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊓ Y) S T)
    {S T : Subgroup G} (hS : S ∈ scriptQPiStar A (lB A) ⊤ (piOf p))
    (hT : T ∈ scriptQPiStar A (lB A) ⊤ (piOf p)) :
    IsConjIn (pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))) S T :=
  rank3II_17_24_2_reduction hp3 h.isSimpleGroup h.nonabelian h.isE27 (isNaturalFamily_lB A) hloc
    hS hT

end Standing

end CFSG.RankThree.PartTwo.Sec14
