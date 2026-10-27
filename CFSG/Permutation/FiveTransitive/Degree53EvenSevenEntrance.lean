module

public import CFSG.Permutation.FiveTransitive.Degree53NineImageExclusion
public import CFSG.Permutation.FiveTransitive.HighDegreeOddLargeFixityEntrance
public import CFSG.Permutation.FiveTransitive.OddMaximalOrderDescent
public import CFSG.Permutation.FiveTransitive.MaximalOrderFixedLowerBound
public import CFSG.Permutation.FiveTransitive.ClassifiedFixedFiveImage

public section

namespace CFSG

namespace FiveTransitive.Degree53EvenSevenEntrance
open MulAction FixedNormalizerAction

theorem exists_subgroup
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 53)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P) :
    ∃ H : Subgroup (Equiv.Perm X), H ≤ P ∧
      IsMultiplyPretransitive H X 5 ∧ ¬ alternatingGroup X ≤ H ∧
      (∀ h : H, Equiv.Perm.sign h.val = 1) ∧
      ∃ Q : Subgroup H, IsPGroup 2 Q ∧ Q ≠ ⊥ ∧
        Nat.card (Fixed (X := X) Q) = 7 ∧ Image (X := X) Q = ⊤ := by
  classical
  have hlarge : 28 ≤ Fintype.card X := by omega
  have hodd : Odd (Fintype.card X) := by rw [hcard]; decide
  obtain ⟨H,hHP,_,_,hH5,hHnot,heven,t,ht,hnine,_⟩ :=
    HighDegreeOddLargeFixityEntrance.exists_entrance X P hlarge h5 hnotAlt hodd
  let R := Subgroup.zpowers t
  have hRcard : Nat.card R = 2 := by rw [Nat.card_zpowers,ht]
  have hR : IsPGroup 2 R := IsPGroup.of_card (n := 1) (by simpa using hRcard)
  have hRfix : 6 ≤ Nat.card (fixedPoints R X) := by
    rw [OyamaSixFixedBranch.fixedPoints_zpowers_eq_fixedBy,Nat.card_coe_set_eq]
    omega
  obtain ⟨Q,hQ,hQfix,hRQ,hmax⟩ := MaximalOrderFixedLowerBound.exists_maximal 2 6 R hR hRfix
  have hQne : Q ≠ ⊥ := by
    intro he
    rw [he,Subgroup.card_bot,hRcard] at hRQ
    omega
  obtain ⟨hseven,hoddQ,hlt,hhalf,htrans,hlocal⟩ :=
    OddMaximalOrderDescent.local_structure X H hlarge hH5 hHnot hodd Q hQ hQne hQfix hmax
  let F := Fixed (X := X) Q
  let _ : Fintype F := Fintype.ofFinite F
  let J := Image (X := X) Q
  change 7 ≤ Nat.card F at hseven
  change Nat.card F ≤ Fintype.card X / 2 at hhalf
  have hclass := SmallDegreeClassification.subgroup_card_classification F J
    (by rw [← Nat.card_eq_fintype_card]; omega)
    (by rw [← Nat.card_eq_fintype_card]; rw [hcard] at hhalf; omega) htrans
  rw [← Nat.card_eq_fintype_card] at hclass
  have hpairs := ClassifiedFixedFiveImage.degree_order_pairs Q hseven hoddQ htrans hlocal hclass
  refine ⟨H,hHP,hH5,hHnot,heven,Q,hQ,hQne,?_⟩
  rcases hpairs with ⟨hF,hJ⟩ | ⟨hF,hJ⟩
  · refine ⟨hF,?_⟩
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_perm,hF,hJ]
    norm_num [Nat.factorial]
  · exact (Degree53NineImageExclusion.excluded H hcard hH5 hHnot Q hF
      (by rw [hJ]; norm_num)).elim

end FiveTransitive.Degree53EvenSevenEntrance

end CFSG
