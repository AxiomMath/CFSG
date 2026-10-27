module

public import CFSG.Permutation.FiveTransitive.NormalSylowFixedFourFive
public import CFSG.Permutation.FiveTransitive.SimpleActionEven

public section

namespace CFSG

namespace FiveTransitive.HighDegreeOddEvenSocle

open MulAction

theorem exists_subgroup
    (X : Type) [Fintype X] [DecidableEq X]
    (G : Subgroup (Equiv.Perm X)) (hcard : 28 ≤ Fintype.card X)
    (h5 : IsMultiplyPretransitive G X 5) (hnotAlt : ¬ alternatingGroup X ≤ G)
    (hodd : Odd (Fintype.card X)) :
    ∃ H : Subgroup (Equiv.Perm X), H ≤ G ∧ IsSimpleGroup H ∧
      ¬ IsMulCommutative H ∧ FaithfulSMul H X ∧
      IsMultiplyPretransitive H X 5 ∧ ¬ alternatingGroup X ≤ H ∧
      ∀ h : H, Equiv.Perm.sign h.val = 1 := by
  obtain ⟨N, ⟨hNnormal, hNne, hNmin, hNsimple, hNnoncomm, hNinj, hN3, hN4⟩, _⟩ :=
    MinimalNormalFour.existsUnique_nonabelian_simple_four_transitive_minimal_normal
      X G (by omega) h5 hnotAlt
  let _ : N.Normal := hNnormal
  let _ : Nontrivial N := N.nontrivial_iff_ne_bot.mpr hNne
  let _ : IsSimpleGroup N := hNsimple
  have hN5 := NormalSylowFixedFourFive.five_transitive_of_odd X G hcard h5 hnotAlt N hodd
  let H := N.map G.subtype
  let e : N ≃* H := N.equivMapOfInjective G.subtype G.subtype_injective
  have hHG : H ≤ G := by
    rintro g ⟨n, hn, rfl⟩
    exact n.property
  have hsimple : IsSimpleGroup H := e.symm.isSimpleGroup
  let _ : IsSimpleGroup H := hsimple
  have hnoncomm : ¬ IsMulCommutative H := by
    intro hc
    apply hNnoncomm
    apply isMulCommutative_iff.mpr
    intro x y
    apply e.injective
    simp only [map_mul]
    exact isMulCommutative_iff.mp hc _ _
  have hH5 : IsMultiplyPretransitive H X 5 := by
    rw [isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨n, hn⟩ := hN5.exists_smul_eq a b
    refine ⟨e n, ?_⟩
    ext i
    exact DFunLike.congr_fun hn i
  refine ⟨H, hHG, hsimple, hnoncomm, inferInstance, hH5,
    fun h => hnotAlt (h.trans hHG), ?_⟩
  intro h
  exact SimpleActionEven.sign_eq_one (X := X) hnoncomm h

end FiveTransitive.HighDegreeOddEvenSocle

end CFSG
