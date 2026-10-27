module

public import CFSG.Permutation.FiveTransitive.HighDegreeOddMaxSevenExclusion
public import CFSG.Permutation.FiveTransitive.MaximalInvolutionSylowCard

public section

namespace CFSG

namespace FiveTransitive.HighDegreeOddLargeFixityEntrance

open MulAction

theorem exists_entrance
    (X : Type) [Fintype X] [DecidableEq X]
    (G : Subgroup (Equiv.Perm X)) (hcard : 28 ≤ Fintype.card X)
    (h5 : IsMultiplyPretransitive G X 5) (hnotAlt : ¬ alternatingGroup X ≤ G)
    (hodd : Odd (Fintype.card X)) :
    ∃ H : Subgroup (Equiv.Perm X), H ≤ G ∧ IsSimpleGroup H ∧
      ¬ IsMulCommutative H ∧ IsMultiplyPretransitive H X 5 ∧
      ¬ alternatingGroup X ≤ H ∧ (∀ h : H, Equiv.Perm.sign h.val = 1) ∧
      ∃ t : H, orderOf t = 2 ∧
        9 ≤ (fixedBy X t).ncard ∧ 2 * (fixedBy X t).ncard ≤ Fintype.card X ∧
        (fixedBy X t).ncard % 4 = Fintype.card X % 4 ∧
        (∀ u : H, orderOf u = 2 → (fixedBy X u).ncard ≤ (fixedBy X t).ncard) ∧
        ∃ Q : Sylow 2 (fixingSubgroup H (fixedBy X t)),
          (∃ q : Q, q.val.val = t) ∧ fixedPoints Q X = fixedBy X t ∧
          (∀ (q : Q) (x : X), x ∉ fixedBy X t → q • x = x → q = 1) ∧
          (∀ q : Q, q ≠ 1 → fixedBy X q = fixedBy X t) ∧
          Nat.card Q ∣ Nat.card X - (fixedBy X t).ncard ∧
          2 ≤ Nat.card Q ∧ Nat.card Q ≤ Nat.card X - (fixedBy X t).ncard := by
  classical
  obtain ⟨H,hHG,hsimple,hnoncomm,_,hH5,hHnot,heven⟩ :=
    HighDegreeOddEvenSocle.exists_subgroup X G hcard h5 hnotAlt hodd
  let _ : IsSimpleGroup H := hsimple
  obtain ⟨t₀,ht₀,hnine⟩ :=
    HighDegreeOddMaxSevenExclusion.exists_involution_fixed_ge_nine X H hcard hH5 hHnot hodd
  obtain ⟨t,ht,hle,hmax⟩ := MaximalInvolutionFixedSet.exists_maximal_involution H X t₀ ht₀
  have htne : t.val ≠ 1 := by
    intro h
    have he : t = 1 := Subtype.ext h
    rw [he, orderOf_one] at ht
    norm_num at ht
  have hsupport := HighDegreeManningSupport.degree_le_two_mul_support H hcard hH5 hHnot
    t.property htne
  have hfixed : (fixedBy X t).ncard = Fintype.card X - t.val.support.card := by
    rw [← Nat.card_coe_set_eq]
    change Nat.card (Function.fixedPoints t.val) = _
    rw [Nat.card_eq_fintype_card, Equiv.Perm.card_fixedPoints, Equiv.Perm.sum_cycleType]
  have hsle := Finset.card_le_univ t.val.support
  have hhalf : 2 * (fixedBy X t).ncard ≤ Fintype.card X := by omega
  have hproper : (fixedBy X t).ncard < Nat.card X := by
    rw [Nat.card_eq_fintype_card]
    omega
  obtain ⟨Q,hcontains,hQfix,hfree,hdvd,hQtwo,hQle⟩ :=
    MaximalInvolutionSylowCard.exists_sylow_fixing_set H X t ht hproper hmax
  refine ⟨H,hHG,hsimple,hnoncomm,hH5,hHnot,heven,t,ht,hnine.trans hle,hhalf,
    SimpleActionEven.fixed_card_mod_four hnoncomm t ht,hmax,Q,hcontains,hQfix,hfree,?_,
    hdvd,hQtwo,hQle⟩
  intro q hq
  ext x
  constructor
  · intro hx
    by_contra hxt
    exact hq (hfree q x hxt hx)
  · intro hx
    rw [← hQfix] at hx
    exact mem_fixedPoints.mp hx q

end FiveTransitive.HighDegreeOddLargeFixityEntrance

end CFSG
