module

public import CFSG.Permutation.FiveTransitive.CharacteristicSimplePower
public import CFSG.Permutation.FiveTransitive.SemiregularNormalTwo
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG

namespace FiveTransitive.PerfectCharacteristicSimpleTwo

open FiveTransitive.CharacteristicSimplePower

private theorem isCancelSMul_of_transitive_centralizer
    (A X : Type*) [Group A] [MulAction A X] [FaithfulSMul A X]
    (N : Subgroup A)
    (hCtrans : MulAction.IsPretransitive (Subgroup.centralizer (N : Set A)) X) :
    IsCancelSMul N X := by
  apply isCancelSMul_iff_eq_one_of_smul_eq.mpr
  intro a x hax
  apply Subtype.ext
  apply FaithfulSMul.eq_of_smul_eq_smul (α := X)
  intro y
  obtain ⟨c, rfl⟩ := hCtrans.exists_smul_eq x y
  change (a : A) • ((c : A) • x) = (1 : A) • ((c : A) • x)
  have hcomm : (a : A) * (c : A) = (c : A) * (a : A) :=
    Subgroup.mem_centralizer_iff.mp c.property (a : A) a.property
  rw [← mul_smul, hcomm, mul_smul]
  simp only [Subgroup.smul_def] at hax
  rw [hax]
  simp

theorem isSimpleGroup_of_perfect_characteristically_simple_two
    (A X : Type*) [Group A] [Finite A] [Nontrivial A] [Fintype X]
    [Group.IsPerfect A] [MulAction A X] [FaithfulSMul A X]
    (hcard : 2 ≤ Fintype.card X)
    (h2 : MulAction.IsMultiplyPretransitive A X 2)
    (hchar : ∀ H : Subgroup A, H.Characteristic → H = ⊥ ∨ H = ⊤) :
    IsSimpleGroup A := by
  classical
  let _ : Nontrivial X := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  let _ : MulAction.IsPreprimitive A X :=
    MulAction.isPreprimitive_of_is_two_pretransitive h2
  obtain ⟨s, N, hNs, hNsimple, hnorm, hiso, hind, hsup⟩ :=
    exists_sSupIndep_isSimpleGroup hchar
  let _ : N.Normal := hnorm N hNs
  let _ : IsSimpleGroup N := hNsimple
  have hNnoncomm : ¬ IsMulCommutative N := by
    intro hNcomm
    apply Group.IsPerfect.not_isMulCommutative A
    let _ : Finite (Subgroup A) :=
      Finite.of_injective (fun H : Subgroup A => (H : Set A)) SetLike.coe_injective
    let _ : Fintype s := Fintype.ofFinite _
    have hind' : iSupIndep (fun i : s => (i : Subgroup A)) :=
      (sSupIndep_iff s).1 hind
    have hsup' : (⨆ i : s, (i : Subgroup A)) = ⊤ := by
      rw [← sSup_eq_iSup' s, hsup]
    let e := (nonempty_mulEquivPi (fun i : s => hnorm i i.2) hind' hsup').some
    apply IsMulCommutative.of_comm
    intro a b
    apply e.injective
    simp only [map_mul]
    funext i
    let f : (i : Subgroup A) ≃* N := (hiso i i.2).some
    apply f.injective
    simp only [Pi.mul_apply, map_mul]
    exact isMulCommutative_iff.mp hNcomm _ _
  have hCbot : Subgroup.centralizer (N : Set A) = ⊥ := by
    by_contra hC
    let C : Subgroup A := Subgroup.centralizer (N : Set A)
    let _ : Nontrivial C := C.nontrivial_iff_ne_bot.mpr hC
    have hCtrans : MulAction.IsPretransitive C X := by
      apply MulAction.IsQuasiPreprimitive.isPretransitive_of_normal
      intro hfixed
      apply not_subsingleton C
      constructor
      intro a b
      apply Subtype.ext
      apply FaithfulSMul.eq_of_smul_eq_smul (α := X)
      intro x
      have hx : x ∈ MulAction.fixedPoints C X := by
        rw [hfixed]
        exact Set.mem_univ x
      exact ((MulAction.mem_fixedPoints.mp hx) a).trans
        ((MulAction.mem_fixedPoints.mp hx) b).symm
    let _ : IsCancelSMul N X := isCancelSMul_of_transitive_centralizer A X N hCtrans
    exact hNnoncomm (FiveTransitive.SemiregularNormalTwo.isMulCommutative_of_simple A X h2 N)
  have hrest : sSup (s \ {N}) ≤ Subgroup.centralizer (N : Set A) :=
    le_centralizer_of_normal_of_disjoint (hnorm N hNs)
      (Subgroup.sSup_normal _ fun K hK => hnorm K hK.1) (hind hNs)
  have hall : N ⊔ sSup (s \ {N}) = ⊤ := by
    rw [← sSup_insert, Set.insert_sdiff_singleton, Set.insert_eq_self.2 hNs, hsup]
  have hrestbot : sSup (s \ {N}) = ⊥ := by
    rw [hCbot] at hrest
    exact le_bot_iff.mp hrest
  have hNtop : N = ⊤ := by simpa only [hrestbot, sup_bot_eq] using hall
  have htopSimple : IsSimpleGroup (⊤ : Subgroup A) := hNtop ▸ hNsimple
  let _ := htopSimple
  exact Subgroup.topEquiv.symm.isSimpleGroup

end FiveTransitive.PerfectCharacteristicSimpleTwo

end CFSG
