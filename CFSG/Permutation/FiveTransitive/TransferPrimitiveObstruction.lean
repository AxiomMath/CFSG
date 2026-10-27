module

public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.GroupAction.Primitive

public section

namespace CFSG

namespace FiveTransitive.TransferPrimitiveObstruction

open MulAction

theorem false_of_small_sylow
    {G X : Type*} [Group G] [Finite G] [Finite X] [Nonempty X]
    [MulAction G X] [FaithfulSMul G X]
    [IsQuasiPreprimitive G X]
    {p : ℕ} [Fact p.Prime] (S : Sylow p G)
    (hsmall : Nat.card S < Nat.card X) (hdegree : p ∣ Nat.card X)
    (hnormalizer : Subgroup.normalizer (S : Set G) ≤ Subgroup.centralizer (S : Set G)) :
    False := by
  classical
  let x : X := Classical.choice inferInstance
  have hdegreeG : Nat.card X ∣ Nat.card G := by
    rw [← index_stabilizer_of_transitive G x]
    exact (stabilizer G x).index_dvd_card
  have hle : Nat.card X ≤ Nat.card G := Nat.le_of_dvd Nat.card_pos hdegreeG
  let f : G →* S := MonoidHom.transferSylow S hnormalizer
  let N : Subgroup G := f.ker
  let _ : N.Normal := by dsimp only [N]; infer_instance
  have hproduct : Nat.card N * Nat.card S = Nat.card G :=
    (MonoidHom.ker_transferSylow_isComplement' S hnormalizer).card_mul_card
  have hNne : N ≠ ⊥ := by
    intro he
    rw [he,Subgroup.card_bot,one_mul] at hproduct
    omega
  let _ : Nontrivial N := N.nontrivial_iff_ne_bot.mpr hNne
  have hNnotFixed : fixedPoints N X ≠ Set.univ := by
    intro hfixed
    apply not_subsingleton N
    constructor
    intro a b
    apply Subtype.ext
    apply FaithfulSMul.eq_of_smul_eq_smul (α := X)
    intro y
    have hy : y ∈ fixedPoints N X := hfixed.symm ▸ Set.mem_univ y
    exact (hy a).trans (hy b).symm
  let _ : IsPretransitive N X := IsQuasiPreprimitive.isPretransitive_of_normal hNnotFixed
  have hdegreeN : Nat.card X ∣ Nat.card N := by
    rw [← index_stabilizer_of_transitive N x]
    exact (stabilizer N x).index_dvd_card
  exact MonoidHom.not_dvd_card_ker_transferSylow S hnormalizer (hdegree.trans hdegreeN)

end FiveTransitive.TransferPrimitiveObstruction

end CFSG
