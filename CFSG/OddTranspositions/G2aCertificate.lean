module

public import Certificates.Certificate1089008
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.OddTranspositions.QZ

theorem centralizer_S3_card_le_two_check :
    ∀ a b : Equiv.Perm (Fin 5), a * a = 1 → a ≠ 1 → b * b = 1 → b ≠ 1 → (a * b) ^ 3 = 1 →
      a * b ≠ 1 →
      (Finset.univ.filter fun π : Equiv.Perm (Fin 5) => π * a * π⁻¹ = a ∧ π * b * π⁻¹ = b).card ≤ 2 :=
  Certificates.certificate1089008

theorem card_aut_fix_S3_le_two
    (x y : alternatingGroup (Fin 5)) (hx : orderOf x = 2)
    (hy : orderOf y = 2) (hxy : orderOf (x * y) = 3) :
    Nat.card {σ : MulAut (alternatingGroup (Fin 5)) // σ x = x ∧ σ y = y} ≤ 2 := by
  classical
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5
    (by norm_num) (by norm_num)
  let e := Equiv.ofBijective _ hbij
  have hsub : {π : Equiv.Perm (Fin 5) // π * (x : Equiv.Perm (Fin 5)) * π⁻¹ = x ∧
      π * (y : Equiv.Perm (Fin 5)) * π⁻¹ = y} ≃
      {σ : MulAut (alternatingGroup (Fin 5)) // σ x = x ∧ σ y = y} :=
    Equiv.subtypeEquiv e fun π => by
      simp only [e, Equiv.ofBijective_apply, Subtype.ext_iff, MulAut.conjNormal_apply]
  rw [← Nat.card_congr hsub, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hx' : orderOf (x : Equiv.Perm (Fin 5)) = 2 := by rwa [Subgroup.orderOf_coe]
  have hy' : orderOf (y : Equiv.Perm (Fin 5)) = 2 := by rwa [Subgroup.orderOf_coe]
  have hxy' : orderOf ((x : Equiv.Perm (Fin 5)) * y) = 3 := by
    rw [← Subgroup.coe_mul, Subgroup.orderOf_coe]; exact hxy
  refine centralizer_S3_card_le_two_check _ _ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← sq, ← hx', pow_orderOf_eq_one]
  · rintro h; rw [h, orderOf_one] at hx'; norm_num at hx'
  · rw [← sq, ← hy', pow_orderOf_eq_one]
  · rintro h; rw [h, orderOf_one] at hy'; norm_num at hy'
  · rw [← hxy', pow_orderOf_eq_one]
  · rintro h; rw [h, orderOf_one] at hxy'; norm_num at hxy'

end CFSG.OddTranspositions.QZ

