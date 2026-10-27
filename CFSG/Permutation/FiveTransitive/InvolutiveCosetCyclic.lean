module

public import CFSG.Permutation.FiveTransitive.InvolutiveCosetAlgebra
public import CFSG.Permutation.FiveTransitive.AbelianTwoCyclic

public section

namespace CFSG

namespace FiveTransitive.InvolutiveCosetCyclic

variable {G : Type*} [Group G] (Q : Subgroup G) (x : G)

private theorem isCyclic_of_centralizer_card_le_two [Finite Q] (hQ : IsPGroup 2 Q)
    (hcoset : ∀ q ∈ Q, (q * x) ^ 2 = 1)
    (hcentral : Nat.card {q : Q // Commute (q : G) x} ≤ 2) : IsCyclic Q := by
  let : CommGroup Q :=
    { (inferInstance : Group Q) with
      mul_comm := fun q r => Subtype.ext
        (InvolutiveCosetAlgebra.mul_comm Q x hcoset q.property r.property) }
  apply AbelianTwoCyclic.isCyclic_of_square_kernel_card_le_two hQ
  have he : {q : Q // q ^ 2 = 1} ≃ {q : Q // Commute (q : G) x} :=
    Equiv.subtypeEquivRight fun q => by
      rw [InvolutiveCosetAlgebra.commute_iff_square_eq_one Q x hcoset q.property]
      exact Subtype.ext_iff
  rw [Nat.card_congr he]
  exact hcentral

private theorem isCyclic_of_centralizer_card_two [Finite Q] (hQ : IsPGroup 2 Q)
    (hcoset : ∀ q ∈ Q, (q * x) ^ 2 = 1)
    (hcentral : Nat.card {q : Q // Commute (q : G) x} = 2) : IsCyclic Q :=
  isCyclic_of_centralizer_card_le_two Q x hQ hcoset hcentral.le

theorem isCyclic_of_centralizer_subgroup_card_two [Finite Q] (hQ : IsPGroup 2 Q)
    (hcoset : ∀ q ∈ Q, (q * x) ^ 2 = 1)
    (hcentral : Nat.card ((Subgroup.centralizer ({x} : Set G)).comap Q.subtype) = 2) :
    IsCyclic Q := by
  apply isCyclic_of_centralizer_card_two Q x hQ hcoset
  have he : ((Subgroup.centralizer ({x} : Set G)).comap Q.subtype) ≃
      {q : Q // Commute (q : G) x} := Equiv.subtypeEquivRight fun q => by
    simp only [Subgroup.mem_comap, Subgroup.subtype_apply,
      Subgroup.mem_centralizer_singleton_iff]
    exact (commute_iff_eq (q : G) x).symm
  rw [← Nat.card_congr he]
  exact hcentral

end FiveTransitive.InvolutiveCosetCyclic

end CFSG
