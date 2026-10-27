module

public import CFSG.LocalAnalysis.ZStar.PrincipalBlockCandidate

public section

namespace CFSG

namespace ZStar.OddNormalBlock

open ZStar.Helpers ZStar

universe u

variable {G : Type u} [Group G] [Fintype G]

noncomputable local instance subgroupFintype (N : Subgroup G) : Fintype N :=
  Fintype.ofFinite N

private noncomputable def oddNormalSum (N : Subgroup G) : GroupAlgebraTwo G :=
  ∑ n : N, MonoidAlgebra.single (n : G) 1

private theorem single_mul_oddNormalSum (N : Subgroup G) (n : N) :
    MonoidAlgebra.single (n : G) 1 * oddNormalSum N = oddNormalSum N := by
  classical
  unfold oddNormalSum
  rw [Finset.mul_sum]
  simp_rw [MonoidAlgebra.single_mul_single, one_mul]
  simpa using
    (Equiv.sum_comp (Equiv.mulLeft n)
      (fun x : N => MonoidAlgebra.single (x : G) 1))

private def normalConjEquiv (N : Subgroup G) [N.Normal] (g : G) : N ≃ N where
  toFun n := ⟨g * (n : G) * g⁻¹,
    (inferInstance : N.Normal).conj_mem n n.property g⟩
  invFun n := ⟨g⁻¹ * (n : G) * g,
    (inferInstance : N.Normal).conj_mem' n n.property g⟩
  left_inv n := by
    apply Subtype.ext
    dsimp
    group
  right_inv n := by
    apply Subtype.ext
    dsimp
    group

private theorem oddNormalSum_central (N : Subgroup G) [N.Normal] :
    IsGroupCentral G (oddNormalSum N) := by
  classical
  intro g
  unfold oddNormalSum
  rw [Finset.mul_sum, Finset.sum_mul]
  simp_rw [MonoidAlgebra.single_mul_single, one_mul]
  apply Fintype.sum_equiv (normalConjEquiv N g)
  intro n
  congr 1
  change g * (n : G) = (g * (n : G) * g⁻¹) * g
  group

private theorem oddNormalSum_idempotent (N : Subgroup G)
    (hNodd : Odd (Nat.card N)) :
    oddNormalSum N * oddNormalSum N = oddNormalSum N := by
  classical
  change (∑ n : N, MonoidAlgebra.single (n : G) 1) * oddNormalSum N =
    oddNormalSum N
  rw [Finset.sum_mul]
  simp_rw [single_mul_oddNormalSum N]
  rw [Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul (ZMod 2)]
  have hcast : (Fintype.card N : ZMod 2) = 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact hNodd.natCast_zmod_two
  rw [hcast, one_smul]

private theorem oddNormalSum_augmentation (N : Subgroup G)
    (hNodd : Odd (Nat.card N)) :
    augmentationTwo G (oddNormalSum N) = 1 := by
  rw [← augmentationHom_apply]
  calc
    augmentationHom G (oddNormalSum N) =
        ∑ n : N, augmentationHom G (MonoidAlgebra.single (n : G) 1) := by
      rw [oddNormalSum, map_sum]
    _ = ∑ _ : N, (1 : ZMod 2) := by
      apply Finset.sum_congr rfl
      intro n hn
      simp [augmentationHom, MonoidAlgebra.lift_single]
    _ = (Nat.card N : ZMod 2) := by
      simp only [Finset.sum_const, Finset.card_univ]
      rw [nsmul_one, Nat.card_eq_fintype_card]
    _ = 1 := hNodd.natCast_zmod_two

theorem single_mul_principalBlockCandidate_of_mem
    (N : Subgroup G) [N.Normal] (hNodd : Odd (Nat.card N)) (n : N) :
    MonoidAlgebra.single (n : G) 1 * principalBlockCandidate G =
      principalBlockCandidate G := by
  let q := oddNormalSum N
  let e := principalBlockCandidate G
  have hqcentral : IsGroupCentral G q := oddNormalSum_central N
  have hqidempotent : q * q = q := oddNormalSum_idempotent N hNodd
  have hqaugmentation : augmentationHom G q = 1 := by
    rw [augmentationHom_apply]
    exact oddNormalSum_augmentation N hNodd
  have heq : e * q = e :=
    principalBlockCandidate_mul_eq_self_of_augmentation_one
      G q hqcentral hqidempotent hqaugmentation
  have hqe : q * e = e := by
    calc
      q * e = e * q := (hqcentral.commute G e).eq
      _ = e := heq
  calc
    MonoidAlgebra.single (n : G) 1 * e =
        MonoidAlgebra.single (n : G) 1 * (q * e) := by rw [hqe]
    _ = (MonoidAlgebra.single (n : G) 1 * q) * e := by
      rw [mul_assoc]
    _ = q * e := by rw [single_mul_oddNormalSum N n]
    _ = e := hqe

theorem mem_algebraStabilizer_principalBlockCandidate
    (N : Subgroup G) [N.Normal] (hNodd : Odd (Nat.card N))
    {n : G} (hn : n ∈ N) :
    n ∈ algebraStabilizer G (principalBlockCandidate G) := by
  exact single_mul_principalBlockCandidate_of_mem N hNodd ⟨n, hn⟩

end ZStar.OddNormalBlock

end CFSG
