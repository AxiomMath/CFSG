module

public import CFSG.RankThree.SubgroupLists.SymplecticQuaternion
public import Certificates.Certificate110
public import Certificates.Certificate43
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {p : ℕ} [Fact p.Prime]

theorem eq_one_or_eq_neg_one_of_scalar {K : Type} [Field K] {z : GL V₄ K}
    (hz : z ∈ StatedSp 2 K) {c : K} (hc : (z : Matrix V₄ V₄ K) = Matrix.scalar V₄ c) :
    z = 1 ∨ z = -1 := by
  have h := transpose_mul_spGram_mul hz
  rw [hc] at h
  have h01 := congrFun (congrFun h (Sum.inl 0)) (Sum.inr 0)
  simp [Matrix.scalar_apply, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks] at h01
  have hc2 : (c - 1) * (c + 1) = 0 := by linear_combination h01
  rcases mul_eq_zero.mp hc2 with h1 | h1
  · left
    apply Units.ext
    rw [hc, Units.val_one, show c = 1 by linear_combination h1, map_one]
  · right
    apply Units.ext
    rw [hc, Units.val_neg, Units.val_one, show c = -1 by linear_combination h1, map_neg, map_one]

theorem quasisimple_sp4_of_involutions_central (hp2 : p ≠ 2) {G : Subgroup (GL V₄ (ZMod p))}
    (hGS : G ≤ StatedSp 2 (ZMod p)) (hq : CFSG.IsQuasisimple G)
    (hcent : ∀ x ∈ G, x * x = 1 → ∀ y ∈ G, x * y = y * x) :
    Nonempty (G ≃* SL(2, ZMod p)) ∨ Nonempty (G ≃* SL(2, GaloisField p 2)) ∨
      Nonempty (G ≃* SL(2, ZMod 5)) ∨ Nonempty (G ≃* SL(2, GaloisField 3 2)) ∨
      (p = 7 ∧ Nat.card (Subgroup.center G) = 2 ∧
        Nonempty ((G ⧸ Subgroup.center G) ≃* alternatingGroup (Fin 7))) := by
  classical
  have : Group.IsPerfect G := hq.1
  by_cases hred : ∃ U : Submodule (ZMod p) (V₄ → ZMod p), IsInvariant G U ∧ U ≠ ⊥ ∧ U ≠ ⊤
  · obtain ⟨U, hU, hU0, hUt⟩ := hred
    rcases quasisimple_reducible_sp4 hp2 hGS hq hU hU0 hUt with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
  have hirr : IsIrreducibleOn G := by
    intro W hW
    by_contra h
    push Not at h
    exact hred ⟨W, hW, h.1, h.2⟩
  by_cases hC : commutant G ≠ ⊥
  · rcases perfect_irreducible_not_absolutely hp2 (by simp) hirr hC with h | h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  push Not at hC
  have hZ : ∀ z ∈ Subgroup.center G, (z : GL V₄ (ZMod p)) = 1 ∨ (z : GL V₄ (ZMod p)) = -1 := by
    intro z hz
    have hM : ((z : GL V₄ (ZMod p)) : Matrix V₄ V₄ (ZMod p)) ∈ commutant G := by
      rw [mem_commutant]
      intro g hg
      have := congrArg (fun y : G => ((y : GL V₄ (ZMod p)) : Matrix V₄ V₄ (ZMod p)))
        (Subgroup.mem_center_iff.mp hz ⟨g, hg⟩)
      simpa using this
    rw [hC, Algebra.mem_bot] at hM
    obtain ⟨c, hc⟩ := hM
    exact eq_one_or_eq_neg_one_of_scalar (hGS z.2)
      (c := c) (by rw [← hc]; simp [Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply])
  by_cases hneg : (-1 : GL V₄ (ZMod p)) ∈ G
  ·
    refine quasisimple_sp4_of_unique_involution hp2 hGS hq hZ fun x hx hx2 => ?_
    have hxc : (⟨x, hx⟩ : G) ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (hcent x hx hx2 y y.2).symm
    exact hZ _ hxc
  ·
    exfalso
    have h2 := two_dvd_card_center_of_neg_one_not_mem hp2 hGS hq hneg
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hz1 : (z : G) ≠ 1 := by
      intro h1
      have : z = 1 := Subtype.ext h1
      rw [this, orderOf_one] at hz
      omega
    rcases hZ z z.2 with h | h
    · exact hz1 (Subtype.ext h)
    · exact hneg (h ▸ (z : G).2)

end CFSG.RankThree.SubgroupLists
