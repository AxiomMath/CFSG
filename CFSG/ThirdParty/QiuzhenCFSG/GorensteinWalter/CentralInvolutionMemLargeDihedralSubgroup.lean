module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27Infra

namespace CFSG
end CFSG
open CFSG

/-!
# The central involution lies in every large dihedral subgroup

A subgroup of order at least eight in a dihedral `2`-group contains the
unique central involution.  This is the membership input for the final
normalizer argument in Gorenstein--Walter Theorem 2.6.
-/

namespace CFSG.GorensteinWalter

universe u

/-- Let `Q ≤ P`, where `P` is a dihedral `2`-group of order at least eight.
Every central involution of `P` belongs to `Q` as soon as `Q` has order at
least eight. -/
public theorem central_involution_mem_large_subgroup_of_dihedral
    {G : Type u} [Group G] [Finite G]
    (P Q : Subgroup G) (hQP : Q ≤ P)
    {m : ℕ} (hm : 2 ≤ m) (e : P ≃* DihedralGroup (2 ^ m))
    {z : G} (hzP : z ∈ P) (hzI : IsInvolution z)
    (hzcenter : (⟨z, hzP⟩ : P) ∈ Subgroup.center P)
    (hQcard : 8 ≤ Nat.card Q) :
    z ∈ Q := by
  let QP : Subgroup P := Q.subgroupOf P
  have hQPcard : Nat.card QP = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQP).toEquiv
  let D : Subgroup (DihedralGroup (2 ^ m)) := QP.map e.toMonoidHom
  have hDcard : Nat.card D = Nat.card QP :=
    (Nat.card_congr
      (Subgroup.equivMapOfInjective QP e.toMonoidHom e.injective).toEquiv).symm
  have hDlarge : 4 ≤ Nat.card D := by
    rw [hDcard, hQPcard]
    omega
  have hrD : DihedralGroup.r
      (2 ^ (m - 1) : ZMod (2 ^ m)) ∈ D :=
    subgroup_card_ge_four_contains_central_rotation
      (by omega : 1 ≤ m) D hDlarge
  rcases Subgroup.mem_map.mp hrD with ⟨q, hqQP, hqeq⟩
  let zP : P := ⟨z, hzP⟩
  have hezCenter : e zP ∈
      Subgroup.center (DihedralGroup (2 ^ m)) := by
    rw [Subgroup.mem_center_iff]
    intro a
    rcases e.surjective a with ⟨p, rfl⟩
    simpa using congrArg e
      (Subgroup.mem_center_iff.mp hzcenter p)
  have hezPow : (e zP) ^ 2 = 1 := by
    calc
      (e zP) ^ 2 = e (zP ^ 2) :=
        (e.toMonoidHom.map_pow zP 2).symm
      _ = 1 := by
        rw [show zP ^ 2 = 1 by
          apply Subtype.ext
          exact hzI.2]
        simp
  have hezNe : e zP ≠ 1 := by
    intro hone
    apply hzI.1
    exact congrArg Subtype.val (e.injective (by simpa using hone))
  have hez : e zP = DihedralGroup.r
      (2 ^ (m - 1) : ZMod (2 ^ m)) :=
    unique_central_involution_of_dihedral_two_pow
      hm (e zP) hezCenter hezPow hezNe
  have hzq : zP = q :=
    e.injective (hez.trans hqeq.symm)
  have hzQP : zP ∈ QP := by
    rw [hzq]
    exact hqQP
  exact Subgroup.mem_subgroupOf.mp hzQP

end CFSG.GorensteinWalter
