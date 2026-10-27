module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralCore
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Index bounds for normal subgroups of dihedral 2-groups

The concrete normal-subgroup classification in `DihedralCore` identifies the
non-rotation subgroups with the index-two families
`dihedralIndexTwoSubgroup m j`.  This file records the small index consequence
needed by the Proposition 9 routes: every normal subgroup is either contained
in the rotation subgroup or has index dividing `2` (and hence index at most
`2` in the non-cyclic case).

The proof computes the index of the even-rotation subgroup
`⟨r 2⟩` as `4`.  Since it is contained in every index-two family, the latter's
index divides `4`; equality with `4` would force the family to equal
`⟨r 2⟩` by the relative-index formula, contradicting the presence of a
reflection.  The remaining divisors of `4` divide `2`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

private lemma card_zpowers_r_two {m : ℕ} (hm : 1 ≤ m) :
    Nat.card (↥(Subgroup.zpowers (DihedralGroup.r (2 : ZMod (2 ^ m))))) = 2 ^ (m - 1) := by
  let : NeZero (2 ^ m) := ⟨pow_ne_zero m (by norm_num : 2 ≠ 0)⟩
  rw [Nat.card_zpowers, DihedralGroup.orderOf_r]
  have hval : (2 : ZMod (2 ^ m)).val = 2 % 2 ^ m := ZMod.val_natCast (2 ^ m) 2
  rw [hval]
  by_cases hm1 : m = 1
  · subst m
    norm_num
  · have hm2 : 2 ≤ m := by omega
    have hlt : 2 < 2 ^ m := by
      have hpow : 4 ≤ 2 ^ m := by
        simpa using (Nat.pow_le_pow_right (by decide : 0 < 2) hm2)
      omega
    rw [Nat.mod_eq_of_lt hlt]
    have hgcd : Nat.gcd (2 ^ m) 2 = 2 := by
      rw [Nat.gcd_eq_right]
      exact pow_dvd_pow 2 (by omega : 1 ≤ m)
    rw [hgcd]
    have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
      calc
        2 ^ m = 2 ^ ((m - 1) + 1) := by congr 1; omega
        _ = 2 ^ (m - 1) * 2 := by rw [pow_succ]
        _ = 2 * 2 ^ (m - 1) := by rw [mul_comm]
    rw [hpow, Nat.mul_div_right _ (by norm_num : 0 < 2)]

private lemma index_zpowers_r_two {m : ℕ} (hm : 1 ≤ m) :
    (Subgroup.zpowers (DihedralGroup.r (2 : ZMod (2 ^ m)))).index = 4 := by
  let R2 : Subgroup (DihedralGroup (2 ^ m)) :=
    Subgroup.zpowers (DihedralGroup.r (2 : ZMod (2 ^ m)))
  have hcardR2 : Nat.card (↥R2) = 2 ^ (m - 1) := card_zpowers_r_two hm
  have hindex := R2.index_mul_card
  rw [hcardR2, DihedralGroup.nat_card] at hindex
  have hpow : 2 * 2 ^ m = 4 * 2 ^ (m - 1) := by
    calc
      2 * 2 ^ m = 2 * (2 * 2 ^ (m - 1)) := by
        congr 1
        calc
          2 ^ m = 2 ^ ((m - 1) + 1) := by congr 1; omega
          _ = 2 ^ (m - 1) * 2 := by rw [pow_succ]
          _ = 2 * 2 ^ (m - 1) := by rw [mul_comm]
      _ = 4 * 2 ^ (m - 1) := by ring
  rw [hpow] at hindex
  exact Nat.eq_of_mul_eq_mul_right (pow_pos (by norm_num : 0 < 2) (m - 1)) hindex

/-- Each non-rotation normal-family subgroup has index dividing two. -/
public theorem dihedralIndexTwoSubgroup_index_dvd_two
    {m : ℕ} (hm : 1 ≤ m) (j : ZMod (2 ^ m)) :
    (dihedralIndexTwoSubgroup m j).index ∣ 2 := by
  let R2 : Subgroup (DihedralGroup (2 ^ m)) :=
    Subgroup.zpowers (DihedralGroup.r (2 : ZMod (2 ^ m)))
  let I : Subgroup (DihedralGroup (2 ^ m)) := dihedralIndexTwoSubgroup m j
  have hR2leI : R2 ≤ I := by
    intro x hx
    rw [show I = dihedralIndexTwoSubgroup m j by rfl]
    rw [mem_dihedralIndexTwoSubgroup_iff hm j x]
    left
    rcases (Subgroup.mem_zpowers_iff.mp hx) with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [← hk, DihedralGroup.r_zpow]
  have hR2index : R2.index = 4 := index_zpowers_r_two hm
  have hIdiv4 : I.index ∣ 2 ^ 2 := by
    norm_num only [pow_two]
    rw [← hR2index]
    exact Subgroup.index_dvd_of_le hR2leI
  have hIne4 : I.index ≠ 4 := by
    intro hI4
    have hrel : R2.relIndex I * I.index = R2.index :=
      Subgroup.relIndex_mul_index hR2leI
    rw [hI4, hR2index] at hrel
    have hrel1 : R2.relIndex I = 1 := by omega
    have hIleR2 : I ≤ R2 := Subgroup.relIndex_eq_one.mp hrel1
    have hsrI : DihedralGroup.sr j ∈ I := by
      rw [show I = dihedralIndexTwoSubgroup m j by rfl]
      rw [mem_dihedralIndexTwoSubgroup_iff hm j (DihedralGroup.sr j)]
      right
      refine ⟨0, ?_⟩
      simp
    have hR2leR : R2 ≤ Subgroup.zpowers (DihedralGroup.r 1) := by
      exact (Subgroup.zpowers_le).mpr (r_mem_zpowers_r_one 2)
    exact sr_not_mem_zpowers_r_one j (hR2leR (hIleR2 hsrI))
  rcases (Nat.dvd_prime_pow Nat.prime_two).mp hIdiv4 with ⟨a, ha, hIa⟩
  have ha_cases : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  rcases ha_cases with rfl | rfl | rfl
  · rw [hIa]
    norm_num
  · rw [hIa]
    norm_num
  · exact False.elim (hIne4 (by simpa using hIa))

/-- A normal subgroup of `DihedralGroup (2 ^ m)` is either a rotation subgroup
or has index dividing two.  This is the index form of the concrete
normal-subgroup classification and is convenient for quotient arguments. -/
public theorem normal_subgroup_dihedral_two_pow_is_rotation_or_index_dvd_two
    {m : ℕ} (hm : 1 ≤ m)
    (D : Subgroup (DihedralGroup (2 ^ m)))
    (hDnormal : D.Normal) :
    (∃ k : ℕ, k ≤ m ∧ D = dihedralRotationSubgroup m k) ∨ D.index ∣ 2 := by
  rcases normal_subgroup_dihedral_two_pow hm D hDnormal with
      ⟨k, hk, hD⟩ | hDtop | ⟨j, hDj⟩
  · left
    exact ⟨k, hk, hD⟩
  · right
    rw [hDtop, Subgroup.index_top]
    norm_num
  · right
    rw [hDj]
    exact dihedralIndexTwoSubgroup_index_dvd_two hm j

/-- A normal non-cyclic subgroup of `DihedralGroup (2 ^ m)` has index at most
two. -/
public theorem normal_noncyclic_subgroup_dihedral_two_pow_index_le_two
    {m : ℕ} (hm : 1 ≤ m)
    (D : Subgroup (DihedralGroup (2 ^ m)))
    (hDnormal : D.Normal)
    (hDnc : ¬ IsCyclic D) :
    D.index ≤ 2 := by
  rcases normal_noncyclic_subgroup_dihedral_two_pow hm D hDnormal hDnc with
      hDtop | ⟨j, hDj⟩
  · rw [hDtop, Subgroup.index_top]
    norm_num
  · rw [hDj]
    exact Nat.le_of_dvd (by norm_num : 0 < 2)
      (dihedralIndexTwoSubgroup_index_dvd_two hm j)

/-- Transported index bound for a normal noncyclic subgroup of an abstract
dihedral group. -/
public theorem normal_noncyclic_subgroup_dihedral_of_mulEquiv_index_le_two
    {S : Type*} [Group S]
    {m : ℕ} (hm : 1 ≤ m)
    (e : S ≃* DihedralGroup (2 ^ m))
    (D : Subgroup S) (hDnormal : D.Normal) (hDnc : ¬ IsCyclic D) :
    D.index ≤ 2 := by
  let D' : Subgroup (DihedralGroup (2 ^ m)) := D.map e.toMonoidHom
  have hD'normal : D'.Normal := by
    exact (e.normal_map_iff).2 hDnormal
  let eD : D ≃* D' :=
    D.equivMapOfInjective e.toMonoidHom e.injective
  have hD'nc : ¬ IsCyclic D' := by
    intro hcyc
    apply hDnc
    exact eD.isCyclic.mpr hcyc
  have hD'index : D'.index ≤ 2 :=
    normal_noncyclic_subgroup_dihedral_two_pow_index_le_two
      hm D' hD'normal hD'nc
  have hindex : D.index = D'.index := by
    calc
      D.index = (D'.comap e.toMonoidHom).index := by
        rw [show D'.comap e.toMonoidHom = D by
          exact Subgroup.comap_map_eq_self_of_injective e.injective D]
      _ = D'.index := D'.index_comap_of_surjective e.surjective
  rwa [hindex]

end CFSG.GorensteinWalter
