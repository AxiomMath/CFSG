module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
import Mathlib.GroupTheory.IndexNormal
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Conjugacy outside a noncyclic index-two subgroup of a dihedral 2-group

A noncyclic index-two subgroup is one of the two reflection extensions of
the even rotations.  The involutions outside it are precisely the reflections
in the other parity class, so they are conjugate by rotations.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- In a dihedral `2`-group of order at least eight, all involutions outside
a noncyclic index-two subgroup are conjugate. -/
public theorem dihedral_involutions_not_mem_noncyclic_index_two_isConj
    {P : Type u} [Group P] [Finite P]
    {m : ℕ} (hm : 2 ≤ m)
    (e : P ≃* DihedralGroup (2 ^ m))
    (H : Subgroup P) (hHindex : H.index = 2)
    (hHnoncyclic : ¬ IsCyclic H)
    {a b : P} (ha : IsInvolution a) (hb : IsInvolution b)
    (haH : a ∉ H) (hbH : b ∉ H) :
    IsConj a b := by
  classical
  let D : Subgroup (DihedralGroup (2 ^ m)) := H.map e.toMonoidHom
  have hHnormal : H.Normal := Subgroup.normal_of_index_eq_two hHindex
  have hDnormal : D.Normal :=
    hHnormal.map e.toMonoidHom e.surjective
  have hDnoncyclic : ¬ IsCyclic D := by
    intro hDcyclic
    apply hHnoncyclic
    exact (e.subgroupMap H).isCyclic.mpr hDcyclic
  have hea_not : e a ∉ D := by
    intro hea
    rcases Subgroup.mem_map.mp hea with ⟨x, hxH, hxea⟩
    apply haH
    have hxa : x = a := e.injective hxea
    rwa [← hxa]
  have heb_not : e b ∉ D := by
    intro heb
    rcases Subgroup.mem_map.mp heb with ⟨x, hxH, hxeb⟩
    apply hbH
    have hxb : x = b := e.injective hxeb
    rwa [← hxb]
  obtain hDtop | ⟨j, hDj⟩ :=
      normal_noncyclic_subgroup_dihedral_two_pow (by omega : 1 ≤ m)
        D hDnormal hDnoncyclic
  · exact False.elim (hea_not (by rw [hDtop]; trivial))
  have hrotation_mem {x : P} (hx : IsInvolution x) :
      ∀ i : ZMod (2 ^ m), e x = DihedralGroup.r i → e x ∈ D := by
    intro i hxi
    have hsq : e x * e x = 1 := by
      simpa [pow_two] using congrArg e hx.2
    have htwo : (2 : ZMod (2 ^ m)) * i = 0 := by
      apply DihedralGroup.r.inj
      calc
        DihedralGroup.r ((2 : ZMod (2 ^ m)) * i) =
            DihedralGroup.r i * DihedralGroup.r i := by
          rw [DihedralGroup.r_mul_r]
          congr 1
          ring
        _ = e x * e x := by rw [hxi]
        _ = 1 := hsq
        _ = DihedralGroup.r 0 := DihedralGroup.r_zero.symm
    rcases (zmod_two_mul_eq_zero_iff hm i).mp htwo with hi | hi
    · rw [hxi, hi, DihedralGroup.r_zero]
      exact D.one_mem
    · rw [hDj, mem_dihedralIndexTwoSubgroup_iff (by omega : 1 ≤ m) j]
      left
      refine ⟨(2 ^ (m - 2) : ℤ), ?_⟩
      rw [hxi, hi]
      congr 1
      have hpow : 2 * 2 ^ (m - 2) = 2 ^ (m - 1) := by
        calc
          2 * 2 ^ (m - 2) = 2 ^ (1 + (m - 2)) := by rw [pow_add]; simp
          _ = 2 ^ (m - 1) := by congr 1; omega
      simpa using
        congrArg (fun n : ℕ => (n : ZMod (2 ^ m))) hpow.symm
  rcases dihedralGroup_cases (e a) with ⟨i, hai⟩ | ⟨i, hai⟩
  · exact False.elim (hea_not (hrotation_mem ha i hai))
  rcases dihedralGroup_cases (e b) with ⟨k, hbk⟩ | ⟨k, hbk⟩
  · exact False.elim (heb_not (hrotation_mem hb k hbk))
  have outside_form {x : ZMod (2 ^ m)}
      (hx : DihedralGroup.sr x ∉ dihedralIndexTwoSubgroup m j) :
      ∃ q : ZMod (2 ^ m),
        x = j + 1 + (2 : ZMod (2 ^ m)) * q := by
    rcases (x - j).val.even_or_odd with ⟨q, hq⟩ | ⟨q, hq⟩
    · exfalso
      apply hx
      rw [mem_dihedralIndexTwoSubgroup_iff (by omega : 1 ≤ m) j]
      right
      refine ⟨(q : ℤ), ?_⟩
      have hdiff : x - j =
          (2 : ZMod (2 ^ m)) * (q : ZMod (2 ^ m)) := by
        rw [← ZMod.natCast_zmod_val (x - j), hq]
        push_cast
        ring
      congr 1
      calc
        x = j + (x - j) := by abel
        _ = j + (2 : ZMod (2 ^ m)) * (q : ZMod (2 ^ m)) := by
          rw [hdiff]
        _ = j + (2 : ZMod (2 ^ m)) * ((q : ℤ) : ZMod (2 ^ m)) := by
          norm_num
    · refine ⟨(q : ZMod (2 ^ m)), ?_⟩
      have hdiff : x - j =
          1 + (2 : ZMod (2 ^ m)) * (q : ZMod (2 ^ m)) := by
        rw [← ZMod.natCast_zmod_val (x - j), hq]
        push_cast
        ring
      calc
        x = j + (x - j) := by abel
        _ = j + (1 + (2 : ZMod (2 ^ m)) * (q : ZMod (2 ^ m))) := by
          rw [hdiff]
        _ = j + 1 + (2 : ZMod (2 ^ m)) * (q : ZMod (2 ^ m)) := by
          ring
  have hai_not : DihedralGroup.sr i ∉ dihedralIndexTwoSubgroup m j := by
    simpa [D, hDj, hai] using hea_not
  have hbk_not : DihedralGroup.sr k ∉ dihedralIndexTwoSubgroup m j := by
    simpa [D, hDj, hbk] using heb_not
  obtain ⟨q, hi⟩ := outside_form hai_not
  obtain ⟨r, hk⟩ := outside_form hbk_not
  have hki : k = i + (2 : ZMod (2 ^ m)) * (r - q) := by
    rw [hi, hk]
    ring
  let z : ZMod (2 ^ m) := q - r
  let u : (DihedralGroup (2 ^ m))ˣ :=
    ⟨DihedralGroup.r z, DihedralGroup.r (-z), by
      rw [DihedralGroup.r_mul_r]
      rw [show z + -z = 0 by abel, DihedralGroup.r_zero], by
      rw [DihedralGroup.r_mul_r]
      rw [show -z + z = 0 by abel, DihedralGroup.r_zero]⟩
  have hmodel : IsConj (DihedralGroup.sr i) (DihedralGroup.sr k) := by
    refine ⟨u, ?_⟩
    change DihedralGroup.r z * DihedralGroup.sr i =
      DihedralGroup.sr k * DihedralGroup.r z
    rw [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r]
    congr 1
    rw [hki]
    dsimp [z]
    ring
  have htransport := MonoidHom.map_isConj e.symm.toMonoidHom hmodel
  have haeq : e.symm (DihedralGroup.sr i) = a := by
    rw [← hai]
    exact e.symm_apply_apply a
  have hbeq : e.symm (DihedralGroup.sr k) = b := by
    rw [← hbk]
    exact e.symm_apply_apply b
  change IsConj (e.symm (DihedralGroup.sr i))
    (e.symm (DihedralGroup.sr k)) at htransport
  rw [haeq, hbeq] at htransport
  exact htransport

end CFSG.GorensteinWalter
