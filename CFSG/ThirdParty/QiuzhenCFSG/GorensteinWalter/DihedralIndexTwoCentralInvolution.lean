module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralCore
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Recognizing the central involution across an index-two subgroup

In a dihedral `2`-group of order at least eight, two distinct commuting
involutions cannot straddle an index-two subgroup arbitrarily: the involution
inside the index-two subgroup is forced to be the central rotation.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- Let `P ≃ D_{2^(m+1)}` with `m ≥ 2`, and let `H` have index two in
`P`.  If nontrivial commuting involutions `t,s` satisfy `t ∈ H` and
`s ∉ H`, then `t` is the central rotation of the dihedral model. -/
public theorem eq_central_involution_of_mem_indexTwo_of_commuting_involution_not_mem
    {P : Type u} [Group P] [Finite P]
    {m : ℕ} (hm : 2 ≤ m)
    (e : P ≃* DihedralGroup (2 ^ m))
    (H : Subgroup P) (hHindex : H.index = 2)
    (t s : P)
    (htH : t ∈ H) (hsH : s ∉ H)
    (htne : t ≠ 1) (hsne : s ≠ 1)
    (htsq : t * t = 1) (hssq : s * s = 1)
    (htscomm : Commute t s) :
    t = e.symm (DihedralGroup.r
      (2 ^ (m - 1) : ZMod (2 ^ m))) := by
  let zM : DihedralGroup (2 ^ m) :=
    DihedralGroup.r (2 ^ (m - 1) : ZMod (2 ^ m))
  let z : P := e.symm zM
  let qM : DihedralGroup (2 ^ m) :=
    DihedralGroup.r (2 ^ (m - 2) : ZMod (2 ^ m))
  let q : P := e.symm qM
  have hpowNat : 2 * 2 ^ (m - 2) = 2 ^ (m - 1) := by
    calc
      2 * 2 ^ (m - 2) = 2 ^ ((m - 2) + 1) := by rw [pow_succ']
      _ = 2 ^ (m - 1) := by congr 1; omega
  have hqM_sq : qM * qM = zM := by
    dsimp [qM, zM]
    apply congrArg DihedralGroup.r
    rw [← two_mul]
    have hcast := congrArg
      (fun n : ℕ ↦ (n : ZMod (2 ^ m))) hpowNat
    simpa [Nat.cast_mul, Nat.cast_pow] using hcast
  have hq_sq : q ^ 2 = z := by
    apply e.injective
    dsimp [q, z]
    rw [map_pow, e.apply_symm_apply, e.apply_symm_apply]
    simpa [pow_two] using hqM_sq
  have hzH : z ∈ H := by
    rw [← hq_sq]
    exact H.sq_mem_of_index_two hHindex q
  have htneS : t ≠ s := by
    intro hts
    apply hsH
    simpa [← hts] using htH
  let T : DihedralGroup (2 ^ m) := e t
  let S : DihedralGroup (2 ^ m) := e s
  have hTne : T ≠ 1 := by
    intro h
    apply htne
    apply e.injective
    simpa [T] using h
  have hSne : S ≠ 1 := by
    intro h
    apply hsne
    apply e.injective
    simpa [S] using h
  have hTSne : T ≠ S := by
    intro h
    exact htneS (e.injective h)
  have hTsq : T * T = 1 := by
    simpa [T] using congrArg e htsq
  have hSsq : S * S = 1 := by
    simpa [S] using congrArg e hssq
  have hTScomm : T * S = S * T := by
    simpa [T, S] using congrArg e htscomm.eq
  have rotation_eq_z
      (i : ZMod (2 ^ m))
      (hsq : DihedralGroup.r i * DihedralGroup.r i = 1)
      (hne : DihedralGroup.r i ≠ 1) :
      DihedralGroup.r i = zM := by
    have htwo : (2 : ZMod (2 ^ m)) * i = 0 := by
      have hri : DihedralGroup.r (i + i) = DihedralGroup.r 0 := by
        simpa only [DihedralGroup.r_mul_r, DihedralGroup.one_def] using hsq
      injection hri with hii
      simpa only [two_mul] using hii
    rcases (zmod_two_mul_eq_zero_iff hm i).mp htwo with hi0 | hihalf
    · exfalso
      apply hne
      rw [hi0, DihedralGroup.r_zero]
    · simp [zM, hihalf]
  rcases dihedralGroup_cases T with ⟨i, hi⟩ | ⟨i, hi⟩
  · have hTz : T = zM := by
      rw [hi]
      apply rotation_eq_z i
      · simpa [hi] using hTsq
      · simpa [hi] using hTne
    apply e.injective
    simpa [T, z, zM] using hTz
  · rcases dihedralGroup_cases S with ⟨j, hj⟩ | ⟨j, hj⟩
    · have hSz : S = zM := by
        rw [hj]
        apply rotation_eq_z j
        · simpa [hj] using hSsq
        · simpa [hj] using hSne
      have hsz : s = z := by
        apply e.injective
        simpa [S, z, zM] using hSz
      apply False.elim
      apply hsH
      simpa [hsz] using hzH
    · have hij : i - j = j - i := by
        simpa [hi, hj, DihedralGroup.sr_mul_sr] using hTScomm.symm
      have htwo : (2 : ZMod (2 ^ m)) * (i - j) = 0 := by
        rw [two_mul]
        calc
          (i - j) + (i - j) = (i - j) + (j - i) := by rw [hij]
          _ = 0 := by abel
      have hdiffne : i - j ≠ 0 := by
        intro hdiff
        have hij' : i = j := sub_eq_zero.mp hdiff
        apply hTSne
        rw [hi, hj, hij']
      have hdiff : i - j =
          (2 ^ (m - 1) : ZMod (2 ^ m)) := by
        rcases (zmod_two_mul_eq_zero_iff hm (i - j)).mp htwo with
          hzero | hhalf
        · exact False.elim (hdiffne hzero)
        · exact hhalf
      have hhalfzero :
          (2 : ZMod (2 ^ m)) *
              (2 ^ (m - 1) : ZMod (2 ^ m)) = 0 :=
        (zmod_two_mul_eq_zero_iff hm
          (2 ^ (m - 1) : ZMod (2 ^ m))).mpr (Or.inr rfl)
      have hhalfneg :
          -(2 ^ (m - 1) : ZMod (2 ^ m)) =
            (2 ^ (m - 1) : ZMod (2 ^ m)) := by
        apply neg_eq_iff_add_eq_zero.mpr
        simpa [two_mul] using hhalfzero
      have hjform : j = i +
          (2 ^ (m - 1) : ZMod (2 ^ m)) := by
        calc
          j = i - (i - j) := by abel
          _ = i - (2 ^ (m - 1) : ZMod (2 ^ m)) := by rw [hdiff]
          _ = i + (2 ^ (m - 1) : ZMod (2 ^ m)) := by
            rw [sub_eq_add_neg, hhalfneg]
      have htsz : t * z = s := by
        apply e.injective
        rw [map_mul]
        change T * e z = S
        have hez : e z = zM := by
          dsimp [z]
          exact e.apply_symm_apply zM
        rw [hez, hi, hj, hjform]
        exact DihedralGroup.sr_mul_r _ _
      apply False.elim
      apply hsH
      rw [← htsz]
      exact H.mul_mem htH hzH

end CFSG.GorensteinWalter
