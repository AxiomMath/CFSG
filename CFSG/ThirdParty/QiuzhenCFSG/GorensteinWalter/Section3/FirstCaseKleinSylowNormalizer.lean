module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalizerFixesCentralInvolutionOfLargeDihedralSubgroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CentralInvolutionMemLargeDihedralSubgroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Normalizers of larger 2-subgroups containing the Klein four core

The source's restriction (5) invokes the assertion that the Klein four core
is Sylow in an odd-element centralizer.  The reusable fact below proves the
slightly stronger statement needed for the transfer: if a dihedral 2-subgroup
contains the Klein four core and has order at least eight, its ambient
normalizer is still controlled by `Ĥ`.  The central involution of the ambient
dihedral group lies in the Klein four, so the already-proved ambient
centralizer bound applies.
-/

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-- A large 2-subgroup containing the Klein four core has normalizer inside
`Ĥ`. -/
public theorem firstCase_klein_large_twoSubgroup_normalizer_le_Hhat
    {G : Type u} [Group G] [Finite G]
    (V Q P H : Subgroup G)
    (hVleQ : V ≤ Q) (hQleP : Q ≤ P)
    (hVklein : IsKleinFour V)
    (hQcard : 8 ≤ Nat.card Q)
    {m : ℕ} (hm : 2 ≤ m) (e : P ≃* DihedralGroup (2 ^ m))
    (hCent : ∀ v : G, v ∈ V → v ≠ 1 →
      Subgroup.centralizer ({v} : Set G) ≤ H) :
    Subgroup.normalizer (Q : Set G) ≤ H := by
  classical
  let z : G := e.symm (DihedralGroup.r (2 ^ (m - 1) : ZMod (2 ^ m)))
  have hzP : z ∈ P := by
    simpa [z] using
      (e.symm (DihedralGroup.r (2 ^ (m - 1) : ZMod (2 ^ m)))).property
  have hmodelord : orderOf (DihedralGroup.r (2 ^ (m - 1) : ZMod (2 ^ m))) = 2 := by
    rw [DihedralGroup.orderOf_r]
    have hbase : (2 : ZMod (2 ^ m)) ^ (m - 1) =
        ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
      calc
        (2 : ZMod (2 ^ m)) ^ (m - 1) =
            ((2 : ℕ) : ZMod (2 ^ m)) ^ (m - 1) := by norm_num
        _ = ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) :=
          (Nat.cast_pow 2 (m - 1)).symm
    rw [hbase, ZMod.val_natCast]
    have hlt : 2 ^ (m - 1) < 2 ^ m :=
      Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by omega)
    rw [Nat.mod_eq_of_lt hlt]
    have hgcd : (2 ^ m).gcd (2 ^ (m - 1)) = 2 ^ (m - 1) := by
      apply Nat.gcd_eq_right_iff_dvd.mpr
      exact pow_dvd_pow 2 (by omega)
    rw [hgcd]
    have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
      calc
        2 ^ m = 2 ^ ((m - 1) + 1) := by congr 1 <;> omega
        _ = 2 ^ (m - 1) * 2 := by rw [pow_succ]
        _ = 2 * 2 ^ (m - 1) := by ac_rfl
    rw [hpow]
    exact Nat.mul_div_cancel 2 (by positivity)
  have hzI : IsInvolution z := by
    refine ⟨?_, ?_⟩
    · intro hz1
      have hz1P : (⟨z, hzP⟩ : P) = 1 := by
        apply Subtype.ext
        exact hz1
      have hmodel : DihedralGroup.r (2 ^ (m - 1) : ZMod (2 ^ m)) = 1 := by
        simpa [z] using congrArg e hz1P
      have hne : DihedralGroup.r (2 ^ (m - 1) : ZMod (2 ^ m)) ≠ 1 := by
        intro h
        have : orderOf (DihedralGroup.r (2 ^ (m - 1) : ZMod (2 ^ m))) = 1 := by
          rw [h, orderOf_one]
        omega
      exact hne hmodel
    · have hpow := pow_orderOf_eq_one
        (DihedralGroup.r (2 ^ (m - 1) : ZMod (2 ^ m)))
      rw [hmodelord] at hpow
      have hzpow :
          (e.symm (DihedralGroup.r (2 ^ (m - 1) : ZMod (2 ^ m)))) ^ 2 = 1 := by
        apply e.injective
        simpa using hpow
      simpa [z] using congrArg Subtype.val hzpow
  have hmodelcenter :
      DihedralGroup.r (2 ^ (m - 1) : ZMod (2 ^ m)) ∈
        Subgroup.center (DihedralGroup (2 ^ m)) := by
    rw [Subgroup.mem_center_iff]
    intro b
    rcases dihedralGroup_cases b with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · rw [DihedralGroup.r_mul_r, DihedralGroup.r_mul_r]
      congr 1
      abel
    · rw [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r]
      congr 1
      have hhalf : (2 ^ (m - 1) : ZMod (2 ^ m)) =
          ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
        calc
          (2 : ZMod (2 ^ m)) ^ (m - 1) =
              ((2 : ℕ) : ZMod (2 ^ m)) ^ (m - 1) := by norm_num
          _ = ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) :=
            (Nat.cast_pow 2 (m - 1)).symm
      have hsum : (2 ^ (m - 1) : ZMod (2 ^ m)) +
          (2 ^ (m - 1) : ZMod (2 ^ m)) = 0 := by
        rw [hhalf, ← Nat.cast_add]
        apply (ZMod.natCast_eq_zero_iff _ _).2
        refine ⟨1, ?_⟩
        simp only [mul_one]
        calc
          2 ^ (m - 1) + 2 ^ (m - 1) = 2 * 2 ^ (m - 1) := by omega
          _ = 2 ^ (m - 1) * 2 := by ac_rfl
          _ = 2 ^ ((m - 1) + 1) := by rw [pow_succ]
          _ = 2 ^ m := by congr 1 <;> omega
      rw [sub_eq_add_neg]
      congr 1
      exact eq_neg_of_add_eq_zero_left hsum
  have hzcenterP : (⟨z, hzP⟩ : P) ∈ Subgroup.center P := by
    rw [Subgroup.mem_center_iff]
    intro a
    apply e.injective
    simpa [z, map_mul] using (Subgroup.mem_center_iff.mp hmodelcenter (e a))
  have hzQ : z ∈ Q := central_involution_mem_large_subgroup_of_dihedral
    P Q hQleP hm e hzP hzI hzcenterP hQcard
  have hzCentV : z ∈ Subgroup.centralizer (V : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hvP : v ∈ P := hQleP (hVleQ hv)
    have hzc : (⟨z, hzP⟩ : P) * ⟨v, hvP⟩ =
        (⟨v, hvP⟩ : P) * ⟨z, hzP⟩ :=
      (Subgroup.mem_center_iff.mp hzcenterP ⟨v, hvP⟩).symm
    exact (congrArg Subtype.val hzc).symm
  have hzV : z ∈ V := by
    have hzcP : (⟨z, hzP⟩ : P) ∈
        Subgroup.centralizer (V.subgroupOf P : Set P) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hwG : (w : G) ∈ V := Subgroup.mem_subgroupOf.mp hw
      have hcomm := (Subgroup.mem_centralizer_iff.mp hzCentV) (w : G) hwG
      exact Subtype.ext hcomm
    have hVkleinP : IsKleinFour (V.subgroupOf P) := by
      let eVP : V.subgroupOf P ≃* V :=
        Subgroup.subgroupOfEquivOfLe (hVleQ.trans hQleP)
      exact {
        card_four := (Nat.card_congr eVP.toEquiv).trans hVklein.card_four
        exponent_two :=
          (Monoid.exponent_eq_of_mulEquiv eVP).trans hVklein.exponent_two }
    have hcentP : Subgroup.centralizer
        (V.subgroupOf P : Set P) ≤ V.subgroupOf P :=
      centralizer_kleinFour_le_of_dihedral_mulEquiv (by omega) e
        (V.subgroupOf P) hVkleinP
    have hzVsub : (⟨z, hzP⟩ : P) ∈ V.subgroupOf P :=
      hcentP hzcP
    exact Subgroup.mem_subgroupOf.mp hzVsub
  intro y hy
  have hyfix : y * z * y⁻¹ = z :=
    normalizer_fixes_central_involution_of_large_subgroup_of_dihedral
      P Q hQleP hm e hzP hzQ hzI hzcenterP hQcard hy
  have hyC : y ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact mul_inv_eq_iff_eq_mul.mp (by simpa [mul_assoc] using hyfix)
  exact hCent z hzV hzI.1 hyC

end CFSG.GorensteinWalter
