module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalOddPSubgroupCentralized

import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.theorem_1_13
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Centralization of invariant odd-prime subgroups in odd `PSL₂`

The centered-Sylow model calculation extends to an arbitrary involution by
choosing a central involution in a Sylow `2`-subgroup and transporting that
whole Sylow subgroup through involution fusion.
-/

open scoped Pointwise

namespace CFSG.GorensteinWalter

open BenderSuzuki.MatrixGroups

universe u

/-- If an odd-prime subgroup of odd `PSL₂(F)` is invariant under the
centralizer of an involution, then that involution centralizes the subgroup. -/
public theorem psl2_invariant_oddP_subgroup_centralized
    {F : Type u} [Field F] [Finite F]
    {r f p : ℕ} [Fact r.Prime] [Fact p.Prime]
    (hFcard : Nat.card F = r ^ f)
    (hrodd : Odd r) (hpodd : Odd p)
    (P : Subgroup (PSL2MatrixGroup F))
    (hPp : IsPGroup p P)
    {t : PSL2MatrixGroup F}
    (ht : IsInvolution t)
    (hPinv : Subgroup.centralizer ({t} : Set (PSL2MatrixGroup F)) ≤
      Subgroup.normalizer (P : Set (PSL2MatrixGroup F))) :
    P ≤ Subgroup.centralizer ({t} : Set (PSL2MatrixGroup F)) := by
  classical
  have hf_ne_zero : f ≠ 0 := by
    intro hf_zero
    have hcard_one : Nat.card F = 1 := by
      simpa [hf_zero, pow_zero] using hFcard
    exact (Nat.ne_of_gt (Finite.one_lt_card (α := F))) hcard_one
  have hoddF : IsOddPrimePower (Nat.card F) :=
    ⟨r, f, Fact.out, hrodd, Nat.one_le_iff_ne_zero.mpr hf_ne_zero, hFcard⟩
  let S0 : Sylow 2 (PSL2MatrixGroup F) := Classical.choice Sylow.nonempty
  obtain ⟨m, _hm, ⟨eS0⟩⟩ :=
    psl2_odd_hasDihedralSylowTwo_model F hoddF S0
  let : Fact (IsPGroup 2 S0) := ⟨S0.isPGroup'⟩
  let : Nontrivial S0 := eS0.toEquiv.nontrivial
  obtain ⟨z, _hzTop, hzCenter, hzNe, hzSq⟩ :=
    exists_nontrivial_mem_center_of_normal_p_subgroup
      (G := S0) (p := 2) (⊤ : Subgroup S0) top_ne_bot
  have hzI : IsInvolution (z : PSL2MatrixGroup F) := by
    constructor
    · intro hzOne
      apply hzNe
      apply Subtype.ext
      exact hzOne
    · exact congrArg Subtype.val hzSq
  obtain ⟨g, hgz⟩ :=
    psl2_involutions_conjugate_of_odd_prime_power F hoddF
      (z : PSL2MatrixGroup F) t hzI ht
  let S : Sylow 2 (PSL2MatrixGroup F) := g • S0
  have htS : t ∈ (S : Subgroup (PSL2MatrixGroup F)) := by
    change t ∈ ((g • S0 : Sylow 2 (PSL2MatrixGroup F)) :
      Subgroup (PSL2MatrixGroup F))
    rw [Sylow.coe_subgroup_smul]
    apply Set.mem_smul_set.mpr
    refine ⟨(z : PSL2MatrixGroup F), z.property, ?_⟩
    simpa using hgz
  have htCenter : (⟨t, htS⟩ : S) ∈ Subgroup.center S := by
    apply Subgroup.mem_center_iff.mpr
    intro x
    apply Subtype.ext
    change (x : PSL2MatrixGroup F) * t = t * (x : PSL2MatrixGroup F)
    have hxS := x.property
    change (x : PSL2MatrixGroup F) ∈
      ((g • S0 : Sylow 2 (PSL2MatrixGroup F)) :
        Subgroup (PSL2MatrixGroup F)) at hxS
    rw [Sylow.coe_subgroup_smul] at hxS
    rcases Set.mem_smul_set.mp hxS with ⟨q, hqS0, hqx⟩
    have hqx' : g * q * g⁻¹ = (x : PSL2MatrixGroup F) := by
      simpa using hqx
    rw [← hqx', ← hgz]
    have hqCommS0 :=
      (Subgroup.mem_center_iff.mp hzCenter) ⟨q, hqS0⟩
    have hqComm : q * (z : PSL2MatrixGroup F) =
        (z : PSL2MatrixGroup F) * q :=
      congrArg Subtype.val hqCommS0
    calc
      (g * q * g⁻¹) * (g * (z : PSL2MatrixGroup F) * g⁻¹) =
          g * (q * (z : PSL2MatrixGroup F)) * g⁻¹ := by group
      _ = g * ((z : PSL2MatrixGroup F) * q) * g⁻¹ := by rw [hqComm]
      _ = (g * (z : PSL2MatrixGroup F) * g⁻¹) *
          (g * q * g⁻¹) := by group
  have hSleC : (S : Subgroup (PSL2MatrixGroup F)) ≤
      Subgroup.centralizer ({t} : Set (PSL2MatrixGroup F)) := by
    intro x hxS
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val
      ((Subgroup.mem_center_iff.mp htCenter) ⟨x, hxS⟩)
  let M : Subgroup (PSL2MatrixGroup F) :=
    Subgroup.normalizer (P : Set (PSL2MatrixGroup F))
  have hPleM : P ≤ M := Subgroup.le_normalizer
  have hPnormal : (P.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPleM).mpr le_rfl
  exact psl2_normal_oddP_centralized_of_contains_sylow
    hFcard hrodd hpodd S M P (hSleC.trans hPinv) hPleM hPnormal hPp
      htS htCenter ht hPinv

end CFSG.GorensteinWalter
