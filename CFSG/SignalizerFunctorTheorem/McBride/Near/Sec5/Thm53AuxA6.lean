module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.External
public import CFSG.SignalizerFunctorTheorem.McBride.Models.Theorem28
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec5.Thm53AuxA4
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec5.Thm52AuxQuot

public section

open CFSG.Open
open scoped commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

namespace Thm53A

open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

variable {Γ : Type u} [Group Γ] [Finite Γ]

theorem compInput_of_nearPSolvable
    {p : ℕ} (hp : p.Prime) {W : Subgroup Γ}
    (hnear : signalizerNearPSolvable p ↥W) : CompInput p W := by
  have hWN : W ≤ AChief.nrm (sol W) := SolQuot.le_nrm_sol W
  have key : ∀ J ∈ lcal (AChief.qimg (sol W) W), NearSimple p ↥J := by
    intro J hJ
    obtain ⟨hJZ, -, hs, hJnc⟩ := mem_lcal_iff.mp hJ
    have hnc' : ∃ x y : ↥J, x * y ≠ y * x := by
      by_contra hcon
      push Not at hcon
      exact hJnc (isMulCommutative_iff.mpr hcon)
    have hsec := Thm52Aux.isSectionOf_of_mem_lcal_qimg hWN hJ
    obtain ⟨hcopY, hmodel⟩ := signalizerNearPSolvable_iff.mp hnear
    have hcop : Nat.Coprime p (Nat.card J) := by
      refine hcopY.coprime_dvd_right ?_
      exact (Subgroup.card_dvd_of_le hJZ).trans
        (Subgroup.card_dvd_of_surjective (SolQuot.qres_surjective hWN))
    exact ⟨hp, hs, hnc', signalizerNearPSolvable_iff.mpr
      ⟨hcop, fun S _ _ hS hnc => hmodel S (hS.trans hsec) hnc⟩⟩
  unfold CompInput
  exact ⟨fun J hJ P hP => NearSimple.outer_perfect_le_inner (key J hJ) P hP,
    fun J hJ P hP => near_aut_pSubgroup_card_dvd (key J hJ) P hP⟩

theorem mem_sol_of_commutator_mem_kOf {L : Subgroup Γ} {d : Γ} (hd : d ∈ L)
    (hc : ∀ x ∈ kOf L, ⁅d, x⁆ ∈ sol L) : d ∈ sol L := by
  have hLN : L ≤ AChief.nrm (sol L) := SolQuot.le_nrm_sol L
  have hsol : sol (AChief.qimg (sol L) L) = ⊥ := SolQuot.sol_qimg_sol L
  set dN : AChief.nrm (sol L) := ⟨d, hLN hd⟩ with hdN
  have hmem : AChief.qmap (sol L) dN ∈ AChief.qimg (sol L) L ⊓
      Subgroup.centralizer ((kOf (AChief.qimg (sol L) L) : Subgroup _) : Set _) := by
    refine Subgroup.mem_inf.mpr ⟨(AChief.mem_qimg_iff _ _ _).mpr ⟨dN, hd, rfl⟩, ?_⟩
    rw [SolQuot.kOf_qimg_sol le_rfl, Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨x, hx, rfl⟩ := (AChief.mem_qimg_iff _ _ _).mp hz
    have h1 : ⁅AChief.qmap (sol L) dN, AChief.qmap (sol L) x⁆ = 1 := by
      rw [← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr (hc x hx))
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
  rw [centralizer_kOf_eq_bot hsol, Subgroup.mem_bot] at hmem
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hmem)

end Thm53A

end CFSG.SignalizerFunctorTheorem.McBride.Near
