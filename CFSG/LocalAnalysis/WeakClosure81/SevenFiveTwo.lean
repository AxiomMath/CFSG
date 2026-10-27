module

public import CFSG.LocalAnalysis.WeakClosure81.SevenFive

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def kOrbCompl (V H E U : Subgroup G) : Subgroup G :=
  ⨆ (U' ∈ omegaSet V H E) (_ : ∀ k ∈ kSub V H E, U' ≠ conjSubgroup U k),
    kOrbSub V H E U'

theorem kOrbCompl_le_kSub {V H E U : Subgroup G}
    (hEH : E ≤ H) (hEnorm : (E.subgroupOf H).Normal)
    (hOmH : ∀ W ∈ omegaSet V H E, W ≤ H) :
    kOrbCompl V H E U ≤ kSub V H E :=
  iSup_le fun U' => iSup_le fun hU' => iSup_le fun _ =>
    kOrbSub_le_kSub hEH hEnorm hOmH hU'

theorem kSub_eq_kOrbSub_sup_kOrbCompl {V H E U : Subgroup G}
    (hEH : E ≤ H) (hEnorm : (E.subgroupOf H).Normal)
    (hOmH : ∀ W ∈ omegaSet V H E, W ≤ H) (hU : U ∈ omegaSet V H E) :
    kSub V H E = kOrbSub V H E U ⊔ kOrbCompl V H E U := by
  refine le_antisymm ?_ ?_
  · refine iSup_le fun U' => iSup_le fun hU' => ?_
    by_cases hP : ∀ k ∈ kSub V H E, U' ≠ conjSubgroup U k
    · have h1 : U' ≤ kOrbSub V H E U' := by
        change U' ≤ ⨆ k : kSub V H E, conjSubgroup U' (k : G)
        simpa [CFSG.Quasithin.conjSubgroup_one] using
          (le_iSup (fun k : kSub V H E => conjSubgroup U' (k : G)) 1)
      have h2 : kOrbSub V H E U' ≤ kOrbCompl V H E U :=
        le_iSup₂_of_le U' hU' (le_iSup (fun _ : (∀ k ∈ kSub V H E,
          U' ≠ conjSubgroup U k) => kOrbSub V H E U') hP)
      exact le_trans h1 (le_trans h2 le_sup_right)
    · push Not at hP
      obtain ⟨k, hk, hkU'⟩ := hP
      have h1 : U' ≤ kOrbSub V H E U := by
        rw [hkU']
        change conjSubgroup U k ≤ ⨆ m : kSub V H E, conjSubgroup U (m : G)
        exact le_iSup (fun m : kSub V H E => conjSubgroup U (m : G)) ⟨k, hk⟩
      exact le_trans h1 le_sup_left
  · exact sup_le (kOrbSub_le_kSub hEH hEnorm hOmH hU)
      (kOrbCompl_le_kSub hEH hEnorm hOmH)

theorem commutator_kOrbSub_kOrbCompl_eq_bot {V H E U : Subgroup G}
    (hV : IsElemAbelian 2 V) (hTI : IsTI V) (hE : IsMulCommutative E)
    (hEH : E ≤ H) (hEnorm : (E.subgroupOf H).Normal)
    (hOmH : ∀ W ∈ omegaSet V H E, W ≤ H) (hU : U ∈ omegaSet V H E) :
    ⁅kOrbSub V H E U, kOrbCompl V H E U⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff]
  refine iSup_le fun U' => iSup_le fun hU' => iSup_le fun hP => ?_
  exact Subgroup.le_centralizer_iff.mpr
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (commutator_kOrbSub_eq_bot hV hTI hE hEH hEnorm hOmH hU hU' hP))

end CFSG.LocalAnalysis.WeakClosure81
