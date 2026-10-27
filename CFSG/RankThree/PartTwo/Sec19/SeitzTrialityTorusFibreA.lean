module

public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityAB
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityModel
public import CFSG.RankThree.PartOne.D4RC.Lines
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityTorusFibreAux1
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityTorusFibreAux2

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
open CFSG.RankThree.PartTwo.Sec11 CFSG.RankThree.PartOne.D4RC

namespace CFSG.RankThree.PartTwo.Sec19

section FibreA


variable {n : ℕ} {X : Type} [Field X] [Finite X] (σ : X ≃+* X)

theorem rce_center_fibre {ε : ℤ} {p : ℕ} {L : Type} [Field L] [Algebra X L] [IsAlgClosure X L]
    [CharP L 2] {F : RclFrame 2 n X σ ε p L} {S : Sylow p (C0 σ)} {c : C0 σ}
    {E : Subgroup (C0 σ)} (Ln : RceLines F S c E) (j : Fin 4)
    (h3 : (3 : ℤ) ∣ ((2 ^ n : ℕ) : ℤ) - ε) :
    ∃ ζ : C0 σ, ζ ∈ rclPx (Ln.sp j) ∧ (∀ u ∈ rclPx (Ln.sp j), ζ * u = u * ζ) ∧ ζ ^ 3 = 1 ∧
      ζ ≠ 1 ∧
      Subgroup.centralizer ({Ln.x j} : Set (C0 σ)) = Subgroup.centralizer ({ζ} : Set (C0 σ)) := by
  obtain ⟨D⟩ := rcl_exists_algData F j
  obtain ⟨z, hz, hc, hz3, hz1⟩ := rcfa_central_order_three D h3
  obtain ⟨ζ, hζ, hPx, hcomm, hζ3, hζ1⟩ := rcfa_zeta (Ln.sp j) D hz hc hz3 hz1
  obtain ⟨b', hb', hker'⟩ := rcfa_kernel (Ln.sp j) hζ hcomm hζ1
  exact ⟨ζ, hPx, hcomm, hζ3, hζ1, rcfa_centralizer_eq (Ln.sp j) hζ hζ3 hζ1 b' hb' hker'⟩

end FibreA

end CFSG.RankThree.PartTwo.Sec19
