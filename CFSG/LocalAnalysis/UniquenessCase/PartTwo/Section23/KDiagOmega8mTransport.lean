module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KDiagL2

public noncomputable section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal

theorem kDiag_of_isOmega8m_of_tail
    (hTail : ∀ {K : Type} [Field K] [Finite K] [CharP K 2] (b c : K),
      (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
      ∀ (θ : MulAut (orthElementaryGroup (quadTail 3 (minusTailForm K b c)))),
        ∀ S : Sylow 2 (orthElementaryGroup (quadTail 3 (minusTailForm K b c))),
          (∀ x ∈ (S : Subgroup (orthElementaryGroup (quadTail 3 (minusTailForm K b c)))),
            θ x ∈ (S : Subgroup _)) →
          ∀ P : Subgroup (orthElementaryGroup (quadTail 3 (minusTailForm K b c))),
            IsParabolicTwo (orthElementaryGroup (quadTail 3 (minusTailForm K b c))) P →
            (S : Subgroup (orthElementaryGroup (quadTail 3 (minusTailForm K b c)))) ≤
              Subgroup.normalizer
                (P : Set (orthElementaryGroup (quadTail 3 (minusTailForm K b c)))) →
            ∀ x ∈ P, θ x ∈ P) :
    ∀ {n : ℕ} {X : Type} [Group X] [Finite X], IsOmega8m X n →
      ∀ (θ : MulAut X), Odd (orderOf θ) →
      ∀ S : Sylow 2 X, (∀ x ∈ (S : Subgroup X), θ x ∈ (S : Subgroup X)) →
      ∀ P : Subgroup X, IsParabolicTwo X P →
        (S : Subgroup X) ≤ Subgroup.normalizer (P : Set X) → ∀ x ∈ P, θ x ∈ P := by
  intro n X _ _ hΩ θ hodd S hSθ P hP hSP x hx
  have hmodel : StatedClassicalModel X .POmegaMinus 4 2 n :=
    LieModel.statedClassicalModel hΩ (by decide)
  obtain ⟨⟨-, hf, -⟩, K, hKfield, hKfin, hKcard, b, c, hirr, ⟨e₀⟩⟩ := hmodel
  letI : Field K := hKfield
  letI : Finite K := hKfin
  have hchar : CharP K 2 :=
    finite_field_prime_power_characteristic (K := K) Nat.prime_two hf hKcard
  letI : CharP K 2 := hchar
  have hE := commutator_orthogonalGroup_quadMinus (K := K) (b := b) (c := c) (n := 4)
    (by norm_num) hirr
  let e : X ≃* orthElementaryGroup (quadTail 3 (minusTailForm K b c)) :=
    e₀.trans
      ((tailProjEquiv (minusTailIsometry 4 K b c) (coe_quadMinus 4 K b c) hE).trans
        ((QuotientGroup.quotientMulEquivOfEq
          (NonsplitOrthogonalCover.elemScalars_quadTail_eq_bot (by norm_num))).trans
          QuotientGroup.quotientBot))
  exact kDiag_transport e (fun θ' _ => hTail b c hirr θ') θ hodd S hSθ P hP hSP x hx

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
