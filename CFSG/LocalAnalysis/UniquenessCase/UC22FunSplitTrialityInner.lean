module

public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitLinearAction
public import CFSG.ClassicalInvolution.AschTight.S19GD4Inv

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.G2D4Models
open CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.CurtisTits CFSG.LieType.Chevalley
open scoped MatrixGroups


theorem odd_normalizer_inner_fundamental_triality
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {e : ℕ} (he : 1 ≤ e)
    (R : Subgroup (twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e)))
    (hR : R ∈ fundamentalSubgroups .trialityD4
      (twistedDatum (iterateFrobenius (GaloisField p (3 * e)) p e)))
    (g : twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e))
    (hg : g ∈ normalizer
      (R : Set (twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e))))
    (hgo : Odd (orderOf g)) :
    ∃ r ∈ R, ∀ x ∈ R, g * x * g⁻¹ = r * x * r⁻¹ := by
  obtain ⟨hσ3, hK1, hC₀, hgF, hoddK, hoddF⟩ :=
    CFSG.ClassicalInvolution.Disconnected.AschTight.S19G.d4_model_data hp2 he
  obtain ⟨i, z₀, hRz⟩ :=
    CFSG.ClassicalInvolution.Asc77.exists_conj_rankOne_node_of_trialityD4 0 p e
      ⟨Fact.out, he, rfl⟩ hR
  obtain ⟨z, hz⟩ : ∃ z : twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e),
      z = z₀ := ⟨z₀, rfl⟩
  have hR' : R = (rankOne
      (twistedRootGroup (iterateFrobenius (GaloisField p (3 * e)) p e)) i).map
      (MulAut.conj z).toMonoidHom := by rw [hz]; exact hRz
  have hi : (i : ℕ) < 2 := i.2
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · have hi' : i = ng 0 := Fin.ext h0
    have hchart : rankOne
        (twistedRootGroup (iterateFrobenius (GaloisField p (3 * e)) p e)) (ng 0) =
        (slLong _ hσ3).range := CFSG.ClassicalInvolution.ModelFacts.rankOne_long_eq_range hσ3
    have hRchart : R = (slLong _ hσ3).range.map (MulAut.conj z).toMonoidHom := by
      exact hR'.trans (congrArg (fun S : Subgroup
        (twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e)) =>
          S.map (MulAut.conj z).toMonoidHom) ((congrArg
            (rankOne (twistedRootGroup (iterateFrobenius (GaloisField p (3 * e)) p e)))
            hi').trans hchart))
    have hg' : g ∈ normalizer ((slLong _ hσ3).range.map
        (MulAut.conj z).toMonoidHom : Set
          (twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e))) := hRchart ▸ hg
    have hinner := exists_inner_normalizer_conj_range_of_linAct hoddF
      (slLong _ hσ3) (slLong_injective hσ3)
      (fun _ hx => linAct_of_centralizes_long hσ3 hK1
        (CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card _ hoddF) hC₀ hgF hx)
      z hg' hgo
    exact hRchart.symm ▸ hinner
  · have hi' : i = ng 1 := Fin.ext h1
    have hchart : rankOne
        (twistedRootGroup (iterateFrobenius (GaloisField p (3 * e)) p e)) (ng 1) =
        (slShort _ hσ3).range := CFSG.ClassicalInvolution.ModelFacts.rankOne_short_eq_range hσ3
    have hRchart : R = (slShort _ hσ3).range.map (MulAut.conj z).toMonoidHom := by
      exact hR'.trans (congrArg (fun S : Subgroup
        (twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e)) =>
          S.map (MulAut.conj z).toMonoidHom) ((congrArg
            (rankOne (twistedRootGroup (iterateFrobenius (GaloisField p (3 * e)) p e)))
            hi').trans hchart))
    have hg' : g ∈ normalizer ((slShort _ hσ3).range.map
        (MulAut.conj z).toMonoidHom : Set
          (twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e))) := hRchart ▸ hg
    have hinner := exists_inner_normalizer_conj_range_of_linAct hoddK
      (slShort _ hσ3) (slShort_injective hσ3)
      (fun _ hx => linAct_of_centralizes_short hσ3 hK1
        (CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card _ hoddK) hC₀ hgF hx)
      z hg' hgo
    exact hRchart.symm ▸ hinner

theorem odd_normalizer_inner_fundamental_triality_model
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {n e : ℕ} (hadm : StatedLieAdmissible .trialityD4 n p e)
    (R : Subgroup (modelUniv .trialityD4 n p e Fact.out).K)
    (hR : R ∈ fundamentalSubgroups .trialityD4
      (modelUniv .trialityD4 n p e Fact.out).D)
    (g : (modelUniv .trialityD4 n p e Fact.out).K)
    (hg : g ∈ normalizer (R : Set (modelUniv .trialityD4 n p e Fact.out).K))
    (hgo : Odd (orderOf g)) :
    ∃ r ∈ R, ∀ x ∈ R, g * x * g⁻¹ = r * x * r⁻¹ :=
  odd_normalizer_inner_fundamental_triality hp2 hadm.2.1 R hR g hg hgo

end CFSG.LocalAnalysis.UniquenessCase.UC22
