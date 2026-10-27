module

public import CFSG.RankThree.PartOne.KC.OrthogonalQPlusOneNatural
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinear

public section

open Module QuadraticMap CFSG CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal

namespace CFSG.RankThree.PartOne

theorem orthogonal_inner_plane_common_centralizer_q_plus_one_of_natural
    {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V) (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpl : p ≠ ringChar K) (hpq : p ∣ Nat.card K + 1)
    (D : Subgroup (MulAut (ProjOrthDerived Q)))
    (hD : (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range ≤ D)
    (A : Subgroup (ProjOrthDerived Q)) (hA : Assembly.IsElemAbelian p A)
    (hAc : Nat.card A = p ^ 2)
    (hnat : ∀ α : MulAut (ProjOrthDerived Q),
      (∀ a ∈ A, a ≠ 1 → ∀ d ∈ CFSG.layer ↥(D ⊓ Subgroup.centralizer
          ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q)))),
        α * (d : MulAut (ProjOrthDerived Q)) = (d : MulAut (ProjOrthDerived Q)) * α) →
      KCOrthogonalAut.InducedBySemilinear Q α) :
    (⨅ (a : ProjOrthDerived Q) (_ : a ∈ A ∧ a ≠ 1),
      Subgroup.centralizer (((CFSG.layer ↥(D ⊓ Subgroup.centralizer
            ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q))))).map
          (D ⊓ Subgroup.centralizer
            ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q)))).subtype :
          Subgroup (MulAut (ProjOrthDerived Q))) : Set (MulAut (ProjOrthDerived Q)))) = ⊥ := by
  refine eq_bot_iff.mpr fun α hα => ?_
  have hcent : ∀ a ∈ A, a ≠ 1 → ∀ d ∈ CFSG.layer ↥(D ⊓ Subgroup.centralizer
      ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q)))),
      α * (d : MulAut (ProjOrthDerived Q)) = (d : MulAut (ProjOrthDerived Q)) * α := by
    intro a ha ha1 d hd
    have h1 := Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hα a) ⟨ha, ha1⟩
    exact (Subgroup.mem_centralizer_iff.mp h1 (d : MulAut (ProjOrthDerived Q)) ⟨d, hd, rfl⟩).symm
  obtain ⟨σ, F, hFσ, μ, hμ, hFQ, hαF⟩ := hnat α hcent
  exact (Subgroup.mem_bot).mpr (qplus_natural hQ hT hp hp3 hpl hpq D hD A hA hAc σ F hFσ μ hμ hFQ
    α hαF hcent).2.2

theorem orthogonal_inner_plane_common_centralizer_q_plus_one_of_dim
    {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V) (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) (hdim : 7 ≤ finrank K V)
    (hD4 : finrank K V = 8 → ¬ ∃ U : Submodule K V, finrank K U = 4 ∧ ∀ u ∈ U, Q u = 0)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpl : p ≠ ringChar K) (hpq : p ∣ Nat.card K + 1)
    (D : Subgroup (MulAut (ProjOrthDerived Q)))
    (hD : (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range ≤ D)
    (A : Subgroup (ProjOrthDerived Q)) (hA : Assembly.IsElemAbelian p A)
    (hAc : Nat.card A = p ^ 2) :
    (⨅ (a : ProjOrthDerived Q) (_ : a ∈ A ∧ a ≠ 1),
      Subgroup.centralizer (((CFSG.layer ↥(D ⊓ Subgroup.centralizer
            ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q))))).map
          (D ⊓ Subgroup.centralizer
            ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q)))).subtype :
          Subgroup (MulAut (ProjOrthDerived Q))) : Set (MulAut (ProjOrthDerived Q)))) = ⊥ :=
  orthogonal_inner_plane_common_centralizer_q_plus_one_of_natural Q hQ hT hp hp3 hpl hpq D hD A hA
    hAc fun α _ => KCOrthogonalAut.orthogonal_aut_semilinear_of_seven_le Q hQ hdim hD4 α

end CFSG.RankThree.PartOne
