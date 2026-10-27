module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection6.lemma_6_6_a

namespace CFSG
end CFSG
open CFSG

open scoped MatrixGroups Pointwise TensorProduct

/-! # Lemma 6.6(b) from BG Section 6 -/

public theorem CFSG.lemma_6_6_b
    {G : Type*} [Group G] [Finite G] [Group.IsSolvable G]
    {p : ℕ} [Fact p.Prime] (hpl : HasPLengthOne (p := p) G) {S : Sylow p G}
    (hle : S ≤ derivedSubgroup G) :
    S ≤ ⁅Subgroup.normalizer (G := G) S, Subgroup.normalizer (G := G) S⁆ := by
  let M : Subgroup G := pPrimeCore p G
  let U : Subgroup G := Subgroup.normalizer (G := G) S
  have hMU_top : M ⊔ U = ⊤ := by
    simpa [M, U, sup_comm] using (lemma_6_6_a (G := G) (p := p) hpl (S := S)).2.2
  have hSU : (S : Subgroup G) ≤ U := by
    exact Subgroup.le_normalizer
  have hcopSM : Nat.Coprime (Nat.card S) (Nat.card M) := by
    rcases (IsPGroup.iff_card.mp S.isPGroup') with ⟨n, hn⟩
    rw [hn]
    exact Nat.Coprime.pow_left n (pPrimeCore_coprime_card (p := p) (G := G))
  have hcomm :
      (S : Subgroup G) ⊓ derivedSubgroup G =
        (S : Subgroup G) ⊓ ⁅U, U⁆ := by
    simpa [M, U] using
      lemma_6_5_a (K := M) (U := U) (H := (S : Subgroup G)) hMU_top hSU hcopSM
  have hS_eq_inf : (S : Subgroup G) = (S : Subgroup G) ⊓ derivedSubgroup G := by
    exact (inf_eq_left.mpr hle).symm
  calc
    (S : Subgroup G) = (S : Subgroup G) ⊓ derivedSubgroup G := hS_eq_inf
    _ = (S : Subgroup G) ⊓ ⁅U, U⁆ := hcomm
    _ ≤ ⁅U, U⁆ := inf_le_right
