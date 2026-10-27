module

public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKSLThreeFieldPure
public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKSLThreeConjAut

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

open CFSG CFSG.RankThree.PartTwo.Sec4

theorem core_field {π : Bool} {p f : ℕ} {K : Type} [Field K] (hK : PiField π p f K)
    (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f) {σ : K ≃+* K} (hσ : orderOf σ = 3)
    {H : GL (Fin 3) K} (hH : H ∈ glPi π 3 (p ^ f) K) {β' : MulAut (slPi π 3 (p ^ f) K)}
    (hβ' : ∀ s : slPi π 3 (p ^ f) K, ((β' s : slPi π 3 (p ^ f) K) : GL (Fin 3) K) =
      H * frobGL σ (H⁻¹ * (s : GL (Fin 3) K) * H) * H⁻¹)
    (hD : NoncyclicDatum β') : False := by
  obtain ⟨γ, hγ⟩ := exists_conjAut_slPi hK hH
  have hγinv : ∀ x : slPi π 3 (p ^ f) K,
      ((γ⁻¹ x : slPi π 3 (p ^ f) K) : GL (Fin 3) K) = H⁻¹ * (x : GL (Fin 3) K) * H := by
    intro x
    have h := hγ (γ⁻¹ x)
    rw [MulAut.apply_inv_self] at h
    calc ((γ⁻¹ x : slPi π 3 (p ^ f) K) : GL (Fin 3) K)
        = H⁻¹ * (H * ((γ⁻¹ x : slPi π 3 (p ^ f) K) : GL (Fin 3) K) * H⁻¹) * H := by group
      _ = H⁻¹ * (x : GL (Fin 3) K) * H := by rw [← h]
  have hD' := hD.conj γ⁻¹
  rw [inv_inv] at hD'
  refine core_field_pure hK hq hq2 hσ ?_ hD'
  intro s
  rw [MulAut.mul_apply, MulAut.mul_apply, hγinv, hβ' (γ s), hγ s]
  have h1 : H⁻¹ * (H * (s : GL (Fin 3) K) * H⁻¹) * H = (s : GL (Fin 3) K) := by group
  rw [h1]
  group

end CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

end
