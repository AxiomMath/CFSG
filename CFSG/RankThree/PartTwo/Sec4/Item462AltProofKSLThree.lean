module

public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKSLThreeStmt
public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKSLThreeModel
public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKSLThreeDatumBridge
public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKSLThreeInner
public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKSLThreeField

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

open CFSG CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial

theorem pow_three_mem_zPi {π : Bool} {p f : ℕ} {K : Type} [Field K] (hK : PiField π p f K)
    (hq : ModThree π (p ^ f)) {y : GL (Fin 3) K} (hy : y ∈ glPi π 3 (p ^ f) K)
    {β' : MulAut (slPi π 3 (p ^ f) K)} (hβ'3 : β' ^ 3 = 1)
    (hS : ∀ s, ((β' s : slPi π 3 (p ^ f) K) : GL (Fin 3) K) = y * s * y⁻¹) :
    y ^ 3 ∈ zPi π 3 (p ^ f) K := by
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  rw [zPi_eq hπ hq' hτ hτ1]
  refine Subgroup.mem_inf.mpr ⟨pow_mem hy 3, ?_⟩
  rw [← centralizer_slPi hπ hq' hτ hτ1, Subgroup.mem_centralizer_iff]
  intro g hg
  have h3 : y * (y * (y * g * y⁻¹) * y⁻¹) * y⁻¹ = g := by
    have := congrArg (fun γ : MulAut (slPi π 3 (p ^ f) K) =>
      ((γ ⟨g, hg⟩ : slPi π 3 (p ^ f) K) : GL (Fin 3) K)) hβ'3
    simp only [pow_three, MulAut.mul_apply, MulAut.one_apply, hS] at this
    exact this
  have : y ^ 3 * g = g * y ^ 3 := by
    calc y ^ 3 * g = (y * (y * (y * g * y⁻¹) * y⁻¹) * y⁻¹) * y ^ 3 := by
          simp only [pow_three]
          group
      _ = g * y ^ 3 := by rw [h3]
  exact this.symm

theorem kSLThreeCentralizerQ_holds : KSLThreeCentralizerQ := by
  intro X _ _ hXq p e _ he hX β hβ3 hβ
  obtain ⟨π, K, _, hK, hq, hq2, φ, hφ, hker, hlift⟩ := exists_coverLift hXq he hX
  haveI := hK.finite
  have hπ : π = false → UnitaryFieldData p e K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ e) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hβ3' : β ^ 3 = 1 := by rw [← hβ3]; exact pow_orderOf_eq_one β
  obtain ⟨β', hβ'3, hβ'⟩ := hlift β hβ3'
  have hZ : Nat.card (Subgroup.center (slPi π 3 (p ^ e) K)) = 3 := KFacts.card_center_slPi hK hq
  have hD := noncyclicDatum_of_innThetaNoncyclic φ hφ hker hZ hβ'3 hβ' hβ
  rcases KFacts.exists_conj_or_field_of_pow_three_eq_one hK hq2 hβ'3 with
    ⟨y, hy, hS⟩ | ⟨σ, hσ, H, hH, hHs⟩
  · have hS' := KFacts.semiAct_one_iff.mp hS
    have hy3 := pow_three_mem_zPi hK hq hy hβ'3 hS'
    have hyZ : y ∉ zPi π 3 (p ^ e) K := by
      intro hyz
      rw [zPi_eq hπ hq' hτ hτ1] at hyz
      have hz' := (Subgroup.mem_inf.mp hyz).2
      have hβ1 : β = 1 := by
        refine MulEquiv.ext fun x => ?_
        obtain ⟨s, rfl⟩ := hφ x
        rw [← hβ' s, MulAut.one_apply]
        congr 1
        apply Subtype.ext
        rw [hS' s]
        have hc : y * (s : GL (Fin 3) K) = (s : GL (Fin 3) K) * y :=
          (commute_of_mem_statedScalars hz' (s : GL (Fin 3) K)).symm
        rw [hc, mul_inv_cancel_right]
      rw [hβ1, orderOf_one] at hβ3
      omega
    obtain ⟨hp2, v, hv3, hv⟩ := core_inner hK hq hq2 hy hyZ hy3 hS' hD
    refine ⟨hp2, φ v, by rw [← map_pow, hv3, map_one], ?_⟩
    refine MulEquiv.ext fun x => ?_
    obtain ⟨s, rfl⟩ := hφ x
    rw [← hβ' s, hv, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
  · exact (core_field hK hq hq2 hσ hH hHs hD).elim

end CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

end
