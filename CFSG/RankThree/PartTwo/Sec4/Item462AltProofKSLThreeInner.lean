module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiFrob
public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKSLThreeInnerAux
public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKSLThreeDatumFixed
public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKSLThreeFixedDatumCyc
public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKSLThreeFixedDatumGLTwo

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

open CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial

theorem core_inner {π : Bool} {p f : ℕ} {K : Type} [Field K] (hK : PiField π p f K)
    (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f) {y : GL (Fin 3) K}
    (hy : y ∈ glPi π 3 (p ^ f) K) (hyZ : y ∉ zPi π 3 (p ^ f) K)
    (hy3 : y ^ 3 ∈ zPi π 3 (p ^ f) K) {β' : MulAut (slPi π 3 (p ^ f) K)}
    (hβ' : ∀ s, ((β' s : slPi π 3 (p ^ f) K) : GL (Fin 3) K) = y * s * y⁻¹)
    (hD : NoncyclicDatum β') :
    p ≠ 2 ∧ ∃ v : slPi π 3 (p ^ f) K, v ^ 3 = 1 ∧ β' = MulAut.conj v := by
  haveI := hK.finite
  have hq3 : 3 < p ^ f := by
    cases π
    · change p ^ f % 3 = 2 at hq
      omega
    · change p ^ f % 3 = 1 at hq
      omega
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hFD := fixedDatum_of_noncyclicDatum hD
  obtain ⟨y', ⟨z, hz, rfl⟩, h1 | h2 | h3⟩ := rank3II_4_10_one hK hq hτ hτ1 hy hyZ hy3
  all_goals
    have hz' : z ∈ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) K :=
      (Subgroup.mem_inf.mp ((zPi_eq hπ hq' hτ hτ1) ▸ hz)).2
    have hβ'' : ∀ s, ((β' s : slPi π 3 (p ^ f) K) : GL (Fin 3) K) =
        (y * z) * (s : GL (Fin 3) K) * (y * z)⁻¹ := by
      intro s
      have hc : z * (s : GL (Fin 3) K) = (s : GL (Fin 3) K) * z :=
        (commute_of_mem_statedScalars hz' (s : GL (Fin 3) K)).symm
      rw [hβ' s]
      calc y * (s : GL (Fin 3) K) * y⁻¹ = y * (z * s * z⁻¹) * y⁻¹ := by
            rw [hc, mul_inv_cancel_right]
        _ = (y * z) * s * (y * z)⁻¹ := by group
    obtain ⟨eF⟩ := fixed_equiv_centralizer hβ''
  · obtain ⟨hg, ⟨hC⟩, -⟩ := h1
    obtain ⟨v, hv3, hv⟩ := exists_cube_one_conj hK hq hτ hg hβ''
    refine ⟨fun hp2 => ?_, v, hv3, hv⟩
    exact false_of_fixedDatum_odd (odd_card_of_char_two hK hp2 ⟨eF.trans hC⟩) hFD
  · obtain ⟨-, ⟨hC⟩, -⟩ := h2
    exact (false_of_fixedDatum_glTwo hK hq3 (eF.trans hC) hFD).elim
  · obtain ⟨-, -, -, hcyc, -⟩ := h3
    haveI : IsCyclic ↥(fixedSub β') := eF.isCyclic.mpr hcyc
    exact (false_of_fixedDatum_cyclic hFD).elim

end CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

end
