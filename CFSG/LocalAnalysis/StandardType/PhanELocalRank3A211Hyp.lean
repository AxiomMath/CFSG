module

public import CFSG.LocalAnalysis.StandardType.PhanELocalRank3A211Def
public import CFSG.LocalAnalysis.StandardType.PhanELocalClsNR

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry Module

variable {K : Type} [Field K] [Finite K] (f : ℕ) [CharP K 2]

private def plh_v2 (s : K) : Fin 2 → K := ![s, 1]

private theorem plh_v2_ne_zero (s : K) : plh_v2 s ≠ 0 := by
  intro h
  have h1 := congrFun h 1
  simpa [plh_v2] using h1

private theorem plh_v2_mem_iff (s t : K) (h : plh_v2 t ∈ K ∙ plh_v2 s) : t = s := by
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h
  have h1 : a = 1 := by
    have h := congrFun ha 1
    simpa [plh_v2] using h
  have h0 : a * s = t := by
    have h := congrFun ha 0
    simpa [plh_v2] using h
  rw [← h0, h1, one_mul]

private theorem plh_v2_notMem_single (s : K) :
    (![1, 0] : Fin 2 → K) ∉ K ∙ plh_v2 s := by
  intro hmem
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
  have h1 : a = 0 := by
    have h := congrFun ha 1
    simpa [plh_v2] using h
  have h0 : a * s = 1 := by
    have h := congrFun ha 0
    simpa [plh_v2] using h
  rw [h1, zero_mul] at h0
  exact zero_ne_one h0

private theorem plh_v2_finrank (s : K) : finrank K (K ∙ plh_v2 s) = 1 :=
  finrank_span_singleton (plh_v2_ne_zero s)

theorem clsHyp_a3_211 (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    ClsHyp (D211 (K := K) f) (2 ^ f + 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro S hS
    by_contra h
    have hmem : ∀ s : K, K ∙ plh_v2 s ∈ S := by
      intro s
      by_contra hs
      exact h ⟨K ∙ plh_v2 s, plh_v2_notMem_single s, plh_v2_finrank s, hs⟩
    haveI : Fintype K := Fintype.ofFinite K
    let g : K → ↥S := fun s => ⟨K ∙ plh_v2 s, hmem s⟩
    have hg : Function.Injective g := by
      intro s t hst
      have hst' : K ∙ plh_v2 s = K ∙ plh_v2 t := congrArg Subtype.val hst
      exact (plh_v2_mem_iff s t (by rw [hst']; exact Submodule.mem_span_singleton_self _)).symm
    have hcard := Fintype.card_le_of_injective g hg
    rw [Fintype.card_coe] at hcard
    have h16 : 16 ≤ Fintype.card K := by
      rw [← Nat.card_eq_fintype_card, hK]
      simpa using Nat.pow_le_pow_left hq 2
    omega
  · intro c _ _
    exact exists_two_nrpt (K := K) f hK hq
  · intro c c' _ _ _ _ _
    obtain ⟨M₁, M₂, hneM, hM₁V, hM₂V, hf₁, hf₂, hg₁, hg₂⟩ :=
      exists_two_nrpt (K := K) f hK hq
    exact ⟨M₁, hM₁V, hf₁, hg₁, hg₁⟩
  · intro a b d _ _ _ _ _ _ _ _ _
    obtain ⟨B, hBne, hBcard, hBmem, hBgood⟩ := exists_nr_lines (K := K) f hK hq
    refine ⟨B, hBne, hBcard, hBmem, ?_⟩
    intro w hwV hwB
    obtain ⟨hw0, hwNR⟩ := hBgood w hwV hwB
    exact ⟨hw0, hwNR, hwNR, hwNR⟩
  · rw [hK]
    nlinarith [hq]

end CFSG.ClassicalInvolution.Phan.PhanE

end
