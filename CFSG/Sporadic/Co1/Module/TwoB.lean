module

public import CFSG.Monster.GMS.Facts.Co1TwoB
public import CFSG.Sporadic.Co1.Module.TwoBCert
public import CFSG.Monster.B.TwoA.Census.LatticeInv
public import CFSG.Sporadic.Co1.Module.InvAssemble
public import CFSG.Sporadic.Co1.Module.InvClass

public section

namespace CFSG.Monster.GMS

open CFSG.Monster.B.TwoA.Census CFSG.Sporadic.Co1.Module CFSG.Sporadic.Co1.Module.TwoB
  CFSG.Blueprint.NativeSporadic

theorem co1_involution_classes :
    ∃ sA sB sC : Co1, RepFacts sA sB sC ∧
    ∀ s : Co1, orderOf s = 2 → IsConj s sA ∨ IsConj s sB ∨ IsConj s sC := by
  obtain ⟨sA, sB, sC, hrep⟩ := rep_facts
  obtain ⟨-, -, hmem, hcls, -⟩ := lattice_quotient_three_involution_classes
  obtain ⟨c, hc⟩ := exists_conj_three_of_chevalley monoN hmem hcls
  exact ⟨sA, sB, sC, hrep, co1Inv_classes hrep c hc⟩

theorem isCo1TwoB_isConj
    {s t : Co1} (hs : IsCo1TwoB s) (ht : IsCo1TwoB t) : IsConj s t := by
  obtain ⟨sA, sB, sC, hrep, hcls⟩ := co1_involution_classes
  obtain ⟨-, -, -, hfA, hfB, hfC, hqA, hqB, hqC, -⟩ := hrep
  have key : ∀ u : Co1, IsCo1TwoB u → IsConj u sB := by
    intro u hu
    obtain ⟨hord, hcard, hq⟩ := hu
    rcases hcls u hord with h | h | h
    · exfalso
      have h1 := (co1Inv_isConj_invariants h).1
      have e1 : (co1Fix sA).ncard = 2 ^ 16 := hfA
      rw [hcard, e1] at h1
      norm_num at h1
    · exact h
    · exfalso
      have h1 := (co1Inv_isConj_invariants h).2.1
      have hempty : {v : Fin 24 → ZMod 2 | CFSG.Sporadic.Co1.Module.co1Act u v = v ∧
          CFSG.Sporadic.Co1.Module.q₀ v = 1} = ∅ := by
        ext v
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro hv hq1
        have := hq v hv
        rw [hq1] at this
        exact absurd this (by decide)
      rw [hempty, hqC] at h1
      norm_num at h1
  exact (key s hs).trans (key t ht).symm

theorem isCo1TwoB_sBc :
    IsCo1TwoB sBc := by
  refine ⟨?_, ncard_fix_sBc, fun v hv => ?_⟩
  · obtain ⟨-, -, ho, -⟩ := repOK_facts repOK_B
    exact orderOf_eq_of_orderIs matHom_sBc (by norm_num) ho
  · by_contra h
    have h1 : CFSG.Sporadic.Co1.Module.q₀ v = 1 := by
      rcases zmod2_cases (CFSG.Sporadic.Co1.Module.q₀ v) with h0 | h1
      · exact absurd h0 h
      · exact h1
    have hmem : v ∈ {v : Fin 24 → ZMod 2 | CFSG.Sporadic.Co1.Module.co1Act sBc v = v ∧
        CFSG.Sporadic.Co1.Module.q₀ v = 1} := ⟨hv, h1⟩
    have := ncard_fixQ_sBc
    rw [Set.ncard_eq_zero (Set.toFinite _)] at this
    rw [this] at hmem
    exact hmem

theorem co1TwoBFacts :
    Co1TwoBFacts := by
  intro s hs
  obtain ⟨c, hc⟩ := isConj_iff.1 (isCo1TwoB_isConj hs isCo1TwoB_sBc)
  have hfacts : TwoBFacts s := by
    have h := twoBFacts_conj twoBFacts_sBc c⁻¹
    rwa [← hc, show c⁻¹ * (c * s * c⁻¹) * c⁻¹⁻¹ = s by group] at h
  obtain ⟨hcard, hb, ht, S, T, hS, hT, hSc, hTc, hint⟩ := hfacts
  refine ⟨by rw [hcard]; norm_num, fun v hv hv0 => hb v hv hv0,
    fun v hv w hw hv0 hw0 => ht v w hv hw hv0 hw0, ?_⟩
  intro H hH hidx N hNH hNnorm hNp
  have h := card_le_of_normal_two_subgroup (k := 15) (m := 61425) hH hidx hS hT (by decide)
    (by rw [hcard]; norm_num) hSc hTc hNH hNnorm hNp
  exact h.trans hint

end CFSG.Monster.GMS
