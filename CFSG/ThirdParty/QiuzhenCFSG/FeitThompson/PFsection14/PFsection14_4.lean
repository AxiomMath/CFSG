module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection14.PFsection14_2_SourceData

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 14: theorem (14.4)
-/

noncomputable section

open scoped BigOperators Pointwise

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section14

universe u v w

/-! ## (14.4) -/


public theorem section14_theorem_14_4_source_data_of_q_lt_p
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 P Q U V C D : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d : ℕ}
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    Section13.case_9_7_b_sourceDataForSection13 Tmax Q V W2 W1 D q p v ∧
      v = (q ^ p - 1) / (q - 1) := by
  have hp_ne_three : p ≠ 3 := by
    rcases section14_context_primes_of_sourceData hctx with ⟨_hpPrime, hqPrime⟩
    rcases hctx.1 with
      ⟨hcase, _hSTypeP, _hTTypeP, _hp_card, hq_card, _hC, _hD, _hc, _hd,
        _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, hNotation,
        _hChoice, _hMin⟩
    have hW1Odd : Odd (Nat.card W1) := by
      rcases hcase with
        ⟨hprod, _hcyc, _hW1ne, _hW2ne, _hnorm, _hSmax, _hTmax, _hSMF,
          _hTMF, _hSeq, _hTeq, _hSdisj, _hTdisj, _hST, _hTypeII, _hSType,
          _hTType, _hCover⟩
      rcases hNotation with
        ⟨_ω, _η, _μ, _ν, _μsum, _νsum, _δ, _δ', _σ, hNotationFor⟩
      rcases hNotationFor with
        ⟨hω, _hσ, _hη, _hδ, _hδ', _hμirr, _hνirr, _hμzero_nonprincipal, _hνzero_nonprincipal,
      _hμind, _hνind,
          _hμsum, _hνsum⟩
      rcases hω with ⟨h31, _hqpos, _hppos, _ωFin, _hωNotation, _hωNat⟩
      change Section3.isCyclicTIHypothesis W1 W2 W at h31
      rcases h31 with
        ⟨_hW1le, _hW2le, _hprod31, _hcyc31, hWOdd, _hW1card, _hW2card, _hTI⟩
      exact Odd.of_dvd_nat hWOdd (Subgroup.card_dvd_of_le hprod.1)
    have hqOdd : Odd q := by
      rw [hq_card]
      exact hW1Odd
    have hq_ne_two : q ≠ 2 := by
      intro hq2
      rw [hq2] at hqOdd
      rcases hqOdd with ⟨k, hk⟩
      omega
    have hq_gt_two : 2 < q := lt_of_le_of_ne hqPrime.two_le (Ne.symm hq_ne_two)
    have hqp : q < p := hctx.2
    omega
  have hcase :
      Section13.case_9_7_b_sourceDataForSection13 Tmax Q V W2 W1 D q p v :=
    Section13.theorem_13_13_case_9_7_b_sourceData_of_q_ne_three
      Tmax Smax W W2 W1 Q P V U D C Tfam Sfam τT τS
      q p v u d c (section14_hypothesis_13_1_sourceData_swap hctx.1)
      hp_ne_three
  have h13_15 := Section13.theorem_13_15 Tmax Smax W W2 W1 Q P V U D C
    Tfam Sfam τT τS q p v u d c
    (section14_hypothesis_13_1_sourceData_swap hctx.1) hcase
  rcases section14_context_primes_of_sourceData hctx with ⟨_hp, hq⟩
  have hq_mod_ne_one : q % p ≠ 1 := by
    rw [Nat.mod_eq_of_lt hctx.2]
    exact hq.ne_one
  exact ⟨hcase, h13_15.1 hq_mod_ne_one⟩


public theorem section14_theorem_14_4_source_data_bridge
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        Section13.case_9_7_b_sourceDataForSection13 Tmax Q V W2 W1 D q p v ∧
          v = (q ^ p - 1) / (q - 1) := by
  intro hctx h143
  exact section14_theorem_14_4_source_data_of_q_lt_p hctx

public theorem section14_theorem_14_4_source_bridge
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        Section13.case_9_7_b_for_section13 Tmax D q p v ∧
          v = (q ^ p - 1) / (q - 1) := by
  intro hctx h143
  rcases section14_theorem_14_4_source_data_bridge
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL p q u v c d hctx h143 with
    ⟨hsource, hv⟩
  exact ⟨section14_case_9_7_b_for_section13_of_sourceData hsource, hv⟩

public theorem section14_theorem_14_4_context_bridge
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      Section13.case_9_7_b_for_section13 Tmax D q p v ∧
        v = (q ^ p - 1) / (q - 1) := by
  intro hctx
  rcases section14_theorem_14_4_source_data_of_q_lt_p hctx with
    ⟨hsource, hv⟩
  exact ⟨section14_case_9_7_b_for_section13_of_sourceData hsource, hv⟩


/-- Proof placeholder for `theorem_14_4_statement`. -/
public theorem theorem_14_4
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D L _ : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (_ : Finset (Section1.ClassFunction L))
    (_ : G → Subgroup G)
    (_ _ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (_ : Section1.ClassFunction L)
    (_ : Section1.ClassFunction Smax)
    (_ : Section1.ClassFunction Tmax)
    (_ : Section1.ClassFunction Smax)
    (_ : Section1.ClassFunction Tmax)
    (_ : Section1.ClassFunction L)
    (p q u v c d : ℕ)
    : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      Section13.case_9_7_b_for_section13 Tmax D q p v ∧
        v = (q ^ p - 1) / (q - 1) := by
  exact section14_theorem_14_4_context_bridge
    Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d

end CFSG.Section14
