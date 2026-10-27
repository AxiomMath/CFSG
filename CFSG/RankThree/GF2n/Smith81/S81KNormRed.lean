module

public import CFSG.RankThree.GF2n.Smith81.S81TCond
public import CFSG.RankThree.GF2n.Smith81.S81UAct

public section

namespace CFSG.RankThree.GF2n.Smith81.SK

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81
  CFSG.RankThree.GF2n.Smith81.EGeom

section NormQuotTargets

open CFSG.RankThree.GF2n.Smith81.D6Spin

theorem normQuotE4_of_core
    (hcore : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K → ∀ T : W K ≃ₗ[K] W K, (∀
        g ∈ EAut0 K, ∃ g' ∈ EAut0 K, T * g = g' * T) → (∃ k : ℕ, T ^ (2 ^ k) = 1) → T ∈ EAut0
        K) (hFE1 : D6Spin.Smith24E4UniformStatement) :
    NormQuotE4Statement := by
  intro G _ _ M Q Z B IH hc h4 E hEH0 hE2
  obtain ⟨K, _, _, _, γ, M₀, hg⟩ := stroth_globalModelData hc.ctx.hyp
  obtain ⟨ψ, φ, d⟩ := hFE1 G M Q Z B IH hc.toRemCfg h4 K γ M₀ hg
  have hctx : Ctx M Q Z B := hc.ctx
  have hH : StrothHyp M Q Z := hctx.hyp
  have hq : 4 ≤ Nat.card K := hg.card ▸ hH.q4
  have hEM : ∀ m ∈ E, m ∈ M := fun m hm => (Subgroup.mem_inf.mp (hEH0 hm)).1
  have hpow : ∀ m ∈ E, ∃ k : ℕ, m ^ (2 ^ k) = 1 := by
    intro m hm
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hE2) ⟨m, hm⟩
    refine ⟨k, ?_⟩
    have h1 := pow_orderOf_eq_one (⟨m, hm⟩ : E)
    rw [hk] at h1
    exact congrArg Subtype.val h1
  have hEL : E ≤ Lgen M (LB M Q B) := by
    intro m hm
    obtain ⟨T, hT⟩ := exists_actsOnQtAsU hg ψ (hEH0 hm)
    obtain ⟨k, hk⟩ := hpow m hm
    exact hT.mem_Lgen hctx d (hEM m hm)
      (hcore K hq T (hT.normalizesGamma hctx d (hEM m hm)) ⟨k, hT.pow_eq_one hH (hEM m hm) hk⟩)
  rw [inf_eq_left.mpr hEL]
  omega

end NormQuotTargets

end CFSG.RankThree.GF2n.Smith81.SK
