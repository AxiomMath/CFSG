module

public import CFSG.LocalAnalysis.StandardType.GGKD2Connected1619Contracts
public import CFSG.Open.StatedAPI
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldSympMark
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnSympRed
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119

public section

namespace S2MathAs3_1619Final

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Open S2MathAs3_1615

private noncomputable def ltrspa_spProjEquiv (m : ℕ) (K : Type) [Field K] [CharP K 2] :
    LargeEvenProj (LargeEvenSpGroup K m) ≃* StatedSp m K :=
  (QuotientGroup.quotientMulEquivOfEq
    (CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot (n := m) (K := K))).trans
    QuotientGroup.quotientBot

private theorem ltrspa_of_recipe (lab : LargeEvenLabel) (Q : LargeEvenRawCont)
    (hn : 1 ≤ lab.n)
    (hraw : LargeEvenRecipeSymplectic lab.rank (2 ^ lab.n) false Q) :
    LargeEvenRecipeSymplectic lab.rank (2 ^ lab.n) false
      (fun R _ I F => Q R I F ∧ SpRawRealization lab R I) := by
  obtain ⟨K, hField, hFinite, hcard, hQ⟩ := hraw
  letI : Field K := hField
  letI : Finite K := hFinite
  have h2 : (2 : K) = 0 := by
    have h0 : Nat.card K • (1 : K) = 0 := card_nsmul_eq_zero'
    rw [nsmul_one, hcard, Nat.cast_pow, Nat.cast_ofNat] at h0
    exact (pow_eq_zero_iff (by omega : lab.n ≠ 0)).mp h0
  have hchar : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  letI : CharP K 2 := hchar
  have hft : ¬ (false = true) := by simp
  simp only [LargeEvenRecipeSymplectic, if_neg hft] at hQ ⊢
  refine ⟨K, hField, hFinite, hcard, hQ, ?_⟩
  let theta : LargeEvenProj (LargeEvenSpGroup K lab.rank) ≃* StatedSp lab.rank K :=
    ltrspa_spProjEquiv lab.rank K
  refine ⟨K, hField, hFinite, hchar, hcard, theta, ?_⟩
  intro beta hbeta
  let i : MulAut (StatedProj (StatedSp lab.rank K)) := beta
  have hi : i ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSpGroup K lab.rank)) (LargeEvenGSpSet K lab.rank) := hbeta
  obtain ⟨A, hA⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GFldSympMark.exists_conjAut_eq_of_mem_matConjImage
      (m := lab.rank) (K := K) hi
  obtain ⟨x, hx⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnSympRed.exists_conjAut_eq_conj
      (m := lab.rank) (K := K) h2 A
  refine ⟨theta (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj lab.rank K x), ?_⟩
  intro r
  have hb : beta =
      MulAut.conj (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj lab.rank K x) :=
    hA.symm.trans hx
  rw [hb, MulAut.conj_apply, map_mul, map_mul, map_inv]

private theorem ltrspa_recipe_bc (lab : LargeEvenLabel) (Q : LargeEvenRawCont)
    (hn : 1 ≤ lab.n) (htag : lab.tag = .B ∨ lab.tag = .C)
    (hraw : CFSG.StandardType.LargeEvenRawDatum lab Q) :
    CFSG.StandardType.LargeEvenRawDatum lab
      (fun R _ I F => Q R I F ∧ SpRawRealization lab R I) := by
  rcases htag with hB | hC
  · have h := ltrspa_of_recipe lab Q hn
      (by simpa only [CFSG.StandardType.LargeEvenRawDatum, hB] using hraw)
    simpa only [CFSG.StandardType.LargeEvenRawDatum, hB] using h
  · have h := ltrspa_of_recipe lab Q hn
      (by simpa only [CFSG.StandardType.LargeEvenRawDatum, hC] using hraw)
    simpa only [CFSG.StandardType.LargeEvenRawDatum, hC] using h

theorem spProducer_holds :
    ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → (lab.tag = .B ∨ lab.tag = .C) →
      LargeEvenLabelAll lab (fun R _ I _ => SpRawRealization lab R I) := by
  intro lab hΛ htag Q hraw
  exact ltrspa_recipe_bc lab Q hΛ.1 htag hraw

end S2MathAs3_1619Final

end