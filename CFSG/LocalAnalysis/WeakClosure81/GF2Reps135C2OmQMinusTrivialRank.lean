module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusInterfaces
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusTrivial
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusNFWeyl
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusWeightRank
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusTorus
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusWeights
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusWeightsTorus
import CFSG.LieType.TorusWeights.RootOp
public import CFSG.HardMathSupport.GuralnickMalle.EndFieldDescent.Basic
public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.OffenderBasic
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQPlusInterfaces

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted CFSG.Quasithin.SmithCurtis
  CFSG.LieType.RootSystem CFSG.StandardType
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

theorem omq_omMinus_trivial_rank (h1s : OmqMinusWeightVectorShort) (h2 : OmqRankFromWeights)
    {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {k V : Type} [Field k] [CharP k 2]
    [AddCommGroup V] [Module k V] [Module.Finite k V] (ι : K →+* k) (ι' : ShortField b c →+* k)
    (hι' : ∀ x : K, ι' (algebraMap K (ShortField b c) x) = ι x)
    {σ : Representation k (spinGroup (quadMinus n K b c)) V} (hσ : IsSimpleRep σ) {y : V}
    {χ : spinGroup (quadMinus n K b c) → k} {μ : Fin (n - 1) → k}
    (ht : (SmallO8mCurtis.curtisDatum n hn hirr).IsCurtisType σ y χ μ)
    (hex : ∃ i : Fin (n - 1), μ i = (SmallO8mCurtis.curtisDatum n hn hirr).dScalar χ i)
    (hχ1 : ∀ h ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H, χ h = 1) {f : ℕ}
    (hF : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    {x : (coxeterMatrix (isFiniteType_cartanB (n - 1))).Group} {π : Equiv.Perm (Fin (n - 1))}
    {s : Fin (n - 1) → ℤ} (hxr : omqnfRealizes (n - 1) x π s) (hs : SpIsSign s)
    (hsh : OmqMinusShape (by omega : 2 ≤ n - 1) π s) :
    7 ≤ Module.finrank k
      (LinearMap.range (σ ((SmallO8mCurtis.curtisDatum n hn hirr).nW x) - 1)) := by
  classical
  haveI := fact_shortField hirr
  haveI := finite_shortField (b := b) (c := c)
  haveI : CharP (ShortField b c) 2 :=
    charP_of_injective_algebraMap (algebraMap K (ShortField b c)).injective 2
  have hm : Nat.card Kˣ = 2 ^ f - 1 := by rw [Nat.card_units, hF]
  have hh : Nat.card K + 1 = 2 ^ f + 1 := by rw [hF]
  obtain ⟨J, hJrange, hJinj, hJmove⟩ :=
    omq_minus_exists_trivial_weights hf (by omega : 3 ≤ n - 1) hm hh hs hsh
  have hC : Nat.card (ShortField b c)ˣ = Nat.card Kˣ * (Nat.card K + 1) :=
    omq_omMinus_card_shortField_units hirr
  have hχC : ∀ u : (ShortField b c)ˣ,
      χ (shortTorusHom n hirr ⟨0, by omega⟩ u) =
        ι' (u : ShortField b c) ^ Nat.card (ShortField b c)ˣ := by
    intro u
    rw [hχ1 _ ((omq_omMinus_torus_mem_H hn hirr).2 _ u), ← map_pow,
      ← Units.val_pow_eq_pow_val, pow_card_eq_one', Units.val_one, map_one]
  have hvec : ∀ i : Fin 7, ∃ w : V, w ≠ 0 ∧ ∀ g ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H,
      σ g w = omqMinusWt n ι ι' (omqMinusTriv (n - 1) (Nat.card Kˣ) (Nat.card K + 1) (J i)
        (by omega)) g • w := by
    intro i
    obtain ⟨w, hw0, hw⟩ := h1s hn hirr ι ι' hι' hσ ht hex (C := Nat.card (ShortField b c)ˣ)
      (j := J i) (by rw [hC]; have := (hJrange i).1; have := (hJrange i).2; nlinarith)
      le_rfl hχC (CFSG.LieType.TorusWeights.odd_choose_card_units
        (by rw [hC]; exact (hJrange i).2.le))
    refine ⟨w, hw0, fun g hg => ?_⟩
    rw [hw g hg, hχ1 g hg, one_mul]
    congr 1
    have hneg := omq_omMinus_wt_neg hn hirr rfl rfl ι ι' ((Pi.single ⟨0, by omega⟩
      (1 : ZMod (Nat.card Kˣ)) : Fin (n - 1) → ZMod (Nat.card Kˣ)),
        (1 : ZMod (Nat.card K + 1))) hg
    rw [← hneg, ← omq_omMinus_wt_nsmul hn hirr rfl rfl ι ι' (J i) _ hg]
    congr 1
    refine Prod.ext ?_ ?_
    · funext l
      by_cases hl : l = ⟨0, by omega⟩
      · subst hl
        simp [omqMinusTriv]
      · simp [omqMinusTriv, hl, Pi.single_apply]
    · simp [omqMinusTriv]
  choose w hw0 hw using hvec
  exact omq_omMinus_rank_of_weights h2 hn hirr ι ι' hxr hs (d := 7)
    (ν := fun i => omqMinusTriv (n - 1) (Nat.card Kˣ) (Nat.card K + 1) (J i) (by omega))
    hJinj hJmove hw0 hw

end CFSG.LocalAnalysis.WeakClosure81
