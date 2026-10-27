module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusInterfaces
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusNFWeyl
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusNFWeylEx
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusWeightsConj
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusWeightsInj
public import CFSG.HardMathSupport.GuralnickMalle.EndFieldDescent.Basic
public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.OffenderBasic
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQPlusInterfaces

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted CFSG.Quasithin.SmithCurtis
  CFSG.LieType.RootSystem CFSG.StandardType
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

theorem omq_omMinus_rank_of_weights (h2 : OmqRankFromWeights) {n : ℕ} (hn : 4 ≤ n) {K : Type}
    [Field K] [Finite K] [CharP K 2] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {k V : Type} [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V] (ι : K →+* k)
    (ι' : ShortField b c →+* k) {σ : Representation k (spinGroup (quadMinus n K b c)) V}
    {x : (coxeterMatrix (isFiniteType_cartanB (n - 1))).Group} {π : Equiv.Perm (Fin (n - 1))}
    {s : Fin (n - 1) → ℤ} (hxr : omqnfRealizes (n - 1) x π s) (hs : SpIsSign s) {d : ℕ}
    {ν : Fin d → OmqMinusLat (n - 1) (Nat.card Kˣ) (Nat.card K + 1)}
    (hinj : Function.Injective ν) (hmove : ∀ i i', ν i ≠ omqMinusAct π s (ν i'))
    {w : Fin d → V} (hw0 : ∀ i, w i ≠ 0)
    (hw : ∀ i, ∀ g ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H,
      σ g (w i) = omqMinusWt n ι ι' (ν i) g • w i) :
    d ≤ Module.finrank k
      (LinearMap.range (σ ((SmallO8mCurtis.curtisDatum n hn hirr).nW x) - 1)) := by
  classical
  have hnorm : ∀ g ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H,
      ((SmallO8mCurtis.curtisDatum n hn hirr).nW x)⁻¹ * g *
        (SmallO8mCurtis.curtisDatum n hn hirr).nW x ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H :=
    fun g hg => (omq_omMinus_wt_conj hn hirr rfl rfl ι ι' hxr hs
      (0 : OmqMinusLat (n - 1) (Nat.card Kˣ) (Nat.card K + 1)) hg).1
  have hdist : ∀ l l' : Fin d, l ≠ l' → ∃ g ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H,
      omqMinusWt n ι ι' (ν l) g ≠ omqMinusWt n ι ι' (ν l') g := by
    intro l l' hll
    by_contra hcon
    apply hll
    apply hinj
    refine omq_omMinus_wt_injective hn hirr rfl rfl ι ι' (fun g hg => ?_)
    by_contra hne
    exact hcon ⟨g, hg, hne⟩
  have hmv : ∀ l l' : Fin d, ∃ g ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H,
      omqMinusWt n ι ι' (ν l) (((SmallO8mCurtis.curtisDatum n hn hirr).nW x)⁻¹ * g *
        (SmallO8mCurtis.curtisDatum n hn hirr).nW x) ≠ omqMinusWt n ι ι' (ν l') g := by
    intro l l'
    by_contra hcon
    have hne : omqMinusAct π s (ν l) ≠ ν l' := (hmove l' l).symm
    apply hne
    refine omq_omMinus_wt_injective hn hirr rfl rfl ι ι' (fun g hg => ?_)
    have hc := omq_omMinus_wt_conj hn hirr rfl rfl ι ι' hxr hs (ν l) hg
    rw [← hc.2]
    by_contra hne'
    exact hcon ⟨g, hg, hne'⟩
  exact h2 σ (SmallO8mCurtis.curtisDatum n hn hirr).H
    ((SmallO8mCurtis.curtisDatum n hn hirr).nW x) hnorm d
    (fun i => omqMinusWt n ι ι' (ν i)) w hw0 hw hdist hmv

theorem omq_omMinus_rank_of_weight_orbit (h2 : OmqRankFromWeights) {n : ℕ} (hn : 4 ≤ n)
    {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {k V : Type} [Field k] [AddCommGroup V]
    [Module k V] [Module.Finite k V] (ι : K →+* k) (ι' : ShortField b c →+* k)
    {σ : Representation k (spinGroup (quadMinus n K b c)) V}
    {x : (coxeterMatrix (isFiniteType_cartanB (n - 1))).Group} {π : Equiv.Perm (Fin (n - 1))}
    {s : Fin (n - 1) → ℤ} (hxr : omqnfRealizes (n - 1) x π s) (hs : SpIsSign s)
    {ν₀ : OmqMinusLat (n - 1) (Nat.card Kˣ) (Nat.card K + 1)} {w₀ : V} (hw0 : w₀ ≠ 0)
    (hw : ∀ g ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H,
      σ g w₀ = omqMinusWt n ι ι' ν₀ g • w₀) {d : ℕ}
    {u : Fin d → OmqMinusLat (n - 1) (Nat.card Kˣ) (Nat.card K + 1)}
    (hinj : Function.Injective u) (horb : ∀ i, OmqMinusInOrbit ν₀ (u i))
    (hmove : ∀ i i', u i ≠ omqMinusAct π s (u i')) :
    d ≤ Module.finrank k
      (LinearMap.range (σ ((SmallO8mCurtis.curtisDatum n hn hirr).nW x) - 1)) := by
  classical
  choose π' s' hs' hact using horb
  have hex : ∀ i, ∃ y : (coxeterMatrix (isFiniteType_cartanB (n - 1))).Group,
      omqnfRealizes (n - 1) y (π' i) (s' i) :=
    fun i => exists_omqnfRealizes_of_signedPerm (π' i) (hs' i)
  choose y hy using hex
  have key : ∀ i, σ ((SmallO8mCurtis.curtisDatum n hn hirr).nW (y i)) w₀ ≠ 0 ∧
      ∀ g ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H,
        σ g (σ ((SmallO8mCurtis.curtisDatum n hn hirr).nW (y i)) w₀) =
          omqMinusWt n ι ι' (u i) g •
            σ ((SmallO8mCurtis.curtisDatum n hn hirr).nW (y i)) w₀ := by
    intro i
    refine ⟨fun h0 => hw0 ?_, fun g hg => ?_⟩
    · have h1 := congrArg
        (fun z => σ (((SmallO8mCurtis.curtisDatum n hn hirr).nW (y i))⁻¹) z) h0
      simpa only [map_zero, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply] using h1
    · have hc := omq_omMinus_wt_conj hn hirr rfl rfl ι ι' (hy i) (hs' i) ν₀ hg
      have hgm : g * (SmallO8mCurtis.curtisDatum n hn hirr).nW (y i) =
          (SmallO8mCurtis.curtisDatum n hn hirr).nW (y i) *
            (((SmallO8mCurtis.curtisDatum n hn hirr).nW (y i))⁻¹ * g *
              (SmallO8mCurtis.curtisDatum n hn hirr).nW (y i)) := by group
      calc σ g (σ ((SmallO8mCurtis.curtisDatum n hn hirr).nW (y i)) w₀)
          = σ (g * (SmallO8mCurtis.curtisDatum n hn hirr).nW (y i)) w₀ := by
            rw [map_mul, Module.End.mul_apply]
        _ = σ ((SmallO8mCurtis.curtisDatum n hn hirr).nW (y i))
              (σ (((SmallO8mCurtis.curtisDatum n hn hirr).nW (y i))⁻¹ * g *
                (SmallO8mCurtis.curtisDatum n hn hirr).nW (y i)) w₀) := by
            rw [hgm, map_mul, Module.End.mul_apply]
        _ = omqMinusWt n ι ι' (u i) g •
              σ ((SmallO8mCurtis.curtisDatum n hn hirr).nW (y i)) w₀ := by
            rw [hw _ hc.1, map_smul, hc.2, hact i]
  exact omq_omMinus_rank_of_weights h2 hn hirr ι ι' hxr hs hinj hmove
    (fun i => (key i).1) (fun i => (key i).2)

end CFSG.LocalAnalysis.WeakClosure81
