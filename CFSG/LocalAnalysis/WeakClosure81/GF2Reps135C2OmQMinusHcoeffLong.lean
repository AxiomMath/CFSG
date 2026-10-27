module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQHcoeffGen
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusFinite
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallO8mCurtis

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted CFSG.Quasithin.SmithCurtis
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

theorem omq_omMinus_hcoeff_long {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2]
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {k : Type} [Field k] [CharP k 2]
    (ι : K →+* k) {V : Type} [AddCommGroup V] [Module k V]
    {σ : Representation k (spinGroup (quadMinus n K b c)) V} (hσ : IsSimpleRep σ) {y : V}
    {χ : spinGroup (quadMinus n K b c) → k} {μ : Fin (n - 1) → k}
    (ht : (SmallO8mCurtis.curtisDatum n hn hirr).IsCurtisType σ y χ μ)
    (hμ : μ ⟨0, by omega⟩ = (SmallO8mCurtis.curtisDatum n hn hirr).dScalar χ ⟨0, by omega⟩)
    {cc : ℕ} (hcc : 1 ≤ cc)
    (hχ : ∀ a : Kˣ, χ ((minusFrame n b c).longTorus
      (succ_ne_of_lt n (k := ⟨0, by omega⟩) (by show 0 + 1 < n - 1; omega)) true false a) =
        ι (a : K) ^ cc) :
    ∃ φ : Module.Dual k V, φ y = 1 ∧ ∀ s t : K,
      φ (σ ((minusFrame n b c).longRoot
          (succ_ne_of_lt n (k := ⟨0, by omega⟩) (by show 0 + 1 < n - 1; omega)) true false
          (Multiplicative.ofAdd s) *
        (minusFrame n b c).longRoot
          (succ_ne_of_lt n (k := ⟨0, by omega⟩) (by show 0 + 1 < n - 1; omega)).symm true false
          (Multiplicative.ofAdd t)) y) = (1 + ι s * ι t) ^ cc := by
  classical
  let D := SmallO8mCurtis.curtisDatum n hn hirr
  have hk : (⟨0, by omega⟩ : Fin (n - 1)).val + 1 < n - 1 := by show 0 + 1 < n - 1; omega
  set Φ := (minusFrame n b c).longSL2 (succ_ne_of_lt n (k := ⟨0, by omega⟩) hk) true false
    with hΦ
  have hX : ∀ a, Φ (upperSL2 a) ∈ D.U := by
    intro a
    rw [hΦ, HypFrame.longSL2_upperSL2]
    apply D.X_le ⟨0, by omega⟩
    change _ ∈ minusRootGroup n hirr (Pi.single (⟨0, by omega⟩ : Fin (n - 1)) 1)
    rw [minusRootGroup_single_of_lt n hirr hk]
    exact ⟨Multiplicative.ofAdd a, rfl⟩
  have hY : ∀ a, Φ (lowerSL2 a) ∈ D.L := by
    intro a
    rw [hΦ, HypFrame.longSL2_lowerSL2]
    have hmem : (minusFrame n b c).longRoot (succ_ne_of_lt n (k := ⟨0, by omega⟩) hk).symm
        (!false) (!true) (Multiplicative.ofAdd a) ∈
        ((minusFrame n b c).longRoot (succ_ne_of_lt n (k := ⟨0, by omega⟩) hk).symm true
          false).range := ⟨_, rfl⟩
    rw [← minusRootGroup_neg_single_of_lt n hirr hk] at hmem
    exact D.Y_le ⟨0, by omega⟩ hmem
  have hT : ∀ a : Kˣ, Φ (diagSL2 a) ∈ D.H := by
    intro a
    refine Subgroup.mem_iSup_of_mem (⟨0, by omega⟩ : Fin (n - 1)) ?_
    rw [minusTorus_of_lt n hirr hk]
    exact ⟨a, rfl⟩
  have hN : σ (Φ (weylSL2 1)) y ∈ augSub σ D.L := by
    have h := D.act_n_sub_mem_augL σ ⟨0, by omega⟩ ht.1
    rw [ht.2.2.2 _, D.heckeD_weight σ _ ht.2.2.1, ← sub_smul, hμ, sub_self, zero_smul,
      sub_zero] at h
    have hnn : D.n ⟨0, by omega⟩ = Φ (weylSL2 1) := by
      change minusWeyl n hirr ⟨0, by omega⟩ = _
      rw [minusWeyl_of_lt n hirr hk]
      rfl
    rwa [hnn] at h
  obtain ⟨φ, hφ1, hφ⟩ := omq_curtis_hcoeff_of_sl2 D ι hσ ht Φ hX hY hT hcc
    (fun a => by rw [hΦ, ← HypFrame.longTorus_apply]; exact hχ a) hN
  refine ⟨φ, hφ1, fun s t => ?_⟩
  have h := hφ s t
  rw [hΦ, HypFrame.longSL2_upperSL2, HypFrame.longSL2_lowerSL2] at h
  simpa using h

end CFSG.LocalAnalysis.WeakClosure81
