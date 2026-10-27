module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusInterfaces
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusTwoCoord
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusNFWeyl
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQBinaryDigit
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusWeightRank
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusTorus
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusPlane
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusWeights
public import CFSG.HardMathSupport.GuralnickMalle.EndFieldDescent.Basic
public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.OffenderBasic
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQPlusInterfaces

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted CFSG.Quasithin.SmithCurtis
  CFSG.LieType.RootSystem CFSG.StandardType
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

theorem omq_omMinus_nonbinary_rank (h1l : OmqMinusWeightVectorLong) (h2 : OmqRankFromWeights)
    {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {k V : Type} [Field k] [CharP k 2]
    [AddCommGroup V] [Module k V] [Module.Finite k V] (ι : K →+* k) (ι' : ShortField b c →+* k)
    (hι' : ∀ x : K, ι' (algebraMap K (ShortField b c) x) = ι x)
    {σ : Representation k (spinGroup (quadMinus n K b c)) V} (hσ : IsSimpleRep σ) {y : V}
    {χ : spinGroup (quadMinus n K b c) → k} {μ : Fin (n - 1) → k}
    (ht : (SmallO8mCurtis.curtisDatum n hn hirr).IsCurtisType σ y χ μ)
    (hsep : μ ⟨0, by omega⟩ = (SmallO8mCurtis.curtisDatum n hn hirr).dScalar χ ⟨0, by omega⟩)
    {cc : ℕ} (hc1 : 1 ≤ cc) (hcq : cc ≤ Nat.card Kˣ)
    (hχ : ∀ h ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H,
      χ h = ι (mat n h (Sum.inl ⟨0, by omega⟩) (Sum.inl ⟨0, by omega⟩)) ^ cc)
    (hpow : ∀ a : ℕ, cc ≠ 2 ^ a)
    {x : (coxeterMatrix (isFiniteType_cartanB (n - 1))).Group} {π : Equiv.Perm (Fin (n - 1))}
    {s : Fin (n - 1) → ℤ} (hxr : omqnfRealizes (n - 1) x π s) (hs : SpIsSign s)
    (hsh : OmqMinusShape (by omega : 2 ≤ n - 1) π s) :
    4 ≤ Module.finrank k
      (LinearMap.range (σ ((SmallO8mCurtis.curtisDatum n hn hirr).nW x) - 1)) := by
  classical
  obtain ⟨j, hj0, hjc, hjodd⟩ := omq_exists_odd_choose_lt hc1 hpow
  have hodd : Odd (Nat.card Kˣ) := by
    rw [Nat.card_units]
    haveI : Fintype K := Fintype.ofFinite K
    obtain ⟨e, he⟩ := Nat.even_iff.mpr (FiniteField.even_card_of_char_two (ringChar.eq K 2))
    rw [Nat.card_eq_fintype_card]
    have h2 : 2 ≤ Fintype.card K := by
      have := Fintype.one_lt_card (α := K)
      omega
    exact ⟨e - 1, by omega⟩
  have hi0 : (⟨0, by omega⟩ : Fin (n - 1)).val + 1 < n - 1 := by
    show 0 + 1 < n - 1
    omega
  have hχα : ∀ a : Kˣ, χ ((minusFrame n b c).longTorus
      (succ_ne_of_lt n (k := ⟨0, by omega⟩) (by show 0 + 1 < n - 1; omega)) true false a) =
        ι (a : K) ^ cc := by
    intro a
    have hmem := (omq_omMinus_torus_mem_H hn hirr).1 ⟨0, by omega⟩ hi0 a
    rw [hχ _ hmem]
    have htoral := omq_omMinus_toral_longTorus (n := n) (b := b) (c := c)
      (i := ⟨0, by omega⟩) hi0 a
    rw [htoral.mat_inl_inl]
    simp
  obtain ⟨w, hw0, hw⟩ := h1l hn hirr ι ι' hι' hσ ht hsep hc1 hcq hχα hjodd
  have hm3 : 3 ≤ Nat.card Kˣ := by
    have h1 : cc ≠ 1 := fun h => hpow 0 (by rw [h]; norm_num)
    have h2' : cc ≠ 2 := fun h => hpow 1 (by rw [h]; norm_num)
    omega
  have hjm : j < Nat.card Kˣ := by omega
  have hBc : (j : ZMod (Nat.card Kˣ)) ≠ 0 := by
    intro h
    have hdiv : Nat.card Kˣ ∣ j := (ZMod.natCast_eq_zero_iff j _).mp h
    exact absurd (Nat.le_of_dvd hj0 hdiv) (by omega)
  have hAc : (cc : ZMod (Nat.card Kˣ)) - (j : ZMod (Nat.card Kˣ)) ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    by_cases hcm : cc = Nat.card Kˣ
    · rw [hcm] at h
      apply hBc
      rw [← h]
      simp
    · have hclt : cc < Nat.card Kˣ := lt_of_le_of_ne hcq hcm
      have hmod : cc ≡ j [MOD Nat.card Kˣ] := (ZMod.natCast_eq_natCast_iff cc j _).mp h
      exact absurd (Nat.ModEq.eq_of_lt_of_lt hmod hclt hjm) (by omega)
  have hwt : ∀ g ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H,
      σ g w = omqMinusWt n ι ι' (((Pi.single ⟨0, by omega⟩
        ((cc : ZMod (Nat.card Kˣ)) - (j : ZMod (Nat.card Kˣ))) +
          Pi.single ⟨1, by omega⟩ (j : ZMod (Nat.card Kˣ)) : Fin (n - 1) → ZMod (Nat.card Kˣ)),
            (0 : ZMod (Nat.card K + 1))) : OmqMinusLat (n - 1) (Nat.card Kˣ) (Nat.card K + 1))
        g • w := by
    intro g hg
    rw [hw g hg]
    congr 1
    have hχθ : χ g = omqMinusWt n ι ι' (((Pi.single ⟨0, by omega⟩ (cc : ZMod (Nat.card Kˣ)) :
        Fin (n - 1) → ZMod (Nat.card Kˣ)), (0 : ZMod (Nat.card K + 1))) :
          OmqMinusLat (n - 1) (Nat.card Kˣ) (Nat.card K + 1)) g := by
      rw [omq_omMinus_wt_single hn hirr rfl ι ι' ⟨0, by omega⟩ cc hg, hχ g hg]
    rw [hχθ, ← omq_omMinus_wt_neg hn hirr rfl rfl ι ι' _ hg,
      ← omq_omMinus_wt_nsmul hn hirr rfl rfl ι ι' j _ hg,
      ← omq_omMinus_wt_add hn hirr rfl rfl ι ι' _ _ hg]
    congr 1
    refine Prod.ext ?_ ?_
    · funext l
      by_cases hl0 : l = ⟨0, by omega⟩
      · subst hl0
        simp [Pi.single_apply, sub_eq_add_neg]
      · by_cases hl1 : l = ⟨1, by omega⟩
        · subst hl1
          simp [Pi.single_apply]
        · simp [Pi.single_apply, hl0, hl1]
    · simp
  obtain ⟨u, hinj, horb, hmove⟩ := omq_minus_exists_four_two_coord (by omega : 3 ≤ n - 1)
    (m := Nat.card Kˣ) (h := Nat.card K + 1) hodd hAc hBc hs hsh
  exact omq_omMinus_rank_of_weight_orbit h2 hn hirr ι ι' hxr hs hw0 hwt hinj horb hmove

end CFSG.LocalAnalysis.WeakClosure81
