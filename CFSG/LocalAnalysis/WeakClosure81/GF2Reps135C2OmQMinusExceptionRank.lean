module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusInterfaces
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusException
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusNFWeyl
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusWeightRank
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusTorus
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusWeights
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusWeightsInj
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusWeightsTorus
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusLabelsLong
public import CFSG.HardMathSupport.GuralnickMalle.EndFieldDescent.Basic
public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.OffenderBasic
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQPlusInterfaces

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted CFSG.Quasithin.SmithCurtis
  CFSG.LieType.RootSystem CFSG.StandardType
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

theorem omq_omMinus_exception_rank (h1s : OmqMinusWeightVectorShort) (h2 : OmqRankFromWeights)
    {n : ℕ} (hn : 4 ≤ n) (hn4 : n = 4) {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {k V : Type} [Field k] [CharP k 2]
    [AddCommGroup V] [Module k V] [Module.Finite k V] (ι : K →+* k) (ι' : ShortField b c →+* k)
    (hι' : ∀ x : K, ι' (algebraMap K (ShortField b c) x) = ι x)
    {σ : Representation k (spinGroup (quadMinus n K b c)) V} (hσ : IsSimpleRep σ) {y : V}
    {χ : spinGroup (quadMinus n K b c) → k} {μ : Fin (n - 1) → k}
    (ht : (SmallO8mCurtis.curtisDatum n hn hirr).IsCurtisType σ y χ μ)
    (hshort : μ ⟨n - 2, by omega⟩ =
      (SmallO8mCurtis.curtisDatum n hn hirr).dScalar χ ⟨n - 2, by omega⟩)
    (hlong : ∀ i : Fin (n - 1), i.val + 1 < n - 1 →
      μ i ≠ (SmallO8mCurtis.curtisDatum n hn hirr).dScalar χ i)
    (hχne : ∃ h ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H, χ h ≠ 1) {κ : ℕ} (hκ1 : 1 ≤ κ)
    (hκ3 : κ ≤ 3) (hfrob : ∀ h ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H, χ h ^ 2 ^ κ = χ h)
    {f : ℕ} (hF : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    {x : (coxeterMatrix (isFiniteType_cartanB (n - 1))).Group} {π : Equiv.Perm (Fin (n - 1))}
    {s : Fin (n - 1) → ℤ} (hxr : omqnfRealizes (n - 1) x π s)
    (hA : (∀ a, s a = 1) ∧ π * π = 1 ∧ π ⟨0, by omega⟩ = ⟨1, by omega⟩ ∧
      π ⟨1, by omega⟩ = ⟨0, by omega⟩) :
    4 ≤ Module.finrank k
      (LinearMap.range (σ ((SmallO8mCurtis.curtisDatum n hn hirr).nW x) - 1)) := by
  classical
  have hm : Nat.card Kˣ = 2 ^ f - 1 := by rw [Nat.card_units, hF]
  have hh : Nat.card K + 1 = 2 ^ f + 1 := by rw [hF]
  have hmodd : Odd (Nat.card Kˣ) := by
    rw [hm]
    exact Nat.Even.sub_odd Nat.one_le_two_pow (Even.pow_of_ne_zero even_two (by omega)) odd_one
  have hhodd : Odd (Nat.card K + 1) := by
    rw [hh]
    exact (Even.pow_of_ne_zero even_two (by omega)).add_one
  have hs : SpIsSign s := fun a => Or.inl (hA.1 a)
  obtain ⟨a, d, hχθ⟩ := omq_omMinus_chi_of_long_trivial hn hirr ι ι' hι' ht hlong
  obtain ⟨C, hC1, hCle, hCa, hCd, hCshort⟩ :=
    omq_omMinus_exists_short_exponent (n := n) hirr rfl rfl ι ι' hι' a d
  have hCQ : C < Nat.card Kˣ * (Nat.card K + 1) := by
    refine lt_of_le_of_ne hCle ?_
    intro hCeq
    have ha0 : a = 0 := by
      by_contra ha
      have h2a : (2 : ZMod (Nat.card Kˣ)) * a = 0 := by
        rw [← hCa, hCeq]
        push_cast
        simp
      exact ZMod.ne_neg_self hmodd ha (by linear_combination h2a)
    have hd0 : d = 0 := by
      by_contra hd
      have h2d : (2 : ZMod (Nat.card K + 1)) * d = 0 := by
        rw [← hCd, hCeq]
        push_cast
        simp
      exact ZMod.ne_neg_self hhodd hd (by linear_combination h2d)
    obtain ⟨g, hg, hne⟩ := hχne
    apply hne
    rw [hχθ g hg, ha0, hd0]
    exact omq_omMinus_wt_zero ι ι' g
  have hfrob' : (2 ^ κ : ℕ) •
      (((fun _ => a : Fin (n - 1) → ZMod (Nat.card Kˣ)), d) :
        OmqMinusLat (n - 1) (Nat.card Kˣ) (Nat.card K + 1)) = ((fun _ => a), d) := by
    refine omq_omMinus_wt_injective hn hirr rfl rfl ι ι' (fun g hg => ?_)
    rw [omq_omMinus_wt_nsmul hn hirr rfl rfl ι ι' _ _ hg, ← hχθ g hg]
    exact hfrob g hg
  have ha : ((2 ^ κ - 1 : ℕ) : ZMod (Nat.card Kˣ)) * a = 0 := by
    have h0 := congrArg (fun p => p.1 ⟨0, by omega⟩) hfrob'
    simp only [Prod.smul_fst] at h0
    simp only [Pi.smul_apply, nsmul_eq_mul] at h0
    rw [Nat.cast_sub Nat.one_le_two_pow, sub_mul, h0, Nat.cast_one, one_mul, sub_self]
  have hd : ((2 ^ κ - 1 : ℕ) : ZMod (Nat.card K + 1)) * d = 0 := by
    have h0 := congrArg (fun p => p.2) hfrob'
    simp only [Prod.smul_snd] at h0
    rw [nsmul_eq_mul] at h0
    rw [Nat.cast_sub Nat.one_le_two_pow, sub_mul, h0, Nat.cast_one, one_mul, sub_self]
  have hpowC : ∀ u : ℕ, C ≠ 2 ^ u :=
    omq_minus_not_pow_two hf hκ1 hκ3 hm hh hCa hCd ha hd
  have hχshort : ∀ u : (ShortField b c)ˣ,
      χ (shortTorusHom n hirr ⟨0, by omega⟩ u) = ι' (u : ShortField b c) ^ C := by
    intro u
    rw [hχθ _ ((omq_omMinus_torus_mem_H hn hirr).2 _ u)]
    exact hCshort _ u
  have hCle' : C ≤ Nat.card (ShortField b c)ˣ := by
    rw [omq_omMinus_card_shortField_units hirr]
    exact hCle
  subst hn4
  obtain ⟨j, hj0, hjC, hjodd, u, hinj, horb, hmove⟩ :=
    omq_minus_exists_exception_weights hf hm hh hC1 hCQ hpowC hCa hCd (π := π) (s := s) hA
  obtain ⟨w, hw0, hw⟩ := h1s hn hirr ι ι' hι' hσ ht ⟨⟨4 - 2, by omega⟩, hshort⟩ (C := C)
    (j := j) hC1 hCle' hχshort hjodd
  have hwt : ∀ g ∈ (SmallO8mCurtis.curtisDatum 4 hn hirr).H,
      σ g w = omqMinusWt 4 ι ι'
        (((![a - (j : ZMod (Nat.card Kˣ)), a, a] : Fin 3 → ZMod (Nat.card Kˣ)),
          d - (j : ZMod (Nat.card K + 1))) :
            OmqMinusLat (4 - 1) (Nat.card Kˣ) (Nat.card K + 1)) g • w := by
    intro g hg
    rw [hw g hg]
    congr 1
    rw [hχθ g hg, ← omq_omMinus_wt_neg hn hirr rfl rfl ι ι' _ hg,
      ← omq_omMinus_wt_nsmul hn hirr rfl rfl ι ι' j _ hg,
      ← omq_omMinus_wt_add hn hirr rfl rfl ι ι' _ _ hg]
    congr 1
    refine Prod.ext ?_ ?_
    · funext l
      fin_cases l <;> simp [Pi.single_apply, sub_eq_add_neg]
    · simp [sub_eq_add_neg]
  exact omq_omMinus_rank_of_weight_orbit h2 hn hirr ι ι' hxr hs hw0 hwt hinj horb hmove

end CFSG.LocalAnalysis.WeakClosure81
