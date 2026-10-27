module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQPlusInterfaces
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQPlusSingle
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQPlusNonBinary
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQPlusIsoNat
import CFSG.LieType.Steinberg.CurtisDatum.TorusSums
public import CFSG.HardMathSupport.GuralnickMalle.EndFieldDescent.Basic
public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.OffenderBasic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.Quasithin.SmithCurtis

private theorem c2slomqnz_d'Scalar_eq_dScalar {n : ℕ} (hn : 3 ≤ n) {F : Type} [Field F]
    [Finite F] [CharP F 2] {k : Type*} [Field k] (χ : spinGroup (quadPlus n F) → k)
    (i : Fin n) :
    (omPlusCurtisDatum n F hn).d'Scalar χ i = (omPlusCurtisDatum n F hn).dScalar χ i :=
  CFSG.LieType.Steinberg.curtisDatumOf_d'Scalar_eq_dScalar
    (CFSG.LieType.Steinberg.SpinPlus.isCTGroupDatum hn) (plusDatum_steinbergExtras hn)
    (CFSG.StandardType.GGRootSpinPlus.bruhatExtras hn) 2
    (fun _ hγ => isPGroup_plusRootGroup n F hn hγ) χ i

theorem omq_omPlus_node_zero_dichotomy (h1 : OmqPlusWeightVector) (h2 : OmqRankFromWeights)
    {n : ℕ} (hn : 3 ≤ n) {F : Type} [Field F] [Finite F] [CharP F 2] (hF4 : 4 ≤ Nat.card F)
    {k V : Type} [Field k] [CharP k 2] [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ι : F →+* k) {σ : Representation k (spinGroup (quadPlus n F)) V} (hσ : IsSimpleRep σ)
    {y : V} {χ : spinGroup (quadPlus n F) → k} {μ : Fin n → k}
    (ht : (omPlusCurtisDatum n F hn).IsCurtisType σ y χ μ)
    (hJ : ∀ i : Fin n, μ i = (omPlusCurtisDatum n F hn).dScalar χ i ↔ i.val = 0)
    {g : spinGroup (quadPlus n F)} (hg2 : g * g = 1) (hσg : σ g ≠ 1) :
    (∃ (a : ℕ) (β : V ≃ₗ[k] (Fin n ⊕ Fin n → k)), ∀ (g' : spinGroup (quadPlus n F)) (v : V),
      β (σ g' v) = omPlusNatRep n (ι.comp (iterateFrobenius F 2 a)) g' (β v)) ∨
    4 ≤ Module.finrank k (LinearMap.range (σ g - 1)) := by
  obtain ⟨c, hc1, hcq, hχ, hμ1, hμ0⟩ := omq_omPlus_label_of_single hn ι ht hJ
  by_cases hpow : ∃ a : ℕ, c = 2 ^ a
  · obtain ⟨a, rfl⟩ := hpow
    left
    have hF : 2 < Nat.card F := by omega
    have hodd : Odd (Nat.card Fˣ) := by
      rw [Nat.card_units]
      letI : Fintype F := Fintype.ofFinite F
      obtain ⟨n, -, hcard⟩ := FiniteField.card F 2
      have hcard' : Nat.card F = 2 ^ (n : ℕ) := by
        rw [Nat.card_eq_fintype_card, hcard]
      rw [hcard']
      exact Nat.Even.sub_odd (Nat.succ_le_of_lt (Nat.two_pow_pos (n : ℕ)))
        (Even.pow_of_ne_zero (even_two : Even (2 : ℕ)) n.2.ne') odd_one
    have hclt : 2 ^ a < Nat.card Fˣ := by
      rcases Nat.eq_zero_or_pos a with ha | ha
      · subst ha
        rw [pow_zero]
        have h3 : 3 ≤ Nat.card Fˣ := by
          rw [Nat.card_units]
          omega
        omega
      · have heven : Even (2 ^ a) := even_two.pow_of_ne_zero (Nat.ne_of_gt ha)
        have hne : 2 ^ a ≠ Nat.card Fˣ := by
          intro h
          exact (Nat.not_even_iff_odd.mpr hodd) (h ▸ heven)
        exact lt_of_le_of_ne hcq hne
    have hμzero : μ = 0 := by
      funext i
      by_cases hi : i.val = 0
      · have hie : i = (⟨0, by omega⟩ : Fin n) := Fin.ext hi
        rw [hie]
        exact hμ0 hclt
      · have hne : μ i ≠ (omPlusCurtisDatum n F hn).dScalar χ i := fun h => hi ((hJ i).mp h)
        rcases ht.mu_eq i with h0 | hd
        · exact h0
        · exact absurd (hd.trans (c2slomqnz_d'Scalar_eq_dScalar hn χ i)) hne
    obtain ⟨β, hβ⟩ := omq_omPlus_iso_natural hn hF ι hσ ht hμzero (a := a) hχ
    exact ⟨a, β, hβ⟩
  · right
    exact omq_omPlus_nonbinary_rank h1 h2 hn hF4 ι hσ ht hJ hc1 hcq hχ
      (fun a h => hpow ⟨a, h⟩) hg2 hσg

end CFSG.LocalAnalysis.WeakClosure81
