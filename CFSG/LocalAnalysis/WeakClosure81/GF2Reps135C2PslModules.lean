module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslCover
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslLabelExt
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslLEnd
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslCenter
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslRangeFive
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslRangeFour
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslRangeThree
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslRangeTwo
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslNatural
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslFive
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslAdjoint
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslOrthSix
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslTwoSmall
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslDimAdjoint
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslDimSingle
import CFSG.LieType.SpecialLinear.ExteriorModel.WeightDim

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Finset
open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar
open CFSG.LieType.SpecialLinear CFSG.LieType.SpecialLinear.ExteriorModel
open Matrix

private theorem c2slmod_card_le_one_two {f : ℕ} (ε : Fin f → Finset (Fin 2))
    (h0 : ∀ r, (⟨0, by omega⟩ : Fin 2) ∉ ε r) (r : Fin f) : (ε r).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  have ha' : (a : ℕ) ≠ 0 := fun h => h0 r (by rwa [show (⟨0, by omega⟩ : Fin 2) = a from
    Fin.ext h.symm])
  have hb' : (b : ℕ) ≠ 0 := fun h => h0 r (by rwa [show (⟨0, by omega⟩ : Fin 2) = b from
    Fin.ext h.symm])
  exact Fin.ext (by have := a.isLt; have := b.isLt; omega)

private theorem c2slmod_dim_two {f : ℕ} (ε : Fin f → Finset (Fin 2))
    (h0 : ∀ r, (⟨0, by omega⟩ : Fin 2) ∉ ε r) :
    ∏ r, ∏ i ∈ ε r, (2 : ℕ).choose (i : ℕ) = 2 ^ (univ.filter fun r => ε r ≠ ∅).card := by
  classical
  have hone : ∀ r, ∏ i ∈ ε r, (2 : ℕ).choose (i : ℕ) = if ε r = ∅ then 1 else 2 := by
    intro r
    by_cases hr : ε r = ∅
    · simp [hr]
    · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hr
      have ha1 : (a : ℕ) = 1 := by
        have : (a : ℕ) ≠ 0 := fun h => h0 r (by rwa [show (⟨0, by omega⟩ : Fin 2) = a from
          Fin.ext h.symm])
        have := a.isLt
        omega
      have hsing : ε r = {a} := by
        rw [Finset.eq_singleton_iff_unique_mem]
        refine ⟨ha, fun b hb => ?_⟩
        have hbne : (b : ℕ) ≠ 0 := fun h => h0 r (by rwa [show (⟨0, by omega⟩ : Fin 2) = b from
          Fin.ext h.symm])
        exact Fin.ext (by have := b.isLt; omega)
      simp [hr, hsing, ha1]
  simp_rw [hone]
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]

private theorem c2slmod_natural {W : Type} [CommGroup W] [Finite W]
    [Module (ZMod 2) (Additive W)] {L : Subgroup (MulAut W)} {m f : ℕ} {K : Type} [Field K]
    [Fintype K] [CharP K 2] (hK : Fintype.card K = 2 ^ f)
    (φ : Matrix.SpecialLinearGroup (Fin (m + 1)) K →* ↥L) (hφs : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) K)) (hm : 1 ≤ m)
    {ε : Fin f → Finset (Fin (m + 1))} (h0 : ∀ r, (⟨0, by omega⟩ : Fin (m + 1)) ∉ ε r)
    (hdesc : ∀ (r₀ : Fin f) (j : Fin (m + 1)), (∀ r, r ≠ r₀ → ε r = ∅) → ε r₀ = {j} →
      ∃ β : Additive W ≃+ (Set.powersetCard (Fin (m + 1)) (j : ℕ) → K),
        ∀ g w, β (pslRep φ g w) = extTwist (m + 1) (j : ℕ) (r₀ : ℕ) K g *ᵥ β w)
    {r₀ : Fin f} {j : Fin (m + 1)} (hone : ∀ r, r ≠ r₀ → ε r = ∅) (hεj : ε r₀ = {j})
    (hj : (j : ℕ) = 1 ∨ (j : ℕ) + 1 = m + 1) : Chev2Natural W L := by
  obtain ⟨β, hβ⟩ := hdesc r₀ j hone hεj
  exact w135c2_psl_natural (by omega) hK φ hφs hker hj β hβ

theorem chev2SmallModules_psl
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {L : Subgroup (MulAut W)} (hQ : IsQuasisimple ↥L) (hirr : IsIrrOn L ⊤ ⊥) {n f : ℕ}
    (hn41 : ¬ (n = 4 ∧ f = 1)) (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .PSL n 2 f) {k d : ℕ}
    (hk : Nat.card (LEnd L) = 2 ^ k) (hrk : rk W = k * d)
    (hrange : (k = 1 ∧ d ≤ 3 * gs03Bound .PSL n f) ∨
      ((k = 2 ∨ k = 3) ∧ d ≤ gs03Bound .PSL n f)) :
    Chev2Natural W L ∨ Chev2Item3 W L ∨ Chev2RowIdx .PSL n f (k * d) := by
  classical
  have hW2 : ∀ a : Additive W, (2 : ℕ) • a = 0 := fun a => by
    apply Additive.toMul.injective
    show (Additive.toMul a) ^ 2 = 1
    exact hW _
  letI : Module (ZMod 2) (Additive W) := AddCommGroup.zmodModule hW2
  obtain ⟨hn2, K, _, _, _, hKcard, φ, hφs, hker, -⟩ := w135c2_psl_cover hW hQ hirr hlie
  have hirrρ := w135c2_psl_rep_irreducible hirr φ hφs
  have hne := w135c2_psl_rep_ne_one hQ φ hφs
  have hEnd := w135c2_psl_lend_card φ hφs
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · rw [h, pow_zero] at hKcard
      exact absurd hKcard (Nat.ne_of_gt Fintype.one_lt_card)
    · exact h
  have hcard2 : Nat.card W = 2 ^ (k * d) := by rw [w135_card_eq_two_pow_rk hW, hrk]
  have hcardA : Nat.card W = Nat.card (Additive W) := (Nat.card_congr Additive.toMul).symm
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨s, ε, hs1, hEs, h0, hact, hper, -, ⟨k', _, _, hcardW⟩, hdesc, hrot, hmin⟩ :=
    w135c2_psl_label_ext (m := m) (f := f) (by omega) hKcard (pslRep φ) hirrρ hne
  have hsk : s = k := by
    have h : 2 ^ k = 2 ^ s := by rw [← hk, hEnd, hEs]
    exact (Nat.pow_right_injective le_rfl h).symm
  subst hsk
  have hD : d = Module.finrank k' (BModel k' ε) := by
    have h : 2 ^ (s * d) = 2 ^ (s * Module.finrank k' (BModel k' ε)) := by
      rw [← hcard2, hcardA, hcardW]
    exact Nat.eq_of_mul_eq_mul_left hs1 (Nat.pow_right_injective le_rfl h)
  have hlow : ∏ r ∈ univ.filter (fun r => ε r ≠ ∅), orbitSize (ε r) ≤ d := by
    rw [hD]
    exact prod_orbitSize_le_finrank (k := k') ε
  have hnat : ∀ {r₀ : Fin f} {j : Fin (m + 1)}, (∀ r, r ≠ r₀ → ε r = ∅) → ε r₀ = {j} →
      ((j : ℕ) = 1 ∨ (j : ℕ) + 1 = m + 1) → Chev2Natural W L := fun hone hεj hj =>
    c2slmod_natural hKcard φ hφs hker (by omega) h0 hdesc hone hεj hj
  by_cases hm1 : m = 1
  ·
    subst hm1
    have hc1 := c2slmod_card_le_one_two ε h0
    have hdD : d = 2 ^ (univ.filter fun r => ε r ≠ ∅).card := by
      rw [hD, w135c2_finrank_bModel_of_card_le_one (k := k') ε hc1]
      exact c2slmod_dim_two ε h0
    have hrange2 : (s = 1 ∧ d ≤ 3 * (if Even f then 4 else 3)) ∨
        ((s = 2 ∨ s = 3) ∧ d ≤ if Even f then 4 else 3) := by
      simpa [gs03Bound] using hrange
    have hsd := w135c2_psl_range_two hs1 ε h0 hact hper hrot hmin hdD hrange2
    have hlt : Nat.card W < 2 ^ (4 * f) := by
      rw [hcard2]
      exact Nat.pow_lt_pow_right (by norm_num) hsd
    rcases w135c2_psl_two_small hf1 hKcard φ hφs hker hirrρ hne hlt with hnat2 | ⟨l, hl, hl8⟩
    · exact Or.inl hnat2
    · right
      right
      have hsd12 : s * d ≤ 12 := by
        rcases hrange2 with ⟨h1, h⟩ | ⟨h1, h⟩
        · subst h1
          split_ifs at h <;> omega
        · rcases h1 with h1 | h1 <;> subst h1 <;> split_ifs at h <;> omega
      have hkd : s * d = 8 * l := Nat.pow_right_injective le_rfl (hcard2.symm.trans hl8)
      have hl1 : l = 1 := by omega
      subst hl1
      have hf3 : f = 3 := by omega
      subst hf3
      have h8 : s * d = 8 := by omega
      rw [h8]
      exact (trivial : Chev2RowIdx .PSL 2 3 8)
  by_cases hm2 : m = 2
  ·
    subst hm2
    have hrange3 : (s = 1 ∧ d ≤ 3 * (if f = 1 then 3 else 4)) ∨
        ((s = 2 ∨ s = 3) ∧ d ≤ if f = 1 then 3 else 4) := by
      simpa [gs03Bound] using hrange
    rcases w135c2_psl_range_three hs1 ε h0 hact hper hrot hmin hlow hrange3 with
      ⟨r₀, j, hone, hεj, -, -⟩ | ⟨hf1', hs1', a, b, ha, hb, hεall⟩ | ⟨hf2, hs1', j, hεall⟩
    ·
      left
      refine hnat hone hεj ?_
      have hj0 : (j : ℕ) ≠ 0 := fun h => h0 r₀ (by
        rw [hεj]
        exact Finset.mem_singleton.mpr (Fin.ext h.symm))
      have := j.isLt
      omega
    ·
      subst hf1'
      subst hs1'
      have hdim : d = 8 := by
        rw [hD]
        exact w135c2_finrank_bModel_adjoint_three (k := k') ε a b ha hb hεall
      have hW8 : Nat.card W = 2 ^ 8 := by rw [hcard2, hdim]
      right
      left
      exact w135c2_psl_adjoint (by simpa using hKcard) φ hφs hker hW8
    ·
      subst hf2
      subst hs1'
      have hc1 : ∀ r, (ε r).card ≤ 1 := fun r => by rw [hεall r]; simp
      have hj0 : (j : ℕ) ≠ 0 := fun h => h0 0 (by
        rw [hεall 0]
        exact Finset.mem_singleton.mpr (Fin.ext h.symm))
      have hdim : d = 9 := by
        rw [hD, w135c2_finrank_bModel_of_card_le_one (k := k') ε hc1]
        simp only [hεall, Finset.prod_singleton, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin]
        have h3 : (3 : ℕ).choose (j : ℕ) = 3 := by
          have := j.isLt
          interval_cases hjj : (j : ℕ) <;> simp_all
        rw [h3]
        norm_num
      have hW9 : Nat.card W = 2 ^ 9 := by rw [hcard2, hdim]
      have hLie := w135c2_lieModel_of_lend_card_two (by simpa using hk) hlie
      right
      left
      exact Or.inr (Or.inr (Or.inl ⟨hLie, hW9⟩))
  by_cases hm3 : m = 3
  ·
    subst hm3
    have hf2 : 2 ≤ f := by
      rcases Nat.lt_or_ge f 2 with h | h
      · exact absurd ⟨rfl, by omega⟩ hn41
      · exact h
    have hrange4 : (s = 1 ∧ d ≤ 3 * 6) ∨ ((s = 2 ∨ s = 3) ∧ d ≤ 6) := by
      simpa [gs03Bound, show f ≠ 1 by omega] using hrange
    rcases w135c2_psl_range_four hf2 hs1 ε h0 hact hper hrot hmin hlow hrange4 with
      ⟨r₀, j, hone, hεj, hj, -, -⟩ | ⟨r₀, j, hone, hεj, hj2, -, -⟩ | ⟨hf2', hs1', j, hj13, hεall⟩
    · left
      exact hnat hone hεj (by omega)
    · left
      obtain ⟨β, hβ⟩ := hdesc r₀ j hone hεj
      exact w135c2_psl_orth_six hKcard φ hφs hker hj2 β hβ
    · subst hf2'
      subst hs1'
      have hc1 : ∀ r, (ε r).card ≤ 1 := fun r => by rw [hεall r]; simp
      have hdim : d = 16 := by
        rw [hD, w135c2_finrank_bModel_of_card_le_one (k := k') ε hc1]
        simp only [hεall, Finset.prod_singleton, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin]
        have h4 : (4 : ℕ).choose (j : ℕ) = 4 := by
          have := j.isLt
          rcases hj13 with h | h <;> rw [h] <;> norm_num
        rw [h4]
        norm_num
      right
      right
      rw [hdim]
      exact (trivial : Chev2RowIdx .PSL 4 2 16)
  have hm4 : 4 ≤ m := by omega
  have hbound : gs03Bound .PSL (m + 1) f = m + 1 := by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 4 := ⟨m - 4, by omega⟩
    simp [gs03Bound]
  have hrange5 : (s = 1 ∧ d ≤ 3 * (m + 1)) ∨ ((s = 2 ∨ s = 3) ∧ d ≤ m + 1) := by
    rw [hbound] at hrange
    exact hrange
  rcases w135c2_psl_range_ge5 (n := m + 1) (by omega) hs1 ε h0 hact hper hrot hmin hlow
    hrange5 with ⟨r₀, j, hone, hεj, hj, -, -⟩ | ⟨hf1', hs1', j, hεall, hcases⟩
  · left
    exact hnat hone hεj hj
  · subst hf1'
    subst hs1'
    have hc1 : ∀ r, (ε r).card ≤ 1 := fun r => by rw [hεall r]; simp
    have hdim : d = (m + 1).choose (j : ℕ) := by
      rw [hD, w135c2_finrank_bModel_of_card_le_one (k := k') ε hc1]
      simp [hεall]
    rcases hcases with ⟨hn5, hj5⟩ | ⟨hn6, hj6⟩ | ⟨hn7, hj7⟩
    ·
      have hm4' : m = 4 := by omega
      subst hm4'
      obtain ⟨β, hβ⟩ := hdesc 0 j (fun r hr => absurd (Subsingleton.elim r 0) hr) (hεall 0)
      right
      left
      exact w135c2_psl_five (by simpa using hKcard) φ hφs hker hj5 β hβ
    ·
      have hm5 : m = 5 := by omega
      subst hm5
      right
      right
      have hd15 : d = 15 := by
        rw [hdim]
        rcases hj6 with h | h <;> rw [h] <;> decide
      rw [hd15]
      exact (trivial : Chev2RowIdx .PSL 6 1 15)
    ·
      have hm6 : m = 6 := by omega
      subst hm6
      right
      right
      have hd21 : d = 21 := by
        rw [hdim]
        rcases hj7 with h | h <;> rw [h] <;> decide
      rw [hd21]
      exact (trivial : Chev2RowIdx .PSL 7 1 21)

end CFSG.LocalAnalysis.WeakClosure81
