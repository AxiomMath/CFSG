module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenAk
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDeltaBound
import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.OTwoFixedSquare

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c11_one_add_lt_gammaN_one {M V : Subgroup G} {k n : ℕ} (hk : 1 ≤ k)
    (h : ((k + n : ℕ) : ℕ∞) < gammaN k M V) : ((1 + n : ℕ) : ℕ∞) < gammaN 1 M V :=
  lt_of_le_of_lt (by exact_mod_cast Nat.add_le_add_right hk n) (h.trans_le (gammaN_anti hk))

theorem s16c11_comm_eq_one_of_ti (D : Data G) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) {g : G}
    (hAM : conjSubgroup V g ≤ D.M)
    (hTI : V₀ ⊓ conjSubgroup V g = ⊥ ∧ V ⊓ conjSubgroup V₀ g = ⊥)
    (hm : MBarGT D.M V₀ V 1) (hr : ((1 + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V)
    {D' : Subgroup G} (hD' : D' ≤ conjSubgroup V g)
    (hD'1 : E3.mQuot (conjSubgroup V g) D' = 1) {u : G} (hu : u ∈ V)
    (huD : ∀ d ∈ D', ⁅u, d⁆ ∈ V₀) : ∀ a ∈ conjSubgroup V g, ⁅u, a⁆ = 1 := by
  set A := conjSubgroup V g with hAdef
  have h62 : Hyp62 D.M V₀ V := h.hyp62
  have hV : IsElemAbelian 2 V := h62.isElemAbelian
  have hAel : IsElemAbelian 2 A := E3.isElemAbelian_conjSubgroup hV g
  have hD'M : D' ≤ A ⊓ D.M := le_inf hD' (hD'.trans hAM)
  have hD'st : D' ≤ stabTil V₀ V := h62.le_stabTil hD'M
  have hUmem : u ∈ preCTilde V₀ V D' hV := (mem_preCTilde_iff hV hD'st hu).2 huD
  have huMg : u ∈ conjSubgroup D.M g :=
    six_two_one h62 hD'M (by rw [← hAdef, hD'1]; exact hr) hUmem
  have huN : u ∈ normalizer (A : Set G) := by
    rw [hAdef, ← E3.conjSubgroup_normalizer, h62.normalizer_eq]
    exact huMg
  have hcentD' : ∀ d ∈ D', u * d * u⁻¹ = d := by
    intro d hd
    have hcomm : ⁅u, d⁆ = 1 := by
      have hV₀ : ⁅u, d⁆ ∈ V₀ := huD d hd
      have hA : ⁅u, d⁆ ∈ A := by
        rw [commutatorElement_def]
        exact A.mul_mem ((Subgroup.mem_normalizer_iff.1 huN d).1 (hD' hd))
          (A.inv_mem (hD' hd))
      have hmem : ⁅u, d⁆ ∈ V₀ ⊓ A := Subgroup.mem_inf.2 ⟨hV₀, hA⟩
      rw [hTI.1, Subgroup.mem_bot] at hmem
      exact hmem
    rw [commutatorElement_eq_one_iff_mul_comm.1 hcomm]
    group
  have hD'rel : D'.relIndex A = 2 := by
    have h := E3.relIndex_eq_two_pow hAel.isPGroup D'
    rw [hD'1, pow_one] at h
    exact h
  have hD'le : D' ≤ A ⊓ Subgroup.centralizer ({u} : Set G) := by
    refine le_inf hD' fun d hd => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (mul_inv_eq_iff_eq_mul.1 (hcentD' d hd)).symm
  have hrel : (A ⊓ Subgroup.centralizer ({u} : Set G)).relIndex A ≤ 2 := by
    have hdvd : (A ⊓ Subgroup.centralizer ({u} : Set G)).relIndex A ∣ D'.relIndex A :=
      Subgroup.relIndex_dvd_of_le_left A hD'le
    rw [hD'rel] at hdvd
    exact Nat.le_of_dvd (by norm_num : 0 < 2) hdvd
  have hsqC_A : u ^ 2 ∈ Subgroup.centralizer (A : Set G) :=
    sq_mem_centralizer_of_relIndex_le_two hAel huN hrel
  have hsqC : CentralizesMod (conjSubgroup V₀ g) A (u * u) := by
    intro v hv
    have hcomm : (u * u) * v = v * (u * u) := by
      have h := Subgroup.mem_centralizer_iff.1 hsqC_A v hv
      rw [pow_two] at h
      exact h.symm
    have h1 : (u * u) * v * (u * u)⁻¹ = v := by
      rw [hcomm]
      group
    rw [h1, mul_inv_cancel]
    exact (conjSubgroup V₀ g).one_mem
  have hCmod : CentralizesMod (conjSubgroup V₀ g) A u := by
    by_contra hnot
    have hGT : MBarGT (conjSubgroup D.M g) (conjSubgroup V₀ g) A 1 :=
      (mBarGT_conj D.M V₀ V g 1).2 hm
    have hcard := hGT.1 u huMg hnot hsqC
    have hle_cent : D' ≤ centMod (conjSubgroup V₀ g) A u := by
      intro d hd
      refine ⟨hD' hd, ?_⟩
      have h1 : u * d * u⁻¹ = d := hcentD' d hd
      rw [h1, mul_inv_cancel]
      exact (conjSubgroup V₀ g).one_mem
    have hcardD'le : Nat.card D' ≤ Nat.card (centMod (conjSubgroup V₀ g) A u) :=
      Nat.card_mono (Set.toFinite _) hle_cent
    have hcardA : Nat.card A = 2 * Nat.card D' := by
      have h := E3.card_eq_two_pow_mul hAel.isPGroup hD'
      rw [hD'1, pow_one] at h
      exact h
    have hle : 4 * Nat.card D' ≤ 2 * Nat.card D' := by
      calc 4 * Nat.card D'
          = 2 ^ (1 + 1) * Nat.card D' := by norm_num
        _ ≤ 2 ^ (1 + 1) * Nat.card (centMod (conjSubgroup V₀ g) A u) :=
            Nat.mul_le_mul_left _ hcardD'le
        _ ≤ Nat.card A := hcard
        _ = 2 * Nat.card D' := hcardA
    have hpos : 0 < Nat.card D' := Nat.card_pos
    omega
  intro a ha
  have hcV₀ : ⁅u, a⁆ ∈ conjSubgroup V₀ g := by
    simpa only [commutatorElement_def] using hCmod a ha
  have haN : a ∈ normalizer (V : Set G) := by
    rw [h62.normalizer_eq]
    exact hAM ha
  have hconj : a * u⁻¹ * a⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.1 haN u⁻¹).1 (V.inv_mem hu)
  have hcV : ⁅u, a⁆ ∈ V := by
    rw [commutatorElement_def]
    simpa only [mul_assoc] using V.mul_mem hu hconj
  have hmem : ⁅u, a⁆ ∈ V ⊓ conjSubgroup V₀ g := Subgroup.mem_inf.2 ⟨hcV, hcV₀⟩
  rw [hTI.2, Subgroup.mem_bot] at hmem
  exact hmem

theorem s16c11_comm_eq_one_of_not_le (D : Data G) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) {g : G}
    (hAM : conjSubgroup V g ≤ D.M) (hVg : ¬ V ≤ conjSubgroup D.M g)
    {D' : Subgroup G} (hD' : D' ≤ conjSubgroup V g)
    (hr : ((E3.mQuot (conjSubgroup V g) D' + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V)
    (hβ : (E3.mQuot (conjSubgroup V g) D' : ℕ∞) < betaN 0 D.M V)
    (hU : V₀ ⊓ conjSubgroup V g = ⊥ ∨
      ((E3.mQuot (conjSubgroup V g) D' + mSub V₀ : ℕ) : ℕ∞) <
        gammaN (E3.mQuot (conjSubgroup V g) D') D.M V)
    {u : G} (hu : u ∈ V) (huD : ∀ d ∈ D', ⁅u, d⁆ ∈ V₀) :
    ∀ a ∈ conjSubgroup V g, ⁅u, a⁆ = 1 := by
  have h62 : Hyp62 D.M V₀ V := h.hyp62
  have hD'M : D' ≤ conjSubgroup V g ⊓ D.M := le_inf hD' (hD'.trans hAM)
  have hD'st : D' ≤ stabTil V₀ V := h62.le_stabTil hD'M
  have hUmem : u ∈ preCTilde V₀ V D' h62.isElemAbelian :=
    (mem_preCTilde_iff h62.isElemAbelian hD'st hu).2 huD
  have hcomm : ⁅preCTilde V₀ V D' h62.isElemAbelian, D'⁆ = ⊥ := by
    rcases hU with hTI | hγ
    · have hUMg : preCTilde V₀ V D' h62.isElemAbelian ≤ conjSubgroup D.M g :=
        six_two_one h62 hD'M hr
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro x hx d hd
      rw [Subgroup.mem_bot]
      have hxV : x ∈ V := preCTilde_le V₀ V D' h62.isElemAbelian hx
      have hxV₀ : ⁅x, d⁆ ∈ V₀ := (mem_preCTilde_iff h62.isElemAbelian hD'st hxV).1 hx d hd
      have hxN : x ∈ normalizer (conjSubgroup V g : Set G) := by
        rw [← E3.conjSubgroup_normalizer, h62.normalizer_eq]
        exact hUMg hx
      have hxA : ⁅x, d⁆ ∈ conjSubgroup V g := by
        rw [commutatorElement_def]
        exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.1 hxN d).1 (hD' hd))
          (Subgroup.inv_mem _ (hD' hd))
      have hmem : ⁅x, d⁆ ∈ V₀ ⊓ conjSubgroup V g := Subgroup.mem_inf.2 ⟨hxV₀, hxA⟩
      rw [hTI, Subgroup.mem_bot] at hmem
      exact hmem
    · exact six_two_two h62 hD'M hr (Or.inr hγ)
  have huC : u ∈ V ⊓ Subgroup.centralizer (D' : Set G) := by
    refine Subgroup.mem_inf.2 ⟨hu, Subgroup.mem_centralizer_iff.2 fun d hd => ?_⟩
    have h1 : ⁅u, d⁆ = 1 := by
      have := Subgroup.commutator_mem_commutator hUmem hd
      rw [hcomm, Subgroup.mem_bot] at this
      exact this
    exact (commutatorElement_eq_one_iff_mul_comm.1 h1).symm
  have h0 : E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ D.M) = 0 := by
    rw [inf_eq_left.2 hAM, E3.mQuot_self]
  have h3 := six_two_three h62 hD'M hr hVg (by rw [h0]; exact hβ)
  intro a ha
  have h4 := Subgroup.commutator_mem_commutator huC (Subgroup.mem_inf.2 ⟨ha, hAM ha⟩)
  rw [h3, Subgroup.mem_bot] at h4
  exact h4

theorem s16c11_barSub_mem_calABar_of_forall {M V₀ V A : Subgroup G} {k : ℕ}
    (hV : IsElemAbelian 2 V) (hAM : A ≤ M) (hAst : A ≤ stabTil V₀ V)
    (hAel : IsElemAbelian 2 A) (hA1 : barSub V₀ V hV A ≠ ⊥)
    (hhyp : ∀ B : Subgroup G, B ≤ A → 0 < E3.mQuot A B → E3.mQuot A B < k →
      ∀ u ∈ V, (∀ d ∈ B, ⁅u, d⁆ ∈ V₀) → ∀ a ∈ A, ⁅u, a⁆ ∈ V₀) :
    barSub V₀ V hV A ∈ calABar k M V₀ V hV := by
  refine ⟨barSub_mono V₀ V hV hAM, hA1, isElemAbelian2_barSub hV hAel, ?_⟩
  intro C hC hlt
  have hBA : preBarSub A V₀ V hV C ≤ A := inf_le_left
  have hBst : preBarSub A V₀ V hV C ≤ stabTil V₀ V := hBA.trans hAst
  have hbarB : barSub V₀ V hV (preBarSub A V₀ V hV C) = C := by
    rw [barSub_preBarSub]
    exact inf_eq_left.2 hC
  have hmB : E3.mQuot A (preBarSub A V₀ V hV C) = E3.mQuot (barSub V₀ V hV A) C :=
    (mQuot_barSub_preBarSub_gen hV hAst hC).symm
  generalize hBdef : preBarSub A V₀ V hV C = B at hBA hBst hbarB hmB
  have hltB : E3.mQuot A B < k := by rw [hmB]; exact hlt
  have hpre : preCTilde V₀ V B hV = preCTilde V₀ V A hV := by
    rcases Nat.eq_zero_or_pos (E3.mQuot A B) with h0 | hpos
    · rw [(E3.mQuot_eq_zero_iff (CFSG.Open.IsElemAbelian.isPGroup hAel) hBA).1 h0]
    · apply le_antisymm
      · intro u hu
        have huV := preCTilde_le V₀ V B hV hu
        rw [mem_preCTilde_iff hV hBst huV] at hu
        rw [mem_preCTilde_iff hV hAst huV]
        exact fun a ha => hhyp B hBA hpos hltB u huV hu a ha
      · intro u hu
        have huV := preCTilde_le V₀ V A hV hu
        rw [mem_preCTilde_iff hV hAst huV] at hu
        rw [mem_preCTilde_iff hV hBst huV]
        exact fun d hd => hu d (hBA hd)
  exact (congrArg fixV hbarB).symm.trans (fixV_barSub_eq_of_preCTilde_eq hV hpre)

theorem s16c11_barSub_conj_eq_bot_or_mem_calABar_two (D : Data G) {V₀ V : Subgroup G}
    (hV : IsElemAbelian 2 V) (h : Hyp125 D V₀ V) {g : G} (hAM : conjSubgroup V g ≤ D.M)
    (hm : MBarGT D.M V₀ V 1) (hr : ((1 + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V)
    (hγ : V₀ ⊓ conjSubgroup V g = ⊥ ∨ ((1 + mSub V₀ : ℕ) : ℕ∞) < gammaN 1 D.M V)
    (hcase : (V₀ ⊓ conjSubgroup V g = ⊥ ∧ V ⊓ conjSubgroup V₀ g = ⊥) ∨
      ¬ V ≤ conjSubgroup D.M g) :
    barSub V₀ V hV (conjSubgroup V g) = ⊥ ∨
      barSub V₀ V hV (conjSubgroup V g) ∈ calABar 2 D.M V₀ V hV := by
  by_cases h1 : barSub V₀ V hV (conjSubgroup V g) = ⊥
  · exact Or.inl h1
  refine Or.inr ?_
  have hP := h.pairFacts
  have hMst : D.M ≤ stabTil V₀ V := le_stabTil hP.le_normalizer hP.le_normalizer₀
  have hVg : IsElemAbelian 2 (conjSubgroup V g) := E3.isElemAbelian_conjSubgroup hV g
  refine s16c11_barSub_mem_calABar_of_forall hV hAM (hAM.trans hMst) hVg h1 ?_
  intro B hBA hB0 hB2 u hu huB a ha
  have hB1 : E3.mQuot (conjSubgroup V g) B = 1 := by omega
  have key : ∀ a ∈ conjSubgroup V g, ⁅u, a⁆ = 1 := by
    rcases hcase with hTI | hVg'
    · exact s16c11_comm_eq_one_of_ti D h hAM hTI hm hr hBA hB1 hu huB
    · have hβ : (E3.mQuot (conjSubgroup V g) B : ℕ∞) < betaN 0 D.M V := by
        rw [hB1]
        have h2 := (succ_le_deltaN_of_mBarGT D h hm 0).trans (deltaN_le_betaN 0)
        exact lt_of_lt_of_le (by exact_mod_cast (by norm_num : 1 < 1 + 1)) h2
      refine s16c11_comm_eq_one_of_not_le D h hAM hVg' hBA (by rw [hB1]; exact hr) hβ ?_ hu huB
      rcases hγ with h0 | hγ'
      · exact Or.inl h0
      · exact Or.inr (by rw [hB1]; exact hγ')
  rw [key a ha]
  exact V₀.one_mem

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
