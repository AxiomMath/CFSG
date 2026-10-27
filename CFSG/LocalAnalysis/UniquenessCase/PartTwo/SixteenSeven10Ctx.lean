module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResults
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen24R
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4136Mbar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataKParam
public import CFSG.LocalAnalysis.WeakClosure81.SixThirteenCore
public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenMain

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def Out10 (D : Data G) (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) : Prop :=
  D.k < mBar D.M V₀ V hV ∧ (V₀ ≠ ⊥ → ∀ g : G, ¬ InCalO1 D.k D.M V₀ V g)

theorem s16c1610_hyp6H (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1114 : R1114 D) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) : Hyp6H D.M V₀ V := by
  by_cases hV₀ : V₀ = ⊥
  · subst hV₀
    have hP := h.pairFacts
    exact ⟨hP.elemAbelian, h.normalizer_eq, hP.le, hP.le_normalizer₀,
      fun h => absurd rfl h, fun h => absurd rfl h, fun h => absurd rfl h, fun h => absurd rfl h⟩
  · exact (weakClosureSetting_of_hyp125 D hx h61 h127 h1114 h hV₀).hyp6H

theorem r16_10_1_of_out10 (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1114 : R1114 D) (h126 : R126 D)
    (hout : ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Counterex16 D V₀ V L hV →
      Out10 D V₀ V hV) :
    R16_10_1 D := by
  intro V₀ V L hV hc H₀ hmin
  have h : Hyp125 D V₀ V := hc.setting.hyp16.hyp125
  have hH := s16c1610_hyp6H D hx h61 h127 h1114 h
  obtain ⟨hk, hno⟩ := hout V₀ V L hV hc
  have hkr : (D.k : ℕ∞) < rMV D.M V := Sixteen24.k_lt_rMV_of_hyp125 D hSg h1219 hx h61 h
  have hS : IsSylowIn 2 D.T H₀ := TwelveShort.isSylowIn_of_le D hmin.1.1
  have hE : E1.InE D.k H₀ := h126 H₀ hmin
  have := six_thirteen_two_of_no_calO1 hH hkr hk hno hS hE
  rwa [sup_comm] at this

theorem s16c1610_k_cases (D : Data G) : D.k = 1 ∨ D.k = 2 := by
  by_cases h : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M
  · exact Or.inl (Data.k_eq_one_of_isStronglyPEmbedded D h)
  · exact Or.inr ((Data.k_eq_two_iff D).2 h)

structure In10 (D : Data G) : Prop where
  hSg : UC6S846.SigmaStd D
  h1219 : D.sig = D.sig1
  hx : DataExt D
  h61 : UC6.R6_1 D
  h127 : R127 D
  h1114 : R1114 D
  h126 : R126 D
  h1214 : F12.R1214 D
  h162 : W3Thm162Ext G
  h139 : Hyp139
  h169 : R16_9 D

section Certified

theorem s16c1610_out10_of_r14 (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1114 : R1114 D) (h162 : W3Thm162Ext G) (h139 : Hyp139) {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) (hkm : D.k < mBar D.M V₀ V h.isElemAbelian) {p : ℕ} (hp : p.Prime)
    (hpk : 2 ^ (D.k + 1) - 1 ≤ p) {X : Subgroup (MulAut (Vtil V₀ V h.isElemAbelian))}
    (hXM : X ≤ Mbar D.M V₀ V h.isElemAbelian) (hXcard : Nat.card X = p)
    (hXnorm : ∀ m ∈ Mbar D.M V₀ V h.isElemAbelian, ∀ x ∈ X, m * x * m⁻¹ ∈ X)
    (hnot : ¬ Concl614 (Vtil V₀ V h.isElemAbelian) (Mbar D.M V₀ V h.isElemAbelian) X) :
    Out10 D V₀ V h.isElemAbelian := by
  refine ⟨hkm, fun hV₀ g hO1 => ?_⟩
  have hk := s16c1610_k_cases D
  have hH := s16c1610_hyp6H D hx h61 h127 h1114 h
  have hm1 : 1 < mBar D.M V₀ V h.isElemAbelian := by omega
  have hr : ((mSub V₀ + D.k : ℕ) : ℕ∞) < rMV D.M V := by
    have hW := weakClosureSetting_of_hyp125 D hx h61 h127 h1114 h hV₀
    have h1 := h162 D V₀ V hW hx h61 hV₀ hm1
    refine lt_of_lt_of_le ?_ h1
    exact_mod_cast (by omega : mSub V₀ + D.k < mBar D.M V₀ V h.isElemAbelian + mSub V₀)
  have hstar := (hH.hyp65 hV₀ hO1).inCalOStar_of_lt_rMV hr
  have h64 := hH.hyp64 hstar
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀
  exact hnot (six_fourteen_of_calOStar h139 hk hp hpk h64 (hH.conjGenerated hV₀)
    (isKGroup_mbar D h.isElemAbelian hMs) hkm hXM hXcard hXnorm)

theorem s16c1610_out10_of_r13 (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1114 : R1114 D) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    (hkm : D.k < mBar D.M V₀ V h.isElemAbelian) {p : ℕ} (hp : p.Prime) (hpk : D.k + 1 < p)
    {X : Subgroup (MulAut (Vtil V₀ V h.isElemAbelian))} (hXne : X ≠ ⊥)
    (hXM : X ≤ Mbar D.M V₀ V h.isElemAbelian) (hXp : IsPGroup p X)
    (hXnorm : ∀ m ∈ Mbar D.M V₀ V h.isElemAbelian, ∀ x ∈ X, m * x * m⁻¹ ∈ X)
    (hβ : V₀ ≠ ⊥ → ((D.k + 1 : ℕ) : ℕ∞) < betaN D.k D.M V)
    (hrm : V₀ ≠ ⊥ → ((D.k + 1 : ℕ) : ℕ∞) < rMV D.M V - (mSub V₀ : ℕ∞)) :
    Out10 D V₀ V h.isElemAbelian :=
  ⟨hkm, fun hV₀ g => not_inCalO1 (s16c1610_hyp6H D hx h61 h127 h1114 h) hV₀
    ⟨s16c1610_k_cases D, hkm, hXne, hXM, hXp, hXnorm, hp, hpk,
      lt_min_iff.2 ⟨hβ hV₀, hrm hV₀⟩⟩ g⟩

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
