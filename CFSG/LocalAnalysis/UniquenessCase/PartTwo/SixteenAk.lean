module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResultsB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResults2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenTwentyThree
public import CFSG.LocalAnalysis.WeakClosure81.FourteenNine
public import CFSG.LocalAnalysis.WeakClosure81.SixOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsSetting
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
public import CFSG.LocalAnalysis.UniquenessCase.UCR638
public import CFSG.Milestones.ASVolI.I2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem isElemAbelian2_barSub {V₀ V X : Subgroup G} (hV : IsElemAbelian 2 V)
    (hX : IsElemAbelian 2 X) : IsElemAbelian2 (barSub V₀ V hV X) := by
  refine ⟨?_, ?_⟩
  · intro a ha b hb
    obtain ⟨ga, hga, rfl⟩ := (mem_barSub V₀ V hV X a).1 ha
    obtain ⟨gb, hgb, rfl⟩ := (mem_barSub V₀ V hV X b).1 hb
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (B2F.isElemAbelian_comm hX hga hgb)
  · intro a ha
    obtain ⟨ga, hga, rfl⟩ := (mem_barSub V₀ V hV X a).1 ha
    rw [← map_pow]
    have hga2 : ga ^ 2 = 1 := Subtype.ext (by simpa using hX.2 (ga : G) hga)
    rw [hga2, map_one]

theorem preCTilde_eq_inf_centralizer_of {V₀ V D : Subgroup G} (hV : IsElemAbelian 2 V)
    (hD : D ≤ stabTil V₀ V)
    (hc : ∀ v ∈ V, (∀ d ∈ D, ⁅v, d⁆ ∈ V₀) → v ∈ centralizer (D : Set G)) :
    preCTilde V₀ V D hV = V ⊓ centralizer (D : Set G) := by
  apply le_antisymm
  · intro u hu
    have huV : u ∈ V := preCTilde_le V₀ V D hV hu
    exact Subgroup.mem_inf.2 ⟨huV, hc u huV ((mem_preCTilde_iff hV hD huV).1 hu)⟩
  · intro u hu
    rw [Subgroup.mem_inf] at hu
    refine (mem_preCTilde_iff hV hD hu.1).2 fun d hd => ?_
    have h1 : ⁅u, d⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_centralizer_iff.1 hu.2 d hd).symm
    rw [h1]
    exact V₀.one_mem

theorem fixV_barSub_eq_of_preCTilde_eq {V₀ V B D : Subgroup G} (hV : IsElemAbelian 2 V)
    (h : preCTilde V₀ V B hV = preCTilde V₀ V D hV) :
    fixV (barSub V₀ V hV B) = fixV (barSub V₀ V hV D) := by
  have hB := imgTil_preTil V₀ V hV (fixV (barSub V₀ V hV B))
  have hD := imgTil_preTil V₀ V hV (fixV (barSub V₀ V hV D))
  unfold preCTilde at h
  rw [← hB, ← hD, h]

theorem mQuot_le_rk_of_le {V U : Subgroup G} (hV : IsPGroup 2 V) (hUV : U ≤ V) :
    E3.mQuot V U ≤ rk V := by
  have h := E3.card_eq_two_pow_mul hV hUV
  rw [card_eq_two_pow_of_isPGroup hV, card_eq_two_pow_of_isPGroup (hV.to_le hUV),
    ← pow_add] at h
  have h' := Nat.pow_right_injective (le_refl 2) h
  omega

theorem barSub_mem_calABar_of_gammaSet (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) (h21 : R1621 D) (h22 : R1622 D) {V₀ V : Subgroup G}
    (h : Hyp16 D V₀ V) {i k : ℕ} (hr : ((k + i + mSub V₀ : ℕ) : ℕ∞) ≤ rMV D.M V)
    (hδ : ((k + i : ℕ) : ℕ∞) ≤ deltaInf D.M V) {A : Subgroup G}
    (hA : A ∈ E3.gammaSet V i D.M) (hA1 : barSub V₀ V h.hyp125.isElemAbelian A ≠ ⊥) :
    barSub V₀ V h.hyp125.isElemAbelian A ∈
      calABar k D.M V₀ V h.hyp125.isElemAbelian := by
  have hV : IsElemAbelian 2 V := h.hyp125.isElemAbelian
  have hP := h.hyp125.pairFacts
  have hMst : D.M ≤ stabTil V₀ V := le_stabTil hP.le_normalizer hP.le_normalizer₀
  obtain ⟨hAM, g, hAg, hmA⟩ := id hA
  have hVg : IsElemAbelian 2 (conjSubgroup V g) := E3.isElemAbelian_conjSubgroup hV g
  have hAst : A ≤ stabTil V₀ V := hAM.trans hMst
  have hAel : IsElemAbelian 2 A := B2F.isElemAbelian_mono hAg hVg
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
  have hjk : E3.mQuot A B < k := hmB ▸ hlt
  have hBγ : B ∈ E3.gammaSet V (E3.mQuot A B + i) D.M :=
    ⟨hBA.trans hAM, g, hBA.trans hAg, by rw [E3.mQuot_add hBA hAg, hmA]⟩
  have hi : ((E3.mQuot A B + i + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V :=
    lt_of_lt_of_le (by exact_mod_cast (by omega : E3.mQuot A B + i + mSub V₀ <
      k + i + mSub V₀)) hr
  have hi0 : ((i + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V :=
    lt_of_lt_of_le (by exact_mod_cast (by omega : i + mSub V₀ < k + i + mSub V₀)) hr
  obtain ⟨-, hcB, -⟩ := sixteen_twentyThree_one D h22 h hBγ (hBA.trans hAg) hi
  obtain ⟨-, hcA, -⟩ := sixteen_twentyThree_one D h22 h hA hAg hi0
  have hpB : preCTilde V₀ V B hV = V ⊓ centralizer (B : Set G) :=
    preCTilde_eq_inf_centralizer_of hV hBst hcB
  have hpA : preCTilde V₀ V A hV = V ⊓ centralizer (A : Set G) :=
    preCTilde_eq_inf_centralizer_of hV hAst hcA
  have hn : E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ D.M) ≤ mSub V := by
    have h1 := mQuot_le_rk_of_le hVg.isPGroup (inf_le_left : conjSubgroup V g ⊓ D.M ≤ _)
    have h2 : rk ↥(conjSubgroup V g) = rk ↥V := by
      unfold rk
      rw [E3.card_conjSubgroup]
    unfold mSub
    omega
  have hδj : ((E3.mQuot A B + i : ℕ) : ℕ∞) <
      deltaN (E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ D.M)) D.M V :=
    lt_of_lt_of_le (by exact_mod_cast (by omega : E3.mQuot A B + i < k + i))
      (hδ.trans (deltaN_anti hn))
  have hcomm := sixteen_twentyThree_two D hSg h1219 h21 h hBγ (hBA.trans hAg) hi hδj
  have hle : V ⊓ centralizer (B : Set G) ≤ V ⊓ centralizer (A : Set G) := by
    intro u hu
    refine Subgroup.mem_inf.2 ⟨hu.1, Subgroup.mem_centralizer_iff.2 fun a ha => ?_⟩
    have h1 := Subgroup.commutator_mem_commutator hu
      (show a ∈ conjSubgroup V g ⊓ D.M from ⟨hAg ha, hAM ha⟩)
    rw [hcomm, Subgroup.mem_bot] at h1
    exact (commutatorElement_eq_one_iff_mul_comm.1 h1).symm
  have hge : V ⊓ centralizer (A : Set G) ≤ V ⊓ centralizer (B : Set G) :=
    inf_le_inf_left V (Subgroup.centralizer_le hBA)
  have hpeq : preCTilde V₀ V B hV = preCTilde V₀ V A hV := by
    rw [hpB, hpA]
    exact le_antisymm hle hge
  exact (congrArg fixV hbarB).symm.trans (fixV_barSub_eq_of_preCTilde_eq hV hpeq)

theorem barSub_mem_calABar_of_gammaSet_zero (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) (h21 : R1621 D) (h22 : R1622 D) {V₀ V : Subgroup G}
    (h : Hyp16 D V₀ V) {k : ℕ} (hr : ((k + mSub V₀ : ℕ) : ℕ∞) ≤ rMV D.M V)
    (hδ : (k : ℕ∞) ≤ deltaInf D.M V) {A : Subgroup G} (hA : A ∈ E3.gammaSet V 0 D.M)
    (hA1 : barSub V₀ V h.hyp125.isElemAbelian A ≠ ⊥) :
    barSub V₀ V h.hyp125.isElemAbelian A ∈
      calABar k D.M V₀ V h.hyp125.isElemAbelian :=
  barSub_mem_calABar_of_gammaSet D hSg h1219 h21 h22 h (i := 0) (by simpa using hr)
    (by simpa using hδ) hA hA1

theorem sixteen_fortyThree_two (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) (h21 : R1621 D) (h22 : R1622 D) (h42 : R16_42 D) :
    R16_43_2 D := by
  intro V₀ V L hV hS h1 i A g hH hi0 hA1
  obtain ⟨hr, hδ, -⟩ := h42 V₀ V L hV hS h1
  subst hi0
  refine barSub_mem_calABar_of_gammaSet_zero D hSg h1219 h21 h22 hS.setting.hyp16 ?_
    (by exact_mod_cast hδ) hH.2.1 hA1
  exact le_trans (by exact_mod_cast (by omega : 2 + mSub V₀ ≤ mSub V₀ + 4)) hr

theorem sixteen_fiftyOne_calABar (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) (h21 : R1621 D) (h22 : R1622 D) (h50 : R16_50 D)
    (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V) (hS : Sect16 D V₀ V L hV)
    (h4 : Case167_4 D V₀ V hV L) {A : Subgroup G} (hA : A ∈ E3.gammaSet V 0 D.M)
    (hA1 : barSub V₀ V hV A ≠ ⊥) : barSub V₀ V hV A ∈ calABar 2 D.M V₀ V hV := by
  obtain ⟨hr, hδ, -⟩ := h50 V₀ V L hV hS h4
  refine barSub_mem_calABar_of_gammaSet_zero D hSg h1219 h21 h22 hS.setting.hyp16 ?_
    (by exact_mod_cast hδ) hA hA1
  exact le_trans (by exact_mod_cast (by omega : 2 + mSub V₀ ≤ mSub V₀ + 4)) hr

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
