module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenEightGraphOuter
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenEightGraphW
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNCtx
public import CFSG.LocalAnalysis.WeakClosure81.NineThirteen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.NineThreeSylData
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.L33GraphOuterHolds

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem exists_witness_of_not_normalizer_wClos_one_le {V T : Subgroup G} (hV : Hyp7 V)
    (hm : 2 < rk ↥V) (hVT : V ≤ T) (hT : IsPGroup 2 T) (hTV : T ≤ normalizer (V : Set G))
    (h1 : ¬ normalizer (E3.wClos V 1 T : Set G) ≤ normalizer (V : Set G)) :
    ∃ h : G, h ∉ normalizer (V : Set G) ∧ conjSubgroup V h ≤ T ∧
      conjSubgroup V h ≤ centralizer (E3.wClos V 0 T : Set G) ∧
      ∃ u ∈ conjSubgroup V h, u ≠ 1 ∧ u ∈ centralizer (E3.wClos V 1 T : Set G) := by
  obtain ⟨h, hh1, hhM⟩ := Set.not_subset.1 h1
  have hVab : IsElemAbelian 2 V := hV.1
  have hTI : IsTI V := hV.2.2
  have hVne : V ≠ ⊥ := by
    intro hb
    have h2 := hV.2.1
    rw [hb, Subgroup.card_bot] at h2
    omega
  set W1 := E3.wClos V 1 T with hW1
  set W0 := E3.wClos V 0 T with hW0
  have hVW1 : V ≤ W1 := by
    have := E3.le_wClos_of_mQuot_le (X := T) hVab 1
      (by rw [CFSG.Quasithin.conjSubgroup_one]; exact hVT) le_rfl
      (by rw [E3.mQuot_self]; omega) (by omega : 1 < rk ↥V)
    rwa [CFSG.Quasithin.conjSubgroup_one] at this
  have hW1conj : conjSubgroup W1 h = W1 := conjSubgroup_eq_iff_mem_normalizer.2 hh1
  have hUW1 : conjSubgroup V h ≤ W1 := by
    have := E3.conjSubgroup_mono_left h hVW1
    rwa [hW1conj] at this
  have hUT : conjSubgroup V h ≤ T := hUW1.trans (E3.wClos_le 1 T)
  obtain ⟨v, hvV, hv1, hvT⟩ := RonanE628.exists_central_of_normalized hT hVT hVne hTV
  have huU : h⁻¹ * v * h ∈ conjSubgroup V h := by
    rw [mem_conjSubgroup_iff]
    simpa [mul_assoc] using hvV
  have hu1 : h⁻¹ * v * h ≠ 1 := by
    intro h0
    apply hv1
    have := congrArg (fun z => h * z * h⁻¹) h0
    simpa [mul_assoc] using this
  have huC : h⁻¹ * v * h ∈ centralizer (W1 : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hw' : h * w * h⁻¹ ∈ W1 := (Subgroup.mem_normalizer_iff.1 hh1 w).1 hw
    have hc := hvT _ (E3.wClos_le 1 T hw')
    calc w * (h⁻¹ * v * h) = h⁻¹ * ((h * w * h⁻¹) * v) * h := by group
      _ = h⁻¹ * (v * (h * w * h⁻¹)) * h := by rw [hc]
      _ = h⁻¹ * v * h * w := by group
  have hV4 : 4 ≤ Nat.card V := by
    rw [card_eq_two_pow_of_isPGroup hVab.isPGroup]
    calc 4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ rk ↥V := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hh0 : h ∈ normalizer (W0 : Set G) := normalizer_wClos_one_le hVab hV4 hh1
  have hW0U : W0 ≤ normalizer (conjSubgroup V h : Set G) := by
    have h2 : conjSubgroup W0 h = W0 := conjSubgroup_eq_iff_mem_normalizer.2 hh0
    have h3 : conjSubgroup W0 h ≤ conjSubgroup (normalizer (V : Set G)) h :=
      E3.conjSubgroup_mono_left h ((E3.wClos_le 0 T).trans hTV)
    rwa [h2, conjSubgroup_normalizer] at h3
  have hUC0 : conjSubgroup V h ≤ centralizer (W0 : Set G) := by
    rw [Subgroup.le_centralizer_iff, hW0, wClos_zero_eq_iSup hVab]
    refine iSup₂_le fun g hg => ?_
    exact NFW.conj_le_centralizer_of_le_normalizer hVab hTI hVne
      ((conjSubgroup_le_wClos_zero hg).trans hW0U)
  exact ⟨h, hhM, hUT, hUC0, h⁻¹ * v * h, huU, hu1, huC⟩

theorem eq_of_le_of_lt_sup_of_card_three {Z S K₀ : Subgroup G} (hZ : Nat.card Z = 3)
    (hZS : (Z : Set G) * (S : Set G) = (S : Set G) * (Z : Set G)) (h1 : S ≤ K₀)
    (h2 : K₀ < Z ⊔ S) : K₀ = S := by
  refine le_antisymm (fun k hk => ?_) h1
  by_contra hkS
  have hkZS : k ∈ ((Z ⊔ S : Subgroup G) : Set G) := h2.le hk
  rw [coe_sup_eq_mul_of_mul_eq_mul hZS] at hkZS
  obtain ⟨z, hz, s, hs, rfl⟩ := hkZS
  have hzK : z ∈ K₀ := by
    have := K₀.mul_mem hk (K₀.inv_mem (h1 hs))
    simpa using this
  have hz1 : z ≠ 1 := by
    rintro rfl
    exact hkS (by simpa using hs)
  have hzo : orderOf z ∣ 3 := by
    rw [← hZ]
    exact Subgroup.orderOf_dvd_natCard Z hz
  have hzo3 : orderOf z = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hzo with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hz1
    · exact h
  have hZz : zpowers z = Z :=
    Subgroup.eq_of_le_of_card_ge (zpowers_le.2 hz) (by rw [hZ, Nat.card_zpowers, hzo3])
  have hZK : Z ≤ K₀ := hZz ▸ zpowers_le.2 hzK
  exact lt_irrefl _ (h2.trans_le (sup_le hZK h1))

end CFSG.LocalAnalysis.WeakClosure81

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.CGT.Timmesfeld75 (IsTI)

variable {G : Type} [Group G] [Finite G]

theorem gap17_8_graphOuterThree_of_graphOuterW (hTim : CFSG.CGT.Timmesfeld75.NodeStatement)
    (hcat : ¬ CFSG.Blueprint.Catalog G) (D : Data G) (h66 : UC6.R6_6 D) (h88 : W3Thm88 G)
    (hKG : K_L33GraphOuter) (hKW : K_L33GraphOuterW) {V₀ V : Subgroup G}
    (h93s : CFSG.LocalAnalysis.WeakClosure81.Thm93Syl V₀ D.T) :
    Gap17_8_graphOuterThree D V₀ V := by
  intro hV L hL hL3 hTL hk _hE9 h8 hN h1 _h2 g hgT hgout _hcard
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set H : Subgroup G := L ⊔ D.T with hHdef
  set Q : Subgroup G := pCoreOf 2 H with hQdef
  have h8' : 8 ≤ Nat.card V₀ := h8.ge
  have hne : V₀ ≠ ⊥ := by
    rintro rfl
    simp at h8
  have hW : InCalV D.M V₀ := hyp125_inCalV hV hne
  have hTI : IsTI V₀ := hyp125_isTI hV hne
  have hVab : IsElemAbelian 2 V₀ := hW.2.2.2
  have hNV : normalizer (V₀ : Set G) = D.M := normalizer_eq_of_inCalV D hW
  have h93 : CFSG.LocalAnalysis.WeakClosure81.Thm93 V₀ D.T := thm93_of_thm93Syl D hW h93s
  have hV7 : Hyp7 V₀ := TwelveSeven.hyp7_of_inCalV D hW hTI h8'
  have hrk : 2 < rk ↥V₀ := TwelveSeven.two_lt_rk_of_card hVab h8'
  have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := by
    by_contra hns
    have h2 : D.k = 2 := (Data.k_eq_two_iff D).2 hns
    omega
  have hInt : ∀ X : Subgroup G, X ≤ D.M → IsPGroup 3 X →
      ∀ x : G, x ∉ D.M → X ⊓ conjSubgroup D.M x = ⊥ := fun X hXM hXp x hx => by
    have hx' : x⁻¹ ∉ D.M := fun h => hx (by simpa using D.M.inv_mem h)
    simpa [conjSubgroup] using hsp.inf_map_conj_eq_bot Nat.prime_three hXM hXp x⁻¹ hx'
  have hHM : H ≤ D.M := sup_le hL.1.le D.sylowM.le
  have hTH : D.T ≤ H := le_sup_right
  have hT2 : IsPGroup 2 D.T := D.sylowM.isPGroup
  have hHQ : H ≤ normalizer (Q : Set G) :=
    Subgroup.le_normalizer.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 H)
  have hVT : V₀ ≤ D.T := uc22p22p_le_T_of_inCalV D hW
  have hTV : D.T ≤ normalizer (V₀ : Set G) := hNV ▸ D.sylowM.le
  have hout : ¬ D.T ≤ L ⊔ Q := fun h => hgout (hgT.trans h)
  have h1216 : ∀ Y : Subgroup G, Y ≤ L → IsPGroup 3 Y → Permutes Y D.T →
      Y ⊔ D.T ≤ normalizer (E3.wClos V₀ 0 D.T : Set G) := fun Y hYL hY3 hYT =>
    (twelve_sixteen hTim hcat D h66 h88 hV h8' h93 (p := 3) (by norm_num) (by norm_num) hY3
      (fun x hx _ => hInt Y (hYL.trans hL.1.le) hY3 x hx)
      (hsp.rankThreeGamma_one_le_of_le Nat.prime_three hY3 (hYL.trans hL.1.le)) hYT).2
  have hW0T : E3.wClos V₀ 0 D.T ≤ D.T := wClos_zero_le V₀ D.T
  obtain ⟨h, hhM, hUT, hUC, u, huU, hu1, huC⟩ :=
    exists_witness_of_not_normalizer_wClos_one_le hV7 hrk hVT hT2 hTV (hNV.symm ▸ h1)
  set U := conjSubgroup V₀ h with hUdef
  have hUW : U ≤ E3.wClos V₀ 0 D.T := conjSubgroup_le_wClos_zero hUT
  obtain ⟨Y₁, hY₁L, hY₁3, -, hY₁T, hP⟩ := exists_three_17_8_graph hKG hL hL3 hTL hout
  have hULQ : U ≤ L ⊔ Q := by
    by_contra hUout
    obtain ⟨-, y, hyY, hnc⟩ := hP _ U hW0T (h1216 Y₁ hY₁L hY₁3 hY₁T) hUW
      (isElemAbelian_conjSubgroup' hVab h) hUout
    apply hnc
    intro a ha b hb
    have hyW : y ∈ normalizer (E3.wClos V₀ 0 D.T : Set G) :=
      h1216 Y₁ hY₁L hY₁3 hY₁T ((le_sup_left : Y₁ ≤ Y₁ ⊔ D.T) hyY)
    have hbW : b ∈ E3.wClos V₀ 0 D.T := by
      have h1' : conjSubgroup U y ≤ conjSubgroup (E3.wClos V₀ 0 D.T) y :=
        E3.conjSubgroup_mono_left y hUW
      rw [conjSubgroup_eq_iff_mem_normalizer.2 hyW] at h1'
      exact h1' hb
    exact (Subgroup.mem_centralizer_iff.1 (hUC ha) b hbW).symm
  have hUQ : U ≤ Q := by
    have hS1 : E3.wClos V₀ 0 (innerT17_8 D L) ≤ Q :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((wClos_zero_le V₀ _).trans (inf_le_left.trans hTH)) hN
        (hT2.to_le ((wClos_zero_le V₀ _).trans inf_le_left))
    exact (conjSubgroup_le_wClos_zero (le_inf hUT hULQ)).trans hS1
  obtain ⟨Y₂, hY₂L, hY₂3, -, hY₂T, hP'⟩ := exists_three_17_8_graphW hKW hL hL3 hTL hout
  obtain ⟨y, -, Z, S', hZ3, hZH, hQS', hS'T, hZS', hAS', hcl⟩ :=
    hP' _ (conjSubgroup V₀ g) hW0T (h1216 Y₂ hY₂L hY₂3 hY₂T) (conjSubgroup_le_wClos_zero hgT)
      (isElemAbelian_conjSubgroup' hVab g) hgout
  have hS'2 : IsPGroup 2 S' := hT2.to_le hS'T
  have hZp : IsPGroup 3 Z := IsPGroup.of_card (n := 1) (by rw [hZ3, pow_one])
  have hZM : Z ≤ normalizer (V₀ : Set G) := hNV ▸ hZH.trans hHM
  have hS'M : S' ≤ normalizer (V₀ : Set G) := hNV ▸ (hS'T.trans (hTH.trans hHM))
  have hKN : Z ⊔ S' ≤ normalizer (E3.wClos V₀ 0 S' : Set G) := by
    by_contra hKW'
    have hmin : ∀ K₀ : Subgroup G, S' ≤ K₀ → K₀ < Z ⊔ S' →
        K₀ ≤ normalizer (E3.wClos V₀ 0 S' : Set G) := fun K₀ hK₀ hlt => by
      rw [eq_of_le_of_lt_sup_of_card_three hZ3 hZS' hK₀ hlt]
      exact Subgroup.le_normalizer.trans (E3.normalizer_le_normalizer_wClos S')
    have h91 : Nine1Hyp V₀ (Z ⊔ S') S' Z 3 :=
      nine1Hyp_of_minimal Nat.prime_three (by norm_num) hZp hZM hS'2 hS'M hZS'
        (Subgroup.le_normalizer.trans (E3.normalizer_le_normalizer_wClos S')) hKW' hmin
    obtain ⟨z, hz, hz3⟩ := NFW.exists_orderOf_three_twoResidual h91.toTwoPTwoIrred
    have hzK : z ∈ Z ⊔ S' := CFSG.Quasithin.twoResidual_le _ hz
    have hzM : z ∈ D.M := (sup_le (hZH.trans hHM) (hS'T.trans (hTH.trans hHM))) hzK
    have key : z * u = u * z → False := by
      intro hzu
      have hzN : z ∈ normalizer (U : Set G) :=
        centralizer_le_normalizer_conj hTI h huU hu1
          (Subgroup.mem_centralizer_singleton_iff.2 hzu)
      have hzMh : z ∈ conjSubgroup D.M h := by
        rw [← hNV, E3.conjSubgroup_normalizer]
        exact hzN
      have hz3p : IsPGroup 3 (zpowers z) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz3, pow_one])
      have hbot := hInt (zpowers z) (zpowers_le.2 hzM) hz3p h (hNV ▸ hhM)
      have hmem : z ∈ zpowers z ⊓ conjSubgroup D.M h := ⟨mem_zpowers z, hzMh⟩
      rw [hbot, mem_bot] at hmem
      rw [hmem, orderOf_one] at hz3
      exact absurd hz3 (by norm_num)
    rcases nine_one hV7 hrk h91 with h91a | h91b | h91c
    · exact hKW' h91a
    · have huS : u ∈ E3.cClos V₀ 1 S' := by
        refine Subgroup.mem_inf.2 ⟨hQS' (hUQ huU), ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        exact (Subgroup.mem_centralizer_iff.1 huC) w (E3.wClos_mono hS'T hw)
      have hzc := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h91b hz
      exact key ((Subgroup.mem_centralizer_iff.1 hzc) u huS).symm
    · have hQK : Q ≤ pCoreOf 2 (Z ⊔ S') :=
        CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hQS'.trans le_sup_right)
          ((sup_le hZH (hS'T.trans hTH)).trans hHQ) (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)
      have hc := Subgroup.commutator_eq_bot_iff_le_centralizer.1
        (h91c.2 U ⟨h, rfl⟩ (hUQ.trans hQK)) huU
      exact key ((Subgroup.mem_centralizer_iff.1 hc) z hz)
  apply hcl (E3.wClos V₀ 0 S')
  · rw [CFSG.Quasithin.conjSubgroup_conjSubgroup] at hAS' ⊢
    exact conjSubgroup_le_wClos_zero hAS'
  · exact wClos_zero_le V₀ S'
  · refine sup_le ((le_sup_left : Z ≤ Z ⊔ S').trans hKN) ?_
    intro t ht
    exact E3.normalizer_le_normalizer_wClos S' ht.2

theorem gap17_8_graphOuterThree_of_W
    (hTim : CFSG.CGT.Timmesfeld75.NodeStatement)
    (hcat : ¬ CFSG.Blueprint.Catalog G) (D : Data G) (h66 : UC6.R6_6 D) (h88 : W3Thm88 G)
    (hKW : K_L33GraphOuterW) {V₀ V : Subgroup G}
    (h93s : CFSG.LocalAnalysis.WeakClosure81.Thm93Syl V₀ D.T) :
    Gap17_8_graphOuterThree D V₀ V :=
  gap17_8_graphOuterThree_of_graphOuterW hTim hcat D h66 h88 k_L33GraphOuter_holds hKW h93s

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
