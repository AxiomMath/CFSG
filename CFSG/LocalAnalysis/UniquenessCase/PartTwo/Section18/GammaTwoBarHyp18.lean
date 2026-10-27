module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.GammaTwoBar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtyThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentyEight
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInputs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSixtyOne

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem eighteen_twenty_exists_gamma {A U : Subgroup G} {V : Subgroup G} {g : G}
    (hV : IsElemAbelian 2 V)
    (hUV : U ≤ V) (hcard : Nat.card V = 2 ^ 2 * Nat.card U)
    (hAeq : A = U.map (MulAut.conj g).toMonoidHom) {j : ℕ} (hj3 : 3 ≤ j)
    (hjU : j ≤ mSub V) :
    ∃ B : Subgroup G, B ∈ F12.Gam (j - 1) A V := by
  have hU2 : IsPGroup 2 U := hV.isPGroup.to_le hUV
  have hcardU : Nat.card U = 2 ^ mSub U := card_eq_two_pow_mSub hU2
  have hcardV : Nat.card V = 2 ^ mSub V := card_eq_two_pow_mSub hV.isPGroup
  have hmU : mSub V = 2 + mSub U := by
    rw [hcardV, hcardU] at hcard
    have h4 : 2 ^ mSub V = 2 ^ (2 + mSub U) := by
      rw [hcard, pow_add]
    exact Nat.pow_right_injective (by norm_num) h4
  have hU' : ∃ U' : Subgroup G, U' ≤ U ∧ Nat.card U = 2 ^ (j - 3) * Nat.card U' := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥U) 2
      (n := mSub U - (j - 3)) (by
        rw [hcardU]
        exact pow_dvd_pow 2 (Nat.sub_le _ _))
    refine ⟨K.map U.subtype, Subgroup.map_subtype_le K, ?_⟩
    rw [Subgroup.card_map_of_injective U.subtype_injective, hK, hcardU, ← pow_add]
    congr 1
    omega
  obtain ⟨U', hU'U, hU'card⟩ := hU'
  refine ⟨U'.map (MulAut.conj g).toMonoidHom, ⟨?_, U', g, hU'U.trans hUV, ?_, rfl⟩⟩
  · rw [hAeq]
    exact Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hU'U
  · have hpow : 2 ^ 2 * 2 ^ (j - 3) = 2 ^ (j - 1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hcard, hU'card, ← mul_assoc, hpow]

theorem exists_gammaTwo_barSub_ne_bot_of_hyp18 (D : Data G) (V₀ V : Subgroup G) (p : ℕ)
    (L : Subgroup G)
    (h : Hyp18 D V₀ V p L)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h126 : R126 D) (h66 : UC6.R6_6 D)
    (h127 : R127 D) (h1114 : R1114 D) (h111 : W3Thm111 G) (h183 : W3Thm183 G)
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3) :
    ∃ A ∈ F12.Gam 2 D.T V, barSub V₀ V h.hyp125.isElemAbelian A ≠ ⊥ := by
  have hV : IsElemAbelian 2 V := h.hyp125.isElemAbelian
  have hrkO : ∀ q ∈ D.sig, 3 ≤ CFSG.Open.pRank q D.M := hx.three_le
  have hrk : ∀ q ∈ D.sig, 3 ≤ CFSG.pRank q D.M := fun q hq => by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact hrkO q hq
  by_cases hV₀ : V₀ = ⊥
  · subst hV₀
    by_contra hcon
    push Not at hcon
    have hm3 : MBarGT D.M ⊥ V 3 := h1669 (by simp)
    have hmbar : 3 < mBar D.M ⊥ V hV := (h.hyp125.mBarGT_iff_lt_mBar 3).1 hm3
    have hkr : 2 < rk ↥V :=
      lt_of_lt_of_le (by norm_num : (2 : ℕ) < 3)
        (hmbar.le.trans (CFSG.LocalAnalysis.WeakClosure81.mBar_le_rk (M := D.M) hV bot_le))
    have hW2 : E3.wClos V 2 D.T ≤ Subgroup.centralizer (V : Set G) := by
      refine E3.wClos_le_of_forall fun A hA => ?_
      have hA' : A ∈ F12.Gam 2 D.T V := by rwa [S17.gam_eq_gammaSet]
      exact (S17.barSub_bot_iff_le_centralizer h.hyp125 (hA.1.trans D.sylowM.le)).1
        (hcon A hA')
    have hW0 : E3.wClos V 0 D.T ≤ Subgroup.centralizer (V : Set G) :=
      (wClos_le_wClos_of_le hV (Nat.zero_le 2) hkr D.T).trans hW2
    have hNW0 : normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M :=
      fifteen_thirteen_a D (r129_1_of_r127 D h127) h61 hx.sig_nonempty hrk h.hyp125 hW0
    have hk2 : D.k ≤ 2 := TwelveSeven.k_le_two D
    have hVT : V ≤ D.T := uc22p22p_le_T_of_inCalV D h.hyp125.inCalV
    have hWkW2 : E3.wClos V D.k D.T ≤ E3.wClos V 2 D.T :=
      wClos_le_wClos_of_le hV (by omega) hkr D.T
    have hW2comm : ⁅E3.wClos V 2 D.T, V⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.2 hW2
    have hWkC : E3.wClos V D.k D.T ≤ centralizer (V : Set G) := by
      have h : ⁅E3.wClos V D.k D.T, V⁆ = ⊥ := by
        rw [eq_bot_iff]
        have h' := Subgroup.commutator_mono hWkW2 (le_refl V)
        rwa [hW2comm] at h'
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
    have hVc : V ≤ E3.cClos V D.k D.T :=
      le_inf hVT (Subgroup.le_centralizer_iff.1 hWkC)
    have hCk : centralizer (E3.cClos V D.k D.T : Set G) ≤ D.M :=
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hVc)).trans
        (centralizer_le_of_inCalV D h.hyp125.inCalV)
    have hmk : MBarGT D.M ⊥ V (D.k + 0) := TwelveShort.mBarGT_mono hm3 (by omega)
    rcases twelve_ten_two D hx h61 h126 h111 h.hyp125 rfl (i := 0) hmk with hN | hC
    · exact hN hNW0
    · exact hC (by simpa using hCk)
  · by_contra hcon
    push Not at hcon
    have hm3 : MBarGT D.M V₀ V 3 :=
      h1669 (by
        have h2 : Nat.card V₀ ≤ 2 :=
          (mSub_le_one_iff h.hyp125.pairFacts.elemAbelian₀).1 h.small
        omega)
    have hmbar : 3 < mBar D.M V₀ V hV := (h.hyp125.mBarGT_iff_lt_mBar 3).1 hm3
    have hkr : 2 < rk ↥V :=
      lt_of_lt_of_le (by norm_num : (2 : ℕ) < 3)
        (hmbar.le.trans
          (CFSG.LocalAnalysis.WeakClosure81.mBar_le_rk (M := D.M) hV h.hyp125.pairFacts.le))
    have hW2 : E3.wClos V 2 D.T ≤ F11.CTilde D.M V₀ V := by
      refine E3.wClos_le_of_forall fun A hA => ?_
      have hA' : A ∈ F12.Gam 2 D.T V := by rwa [S17.gam_eq_gammaSet]
      exact (CFSG.LocalAnalysis.WeakClosure81.barSub_eq_bot_iff hV
        h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
        (hA.1.trans D.sylowM.le)).1 (hcon A hA')
    have hW0 : E3.wClos V 0 D.T ≤ F11.CTilde D.M V₀ V :=
      (wClos_le_wClos_of_le hV (Nat.zero_le 2) hkr D.T).trans hW2
    have hNW0 : normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M :=
      normalizer_wClos_le_of_le_cTilde D (r129_1_of_r127 D h127) h61 hx.sig_nonempty hrkO
        h.hyp125 h.small hW0
    have hm2 : MBarGT D.M V₀ V 2 := TwelveShort.mBarGT_mono hm3 (by omega)
    exact twelve_ten_one_zero D hx h61 h66 h127 h1114 h183 h.hyp125 hV₀ hm2 hNW0

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
