module

public import CFSG.LocalAnalysis.WeakClosure81.W16LBDefs
public import CFSG.LocalAnalysis.WeakClosure81.W16LBLin
public import CFSG.LocalAnalysis.WeakClosure81.W16LBAlt6
public import CFSG.LocalAnalysis.WeakClosure81.W16LBBorel
public import CFSG.LocalAnalysis.WeakClosure81.W16LBSym
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveGapFour
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveGapSixHolds
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveTwoSplitSmall
public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2KFactsF
public import CFSG.LocalAnalysis.WeakClosure81.TimTI.BenderTransv
public import CFSG.RankThree.GF2n.QTwo

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup CFSG.Open CFSG.LocalAnalysis.WeakClosure81.SevenK

theorem w16l_isSpGp_two_of_isL2Gp {Y : Type} [Group Y] {n : ℕ} (h : IsL2Gp Y n) :
    IsSpGp Y 2 n := by
  obtain ⟨F, hF, hFin, hcard, ⟨e⟩⟩ := h
  let r := CFSG.RankThree.GF2n.Stroth80.reindexGL (K := F)
    CFSG.RankThree.GF2n.Stroth80.sumFinTwo
  let e₂ : ↥(StatedSp 1 F) ≃* ↥(StatedSL 2 F) :=
    (Subgroup.equivMapOfInjective (StatedSp 1 F) r.toMonoidHom r.injective).trans
      (MulEquiv.subgroupCongr CFSG.RankThree.GF2n.Stroth80.map_reindexGL_statedSp_one)
  let e₃ : Matrix.SpecialLinearGroup (Fin 2) F ≃* ↥(StatedSL 2 F) :=
    (MonoidHom.ofInjective Matrix.SpecialLinearGroup.toGL_injective).trans
      (MulEquiv.subgroupCongr (CFSG.Open.StatedAPI.statedSL_eq_range_toGL 2 F).symm)
  exact ⟨1, by norm_num, F, hF, hFin, hcard, ⟨e.trans (e₃.trans e₂.symm)⟩⟩

theorem w16l_isSymplecticTransvection_of_l2 {X : Type} [Group X] [Finite X] {n : ℕ} {s : X}
    (hZo : Odd (Nat.card (Subgroup.center X))) (hL2 : IsL2Gp (X ⧸ Subgroup.center X) n)
    (hs2 : s * s = 1) (hs1 : s ≠ 1) : IsSymplecticTransvection X 2 n s := by
  classical
  obtain ⟨F, hF, hFin, hFcard, ⟨eL⟩⟩ := hL2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn1 : 1 ≤ n := by
    by_contra h
    have hn0 : n = 0 := by omega
    rw [hn0, pow_zero] at hFcard
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    omega
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (f := n) (by
    rw [← Nat.card_eq_fintype_card]
    exact hFcard)
  let Z : Subgroup X := Subgroup.center X
  let q : X →* X ⧸ Z := QuotientGroup.mk' Z
  let sbar : X ⧸ Z := q s
  have hsbar2 : sbar * sbar = 1 := by
    dsimp [sbar]
    rw [← map_mul, hs2, map_one]
  have hsbar1 : sbar ≠ 1 := by
    intro h
    have hq : (QuotientGroup.mk s : X ⧸ Z) = 1 := by simpa [sbar, q] using h
    have hsZ : s ∈ Z := (QuotientGroup.eq_one_iff (N := Z) s).mp hq
    have hord2 : orderOf s = 2 := by
      have hdvd : orderOf s ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rwa [pow_two])
      have hne : orderOf s ≠ 1 := fun h1 => hs1 (orderOf_eq_one_iff.mp h1)
      rcases Nat.prime_two.eq_one_or_self_of_dvd (orderOf s) hdvd with h1 | h2
      · exact absurd h1 hne
      · exact h2
    have h2dvd : 2 ∣ Nat.card Z := by
      rw [← hord2]
      exact Z.orderOf_dvd_natCard hsZ
    exact (show Odd (Nat.card Z) from hZo).not_two_dvd_nat h2dvd
  let r := CFSG.RankThree.GF2n.Stroth80.reindexGL (K := F)
    CFSG.RankThree.GF2n.Stroth80.sumFinTwo
  let e₂ : ↥(StatedSp 1 F) ≃* ↥(StatedSL 2 F) :=
    (Subgroup.equivMapOfInjective (StatedSp 1 F) r.toMonoidHom r.injective).trans
      (MulEquiv.subgroupCongr CFSG.RankThree.GF2n.Stroth80.map_reindexGL_statedSp_one)
  let e₃ : Matrix.SpecialLinearGroup (Fin 2) F ≃* ↥(StatedSL 2 F) :=
    (MonoidHom.ofInjective Matrix.SpecialLinearGroup.toGL_injective).trans
      (MulEquiv.subgroupCongr (CFSG.Open.StatedAPI.statedSL_eq_range_toGL 2 F).symm)
  let esp : (X ⧸ Z) ≃* ↥(StatedSp 1 F) := eL.trans (e₃.trans e₂.symm)
  have hsp2 : esp sbar * esp sbar = 1 := by
    rw [← map_mul, hsbar2, map_one]
  have hsp1 : esp sbar ≠ 1 := by
    intro h
    exact hsbar1 (esp.injective (by simpa using h))
  have htr := TimTI.isSymplecticTransvectionIn_one_of_mul_self hsp2 hsp1
  refine ⟨1, by norm_num, F, hF, hFin, hFcard, esp, ?_⟩
  change IsSymplecticTransvectionIn 1 (esp sbar)
  exact htr

private theorem w16l_centralInSylow_of_card_two {X : Type} [Group X] [Finite X]
    {B P : Subgroup X} (hc : BarConf X B P) (hB2 : Nat.card B = 2) :
    CentralInSylow X B := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnorm : ∀ p ∈ P, p ∈ Subgroup.normalizer (B : Set X) := by
    intro p hp
    exact hc.normalizer_le p (Subgroup.le_normalizer hp)
  have hcomm : ∀ s ∈ B, ∀ p ∈ P, s * p = p * s := by
    intro s hs p hp
    by_cases hs1 : s = 1
    · subst s
      simp
    · have hmem : p * s * p⁻¹ ∈ B :=
        (Subgroup.mem_normalizer_iff.mp (hnorm p hp) s).mp hs
      have hne : p * s * p⁻¹ ≠ 1 := by
        intro h
        have hconj : p⁻¹ * (p * s * p⁻¹) * p = s := by group
        have hone : p⁻¹ * (p * s * p⁻¹) * p = 1 := by rw [h]; group
        exact hs1 (hconj.symm.trans hone)
      have heq : p * s * p⁻¹ = s :=
        CFSG.RankThree.GF2n.eq_of_mem_of_card_eq_two hB2 hmem hs hne hs1
      have hps : p * s = s * p := by
        calc p * s = (p * s * p⁻¹) * p := by group
          _ = s * p := by rw [heq]
      exact hps.symm
  refine ⟨hc.isPGroup.toSylow hc.index_odd, ?_, ?_⟩
  · simpa using hc.le
  · intro s hs p hp
    exact hcomm s hs p (by simpa using hp)

theorem w16l_hat_shape {X : Type} [Group X] [Finite X] {B P : Subgroup X} {n : ℕ}
    (hc : BarConf X B P) (hB : B ≠ ⊥) (hcard : Nat.card B = 2 ^ n)
    (hAlt : SevenElevenAlt X B) (h85 : NoHyp85 X B) : HatShape166 X B n := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZo : Odd (Nat.card (Subgroup.center X)) :=
    odd_card_center_of_pCore_eq_bot hc.pCore_eq_bot
  have hn1 : 1 ≤ n := by
    by_contra h
    have hn0 : n = 0 := by omega
    rw [hn0, pow_zero] at hcard
    exact hB (Subgroup.eq_bot_of_card_eq (H := B) hcard)
  rcases hAlt with ⟨hroot, -⟩ | hlin | ⟨-, hA6⟩ | ⟨hB2, m, n', hcases⟩ | ⟨hB2, k, hSym⟩ |
    ⟨hB2, h6⟩
  · rcases hroot with ⟨n', hroot'⟩
    rcases hroot' with ⟨m, hSp, hrootSp⟩ | ⟨m, hU, hrootU⟩ | ⟨hSz, hrootSz⟩
    · obtain ⟨hcardB, k, hk, F, hF, hFin, hFcard, e, he⟩ := hrootSp
      have hn'n : n' = n := Nat.pow_right_injective (le_refl 2) (hcardB.symm.trans hcard)
      subst n'
      by_cases hk0 : k = 0
      · have hm0 : m = 0 := by omega
        have h0 : IsSpGp (X ⧸ Subgroup.center X) 0 n := by simpa [hm0] using hSp
        exact absurd (eq_bot_of_subsingleton_quot hc.toBarSituation
          (subsingleton_of_isSpGp_zero h0)) hB
      · by_cases hk1 : k = 1
        · have hm2 : m = 2 := by omega
          have hSp2 : IsSpGp (X ⧸ Subgroup.center X) 2 n := by simpa [hm2] using hSp
          by_cases hn1' : n = 1
          · have hB2n : Nat.card B = 2 := by rw [hcard, hn1', pow_one]
            exact ⟨hcard, Or.inr ⟨hn1', w16l_sp_two_one hB2n hc.pCore_eq_bot (by
              simpa [hn1'] using hSp2)⟩⟩
          · have hngt : 1 < n := by omega
            exact ⟨hcard, Or.inl ⟨hngt, Or.inl hSp2⟩⟩
        · have hk2 : 2 ≤ k := by omega
          exact (h85.1 ⟨m, n, by omega, hSp, hcard⟩).elim
    · obtain ⟨hcardB, F, hF, hFin, hFcard, e, he⟩ := hrootU
      have hn'n : n' = n := Nat.pow_right_injective (le_refl 2) (hcardB.symm.trans hcard)
      subst n'
      obtain ⟨hm3, hn1'⟩ := three_le_of_isPSUGp hU
      have hne := (CFSG.Blueprint.LieModel.admissible hU).2.2.2
      rcases lt_or_eq_of_le hm3 with hlt | heq
      · exact (h85.2.1 ⟨m, n, hlt, hU, hcard⟩).elim
      · have hm_eq : m = 3 := heq.symm
        have hngt : 1 < n := by
          rcases lt_or_eq_of_le hn1' with hlt | hEq
          · exact hlt
          · exfalso
            apply hne
            rw [hm_eq, ← hEq, pow_one]
        have hU3 : IsPSUGp (X ⧸ Subgroup.center X) 3 n := by simpa [hm_eq] using hU
        exact ⟨hcard, Or.inl ⟨hngt, Or.inr (Or.inr hU3)⟩⟩
    · have hcardB : Nat.card B = 2 ^ n' :=
        kFacts1234_holds.card_suzukiRoot (X := X) n' B hZo hSz hrootSz
      have hn'n : n' = n := Nat.pow_right_injective (le_refl 2) (hcardB.symm.trans hcard)
      subst n'
      have hngt : 1 < n := by
        obtain ⟨-, a, ha, K, hK, hKfin, hn_eq, -, -⟩ := hSz
        omega
      exact ⟨hcard, Or.inl ⟨hngt, Or.inr (Or.inl hSz)⟩⟩
  · obtain ⟨m, n', hm3, hmodel, hlin, T, hle, hwc⟩ := hlin
    exact (w16l_false_of_linear hm3 hlin hc.pCore_eq_bot hc.elemAbelian
      hc.normalClosure_eq_top hc.free).elim
  · obtain ⟨hsh, hcard4, T, hle, hwc⟩ := hA6
    exact (w16l_false_of_alt6 hsh hcard4 hc.elemAbelian hc.pCore_eq_bot hc.free).elim
  · have hn_eq : n = 1 := Nat.pow_right_injective (le_refl 2) (hcard.symm.trans hB2)
    subst n
    have hPS : CentralInSylow X B := w16l_centralInSylow_of_card_two hc hB2
    rcases hcases with ⟨hSp, htrans⟩ | ⟨hPSU, htransU⟩ | hOrth | hWr
    · have hn'1 : 1 ≤ n' := one_le_of_isSpGp hSp
      rcases Nat.lt_or_ge 1 n' with hngt | hn'le
      · exact (w16l_false_of_borel_sp hngt hB2 hc.pCore_eq_bot hc.le hc.isPGroup
          hc.index_odd hc.normalizer_le htrans).elim
      · have hn'eq : n' = 1 := by omega
        have hSp' : IsSpGp (X ⧸ Subgroup.center X) m n' := hSp
        obtain ⟨k, hk, F, hF, hFin, hFcard, e⟩ := hSp
        by_cases hk0 : k = 0
        · have hm0 : m = 0 := by omega
          have h0 : IsSpGp (X ⧸ Subgroup.center X) 0 1 := by
            simpa [hm0, hn'eq] using hSp'
          exact absurd (eq_bot_of_subsingleton_quot hc.toBarSituation
            (subsingleton_of_isSpGp_zero h0)) hB
        · by_cases hk1 : k = 1
          · have hm2 : m = 2 := by omega
            have hSp2 : IsSpGp (X ⧸ Subgroup.center X) 2 1 := by
              simpa [hm2, hn'eq] using hSp'
            exact ⟨hcard, Or.inr ⟨rfl, w16l_sp_two_one hB2 hc.pCore_eq_bot hSp2⟩⟩
          · have hk2 : 2 ≤ k := by omega
            exact (h85.1 ⟨m, 1, by omega, by simpa [hn'eq] using hSp', hcard⟩).elim
    · obtain ⟨hm3, hn'1⟩ := three_le_of_isPSUGp hPSU
      have hne := (CFSG.Blueprint.LieModel.admissible hPSU).2.2.2
      rcases Nat.lt_or_ge 1 n' with hngt | hn'le
      · exact (w16l_false_of_borel_psu hngt hm3 hB2 hc.pCore_eq_bot hc.le hc.isPGroup
          hc.index_odd hc.normalizer_le htransU).elim
      · have hn'eq : n' = 1 := by omega
        have hm_gt3 : 3 < m := by
          by_contra hnot
          have hmeq : m = 3 := by omega
          exact hne (by rw [hmeq, hn'eq, pow_one])
        exact (h85.2.1 ⟨m, 1, hm_gt3, by simpa [hn'eq] using hPSU, hcard⟩).elim
    · exact (w3Lem85TwoGap4_holds X B hc.toBarSituation hB2 (Or.inl ⟨m, n', hOrth⟩)
        hPS).elim
    · rcases Nat.lt_or_ge m 2 with hm_lt | hm_ge
      · have hm01 : m = 0 ∨ m = 1 := by omega
        rcases hm01 with hm0 | hm1
        · have hWr0 : IsL2WrSymGp (X ⧸ Subgroup.center X) n' 0 := by
            simpa [hm0] using hWr
          exact absurd (eq_bot_of_subsingleton_quot hc.toBarSituation
            (subsingleton_of_isL2WrSymGp_zero hWr0)) hB
        · have hWr1 : IsL2WrSymGp (X ⧸ Subgroup.center X) n' 1 := by
            simpa [hm1] using hWr
          have hL2 : IsL2Gp (X ⧸ Subgroup.center X) n' :=
            isL2Gp_of_isL2WrSymGp_one hWr1
          have hn'1 : 1 ≤ n' := one_le_of_isSpGp (w16l_isSpGp_two_of_isL2Gp hL2)
          rcases Nat.lt_or_ge 1 n' with hngt | hn'le
          · have hex : ∃ s ∈ B, s ≠ 1 := by
              letI : Fintype B := Fintype.ofFinite B
              have hlt : 1 < Fintype.card B := by
                rw [← Nat.card_eq_fintype_card, hB2]
                norm_num
              obtain ⟨s, hs1⟩ := Fintype.exists_ne_of_one_lt_card hlt (1 : B)
              exact ⟨(s : X), s.2, fun h => hs1 (Subtype.ext h)⟩
            obtain ⟨s, hs, hs1⟩ := hex
            have hs2 : s * s = 1 := by
              simpa [pow_two] using hc.elemAbelian.2 s hs
            have htr : IsSymplecticTransvection X 2 n' s :=
              w16l_isSymplecticTransvection_of_l2 hZo hL2 hs2 hs1
            refine (w16l_false_of_borel_sp (m := 2) (n := n') hngt hB2 hc.pCore_eq_bot
              hc.le hc.isPGroup hc.index_odd hc.normalizer_le ?_).elim
            intro t ht ht1
            rw [CFSG.RankThree.GF2n.eq_of_mem_of_card_eq_two hB2 ht hs ht1 hs1]
            exact htr
          · have hn'eq : n' = 1 := by omega
            have hSp2 : IsSpGp (X ⧸ Subgroup.center X) 2 1 := by
              simpa [hn'eq] using w16l_isSpGp_two_of_isL2Gp hL2
            exact ⟨hcard, Or.inr ⟨rfl, w16l_sp_two_one hB2 hc.pCore_eq_bot hSp2⟩⟩
      · exact (w3Lem85TwoGap4_holds X B hc.toBarSituation hB2 (Or.inr ⟨n', m, hm_ge, hWr⟩)
          hPS).elim
  · have hn_eq : n = 1 := Nat.pow_right_injective (le_refl 2) (hcard.symm.trans hB2)
    subst n
    rcases Nat.lt_or_ge k 4 with hk4 | hkge
    · obtain ⟨hk2, hsup⟩ := w16l_sym_small hB2 hSym hk4
      exact ⟨hcard, Or.inr ⟨rfl, hsup⟩⟩
    · exact (h85.2.2 ⟨k, by omega, hSym⟩).elim
  · have hn_eq : n = 1 := Nat.pow_right_injective (le_refl 2) (hcard.symm.trans hB2)
    subst n
    have hPS : CentralInSylow X B := w16l_centralInSylow_of_card_two hc hB2
    exact (w3Lem85TwoGap6_holds X B hc.toBarSituation hB2 h6 hPS).elim

end CFSG.LocalAnalysis.WeakClosure81

end
