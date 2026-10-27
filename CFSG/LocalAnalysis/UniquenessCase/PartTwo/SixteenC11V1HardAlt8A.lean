module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11DimD
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11BigLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11BigCombA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1HardNat
public import CFSG.Quasithin.H13.VolIAltCoverEight
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1HardAlt8B
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1HardAltDim
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1HardAltFix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1TwoCommonFam

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G]

theorem s16c11_v1_alt_eight_three (D : Data G) (hin : In10 D)
    (h4 : 3 < CFSG.Open.evenRank G) {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D ⊥ V L hV) (hsig : D.sig = {3}) :
    ∃ P : Subgroup (MulAut (Vtil ⊥ V hV)),
      P ≤ Mbar D.M ⊥ V hV ∧ IsPGroup 3 ↥P ∧ ¬ IsCyclic ↥P := by
  have h3 : 3 ≤ CFSG.Open.pRank 3 (Mbar D.M ⊥ V hV) :=
    s16c1610_three_le_pRank_mBar_of_four D hin.hx hin.h61 hin.h127 hc.setting.hyp16 hV h4
      (by rw [hsig]; exact Set.mem_singleton 3)
  obtain ⟨E, hEM, hEab, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) (Mbar D.M ⊥ V hV)
  refine ⟨E, hEM, IsPGroup.of_card hEcard, ?_⟩
  intro hcyc
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥E)
  have h1 : orderOf g ∣ 3 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hEab.2 g.val g.2))
  rw [hg, hEcard] at h1
  have h2 : 3 ^ CFSG.Open.pRank 3 (Mbar D.M ⊥ V hV) ≤ 3 := Nat.le_of_dvd (by norm_num) h1
  have h5 : 3 ^ 3 ≤ 3 ^ CFSG.Open.pRank 3 (Mbar D.M ⊥ V hV) :=
    Nat.pow_le_pow_right (by norm_num) h3
  have h6 : 3 ^ 3 ≤ 3 := le_trans h5 h2
  norm_num at h6

theorem s16c11_v1_cover_section_alt_eight (D : Data G) (hin : In10 D) (h1217 : R1217 D)
    {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D ⊥ V L hV)
    (hs : s15 D.M ⊥ V hV L = 1)
    (hK : IsSym ↥(kBar D.M ⊥ V hV L) 3) (hA : UC22.IsAlt ↥(lBar ⊥ V hV L) 8)
    (hsum : SumOfNat (fun H U Z => AlternatingNatural H U Z 8) (lStar D.M ⊥ V hV L)
      (⊤ : Subgroup (vStar D.M ⊥ V hV L)) ⊥ 2)
    (hV1 : v1Sub D.M ⊥ V hV L ≠ ⊥) {J₀ : Subgroup (Vtil ⊥ V hV)}
    (hM : S16C11Model (Mbar D.M ⊥ V hV) (kBar D.M ⊥ V hV L) J₀) :
    ∃ φ : ↥(lBar ⊥ V hV L) →* MulAut ↥J₀,
      (∀ (x : ↥(lBar ⊥ V hV L)) (j : ↥J₀),
        (((φ x : MulAut ↥J₀) j : ↥J₀) : Vtil ⊥ V hV) =
          (x : MulAut (Vtil ⊥ V hV)) (j : Vtil ⊥ V hV)) ∧
      commV φ.range = ⊤ ∧ fixV φ.range ≠ ⊥ ∧ Nat.card ↥J₀ = 2 ^ 7 ∧
      (altCoreModel 8).Realizes φ.range ⊤ ⊥ := by
  have htop : wStar D.M ⊥ V hV L = ⊤ :=
    s15_Three_wStar_eq_top D h1217 hc.setting.hyp151 hV hc.ne_bot hs
  have hsum' : SumOfNat (fun H U Z => AlternatingNatural H U Z 8) (lStar D.M ⊥ V hV L)
      (wStar D.M ⊥ V hV L) ⊥ 2 := by
    rw [htop]
    exact hsum
  have hF : s16e_two_Fam D ⊥ V L hV (fun H U Z => AlternatingNatural H U Z 8) :=
    s16e_two_fam_alt D hV (by omega) hA hsum'
  obtain ⟨φ, hev, hcomm, hfix, D', hD', hReal⟩ :=
    s16c11_v1_hard_nat_section D hin h1217 hc hs hF
      (Q := fun D' => D' = FFModel.altDn 8)
      (hP := fun H U Z h => ⟨FFModel.altDn 8, rfl, h⟩) hV1 hM
  have hAN : AlternatingNatural φ.range ⊤ (fixV φ.range) 8 := by
    rw [hD'] at hReal
    exact hReal
  have hsq : ∀ v : ↥J₀, v ^ 2 = 1 := fun v =>
    Subtype.ext (s15_Infra_vtil_sq_eq_one ⊥ V hV (v : Vtil ⊥ V hV))
  rcases VolI.altNaturalCoverEight_holds ↥J₀ hsq φ.range (fixV φ.range) le_rfl hcomm hAN with
    hbot | ⟨_, hJcard, hR⟩
  · exact absurd hbot hfix
  · exact ⟨φ, hev, hcomm, hfix, hJcard, hR⟩

theorem s16c11_v1_alt_eight_exists_B (D : Data G) (hin : In10 D) (h1217 : R1217 D)
    (h1610 : R16_10_2 D) {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D ⊥ V L hV)
    (hs : s15 D.M ⊥ V hV L = 1) (hout : Out10 D ⊥ V hV)
    (hsig : D.sig = {3}) (hK : IsSym ↥(kBar D.M ⊥ V hV L) 3)
    {L₀ : Subgroup (MulAut (Vtil ⊥ V hV))}
    (hdir : IsInternalDirect (kBar D.M ⊥ V hV L) L₀ (Mbar D.M ⊥ V hV))
    (hL₀ : IsSym ↥L₀ 8) (hA : UC22.IsAlt ↥(lBar ⊥ V hV L) 8)
    (hsum : SumOfNat (fun H U Z => AlternatingNatural H U Z 8) (lStar D.M ⊥ V hV L)
      (⊤ : Subgroup (vStar D.M ⊥ V hV L)) ⊥ 2)
    (hV1 : v1Sub D.M ⊥ V hV L ≠ ⊥) {J₀ : Subgroup (Vtil ⊥ V hV)}
    (hM : S16C11Model (Mbar D.M ⊥ V hV) (kBar D.M ⊥ V hV L) J₀) :
    ∃ B : Subgroup G, B ≤ D.M ∧ IsPGroup 3 ↥B ∧ ¬ IsCyclic ↥B ∧
      rk ↥(fixV (barSub (⊥ : Subgroup G) V hV B)) = 6 := by
  obtain ⟨φ, hev, hcomm, hfix, hJcard, hR⟩ :=
    s16c11_v1_cover_section_alt_eight D hin h1217 hc hs hK hA hsum hV1 hM
  have hLX : lBar ⊥ V hV L ≤ Mbar D.M ⊥ V hV := s16e_two_lBar_le D hc.setting.hyp151 hV
  have hLK : ∀ l ∈ (lBar ⊥ V hV L : Subgroup (MulAut (Vtil ⊥ V hV))),
      ∀ k ∈ (kBar D.M ⊥ V hV L : Subgroup (MulAut (Vtil ⊥ V hV))), l * k = k * l := by
    intro l hl k hk
    rw [kBar] at hk
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hk).2) l hl
  obtain ⟨hJ, Θ, hΘ⟩ := s16c11_v1_model_pair hM hLX hLK
  have hsq : ∀ v : ↥J₀, v ^ 2 = 1 := fun v =>
    Subtype.ext (s15_Infra_vtil_sq_eq_one ⊥ V hV (v : Vtil ⊥ V hV))
  obtain ⟨E, hEH, hE3, hEnc, hEcard⟩ := s16c11_v1_blocks_eight_of_realizes hsq hR
  have hφeq : φ = CFSG.Quasithin.H13.VolI.resHom (lBar ⊥ V hV L) J₀ hJ := by
    refine MonoidHom.ext fun x => ?_
    refine MulEquiv.ext fun j => ?_
    exact Subtype.ext (by rw [hev x j, CFSG.Quasithin.H13.VolI.coe_resHom_apply])
  have hEL : E ≤ (CFSG.Quasithin.H13.VolI.resHom (lBar ⊥ V hV L) J₀ hJ).range := by
    rw [← hφeq]; exact hEH
  obtain ⟨Bb, hBbL, hBb3, hBbnc, hBbcard⟩ :=
    s16c11_v1_exists_B_alt 3 hM hLX hLK hJ hEL hE3 hEnc hEcard
  have hperfect : ⁅(lBar ⊥ V hV L), (lBar ⊥ V hV L)⁆ = lBar ⊥ V hV L := by
    obtain ⟨e⟩ := hA
    haveI : Group.IsPerfect (alternatingGroup (Fin 8)) :=
      Group.isPerfect_def.mpr (commutator_alternatingGroup_eq_top (by simp))
    haveI : Group.IsPerfect ↥(lBar ⊥ V hV L) :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    exact Subgroup.commutator_eq_self
  have hcardbot : Nat.card (⊥ : Subgroup G) ≤ 4 := by
    rw [Subgroup.card_bot]; norm_num
  obtain ⟨B, hBM, hBp, hBcent, hBbar, hBnc⟩ :=
    s16c11_exists_pGroup_lift D hV hc.setting.hyp16.hyp125 hcardbot hLX hperfect
      Nat.prime_three hBbL hBb3
  refine ⟨B, hBM, hBp, hBnc hBbnc, ?_⟩
  have hrk : rk ↥(fixV Bb) = 6 := by
    have hcard : Nat.card ↥(fixV Bb) = 2 ^ 6 := by simpa using hBbcard
    unfold rk
    rw [hcard]
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact padicValNat.prime_pow 6
  rw [hBbar]
  exact hrk

theorem s16c11_v1_alt_eight_rank (D : Data G) (hin : In10 D) (h1217 : R1217 D)
    (h1610 : R16_10_2 D) {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D ⊥ V L hV)
    (hs : s15 D.M ⊥ V hV L = 1) (hout : Out10 D ⊥ V hV)
    (hsig : D.sig = {3}) (hK : IsSym ↥(kBar D.M ⊥ V hV L) 3)
    {L₀ : Subgroup (MulAut (Vtil ⊥ V hV))}
    (hdir : IsInternalDirect (kBar D.M ⊥ V hV L) L₀ (Mbar D.M ⊥ V hV))
    (hL₀ : IsSym ↥L₀ 8) (hA : UC22.IsAlt ↥(lBar ⊥ V hV L) 8)
    (hsum : SumOfNat (fun H U Z => AlternatingNatural H U Z 8) (lStar D.M ⊥ V hV L)
      (⊤ : Subgroup (vStar D.M ⊥ V hV L)) ⊥ 2)
    (hV1 : v1Sub D.M ⊥ V hV L ≠ ⊥) {J₀ : Subgroup (Vtil ⊥ V hV)}
    (hM : S16C11Model (Mbar D.M ⊥ V hV) (kBar D.M ⊥ V hV L) J₀) :
    ((CFSG.Open.pRank 2 (Mbar D.M ⊥ V hV) + mSub (⊥ : Subgroup G) : ℕ) : ℕ∞) < rMV D.M V := by
  have h125 : Hyp125 D ⊥ V := hc.setting.hyp16.hyp125
  have hp3 : 3 ∈ D.sig := by rw [hsig]; exact Set.mem_singleton 3
  obtain ⟨B, hBM, hBp, hBnc, hB6⟩ :=
    s16c11_v1_alt_eight_exists_B D hin h1217 h1610 hc hs hout hsig hK hdir hL₀ hA hsum hV1
      hM
  have hle := s16c11_mSub_add_rk_fixV_le_rMV D hin.h61 hV h125 hp3 hBM hBp hBnc
    (bot_le : (⊥ : Subgroup G) ≤ centralizer (B : Set G))
  rw [hB6] at hle
  have hp5 : CFSG.Open.pRank 2 (Mbar D.M ⊥ V hV) ≤ 5 := by
    have h := s16c11_big_pRank_le hdir hK hL₀
    norm_num at h ⊢
    exact h
  have hzero : mSub (⊥ : Subgroup G) = 0 := rk_bot
  have hp : CFSG.Open.pRank 2 (Mbar D.M ⊥ V hV) + mSub (⊥ : Subgroup G) <
      mSub (⊥ : Subgroup G) + 6 := by omega
  exact lt_of_lt_of_le (by exact_mod_cast hp) hle

theorem s16c11_v1_alt_eight_aSet_fixV (D : Data G) (hin : In10 D) (h1217 : R1217 D)
    (h1610 : R16_10_2 D) {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D ⊥ V L hV)
    (hs : s15 D.M ⊥ V hV L = 1) (hout : Out10 D ⊥ V hV)
    (hsig : D.sig = {3}) (hK : IsSym ↥(kBar D.M ⊥ V hV L) 3)
    {L₀ : Subgroup (MulAut (Vtil ⊥ V hV))}
    (hdir : IsInternalDirect (kBar D.M ⊥ V hV L) L₀ (Mbar D.M ⊥ V hV))
    (hL₀ : IsSym ↥L₀ 8) (hA : UC22.IsAlt ↥(lBar ⊥ V hV L) 8)
    (hsum : SumOfNat (fun H U Z => AlternatingNatural H U Z 8) (lStar D.M ⊥ V hV L)
      (⊤ : Subgroup (vStar D.M ⊥ V hV L)) ⊥ 2)
    (hV1 : v1Sub D.M ⊥ V hV L ≠ ⊥) {J₀ : Subgroup (Vtil ⊥ V hV)}
    (hM : S16C11Model (Mbar D.M ⊥ V hV) (kBar D.M ⊥ V hV L) J₀) :
    ∀ E ∈ calABar 2 D.M ⊥ V hV, E ≤ barSub (⊥ : Subgroup G) V hV D.T → 6 ≤ rkIdx (fixV E) := by
  intro E hE _
  obtain ⟨φ, hev, hcomm, hfix, hJcard, hR⟩ :=
    s16c11_v1_cover_section_alt_eight D hin h1217 hc hs hK hA hsum hV1 hM
  have hLX : lBar ⊥ V hV L ≤ Mbar D.M ⊥ V hV := s16e_two_lBar_le D hc.setting.hyp151 hV
  have hLK : ∀ l ∈ (lBar ⊥ V hV L : Subgroup (MulAut (Vtil ⊥ V hV))),
      ∀ k ∈ (kBar D.M ⊥ V hV L : Subgroup (MulAut (Vtil ⊥ V hV))), l * k = k * l := by
    intro l hl k hk
    rw [kBar] at hk
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hk).2) l hl
  have hLL₀ : lBar ⊥ V hV L ≤ L₀ := s16c11_v1_le_right_of_centralizes hK hdir hLX hLK
  have hW : ∀ w : Vtil ⊥ V hV, w ^ 2 = 1 := fun w => s15_Infra_vtil_sq_eq_one ⊥ V hV w
  have hcore : ∀ F ∈ E3.aSet 2 (G6.coreAct 8).range, IsPGroup 2 ↥F → F ≠ ⊥ →
      3 ≤ rkIdx (fixV F) := fun F hF h2 hne => s16c11_v1_coreMod_eight_dimD1 hF h2 hne
  have h6 := s16c11_v1_rkIdx_aSet_alt (n := 8) (by norm_num) hcore hW hM hK hdir hL₀ hA
    hLL₀ φ hev hcomm hR hE
  omega

theorem s16c11_v1_alt_eight_dimD1 (D : Data G) (hin : In10 D) (h1217 : R1217 D)
    (h1610 : R16_10_2 D) {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D ⊥ V L hV)
    (hs : s15 D.M ⊥ V hV L = 1) (hout : Out10 D ⊥ V hV)
    (hsig : D.sig = {3}) (hK : IsSym ↥(kBar D.M ⊥ V hV L) 3)
    {L₀ : Subgroup (MulAut (Vtil ⊥ V hV))}
    (hdir : IsInternalDirect (kBar D.M ⊥ V hV L) L₀ (Mbar D.M ⊥ V hV))
    (hL₀ : IsSym ↥L₀ 8) (hA : UC22.IsAlt ↥(lBar ⊥ V hV L) 8)
    (hsum : SumOfNat (fun H U Z => AlternatingNatural H U Z 8) (lStar D.M ⊥ V hV L)
      (⊤ : Subgroup (vStar D.M ⊥ V hV L)) ⊥ 2)
    (hV1 : v1Sub D.M ⊥ V hV L ≠ ⊥) {J₀ : Subgroup (Vtil ⊥ V hV)}
    (hM : S16C11Model (Mbar D.M ⊥ V hV) (kBar D.M ⊥ V hV L) J₀) :
    S16C11DimD1 D ⊥ V hV := by
  intro E hE hET _
  have h6 :=
    s16c11_v1_alt_eight_aSet_fixV D hin h1217 h1610 hc hs hout hsig hK hdir hL₀ hA hsum
      hV1 hM E hE hET
  have hp5 : CFSG.Open.pRank 2 (Mbar D.M ⊥ V hV) ≤ 5 := by
    have h := s16c11_big_pRank_le hdir hK hL₀
    norm_num at h ⊢
    exact h
  intro hle
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
