module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11DimD
public import CFSG.RankThree.PartTwo.KFacts.K412AlternatingSix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1HardNat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1CoverAltTen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1HardAlt10B
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1HardAltDim
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1HardAltFix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11BigLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11BigCombA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1TwoCommonFam
public import CFSG.RankThree.PartTwo.KFacts.K412Alternating

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartTwo.KFacts.K412 (eSix card_eSix)
open CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G]

theorem s16c11_v1_cover_section_alt_ten (D : Data G) (hin : In10 D) (h1217 : R1217 D)
    {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D ⊥ V L hV)
    (hs : s15 D.M ⊥ V hV L = 1)
    (hK : IsSym ↥(kBar D.M ⊥ V hV L) 3) (hA : UC22.IsAlt ↥(lBar ⊥ V hV L) 10)
    (hsum : SumOfNat (fun H U Z => AlternatingNatural H U Z 10) (lStar D.M ⊥ V hV L)
      (⊤ : Subgroup (vStar D.M ⊥ V hV L)) ⊥ 2)
    (hV1 : v1Sub D.M ⊥ V hV L ≠ ⊥) {J₀ : Subgroup (Vtil ⊥ V hV)}
    (hM : S16C11Model (Mbar D.M ⊥ V hV) (kBar D.M ⊥ V hV L) J₀) :
    ∃ φ : ↥(lBar ⊥ V hV L) →* MulAut ↥J₀,
      (∀ (x : ↥(lBar ⊥ V hV L)) (j : ↥J₀),
        (((φ x : MulAut ↥J₀) j : ↥J₀) : Vtil ⊥ V hV) =
          (x : MulAut (Vtil ⊥ V hV)) (j : Vtil ⊥ V hV)) ∧
      commV φ.range = ⊤ ∧ fixV φ.range ≠ ⊥ ∧ Nat.card ↥J₀ = 2 ^ 9 ∧
      (altCoreModel 10).Realizes φ.range ⊤ ⊥ := by
  have htop : wStar D.M ⊥ V hV L = ⊤ :=
    s15_Three_wStar_eq_top D h1217 hc.setting.hyp151 hV hc.ne_bot hs
  have hsum' : SumOfNat (fun H U Z => AlternatingNatural H U Z 10) (lStar D.M ⊥ V hV L)
      (wStar D.M ⊥ V hV L) ⊥ 2 := by
    rw [htop]
    exact hsum
  have hF : s16e_two_Fam D ⊥ V L hV (fun H U Z => AlternatingNatural H U Z 10) :=
    s16e_two_fam_alt D hV (by omega) hA hsum'
  obtain ⟨φ, hev, hcomm, hfix, D', hD', hReal⟩ :=
    s16c11_v1_hard_nat_section D hin h1217 hc hs hF
      (Q := fun D' => D' = FFModel.altDn 10)
      (hP := fun H U Z h => ⟨FFModel.altDn 10, rfl, h⟩) hV1 hM
  have hAN : AlternatingNatural φ.range ⊤ (fixV φ.range) 10 := by
    rw [hD'] at hReal
    exact hReal
  have hsq : ∀ v : ↥J₀, v ^ 2 = 1 := fun v =>
    Subtype.ext (s15_Infra_vtil_sq_eq_one ⊥ V hV (v : Vtil ⊥ V hV))
  rcases s16c11_v1_cover_alt_ten ↥J₀ hsq φ.range (fixV φ.range) le_rfl hcomm hAN with
    hbot | ⟨_, hJcard, hR⟩
  · exact absurd hbot hfix
  · exact ⟨φ, hev, hcomm, hfix, hJcard, hR⟩

theorem s16c11_v1_rMV_alt_ten (D : Data G) (hin : In10 D) (h1217 : R1217 D) (h1610 : R16_10_2 D)
    {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D ⊥ V L hV)
    (hs : s15 D.M ⊥ V hV L = 1) (hout : Out10 D ⊥ V hV)
    (hsig : D.sig = {3}) (hK : IsSym ↥(kBar D.M ⊥ V hV L) 3)
    {L₀ : Subgroup (MulAut (Vtil ⊥ V hV))}
    (hdir : IsInternalDirect (kBar D.M ⊥ V hV L) L₀ (Mbar D.M ⊥ V hV))
    (hL₀ : IsSym ↥L₀ 10) (hA : UC22.IsAlt ↥(lBar ⊥ V hV L) 10)
    (hsum : SumOfNat (fun H U Z => AlternatingNatural H U Z 10) (lStar D.M ⊥ V hV L)
      (⊤ : Subgroup (vStar D.M ⊥ V hV L)) ⊥ 2)
    (hV1 : v1Sub D.M ⊥ V hV L ≠ ⊥) {J₀ : Subgroup (Vtil ⊥ V hV)}
    (hM : S16C11Model (Mbar D.M ⊥ V hV) (kBar D.M ⊥ V hV L) J₀) :
    ((CFSG.Open.pRank 2 (Mbar D.M ⊥ V hV) + mSub (⊥ : Subgroup G) : ℕ) : ℕ∞) < rMV D.M V := by
  have h125 : Hyp125 D ⊥ V := hc.setting.hyp16.hyp125
  have hp3 : 3 ∈ D.sig := by rw [hsig]; exact Set.mem_singleton 3
  obtain ⟨φ, hev, hcomm, hfix, hJcard, hR⟩ :=
    s16c11_v1_cover_section_alt_ten D hin h1217 hc hs hK hA hsum hV1 hM
  have hLX : lBar ⊥ V hV L ≤ Mbar D.M ⊥ V hV := s16e_two_lBar_le D hc.setting.hyp151 hV
  have hLK : ∀ l ∈ (lBar ⊥ V hV L : Subgroup (MulAut (Vtil ⊥ V hV))),
      ∀ k ∈ (kBar D.M ⊥ V hV L : Subgroup (MulAut (Vtil ⊥ V hV))), l * k = k * l := by
    intro l hl k hk
    rw [kBar] at hk
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hk).2) l hl
  obtain ⟨hJ, Θ, hΘ⟩ := s16c11_v1_model_pair hM hLX hLK
  have hsq : ∀ v : ↥J₀, v ^ 2 = 1 := fun v =>
    Subtype.ext (s15_Infra_vtil_sq_eq_one ⊥ V hV (v : Vtil ⊥ V hV))
  obtain ⟨E, hEH, hE3, hEnc, hEcard⟩ := s16c11_v1_blocks_ten_of_realizes hsq hR
  have hφeq : φ = CFSG.Quasithin.H13.VolI.resHom (lBar ⊥ V hV L) J₀ hJ := by
    refine MonoidHom.ext fun x => ?_
    refine MulEquiv.ext fun j => ?_
    exact Subtype.ext (by rw [hev x j, CFSG.Quasithin.H13.VolI.coe_resHom_apply])
  have hEL : E ≤ (CFSG.Quasithin.H13.VolI.resHom (lBar ⊥ V hV L) J₀ hJ).range := by
    rw [← hφeq]; exact hEH
  obtain ⟨B, hBL, hB3, hBnc, hBcard⟩ :=
    s16c11_v1_exists_B_alt 5 hM hLX hLK hJ hEL hE3 hEnc hEcard
  have hperfect : ⁅(lBar ⊥ V hV L), (lBar ⊥ V hV L)⁆ = lBar ⊥ V hV L := by
    obtain ⟨e⟩ := hA
    haveI : Group.IsPerfect (alternatingGroup (Fin 10)) :=
      Group.isPerfect_def.mpr (commutator_alternatingGroup_eq_top (by simp))
    haveI : Group.IsPerfect ↥(lBar ⊥ V hV L) :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    exact Subgroup.commutator_eq_self
  have hcardbot : Nat.card (⊥ : Subgroup G) ≤ 4 := by
    rw [Subgroup.card_bot]; norm_num
  obtain ⟨B', hB'M, hB'p, hB'V₀, hB'bar, hB'nc⟩ :=
    s16c11_exists_pGroup_lift D hV h125 hcardbot hLX hperfect Nat.prime_three hBL hB3
  have hle := s16c11_mSub_add_rk_fixV_le_rMV D hin.h61 hV h125 hp3 hB'M hB'p
    (hB'nc hBnc) hB'V₀
  have hrk10 : rk ↥(fixV B) = 10 := by
    have hcard : Nat.card ↥(fixV B) = 2 ^ 10 := by simpa using hBcard
    unfold rk
    rw [hcard]
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact padicValNat.prime_pow 10
  rw [hB'bar, hrk10] at hle
  have hp6 : CFSG.Open.pRank 2 (Mbar D.M ⊥ V hV) ≤ 6 := by
    have h := s16c11_big_pRank_le hdir hK hL₀
    norm_num at h ⊢
    exact h
  have hp : CFSG.Open.pRank 2 (Mbar D.M ⊥ V hV) + mSub (⊥ : Subgroup G) <
      mSub (⊥ : Subgroup G) + 10 := by omega
  exact lt_of_lt_of_le (by exact_mod_cast hp) hle

theorem s16c11_v1_dimD1_alt_ten (D : Data G) (hin : In10 D) (h1217 : R1217 D) (h1610 : R16_10_2 D)
    {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D ⊥ V L hV)
    (hs : s15 D.M ⊥ V hV L = 1) (hout : Out10 D ⊥ V hV)
    (hsig : D.sig = {3}) (hK : IsSym ↥(kBar D.M ⊥ V hV L) 3)
    {L₀ : Subgroup (MulAut (Vtil ⊥ V hV))}
    (hdir : IsInternalDirect (kBar D.M ⊥ V hV L) L₀ (Mbar D.M ⊥ V hV))
    (hL₀ : IsSym ↥L₀ 10) (hA : UC22.IsAlt ↥(lBar ⊥ V hV L) 10)
    (hsum : SumOfNat (fun H U Z => AlternatingNatural H U Z 10) (lStar D.M ⊥ V hV L)
      (⊤ : Subgroup (vStar D.M ⊥ V hV L)) ⊥ 2)
    (hV1 : v1Sub D.M ⊥ V hV L ≠ ⊥) {J₀ : Subgroup (Vtil ⊥ V hV)}
    (hM : S16C11Model (Mbar D.M ⊥ V hV) (kBar D.M ⊥ V hV L) J₀) :
    S16C11DimD1 D ⊥ V hV := by
  intro E hE hET hmB hle
  obtain ⟨φ, hev, hcomm, hfix, hJcard, hR⟩ :=
    s16c11_v1_cover_section_alt_ten D hin h1217 hc hs hK hA hsum hV1 hM
  have hLX : lBar ⊥ V hV L ≤ Mbar D.M ⊥ V hV := s16e_two_lBar_le D hc.setting.hyp151 hV
  have hLK : ∀ l ∈ (lBar ⊥ V hV L : Subgroup (MulAut (Vtil ⊥ V hV))),
      ∀ k ∈ (kBar D.M ⊥ V hV L : Subgroup (MulAut (Vtil ⊥ V hV))), l * k = k * l := by
    intro l hl k hk
    rw [kBar] at hk
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hk).2) l hl
  have hLL₀ : lBar ⊥ V hV L ≤ L₀ := s16c11_v1_le_right_of_centralizes hK hdir hLX hLK
  have hW : ∀ w : Vtil ⊥ V hV, w ^ 2 = 1 := fun w => s15_Infra_vtil_sq_eq_one ⊥ V hV w
  have hcore : ∀ F ∈ E3.aSet 2 (G6.coreAct 10).range, IsPGroup 2 ↥F → F ≠ ⊥ →
      4 ≤ rkIdx (fixV F) := fun F hF h2 hne => s16c11_v1_coreMod_ten_dimD1 hF h2 hne
  have h24 := s16c11_v1_rkIdx_aSet_alt (n := 10) (by norm_num) hcore hW hM hK hdir hL₀ hA
    hLL₀ φ hev hcomm hR hE
  have hp6 : CFSG.Open.pRank 2 (Mbar D.M ⊥ V hV) ≤ 6 := by
    have h := s16c11_big_pRank_le hdir hK hL₀
    norm_num at h ⊢
    exact h
  omega

theorem s16c11_v1_noncyclic_three_alt_ten (D : Data G) {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} {L₀ : Subgroup (MulAut (Vtil ⊥ V hV))}
    (hdir : IsInternalDirect (kBar D.M ⊥ V hV L) L₀ (Mbar D.M ⊥ V hV))
    (hL₀ : IsSym ↥L₀ 10) :
    ∃ P : Subgroup (MulAut (Vtil ⊥ V hV)),
      P ≤ Mbar D.M ⊥ V hV ∧ IsPGroup 3 ↥P ∧ ¬ IsCyclic ↥P := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard9 : Nat.card ↥eSix = 3 ^ 2 := by rw [card_eSix]; norm_num
  haveI : Nontrivial ↥eSix :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard9]; norm_num)
  have hexp : Monoid.exponent ↥eSix = 3 :=
    CFSG.IsElementaryAbelian.exponent_eq_prime (p := 3) (G := ↥eSix)
  have hEnc : ¬ IsCyclic ↥eSix := by
    rw [not_isCyclic_iff_exponent_eq_prime Nat.prime_three hcard9]
    exact hexp
  obtain ⟨e⟩ := hL₀
  let emb : Fin 6 ↪ Fin 10 := Fin.castLEEmb (by norm_num)
  have hemb : Function.Injective (Equiv.Perm.viaEmbeddingHom emb) :=
    Equiv.Perm.viaEmbeddingHom_injective emb
  have hE9 : IsPGroup 3 ↥eSix := IsPGroup.of_card (n := 2) (by rw [card_eSix]; norm_num)
  have hE₁p : IsPGroup 3 ↥(eSix.map (Equiv.Perm.viaEmbeddingHom emb)) :=
    hE9.map (Equiv.Perm.viaEmbeddingHom emb)
  have hE₁c : ¬ IsCyclic ↥(eSix.map (Equiv.Perm.viaEmbeddingHom emb)) :=
    SpLift.not_isCyclic_map (Equiv.Perm.viaEmbeddingHom emb) hemb hEnc
  have hE₂p : IsPGroup 3 ↥((eSix.map (Equiv.Perm.viaEmbeddingHom emb)).map
      e.symm.toMonoidHom) := hE₁p.map e.symm.toMonoidHom
  have hE₂c : ¬ IsCyclic ↥((eSix.map (Equiv.Perm.viaEmbeddingHom emb)).map
      e.symm.toMonoidHom) :=
    SpLift.not_isCyclic_map e.symm.toMonoidHom e.symm.injective hE₁c
  let P : Subgroup (MulAut (Vtil ⊥ V hV)) :=
    ((eSix.map (Equiv.Perm.viaEmbeddingHom emb)).map e.symm.toMonoidHom).map L₀.subtype
  have hPp : IsPGroup 3 ↥P := hE₂p.map L₀.subtype
  have hPc : ¬ IsCyclic ↥P := SpLift.not_isCyclic_map L₀.subtype L₀.subtype_injective hE₂c
  have hL₀X : L₀ ≤ Mbar D.M ⊥ V hV := by
    rw [← hdir.2.2]
    exact le_sup_right
  refine ⟨P, ?_, hPp, hPc⟩
  intro p hp
  obtain ⟨q, _, hqp⟩ := Subgroup.mem_map.1 hp
  rw [← hqp]
  exact hL₀X q.2

theorem s16c11_v1_dimD_alt_ten (D : Data G) (hin : In10 D) (h1217 : R1217 D)
    (h1610 : R16_10_2 D) {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D ⊥ V L hV)
    (hs : s15 D.M ⊥ V hV L = 1) (hout : Out10 D ⊥ V hV)
    (hsig : D.sig = {3}) (hK : IsSym ↥(kBar D.M ⊥ V hV L) 3)
    {L₀ : Subgroup (MulAut (Vtil ⊥ V hV))}
    (hdir : IsInternalDirect (kBar D.M ⊥ V hV L) L₀ (Mbar D.M ⊥ V hV))
    (hL₀ : IsSym ↥L₀ 10) (hA : UC22.IsAlt ↥(lBar ⊥ V hV L) 10)
    (hsum : SumOfNat (fun H U Z => AlternatingNatural H U Z 10) (lStar D.M ⊥ V hV L)
      (⊤ : Subgroup (vStar D.M ⊥ V hV L)) ⊥ 2)
    (hV1 : v1Sub D.M ⊥ V hV L ≠ ⊥) {J₀ : Subgroup (Vtil ⊥ V hV)}
    (hM : S16C11Model (Mbar D.M ⊥ V hV) (kBar D.M ⊥ V hV L) J₀) :
    ((CFSG.Open.pRank 2 (Mbar D.M ⊥ V hV) + mSub (⊥ : Subgroup G) : ℕ) : ℕ∞) < rMV D.M V ∧
      S16C11DimD1 D ⊥ V hV ∧
      ∃ P : Subgroup (MulAut (Vtil ⊥ V hV)),
        P ≤ Mbar D.M ⊥ V hV ∧ IsPGroup 3 ↥P ∧ ¬ IsCyclic ↥P :=
  ⟨s16c11_v1_rMV_alt_ten D hin h1217 h1610 hc hs hout hsig hK hdir hL₀ hA hsum hV1 hM,
    s16c11_v1_dimD1_alt_ten D hin h1217 h1610 hc hs hout hsig hK hdir hL₀ hA hsum hV1 hM,
    s16c11_v1_noncyclic_three_alt_ten D hdir hL₀⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
