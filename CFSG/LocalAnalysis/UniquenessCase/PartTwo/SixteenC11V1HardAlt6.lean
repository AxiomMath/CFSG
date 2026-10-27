module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1Model
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1Fpz
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1RouteF
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1HardAlt6A
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1HardNat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1HardRes
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1HardAlt6B
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3FourteenSmall
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCase2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1TwoCommonFam

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16c11_v1_realizes_symCore_six (D : Data G) (hin : In10 D) (h1217 : R1217 D)
    {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D ⊥ V L hV)
    (hs : s15 D.M ⊥ V hV L = 1) (hsig : D.sig = {3})
    (hK : IsSym ↥(kBar D.M ⊥ V hV L) 3)
    {L₀ : Subgroup (MulAut (Vtil ⊥ V hV))}
    (hdir : IsInternalDirect (kBar D.M ⊥ V hV L) L₀ (Mbar D.M ⊥ V hV))
    (hL₀ : IsSym ↥L₀ 6) (hA : UC22.IsAlt ↥(lBar ⊥ V hV L) 6)
    (hsum : SumOfNat (fun H U Z => AlternatingNatural H U Z 6) (lStar D.M ⊥ V hV L)
      (⊤ : Subgroup (vStar D.M ⊥ V hV L)) ⊥ 2)
    (hV1 : v1Sub D.M ⊥ V hV L ≠ ⊥) {J₀ : Subgroup (Vtil ⊥ V hV)}
    (hM : S16C11Model (Mbar D.M ⊥ V hV) (kBar D.M ⊥ V hV L) J₀) :
    (G64.symCoreModel 6).Realizes L₀ J₀ ⊥ := by
  classical
  have htop : wStar D.M ⊥ V hV L = ⊤ :=
    s15_Three_wStar_eq_top D h1217 hc.setting.hyp151 hV hc.ne_bot hs
  have hsum' : SumOfNat (fun H U Z => AlternatingNatural H U Z 6) (lStar D.M ⊥ V hV L)
      (wStar D.M ⊥ V hV L) ⊥ 2 := by
    rw [htop]
    exact hsum
  have hF : s16e_two_Fam D ⊥ V L hV (fun H U Z => AlternatingNatural H U Z 6) :=
    s16e_two_fam_alt D hV (by omega) hA hsum'
  obtain ⟨φ, hφcoe, hcomm, hfixne, D', hD'eq, hRD'⟩ :=
    s16c11_v1_hard_nat_section D hin h1217 hc hs
      (P := fun H U Z => AlternatingNatural H U Z 6) (Q := fun D' => D' = FFModel.altDn 6)
      hF (fun H U Z h => ⟨FFModel.altDn 6, rfl, h⟩) hV1 hM
  subst hD'eq
  have hZ : ∀ k ∈ kBar D.M ⊥ V hV L,
      (∀ k' ∈ kBar D.M ⊥ V hV L, k * k' = k' * k) → k = 1 := by
    intro k hk hkc
    have h1 : (⟨k, hk⟩ : ↥(kBar D.M ⊥ V hV L)) = 1 :=
      s16c167_center_of_isSym_three hK ⟨k, hk⟩
        (fun y => Subtype.ext (hkc (y : MulAut (Vtil ⊥ V hV)) y.2).symm)
    exact congrArg Subtype.val h1
  have hLM : lBar ⊥ V hV L ≤ Mbar D.M ⊥ V hV := s16e_two_lBar_le D hc.setting.hyp151 hV
  have hle : lBar ⊥ V hV L ≤ L₀ := by
    refine s16c1614_le_right_of_centralizes hdir hLM ?_ hZ
    intro n hn k hk
    exact (Subgroup.mem_centralizer_iff.1 hk.2) n hn
  have hL₀Mbar : L₀ ≤ Mbar D.M ⊥ V hV := hdir.2.2 ▸ le_sup_right
  have hL₀K : ∀ l ∈ L₀, ∀ k ∈ kBar D.M ⊥ V hV L, l * k = k * l := by
    intro l hl k hk
    exact (s16c11_comm_of_isInternalDirect hdir k hk l hl).symm
  have hLK : ∀ l ∈ lBar ⊥ V hV L, ∀ k ∈ kBar D.M ⊥ V hV L, l * k = k * l := by
    intro l hl k hk
    exact (s16c11_comm_of_isInternalDirect hdir k hk l (hle hl)).symm
  have hJ : ∀ l ∈ L₀, ∀ j ∈ J₀, l j ∈ J₀ := by
    intro l hl j hj
    exact s16c11_mem_of_model (s15_Infra_vtil_sq_eq_one ⊥ V hV) hM (hL₀Mbar hl) (hL₀K l hl) hj
  have hJ' : ∀ l ∈ lBar ⊥ V hV L, ∀ j ∈ J₀, l j ∈ J₀ := fun l hl => hJ l (hle hl)
  have hinj₀ : Function.Injective (CFSG.Quasithin.H13.VolI.resHom L₀ J₀ hJ) :=
    s16c11_v1_resHom_injective hM hL₀Mbar hL₀K hJ
  have hinj' : Function.Injective
      (CFSG.Quasithin.H13.VolI.resHom (lBar ⊥ V hV L) J₀ hJ') :=
    s16c11_v1_resHom_injective hM hLM hLK hJ'
  have hφeq : φ = CFSG.Quasithin.H13.VolI.resHom (lBar ⊥ V hV L) J₀ hJ' := by
    apply MonoidHom.ext
    intro x
    apply MulEquiv.ext
    intro j
    apply Subtype.ext
    rw [hφcoe x j, CFSG.Quasithin.H13.VolI.coe_resHom_apply]
  have hφinj : Function.Injective φ := by
    rw [hφeq]
    exact hinj'
  have heqL : ∀ x : ↥(lBar ⊥ V hV L),
      CFSG.Quasithin.H13.VolI.resHom (lBar ⊥ V hV L) J₀ hJ' x =
        CFSG.Quasithin.H13.VolI.resHom L₀ J₀ hJ ⟨x, hle x.2⟩ := by
    intro x
    apply MulEquiv.ext
    intro j
    apply Subtype.ext
    rw [CFSG.Quasithin.H13.VolI.coe_resHom_apply,
      CFSG.Quasithin.H13.VolI.coe_resHom_apply]
  have hHH₀ : φ.range ≤ (CFSG.Quasithin.H13.VolI.resHom L₀ J₀ hJ).range := by
    rintro _ ⟨x, rfl⟩
    refine ⟨⟨x, hle x.2⟩, ?_⟩
    rw [hφeq]
    exact (heqL x).symm
  have hS₀ : IsSym ↥((CFSG.Quasithin.H13.VolI.resHom L₀ J₀ hJ).range) 6 := by
    obtain ⟨e⟩ := hL₀
    exact ⟨(MonoidHom.ofInjective hinj₀).symm.trans e⟩
  have hAφ : UC22.IsAlt ↥(φ.range) 6 := by
    obtain ⟨e⟩ := hA
    exact ⟨(MonoidHom.ofInjective hφinj).symm.trans e⟩
  have hJ2 : ∀ j : ↥J₀, j ^ 2 = 1 := fun j => Subtype.ext (by
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact s15_Infra_vtil_sq_eq_one ⊥ V hV (j : Vtil ⊥ V hV))
  haveI : Finite ↥J₀ := inferInstance
  have hcover : (G64.symCoreModel 6).Realizes
      (CFSG.Quasithin.H13.VolI.resHom L₀ J₀ hJ).range ⊤ ⊥ :=
    s16c11_v1_symCore_six_of_cover hJ2 hHH₀ hS₀ hAφ hcomm hRD' hfixne
  exact s16c11_v1_realizes_of_resHom hJ hinj₀ hcover

theorem s16c11_v1_rf3_alt_six (D : Data G) (hin : In10 D) (h1217 : R1217 D)
    {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D ⊥ V L hV)
    (hs : s15 D.M ⊥ V hV L = 1) (hsig : D.sig = {3})
    (hK : IsSym ↥(kBar D.M ⊥ V hV L) 3)
    {L₀ : Subgroup (MulAut (Vtil ⊥ V hV))}
    (hdir : IsInternalDirect (kBar D.M ⊥ V hV L) L₀ (Mbar D.M ⊥ V hV))
    (hL₀ : IsSym ↥L₀ 6) (hA : UC22.IsAlt ↥(lBar ⊥ V hV L) 6)
    (hsum : SumOfNat (fun H U Z => AlternatingNatural H U Z 6) (lStar D.M ⊥ V hV L)
      (⊤ : Subgroup (vStar D.M ⊥ V hV L)) ⊥ 2)
    (hV1 : v1Sub D.M ⊥ V hV L ≠ ⊥) {J₀ : Subgroup (Vtil ⊥ V hV)}
    (hM : S16C11Model (Mbar D.M ⊥ V hV) (kBar D.M ⊥ V hV L) J₀) :
    S16C11RF3 L₀ J₀ :=
  s16c11_rf3_of_modelRF3 (G64.symCore_faithful (by norm_num))
    (s16c11_v1_realizes_symCore_six D hin h1217 hc hs hsig hK hdir hL₀ hA hsum hV1 hM)
    s16c11_v1_modelRF3_symCore_six

theorem s16c11_v1_hard_alt_six (D : Data G) (hin : In10 D) (h1217 : R1217 D) (h1610 : R16_10_2 D)
    {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D ⊥ V L hV)
    (hs : s15 D.M ⊥ V hV L = 1) (hout : Out10 D ⊥ V hV)
    (hsig : D.sig = {3}) (hK : IsSym ↥(kBar D.M ⊥ V hV L) 3)
    {L₀ : Subgroup (MulAut (Vtil ⊥ V hV))}
    (hdir : IsInternalDirect (kBar D.M ⊥ V hV L) L₀ (Mbar D.M ⊥ V hV))
    (hL₀ : IsSym ↥L₀ 6) (hA : UC22.IsAlt ↥(lBar ⊥ V hV L) 6)
    (hsum : SumOfNat (fun H U Z => AlternatingNatural H U Z 6) (lStar D.M ⊥ V hV L)
      (⊤ : Subgroup (vStar D.M ⊥ V hV L)) ⊥ 2)
    (hV1 : v1Sub D.M ⊥ V hV L ≠ ⊥) :
    normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := by
  have htop : wStar D.M ⊥ V hV L = ⊤ :=
    s15_Three_wStar_eq_top D h1217 hc.setting.hyp151 hV hc.ne_bot hs
  have hsum' : SumOfNat (fun H U Z => AlternatingNatural H U Z 6) (lStar D.M ⊥ V hV L)
      (wStar D.M ⊥ V hV L) ⊥ 2 := by
    rw [htop]
    exact hsum
  have hF : s16e_two_Fam D ⊥ V L hV (fun H U Z => AlternatingNatural H U Z 6) :=
    s16e_two_fam_alt D hV (by omega) hA hsum'
  have hfpf := s16c11_v1_z_fpf D hin h1217 hc hs hF hK
  obtain ⟨J₀, hM⟩ :=
    s16c11_v1_model_of_fpf (s15_Infra_vtil_sq_eq_one ⊥ V hV) inf_le_left hK hfpf
  exact s16c11_v1_normalizer_le_of_model_rf3 D hin.h61 h1610 hin.h169 hc hsig hM hK hdir
    (s16c11_v1_rf3_alt_six D hin h1217 hc hs hsig hK hdir hL₀ hA hsum hV1 hM)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
