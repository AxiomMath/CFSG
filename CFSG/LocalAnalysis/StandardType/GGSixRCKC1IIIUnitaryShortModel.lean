module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIShortModel
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIUnitaryBlock
public import CFSG.Quasithin.Background.RonanF918FourCases
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUAlignAut
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotXiPartner
public import CFSG.LocalAnalysis.StandardType.SUCenterOdd
public import CFSG.RankThree.PartOne.S11d.OrthRankBase
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2Core
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotXiCaseS
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUnitaryModel
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotPerfectW
public import CFSG.Quasithin.Background.F918Fine4Pf
public import CFSG.Quasithin.Background.SmithB42Alt7Model
public import CFSG.Quasithin.H13.J4Classes
public import CFSG.Sporadic.J4.QT2LocMain
public import CFSG.Sporadic.J4.QT2LocRadMain

public section
namespace CFSG.StandardType.RCKC1

open Matrix CFSG.Assembly CFSG.Blueprint CFSG.Open CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.BorelTits CFSG.StandardType.S2MathFi1035Pos
  CFSG.StandardType.LieKnownR2.Short CFSG.StandardType.RCKK1IIISU


theorem exists_shortRoot_psu_two
    {Jb : Type} [Group Jb] [Finite Jb] [Group.IsPerfect Jb]
    {m : ℕ} (hm : 4 ≤ m) (hJ : LieModel (Jb ⧸ Subgroup.center Jb) .PSU m 2 1)
    {rb : Jb ⧸ Subgroup.center Jb} {Vb : Subgroup (Jb ⧸ Subgroup.center Jb)}
    (hPos : RCKPosShort Jb rb Vb) :
    ∃ (β : Fin (ggU .PSU m 1).D.rank → ℤ) (R : Subgroup Jb),
      β ∈ (ggU .PSU m 1).D.roots ∧ ¬ GGLongRoot (ggU .PSU m 1).D β ∧
        2 • β ∉ (ggU .PSU m 1).D.roots ∧
          GGRootVia (ggU .PSU m 1) ⊤ R β ∧
            rb ∈ R.map (QuotientGroup.mk' (Subgroup.center Jb)) := by
  obtain ⟨t, n, f, β, R, hTag, hf, hβ, hlong, h2β, hVia, hr⟩ := hPos
  have hVia₀ := hVia
  obtain ⟨φ, hφrange, hφker, u, hR⟩ := hVia
  have ht : GGPosTag t := by
    rcases hTag with rfl | rfl
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inl rfl)
  have hAdm : StatedLieAdmissible t n 2 f := by
    rcases hTag with rfl | rfl
    · have hn : 2 ≤ n := sp_two_le_of_shortRoot hβ hlong
      refine ⟨Nat.prime_two, hf, hn, ?_⟩
      intro hbad
      have hn2 : n = 2 := (Prod.mk.inj hbad).1
      have hf1 : f = 1 := Nat.pow_right_injective (by norm_num : 2 ≤ 2)
        (by simpa using (Prod.mk.inj hbad).2)
      subst n
      subst f
      have hZ : Subgroup.center (ggU .PSp 2 1).K = ⊥ :=
        CFSG.ClassicalGroups.Symplectic.center_statedSp_eq_bot_of_charP_two (by omega)
      have hφinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp
        (le_antisymm (hφker.trans hZ.le) bot_le)
      have hφsurj : Function.Surjective φ := MonoidHom.range_eq_top.mp hφrange
      let φe : CFSG.Open.StatedSp 2 (GaloisField 2 1) ≃* Jb :=
        MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
      have hP : Group.IsPerfect (CFSG.Open.StatedSp 2 (GaloisField 2 1)) :=
        Group.IsPerfect.ofSurjective (f := φe.symm.toMonoidHom) φe.symm.surjective
      apply CFSG.Quasithin.RonanF918.not_isPerfect_statedSp_card_two (F := GaloisField 2 1) _ hP
      rw [GaloisField.card 2 1 (by norm_num)]
      norm_num
    · have hU : ggU .PSU n f =
          ⟨SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n,
            Unitary.rootDatum (card_galoisField_two_mul 2 f hf) n⟩ := by
        simp only [ggU, lieUniversal, dif_pos hf]
      exact psu_admissible_of_shortRoot hf hU hβ hlong h2β
  have hLMtop := CFSG.StandardType.RCKRP.irg_lieModel_quot
    (ht := ht) (hadm := hAdm) φ hφrange hφker
  have hLM : LieModel (Jb ⧸ Subgroup.center Jb) t n 2 f := LieModel.of_mulEquiv
    (QuotientGroup.congr (Subgroup.center ↥(⊤ : Subgroup Jb)) (Subgroup.center Jb)
      (Subgroup.topEquiv : ↥(⊤ : Subgroup Jb) ≃* Jb)
      (Subgroup.map_center_eq (Subgroup.topEquiv : ↥(⊤ : Subgroup Jb) ≃* Jb))) hLMtop
  obtain ⟨ht', hn', hf'⟩ := CFSG.SeitzReduction.UnitaryPilot.sumEvenTypeDetAt hm
    (X := Jb ⧸ Subgroup.center Jb) (f := 1) (t := t) (n := n) (f' := f) hJ hAdm hLM
  subst t
  subst n
  subst f
  exact ⟨β, R, hβ, hlong, h2β, hVia₀, hr⟩

theorem sq_eq_one_of_mem_suPair
    {m : ℕ} {v w v' w' : Fin m → SUF}
    (hFrame : SUFrame rckSU_suF_card m v w v' w')
    {r : SUG m} (hr : r ∈ suPair SUσ m v w) : r * r = 1 := by
  obtain ⟨c, hc⟩ := exists_mulVec_of_mem_suPair rckSU_suF_card
    hFrame.2.2.1.1 hFrame.2.2.1.2.1 hFrame.2.2.2.1 hr
  have hwv : (suH rckSU_suF_card m).β w v = 0 :=
    (suH rckSU_suF_card m).refl _ _ hFrame.2.2.2.1
  have hv : natRep (SU SUσ m) r v = v := by
    rw [hc v, hwv, hFrame.2.2.1.1]
    simp
  have hw : natRep (SU SUσ m) r w = w := by
    rw [hc w, hFrame.2.2.1.2.1, hFrame.2.2.2.1]
    simp
  apply natRep_injective (SU SUσ m)
  apply LinearMap.ext
  intro x
  rw [map_mul, Module.End.mul_apply, hc x, map_add, map_add, map_smul, map_smul,
    hv, hw, hc x, map_one, Module.End.one_apply]
  have hdouble (z : Fin m → SUF) : z + z = 0 := by
    ext i
    exact CharTwo.add_self_eq_zero (z i)
  calc
    _ = x + ((c * (suH rckSU_suF_card m).β w x) • v +
          (c * (suH rckSU_suF_card m).β w x) • v) +
        ((SUσ c * (suH rckSU_suF_card m).β v x) • w +
          (SUσ c * (suH rckSU_suF_card m).β v x) • w) := by abel
    _ = x := by rw [hdouble, hdouble, add_zero, add_zero]

theorem rckSURank_of_shortAt_model
    {Jb : Type} [Group Jb] [Finite Jb] {m : ℕ} (hm : 4 ≤ m)
    (η : Jb ≃* SUG m) {rJ : Jb} (hr1 : rJ ≠ 1) (hr2 : rJ ^ 2 = 1)
    {Vb : Subgroup (Jb ⧸ Subgroup.center Jb)}
    (hPos : RCKPosShort Jb (QuotientGroup.mk' (Subgroup.center Jb) rJ) Vb) :
    (mat SUσ m (η rJ) - 1).rank = 2 := by
  have hAdm : StatedLieAdmissible .PSU m 2 1 :=
    ⟨Nat.prime_two, le_rfl, by omega, by intro h; have := (Prod.mk.inj h).1; omega⟩
  have hQ := isQuasisimple_SU rckSU_suF_card (by omega : 3 ≤ m) hAdm.2.2.2
  haveI : Group.IsPerfect (SUG m) := hQ.1
  haveI : Group.IsPerfect Jb :=
    Group.IsPerfect.ofSurjective (f := η.symm.toMonoidHom) η.symm.surjective
  let ηZ := QuotientGroup.congr (Subgroup.center Jb) (Subgroup.center (SUG m)) η
    (Subgroup.map_center_eq η)
  have hLM : LieModel (Jb ⧸ Subgroup.center Jb) .PSU m 2 1 :=
    LieModel.of_mulEquiv ηZ.symm
      (Or.inl ⟨by decide, statedClassicalModel_center_quotient hAdm rckSU_suF_card⟩)
  have hPacket := exists_shortRoot_psu_two hm hLM hPos
  have hU : ggU .PSU m 1 = ⟨SU SUσ m, Unitary.rootDatum rckSU_suF_card m⟩ := by
    simp only [ggU, lieUniversal, dif_pos (show 1 ≤ (1 : ℕ) from le_rfl)]
  rw [hU] at hPacket
  obtain ⟨β, R, hβ, hlong, h2β, hVia, hrR⟩ := hPacket
  obtain ⟨φ, hφrange, hφker, u, hR⟩ := hVia
  have hφsurj : Function.Surjective φ := MonoidHom.range_eq_top.mp hφrange
  have hφinj : Function.Injective φ :=
    (Finite.injective_iff_surjective_of_equiv η.symm.toEquiv).mpr hφsurj
  let φe : SUG m ≃* Jb := MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  obtain ⟨v, w, v', w', hFrame, hPair, _⟩ :=
    CFSG.StandardType.LieKnownR2.Geo.exists_unitPairGroup_eq_conj_rootGroup_SU
      rckSU_suF_card m hβ hlong h2β u
  obtain ⟨s, hsR, hs⟩ := Subgroup.mem_map.mp hrR
  rw [hR] at hsR
  change s ∈ (((Unitary.rootDatum rckSU_suF_card m).rootGroup β).map
    (MulAut.conj u).toMonoidHom).map φ at hsR
  obtain ⟨t, ht, hφt⟩ := Subgroup.mem_map.mp hsR
  have htPair : t ∈ suPair SUσ m v w := by rwa [hPair] at ht
  have ht2 : t * t = 1 := sq_eq_one_of_mem_suPair hFrame htPair
  have hs2 : s * s = 1 := by
    rw [← hφt, ← map_mul, ht2, map_one]
  have hOddSU : Odd (Nat.card (Subgroup.center (SUG m))) :=
    CFSG.StandardType.odd_natCard_of_le_center_SU SUσ le_rfl
  have hOddJ : Odd (Nat.card (Subgroup.center Jb)) := by
    rw [Nat.card_congr (Subgroup.centerCongr η).toEquiv]
    exact hOddSU
  have hsr : s = rJ := CFSG.SeitzReduction.F4Pilot.eq_of_mk_eq_of_mul_self_eq_one
    hOddJ hs2 (by simpa only [pow_two] using hr2) hs
  have hφtr : φe t = rJ := hφt.trans hsr
  have ht1 : t ≠ 1 := by
    intro h
    apply hr1
    rw [← hφtr, h, map_one]
  have hRank : (mat SUσ m t - 1).rank = 2 := rank_sub_one_of_mem_suPair hFrame htPair ht1
  let θ : MulAut (SUG m) := φe.trans η
  obtain ⟨A, τ, hIso, hAut⟩ := CFSG.SeitzReduction.SymplecticPilot.exists_conj_glAut_of_mulAut_SU
    rckSU_suF_card le_rfl (by omega)
      (by rintro ⟨h3, hq⟩; exact hAdm.2.2.2 (Prod.ext h3 hq)) θ
  have hη : η rJ = θ t := by
    change η rJ = η (φe t)
    rw [hφtr]
  rw [hη]
  have hMat : mat SUσ m (θ t) - 1 =
      (A : Matrix (Fin m) (Fin m) SUF) * ((mat SUσ m t - 1).map τ) *
        ((A⁻¹ : GL (Fin m) SUF) : Matrix (Fin m) (Fin m) SUF) := by
    have h := congrArg Units.val (hAut t)
    change mat SUσ m (θ t) = (A : Matrix (Fin m) (Fin m) SUF) *
      (mat SUσ m t).map τ * ((A⁻¹ : GL (Fin m) SUF) : Matrix (Fin m) (Fin m) SUF) at h
    rw [h, Matrix.map_sub τ (map_sub τ), Matrix.map_one _ (map_zero τ) (map_one τ),
      Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    rw [show (A : Matrix (Fin m) (Fin m) SUF) *
      ((A⁻¹ : GL (Fin m) SUF) : Matrix (Fin m) (Fin m) SUF) = 1 from
      congrArg Units.val (mul_inv_cancel A)]
  rw [hMat, Matrix.rank_mul_eq_left_of_isUnit_det _ _
      (isUnit_iff_ne_zero.mpr (Matrix.GeneralLinearGroup.det_ne_zero _)),
    Matrix.rank_mul_eq_right_of_isUnit_det _ _
      (isUnit_iff_ne_zero.mpr (Matrix.GeneralLinearGroup.det_ne_zero _))]
  exact (CFSG.RankThree.PartOne.FieldFix.rank_map_eq τ.toRingHom
    (mat SUσ m t - 1)).trans hRank

end CFSG.StandardType.RCKC1
