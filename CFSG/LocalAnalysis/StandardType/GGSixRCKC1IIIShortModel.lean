module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1Defs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGTyLabelAux
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatTypeDet
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2GeoSUShort
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortSUDefs
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2GeoSp
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortSpNorm
public import CFSG.LocalAnalysis.StandardType.GGPRankBoundsSp
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIISpSiegel
public import CFSG.LocalAnalysis.StandardType.GGSixRCK1416Spin
public import CFSG.ClassicalGroups.Symplectic.ComponentCartanRank
public import CFSG.LieType.Universal.Symplectic
public import CFSG.RankThree.GF2n.Smith81.InspKSpCard
public import CFSG.LargeExtraspecial.A2ModOrd
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.Adapters.StatedClassicalUnitaryOrders
public import CFSG.ClassicalGroups.Symplectic.DiagonalTorusRank

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.LieKnownR2.Geo
  CFSG.StandardType.LieKnownR2.Short CFSG.StandardType.RCKK1IIISp
  CFSG.LieType.BorelTits CFSG.Open

theorem psu_admissible_of_shortRoot {m g : ℕ} (hg : 1 ≤ g)
    {L : LieUniversal}
    (hL : L = ⟨Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * g)) 2 g) m,
      Unitary.rootDatum (card_galoisField_two_mul 2 g hg) m⟩)
    {β : Fin L.D.rank → ℤ} (hβ : β ∈ L.D.roots)
    (hlong : ¬ GGLongRoot L.D β) (h2β : 2 • β ∉ L.D.roots) :
    StatedLieAdmissible .PSU m 2 g := by
  subst hL
  obtain ⟨v, w, v', w', hfr, -, -⟩ :=
    exists_unitPairGroup_eq_conj_rootGroup_SU (F := GaloisField 2 (2 * g)) (f := g)
      (card_galoisField_two_mul 2 g hg) m hβ hlong h2β
      (1 : ↥(Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * g)) 2 g) m))
  have hm4 : 4 ≤ m := four_le_of_suFrame hfr
  exact ⟨Nat.prime_two, hg, by omega, by
    intro h
    have hm3 : m = 3 := (Prod.mk.inj h).1
    omega⟩

theorem sp_two_le_of_shortRoot {m g : ℕ}
    {β : Fin (Symplectic.rootDatum m (GaloisField 2 g)).rank → ℤ}
    (hβ : β ∈ (Symplectic.rootDatum m (GaloisField 2 g)).roots)
    (hlong : ¬ GGLongRoot (Symplectic.rootDatum m (GaloisField 2 g)) β) :
    2 ≤ m := by
  by_contra hm
  have hm1 : m ≤ 1 := by omega
  have hallEven : GGRootSp.AllEven (toStd m β) := by
    obtain ⟨r, hr⟩ := exists_stdVec_of_mem_roots hβ
    rw [← hr]
    rcases r with i | i | ⟨i, j, hij⟩ | ⟨i, j, hij⟩ | ⟨i, j, hij⟩
    · intro a
      simp only [stdVec, Pi.smul_apply, Pi.single_apply]
      split_ifs <;> simp
    · intro a
      simp only [stdVec, Pi.neg_apply, Pi.smul_apply, Pi.single_apply]
      split_ifs <;> simp
    · exact absurd (Fin.ext (by have := i.isLt; have := j.isLt; omega)) hij
    · exact absurd (Fin.lt_def.1 hij) (by have := i.isLt; have := j.isLt; omega)
    · exact absurd (Fin.lt_def.1 hij) (by have := i.isLt; have := j.isLt; omega)
  exact hlong (ggLongRoot_of_allEven hβ hallEven)


theorem exists_shortRoot_psuFour_two {Jb : Type} [Group Jb] [Finite Jb]
    (hJ : LieModel (Jb ⧸ Subgroup.center Jb) .PSU 4 2 1)
    {rb : Jb ⧸ Subgroup.center Jb} {Vb : Subgroup (Jb ⧸ Subgroup.center Jb)}
    (hPos : RCKPosShort Jb rb Vb) (hrb : rb ≠ 1) :
    ∃ (β : Fin (ggU .PSU 4 1).D.rank → ℤ) (R : Subgroup Jb),
      β ∈ (ggU .PSU 4 1).D.roots ∧ ¬ GGLongRoot (ggU .PSU 4 1).D β ∧
        2 • β ∉ (ggU .PSU 4 1).D.roots ∧
          CFSG.StandardType.S2MathFi1035Pos.GGRootVia (ggU .PSU 4 1) ⊤ R β ∧
            rb ∈ R.map (QuotientGroup.mk' (Subgroup.center Jb)) := by
  obtain ⟨t', m, g, β, R, htag, hg1, hβ, hlong, h2β, hvia, hrb⟩ := hPos
  have hvia' := hvia
  obtain ⟨φ, hφrange, hφker, u, huR⟩ := hvia
  have hTag : GGPosTag t' := by
    rcases htag with rfl | rfl
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inl rfl)
  have hspin : Nat.card (ggU .PSp 2 1).K = 720 := by
    have hK : (ggU .PSp 2 1).K = StatedSp 2 (GaloisField 2 1) := by
      simp only [ggU, lieUniversal]
    rw [hK, CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp_two]
    have hF : Nat.card (GaloisField 2 1) = 2 := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      rw [GaloisField.card 2 1 (by norm_num : (1 : ℕ) ≠ 0)]
      norm_num
    rw [hF]
    norm_num
  have hcardq : Nat.card (Jb ⧸ Subgroup.center Jb) = 25920 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_four_two
      (hJ.statedClassicalModel (by decide))
  have hAdm : StatedLieAdmissible t' m 2 g := by
    rcases htag with rfl | rfl
    · have hβ' : β ∈ (Symplectic.rootDatum m (GaloisField 2 g)).roots := hβ
      have hlong' : ¬ GGLongRoot (Symplectic.rootDatum m (GaloisField 2 g)) β := hlong
      have hm2 : 2 ≤ m := sp_two_le_of_shortRoot hβ' hlong'
      refine ⟨Nat.prime_two, hg1, hm2, ?_⟩
      intro h
      have hm_eq : m = 2 := (Prod.mk.inj h).1
      have h2g : 2 ^ g = 2 := (Prod.mk.inj h).2
      have hg_eq : g = 1 := by
        refine Nat.pow_right_injective (by norm_num : 2 ≤ 2) ?_
        simpa using h2g
      subst hm_eq
      subst hg_eq
      have hdvd : Nat.card Jb ∣ 720 := by
        have h := Subgroup.card_range_dvd φ
        rw [hφrange, Subgroup.card_top, hspin] at h
        exact h
      have hle : Nat.card Jb ≤ 720 := Nat.le_of_dvd (by norm_num) hdvd
      have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Jb)
      rw [hcardq] at hmul
      haveI : Nonempty ↥(Subgroup.center Jb) := ⟨⟨1, Subgroup.one_mem _⟩⟩
      have hge : 25920 ≤ Nat.card Jb := by
        rw [hmul]
        exact Nat.le_mul_of_pos_right 25920 Nat.card_pos
      omega
    · have hL : ggU .PSU m g = ⟨Unitary.SU
          (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * g)) 2 g) m,
          Unitary.rootDatum (card_galoisField_two_mul 2 g hg1) m⟩ := by
        simp only [ggU, lieUniversal, hg1, ↓reduceDIte]
      exact psu_admissible_of_shortRoot hg1 hL hβ hlong h2β
  have hMtop : LieModel (↥(⊤ : Subgroup Jb) ⧸ Subgroup.center ↥(⊤ : Subgroup Jb)) t' m 2 g :=
    CFSG.StandardType.RCKRP.irg_lieModel_quot (ht := hTag) (hadm := hAdm) φ hφrange hφker
  have hM' : LieModel (Jb ⧸ Subgroup.center Jb) t' m 2 g :=
    LieModel.of_mulEquiv
      (QuotientGroup.congr (Subgroup.center ↥(⊤ : Subgroup Jb)) (Subgroup.center Jb)
        (Subgroup.topEquiv : ↥(⊤ : Subgroup Jb) ≃* Jb)
        (Subgroup.map_center_eq (Subgroup.topEquiv : ↥(⊤ : Subgroup Jb) ≃* Jb))) hMtop
  obtain ⟨ht'_eq, hm_eq, hg_eq⟩ :=
    CFSG.SeitzReduction.UnitaryPilot.sumEvenTypeDetAt (m := 4) (by norm_num : 4 ≤ 4)
      (X := Jb ⧸ Subgroup.center Jb) (f := 1) (t := t') (n := m) (f' := g)
      hJ hAdm hM'
  subst t'
  subst m
  subst g
  exact ⟨β, R, hβ, hlong, h2β, hvia', hrb⟩

theorem rckSpSiegel_of_shortAt_model
    {Jb : Type} [Group Jb] [Finite Jb] {m : ℕ} (hm : 3 ≤ m)
    (eta : Jb ≃* ↥(StatedSp m (GaloisField 2 1)))
    {rJ : Jb} (hrne : rJ ≠ 1)
    {Vb : Subgroup (Jb ⧸ Subgroup.center Jb)}
    (hpos : RCKPosShort Jb (QuotientGroup.mk' (Subgroup.center Jb) rJ) Vb) :
    ∃ x y : Fin m ⊕ Fin m → GaloisField 2 1,
      spB m x y = 0 ∧ SpSiegel x y (eta rJ) := by
  classical
  have hZsp : Subgroup.center ↥(StatedSp m (GaloisField 2 1)) = ⊥ :=
    CFSG.ClassicalGroups.Symplectic.center_statedSp_eq_bot_of_charP_two (by omega)
  have hZJ : Subgroup.center Jb = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : eta z ∈ Subgroup.center ↥(StatedSp m (GaloisField 2 1)) := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro g
      obtain ⟨y, rfl⟩ := eta.surjective g
      rw [← map_mul, ← map_mul, hz y]
    rw [hZsp, Subgroup.mem_bot] at hz'
    exact eta.injective (by rw [hz', map_one])
  have hinj : Function.Injective (QuotientGroup.mk' (Subgroup.center Jb)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hZJ]
  obtain ⟨t', m', g', β, R, htag, hg1, hβ, hlong, h2β, hvia, hrb⟩ := hpos
  have hvia' := hvia
  obtain ⟨φ, hφrange, hφker, u, huR⟩ := hvia
  have hrR : rJ ∈ R := by
    obtain ⟨s, hsR, hsmk⟩ := Subgroup.mem_map.1 hrb
    have hsr : s = rJ := hinj (by simpa using hsmk)
    simpa [hsr] using hsR
  have hTag : GGPosTag t' := by
    rcases htag with rfl | rfl
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inl rfl)
  have htclass : t' ∈ classicalTags ∨ t' = .twistedB2 := by
    rcases htag with rfl | rfl
    · exact Or.inl (by decide)
    · exact Or.inl (by decide)
  have hspin : Nat.card (ggU .PSp 2 1).K = 720 := by
    have hK : (ggU .PSp 2 1).K = StatedSp 2 (GaloisField 2 1) := by
      simp only [ggU, lieUniversal]
    rw [hK, CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp_two]
    have hF : Nat.card (GaloisField 2 1) = 2 := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      rw [GaloisField.card 2 1 (by norm_num : (1 : ℕ) ≠ 0)]
      norm_num
    rw [hF]
    norm_num
  have hSpLower : 720 < Nat.card ↥(StatedSp m (GaloisField 2 1)) := by
    have hKsp : Nat.card (GaloisField 2 1) = 2 ^ 1 := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      rw [GaloisField.card 2 1 (by norm_num : (1 : ℕ) ≠ 0)]
    have hcard := CFSG.RankThree.GF2n.Smith81.Insp.KFact.card_statedSp_eq_ordBC
      (K := GaloisField 2 1) (f := 1) le_rfl hKsp m
    rw [hcard]
    have h12 : 12096 < CFSG.Open.ordBC m 2 :=
      CFSG.LargeExtraspecial.A2Mod.Ord.twelve_thousand_lt_ordBC hm
    exact lt_trans (by norm_num : 720 < 12096) h12
  have hAdm : StatedLieAdmissible t' m' 2 g' := by
    rcases htag with rfl | rfl
    · have hβ' : β ∈ (Symplectic.rootDatum m' (GaloisField 2 g')).roots := hβ
      have hlong' : ¬ GGLongRoot (Symplectic.rootDatum m' (GaloisField 2 g')) β := hlong
      have hm2 : 2 ≤ m' := sp_two_le_of_shortRoot hβ' hlong'
      refine ⟨Nat.prime_two, hg1, hm2, ?_⟩
      intro h
      have hm_eq : m' = 2 := (Prod.mk.inj h).1
      have h2g : 2 ^ g' = 2 := (Prod.mk.inj h).2
      have hg_eq : g' = 1 := by
        refine Nat.pow_right_injective (by norm_num : 2 ≤ 2) ?_
        simpa using h2g
      subst hm_eq
      subst hg_eq
      have hdvd : Nat.card Jb ∣ 720 := by
        have h := Subgroup.card_range_dvd φ
        rw [hφrange, Subgroup.card_top, hspin] at h
        exact h
      have hle : Nat.card Jb ≤ 720 := Nat.le_of_dvd (by norm_num) hdvd
      have hetaCard : Nat.card Jb = Nat.card ↥(StatedSp m (GaloisField 2 1)) :=
        Nat.card_congr eta.toEquiv
      omega
    · have hL : ggU .PSU m' g' = ⟨Unitary.SU
          (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * g')) 2 g') m',
          Unitary.rootDatum (card_galoisField_two_mul 2 g' hg1) m'⟩ := by
        simp only [ggU, lieUniversal, hg1, ↓reduceDIte]
      exact psu_admissible_of_shortRoot hg1 hL hβ hlong h2β
  have hMtop : LieModel (↥(⊤ : Subgroup Jb) ⧸ Subgroup.center ↥(⊤ : Subgroup Jb)) t' m' 2 g' :=
    CFSG.StandardType.RCKRP.irg_lieModel_quot (ht := hTag) (hadm := hAdm) φ hφrange hφker
  have hM' : LieModel (Jb ⧸ Subgroup.center Jb) t' m' 2 g' :=
    LieModel.of_mulEquiv
      (QuotientGroup.congr (Subgroup.center ↥(⊤ : Subgroup Jb)) (Subgroup.center Jb)
        (Subgroup.topEquiv : ↥(⊤ : Subgroup Jb) ≃* Jb)
        (Subgroup.map_center_eq (Subgroup.topEquiv : ↥(⊤ : Subgroup Jb) ≃* Jb))) hMtop
  have hAdmSp : StatedLieAdmissible .PSp m 2 1 := by
    refine ⟨Nat.prime_two, le_rfl, by omega, ?_⟩
    intro h
    have hm2 : m = 2 := (Prod.mk.inj h).1
    omega
  have hKspCard : Nat.card (GaloisField 2 1) = 2 ^ 1 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [GaloisField.card 2 1 (by norm_num : (1 : ℕ) ≠ 0)]
  have hSCquot : StatedClassicalModel
      (↥(StatedSp m (GaloisField 2 1)) ⧸
        Subgroup.center ↥(StatedSp m (GaloisField 2 1))) .PSp m 2 1 :=
    CFSG.LieType.Universal.Symplectic.statedClassicalModel_center_quotient
      m (GaloisField 2 1) hAdmSp hKspCard
  let eSp : (↥(StatedSp m (GaloisField 2 1)) ⧸
      Subgroup.center ↥(StatedSp m (GaloisField 2 1))) ≃*
      ↥(StatedSp m (GaloisField 2 1)) :=
    (QuotientGroup.quotientMulEquivOfEq hZsp).trans QuotientGroup.quotientBot
  have hSCsp : StatedClassicalModel ↥(StatedSp m (GaloisField 2 1)) .PSp m 2 1 :=
    CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv eSp hSCquot
  let eZ : (Jb ⧸ Subgroup.center Jb) ≃* ↥(StatedSp m (GaloisField 2 1)) :=
    ((QuotientGroup.quotientMulEquivOfEq hZJ).trans QuotientGroup.quotientBot).trans eta
  have hJsp : LieModel (Jb ⧸ Subgroup.center Jb) .PSp m 2 1 :=
    LieModel.of_mulEquiv eZ.symm (Or.inl ⟨by decide, hSCsp⟩)
  obtain ⟨ht'eq, hm'eq, hg'eq⟩ :=
    CFSG.SeitzReduction.SymplecticPilot.sp2mEvenTypeDetClassical m
      (X := Jb ⧸ Subgroup.center Jb) (f := 1) (t := t') (n := m') (f' := g')
      htclass hJsp hAdm hM'
  subst t'
  subst m'
  subst g'
  have hKsp : (ggU .PSp m 1).K = ↥(StatedSp m (GaloisField 2 1)) := by
    simp only [ggU, lieUniversal]
  have hZdom : Subgroup.center (ggU .PSp m 1).K = ⊥ := by
    change Subgroup.center ↥(StatedSp m (GaloisField 2 1)) = ⊥
    exact hZsp
  have hφinj : Function.Injective φ :=
    (MonoidHom.ker_eq_bot_iff φ).1 (le_antisymm (hφker.trans (le_of_eq hZdom)) bot_le)
  have hφsurj : Function.Surjective φ := by
    rw [← MonoidHom.range_eq_top]
    exact hφrange
  let φs : ↥(StatedSp m (GaloisField 2 1)) →* Jb :=
    φ.comp (MonoidHom.id (ggU .PSp m 1).K)
  have hφs_inj : Function.Injective φs := hφinj
  have hφs_surj : Function.Surjective φs := hφsurj
  let φe : ↥(StatedSp m (GaloisField 2 1)) ≃* Jb :=
    MulEquiv.ofBijective φs ⟨hφs_inj, hφs_surj⟩
  let s0 : ↥(StatedSp m (GaloisField 2 1)) := φe.symm rJ
  have hφs0 : φs s0 = rJ := φe.apply_symm_apply rJ
  have hs0ne : s0 ≠ 1 := by
    intro h1
    apply hrne
    rw [← hφs0, h1, map_one]
  let us : ↥(StatedSp m (GaloisField 2 1)) := u
  have hs0Root : s0 ∈ ((Symplectic.rootDatum m (GaloisField 2 1)).rootGroup β).map
      (MulAut.conj us).toMonoidHom := by
    have hrR' : rJ ∈ R := hrR
    rw [huR] at hrR'
    simp only [ggU, lieUniversal, ggRootSub] at hrR'
    obtain ⟨t, ht, hφt⟩ := Subgroup.mem_map.1 hrR'
    have ht' : (show ↥(StatedSp m (GaloisField 2 1)) from t) ∈
        ((Symplectic.rootDatum m (GaloisField 2 1)).rootGroup β).map
          (MulAut.conj us).toMonoidHom := by
      obtain ⟨a, ha, hau⟩ := Subgroup.mem_map.1 ht
      exact ⟨a, ha, hau⟩
    have hts : (show ↥(StatedSp m (GaloisField 2 1)) from t) = s0 := by
      apply φe.injective
      have ht1 : φe (show ↥(StatedSp m (GaloisField 2 1)) from t) = rJ := by
        change φ t = rJ
        exact hφt
      have ht2 : φe s0 = rJ := by
        change φs s0 = rJ
        exact hφs0
      exact ht1.trans ht2.symm
    rwa [hts] at ht'
  obtain ⟨a₁, a₂, b₁, b₂, h1, h2, ⟨h3, h4, h5, h6⟩, hEq, -⟩ :=
    exists_altSiegelGroup_eq_conj_rootGroup_Sp m (GaloisField 2 1) hβ hlong u
  have hs0Alt : s0 ∈ spAltSiegel m (GaloisField 2 1) a₁ a₂ := by
    rw [spAltSiegel]
    show ((StatedSp m (GaloisField 2 1)).subtype s0) ∈
      ClassicalPosition.altSiegelGroup (spJ m (GaloisField 2 1)) a₁ a₂
    rw [← hEq]
    exact ⟨s0, hs0Root, rfl⟩
  have h12 : (spForm m (GaloisField 2 1)).β a₁ a₂ = 0 := by
    simpa [spForm_β, spJ] using h3
  obtain ⟨c, hmul⟩ := exists_mulVec_of_mem_spAltSiegel h12 hs0Alt
  have hc0 : c ≠ 0 := by
    intro hc0
    have hs0_one : s0 = 1 := by
      apply Subtype.ext
      apply Units.ext
      apply Matrix.ext
      intro i j
      have h := hmul (Pi.single j 1)
      rw [hc0] at h
      have h' := congrFun h i
      simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply, eq_comm] using h'
    exact hs0ne hs0_one
  have hc1 : c = 1 := by
    rcases rck1416_gf2_eq_zero_or_one c with h0 | h1
    · exact absurd h0 hc0
    · exact h1
  have hsp : SpSiegel a₁ a₂ s0 := by
    intro v
    rw [spAct_eq_natRep, natRep_apply]
    rw [hmul v, hc1]
    simp only [one_mul, spB_eq_spForm, spForm_β]
  let σ : MulAut ↥(StatedSp m (GaloisField 2 1)) := φe.trans eta
  obtain ⟨d, hd⟩ := CFSG.StandardType.PRankBounds.exists_conj_of_mulAut_spTwo hm σ
  have heta : eta rJ = d * s0 * d⁻¹ := by
    have h := hd (φe.symm rJ)
    simpa [σ, s0, MulEquiv.trans_apply] using h
  have hconj : SpSiegel (spAct d a₁) (spAct d a₂) (d * s0 * d⁻¹) :=
    spSiegel_conj hsp d
  refine ⟨spAct d a₁, spAct d a₂, ?_, ?_⟩
  · rw [spB_eq_spForm, spAct_eq_natRep]
    exact (CFSG.LieType.BorelTits.isIsometric_natRep_statedSp m (GaloisField 2 1) d a₁ a₂).trans
      h12
  · rw [heta]
    exact hconj

end CFSG.StandardType.RCKC1
