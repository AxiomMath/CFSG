module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1OddCoverLift
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIISUThreePlane
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIUnitaryShortModel
import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.Cover
import CFSG.LocalAnalysis.ComponentClassification.Quasisimple
import CFSG.HardMathSupport.Dickson.I271.SporGen
import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.NoComp
import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.StepGen
import CFSG.HardMathSupport.Solomon.Coordinator.I23_26Comp
import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsAlt
import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsHatSixCore
import CFSG.HardMathSupport.Solomon.Coordinator.ONCOut
import CFSG.HardMathSupport.Solomon.LocalBalance.ONFacts

public section

namespace CFSG.StandardType.RCKC1

open Matrix CFSG.Assembly CFSG.Blueprint CFSG.Open CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.StandardType.RCKK1IIISU CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.HardMathSupport.Dickson.I271
  CFSG.StandardType.LieKnownR2.Short
open CFSG.LieType.BorelTits (unitaryInvolution)

section Aut

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f r : ℕ}

theorem exists_mulAut_SU_lift_of_mulAut_center_quot (hF : Nat.card F = (2 ^ f) ^ 2)
    (hf : 1 ≤ f) (hr : 3 ≤ r) (hrq : ¬(r = 3 ∧ 2 ^ f = 2))
    (θ : MulAut (SU (unitaryInvolution F 2 f) r ⧸
      Subgroup.center (SU (unitaryInvolution F 2 f) r))) :
    ∃ γ : MulAut (SU (unitaryInvolution F 2 f) r), ∀ x : SU (unitaryInvolution F 2 f) r,
      θ (QuotientGroup.mk x) = QuotientGroup.mk (γ x) := by
  set h := CFSG.SeitzReduction.SymplecticPilot.ctua_unitaryFieldData hF hf with hh
  have hC : IsPrimeFormGram (CFSG.SeitzReduction.SymplecticPilot.ctuaAntidiagGL r F) :=
    CFSG.SeitzReduction.SymplecticPilot.isPrimeFormGram_ctuaAntidiagGL
  set C : Matrix (Fin r) (Fin r) F :=
    ((CFSG.SeitzReduction.SymplecticPilot.ctuaAntidiagGL r F : GL (Fin r) F) :
      Matrix (Fin r) (Fin r) F) with hCdef
  have hE : SU (unitaryInvolution F 2 f) r = gramSU h C :=
    CFSG.SeitzReduction.SymplecticPilot.SU_eq_gramSU h
  set E : SU (unitaryInvolution F 2 f) r ≃* gramSU h C := MulEquiv.subgroupCongr hE with hEdef
  set EZ : SU (unitaryInvolution F 2 f) r ⧸
        Subgroup.center (SU (unitaryInvolution F 2 f) r) ≃*
      gramSU h C ⧸ Subgroup.center (gramSU h C) :=
    QuotientGroup.congr _ _ E (Subgroup.map_center_eq E) with hEZdef
  set Q : gramSU h C ⧸ Subgroup.center (gramSU h C) ≃* primeFormP h C :=
    QuotientGroup.quotientMulEquivOfEq
      (CFSG.SeitzReduction.F4Pilot.center_gramSU_eq_normOneScalars h hC hr hrq) with hQdef
  set eP : SU (unitaryInvolution F 2 f) r ⧸
        Subgroup.center (SU (unitaryInvolution F 2 f) r) ≃* primeFormP h C :=
    EZ.trans Q with hePdef
  set αb : MulAut (primeFormP h C) := MulAut.congr eP θ with hαbdef
  obtain ⟨⟨A, φ⟩, hAφ⟩ := primeFormPsi_surjective h hC hr hrq αb
  set γ' : gramSU h C ≃* gramSU h C :=
    (primeFormFieldSU h hC φ).trans (primeFormConjSU h C A) with hγ'def
  set γ : MulAut (SU (unitaryInvolution F 2 f) r) := E.trans (γ'.trans E.symm) with hγdef
  have hmkE : ∀ y : SU (unitaryInvolution F 2 f) r,
      eP (QuotientGroup.mk y) = (E y : primeFormP h C) := by
    intro y
    rw [hePdef, MulEquiv.trans_apply, QuotientGroup.congr_mk, hQdef,
      QuotientGroup.quotientMulEquivOfEq_mk]
  refine ⟨γ, fun x => ?_⟩
  apply eP.injective
  calc
    eP (θ (QuotientGroup.mk x)) = αb (eP (QuotientGroup.mk x)) := by
      rw [hαbdef, MulAut.congr_apply]
      simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    _ = αb (E x : primeFormP h C) := by rw [hmkE]
    _ = (primeFormPsi h hC ⟨A, φ⟩) (E x : primeFormP h C) := by rw [hAφ]
    _ = (primeFormConjAut h C A) (primeFormFieldAut h hC φ (E x : primeFormP h C)) := by
      rw [primeFormPsi_apply, MulAut.mul_apply]
      rfl
    _ = (γ' (E x) : primeFormP h C) := by
      rw [primeFormFieldAut_mk, primeFormConjAut_mk, hγ'def, MulEquiv.trans_apply]
    _ = eP (QuotientGroup.mk (γ x)) := by
      rw [hmkE, hγdef]
      simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply]

end Aut

theorem rckSU_rank_mulAut_sub_one {m : ℕ} (hm : 4 ≤ m) (γ : MulAut (SUG m)) (x : SUG m) :
    (mat SUσ m (γ x) - 1).rank = (mat SUσ m x - 1).rank := by
  obtain ⟨A, τ, _, hAut⟩ :=
    CFSG.SeitzReduction.SymplecticPilot.exists_conj_glAut_of_mulAut_SU
      (F := SUF) (f := 1) (r := m) rckSU_suF_card le_rfl (by omega)
        (by rintro ⟨h3, -⟩; omega) γ
  have hMat : mat SUσ m (γ x) - 1 =
      (A : Matrix (Fin m) (Fin m) SUF) * ((mat SUσ m x - 1).map τ) *
        ((A⁻¹ : GL (Fin m) SUF) : Matrix (Fin m) (Fin m) SUF) := by
    have h := congrArg Units.val (hAut x)
    change mat SUσ m (γ x) = (A : Matrix (Fin m) (Fin m) SUF) *
      (mat SUσ m x).map τ * ((A⁻¹ : GL (Fin m) SUF) : Matrix (Fin m) (Fin m) SUF) at h
    rw [h, Matrix.map_sub τ (map_sub τ), Matrix.map_one _ (map_zero τ) (map_one τ),
      Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    rw [show (A : Matrix (Fin m) (Fin m) SUF) *
      ((A⁻¹ : GL (Fin m) SUF) : Matrix (Fin m) (Fin m) SUF) = 1 from
      congrArg Units.val (mul_inv_cancel A)]
  rw [hMat, Matrix.rank_mul_eq_left_of_isUnit_det _ _
      (isUnit_iff_ne_zero.mpr (Matrix.GeneralLinearGroup.det_ne_zero _)),
    Matrix.rank_mul_eq_right_of_isUnit_det _ _
      (isUnit_iff_ne_zero.mpr (Matrix.GeneralLinearGroup.det_ne_zero _))]
  exact CFSG.RankThree.PartOne.FieldFix.rank_map_eq τ.toRingHom (mat SUσ m x - 1)

theorem rank_sub_one_eq_of_central_covers {Y : Type} [Group Y] [Finite Y] {m : ℕ} (hm : 4 ≤ m)
    (φ₁ φ₂ : SUG m →* Y) (h₁ : Function.Surjective φ₁) (h₂ : Function.Surjective φ₂)
    (hk₁ : φ₁.ker ≤ Subgroup.center (SUG m)) (hk₂ : φ₂.ker ≤ Subgroup.center (SUG m))
    {t s : SUG m} (ht : t ^ 2 = 1) (hs : s ^ 2 = 1) (hts : φ₁ t = φ₂ s) :
    (mat SUσ m t - 1).rank = (mat SUσ m s - 1).rank := by
  have hAdm : StatedLieAdmissible .PSU m 2 1 :=
    ⟨Nat.prime_two, le_rfl, by omega, by intro h; have := (Prod.mk.inj h).1; omega⟩
  have hQ := isQuasisimple_SU rckSU_suF_card (by omega : 3 ≤ m) hAdm.2.2.2
  have hc₁ : (Subgroup.center (SUG m)).map φ₁ = Subgroup.center Y :=
    @CFSG.ComponentClassification.Quasisimple.center_map_of_central_kernel (SUG m) Y _ _ hQ.1
      φ₁ h₁ hk₁
  have hc₂ : (Subgroup.center (SUG m)).map φ₂ = Subgroup.center Y :=
    @CFSG.ComponentClassification.Quasisimple.center_map_of_central_kernel (SUG m) Y _ _ hQ.1
      φ₂ h₂ hk₂
  let f₁ : SUG m ⧸ Subgroup.center (SUG m) →* Y ⧸ Subgroup.center Y :=
    QuotientGroup.map _ _ φ₁ (Subgroup.map_le_iff_le_comap.mp hc₁.le)
  have hf₁ : Function.Bijective f₁ := by
    constructor
    · rw [injective_iff_map_eq_one]
      intro x hx
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
      have h1 : φ₁ y ∈ Subgroup.center Y := (QuotientGroup.eq_one_iff _).1 hx
      exact (QuotientGroup.eq_one_iff _).2
        (@mem_center_of_map_mem_center (SUG m) Y _ _ φ₁ hk₁ hQ.1 y h1)
    · intro q
      obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨y, rfl⟩ := h₁ y'
      exact ⟨QuotientGroup.mk y, rfl⟩
  let f₂ : SUG m ⧸ Subgroup.center (SUG m) →* Y ⧸ Subgroup.center Y :=
    QuotientGroup.map _ _ φ₂ (Subgroup.map_le_iff_le_comap.mp hc₂.le)
  have hf₂ : Function.Bijective f₂ := by
    constructor
    · rw [injective_iff_map_eq_one]
      intro x hx
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
      have h1 : φ₂ y ∈ Subgroup.center Y := (QuotientGroup.eq_one_iff _).1 hx
      exact (QuotientGroup.eq_one_iff _).2
        (@mem_center_of_map_mem_center (SUG m) Y _ _ φ₂ hk₂ hQ.1 y h1)
    · intro q
      obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨y, rfl⟩ := h₂ y'
      exact ⟨QuotientGroup.mk y, rfl⟩
  let e₁ : SUG m ⧸ Subgroup.center (SUG m) ≃* Y ⧸ Subgroup.center Y :=
    MulEquiv.ofBijective f₁ hf₁
  let e₂ : SUG m ⧸ Subgroup.center (SUG m) ≃* Y ⧸ Subgroup.center Y :=
    MulEquiv.ofBijective f₂ hf₂
  let θ : MulAut (SUG m ⧸ Subgroup.center (SUG m)) := e₁.trans e₂.symm
  obtain ⟨γ, hγ⟩ := exists_mulAut_SU_lift_of_mulAut_center_quot
    (F := SUF) (f := 1) (r := m) rckSU_suF_card le_rfl (by omega)
      (by rintro ⟨h3, -⟩; omega) θ
  have h₁mk : e₁ (QuotientGroup.mk t) = QuotientGroup.mk (φ₁ t) :=
    QuotientGroup.map_mk (Subgroup.center (SUG m)) (Subgroup.center Y) φ₁
      (Subgroup.map_le_iff_le_comap.mp hc₁.le) t
  have h₂mk : e₂ (QuotientGroup.mk s) = QuotientGroup.mk (φ₂ s) :=
    QuotientGroup.map_mk (Subgroup.center (SUG m)) (Subgroup.center Y) φ₂
      (Subgroup.map_le_iff_le_comap.mp hc₂.le) s
  have hγt : (QuotientGroup.mk (γ t) : SUG m ⧸ Subgroup.center (SUG m)) =
      QuotientGroup.mk s := by
    rw [← hγ t]
    calc θ (QuotientGroup.mk t) = e₂.symm (e₁ (QuotientGroup.mk t)) := by
          rw [show θ = e₁.trans e₂.symm from rfl, MulEquiv.trans_apply]
      _ = e₂.symm (QuotientGroup.mk (φ₁ t)) := by rw [h₁mk]
      _ = e₂.symm (QuotientGroup.mk (φ₂ s)) := by rw [hts]
      _ = QuotientGroup.mk s := by rw [← h₂mk, MulEquiv.symm_apply_apply]
  have hγt2 : γ t * γ t = 1 := by
    rw [← map_mul, ← pow_two, ht, map_one]
  have hs2 : s * s = 1 := by simpa [pow_two] using hs
  have hodd : Odd (Nat.card (Subgroup.center (SUG m))) :=
    odd_natCard_of_le_center_SU SUσ le_rfl
  have hγs : γ t = s :=
    CFSG.SeitzReduction.F4Pilot.eq_of_mk_eq_of_mul_self_eq_one hodd hγt2 hs2 hγt
  rw [← hγs]
  exact (rckSU_rank_mulAut_sub_one hm γ t).symm

section Short


theorem rank_eq_two_of_shortAt_of_central_cover
    {X Y : Type} [Group X] [Finite X] [Group Y] [Finite Y] {m : ℕ} (hm : 4 ≤ m)
    {J : Subgroup X} (hJ : Group.IsPerfect ↥J) (hoddJ : Odd (Nat.card (Subgroup.center ↥J)))
    (ε : ↥J →* Y) (hε : Function.Surjective ε) (hεker : ε.ker ≤ Subgroup.center ↥J)
    (ψ : SUG m →* Y) (hψ : Function.Surjective ψ) (hψker : ψ.ker ≤ Subgroup.center (SUG m))
    {r : ↥J} (hr1 : r ≠ 1) (hr2 : r ^ 2 = 1) (hShort : ShortAt J (r : X))
    {rU : SUG m} (hrU2 : rU ^ 2 = 1) (hrU : ψ rU = ε r) :
    (mat SUσ m rU - 1).rank = 2 := by
  have hAdm : StatedLieAdmissible .PSU m 2 1 :=
    ⟨Nat.prime_two, le_rfl, by omega, by intro h; have := (Prod.mk.inj h).1; omega⟩
  have hQ := isQuasisimple_SU rckSU_suF_card (by omega : 3 ≤ m) hAdm.2.2.2
  let eJ : ↥J ⧸ Subgroup.center ↥J ≃* Y ⧸ Subgroup.center Y :=
    @quotCenterEquivOfCentral ↥J Y _ _ ε hε hεker hJ
  let eSU : SUG m ⧸ Subgroup.center (SUG m) ≃* Y ⧸ Subgroup.center Y :=
    @quotCenterEquivOfCentral (SUG m) Y _ _ ψ hψ hψker hQ.1
  have hLM : LieModel (↥J ⧸ Subgroup.center ↥J) .PSU m 2 1 :=
    LieModel.of_mulEquiv (eSU.trans eJ.symm)
      (Or.inl ⟨by decide, statedClassicalModel_center_quotient hAdm rckSU_suF_card⟩)
  obtain ⟨rJ, hrJval, hPos⟩ := hShort
  have hPos' : RCKPosShort ↥J (QuotientGroup.mk' (Subgroup.center ↥J) r) ⊥ := by
    simpa [Subtype.ext hrJval] using hPos
  have hPacket := @exists_shortRoot_psu_two
   
   
   
   
   
   
    ↥J _ _ hJ _ hm hLM _ _ hPos'
  have hU : ggU .PSU m 1 = ⟨SU SUσ m, Unitary.rootDatum rckSU_suF_card m⟩ := by
    simp only [ggU, lieUniversal, dif_pos (show 1 ≤ (1 : ℕ) from le_rfl)]
  rw [hU] at hPacket
  obtain ⟨β, R, hβ, hlong, h2β, hVia, hrR⟩ := hPacket
  obtain ⟨φ, hφrange, hφker, u, hR⟩ := hVia
  have hφsurj : Function.Surjective φ := MonoidHom.range_eq_top.mp hφrange
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
  have hrsq : r * r = 1 := by simpa [pow_two] using hr2
  have hsr : s = r := CFSG.SeitzReduction.F4Pilot.eq_of_mk_eq_of_mul_self_eq_one
    hoddJ hs2 hrsq hs
  have hφtr : φ t = r := hφt.trans hsr
  have ht1 : t ≠ 1 := by
    intro h
    apply hr1
    rw [← hφtr, h, map_one]
  have hRank : (mat SUσ m t - 1).rank = 2 := rank_sub_one_of_mem_suPair hFrame htPair ht1
  have hker : (ε.comp φ).ker ≤ Subgroup.center (SUG m) := by
    intro x hx
    exact @mem_center_of_map_mem_center (SUG m) ↥J _ _ φ hφker hQ.1 x
      (hεker (by
        rw [MonoidHom.mem_ker] at hx ⊢
        exact hx))
  have hts : (ε.comp φ) t = ψ rU := by
    change ε (φ t) = ψ rU
    rw [hφtr]
    exact hrU.symm
  have h := rank_sub_one_eq_of_central_covers hm (ε.comp φ) ψ (hε.comp hφsurj) hψ hker hψker
    (by simpa [pow_two] using ht2) hrU2 hts
  rw [← h]
  exact hRank

theorem rckSU_exists_conj_suV_of_central_cover
    {X Y : Type} [Group X] [Finite X] [Group Y] [Finite Y] {m : ℕ} (hm : 4 ≤ m)
    {J V : Subgroup X} {r : X} (hJ : Group.IsPerfect ↥J)
    (hoddJ : Odd (Nat.card (Subgroup.center ↥J)))
    (ε : ↥J →* Y) (hε : Function.Surjective ε) (hεker : ε.ker ≤ Subgroup.center ↥J)
    (ψ : SUG m →* Y) (hψ : Function.Surjective ψ) (hψker : ψ.ker ≤ Subgroup.center (SUG m))
    (hFour : FourAt J V r) (hCore : CoreCommAt J V r) (hShort : ShortAt J r) :
    ∃ (hrJ : r ∈ J) (g : SUG m), ε ⟨r, hrJ⟩ = ψ (g * suR hm * g⁻¹) ∧
      (V.subgroupOf J).map ε = (suV hm).map (ψ.comp (MulAut.conj g).toMonoidHom) := by
  have hrJ : r ∈ J := hFour.2.1 hFour.1
  let rJ : ↥J := ⟨r, hrJ⟩
  have hr2J : rJ ^ 2 = 1 := by
    apply Subtype.ext
    change r ^ 2 = 1
    simpa [pow_two] using hFour.2.2.1.2 r hFour.1
  have hr1J : rJ ≠ 1 := by
    intro h
    exact hFour.2.2.2.2.1 (by simpa [rJ] using congrArg Subtype.val h)
  have hFourJ : FourAt (⊤ : Subgroup ↥J) (V.subgroupOf J) rJ := by
    simpa [Subgroup.map_id] using
      fourAt_map_mulEquiv (MulEquiv.refl ↥J) hrJ hFour
  have hCoreJ : CoreCommAt (⊤ : Subgroup ↥J) (V.subgroupOf J) rJ := by
    simpa [Subgroup.map_id] using
      coreCommAt_map_mulEquiv (MulEquiv.refl ↥J) hrJ hCore
  have hoddε : Odd (Nat.card ε.ker) :=
    Odd.of_dvd_nat hoddJ (Subgroup.card_dvd_of_le hεker)
  have hFourε : FourAt (⊤ : Subgroup Y) ((V.subgroupOf J).map ε) (ε rJ) :=
    fourAt_map_of_odd_central_ker ε hε hεker hoddε hFourJ
  have hCoreε : CoreCommAt (⊤ : Subgroup Y) ((V.subgroupOf J).map ε) (ε rJ) :=
    coreCommAt_map_of_odd_central_ker ε hε hεker hoddε hr2J hCoreJ
  have hoddψ : Odd (Nat.card ψ.ker) := odd_natCard_of_le_center_SU SUσ hψker
  obtain ⟨VU, rU, hFourU, hCoreU, hmapU, hrUε⟩ :=
    exists_fourAt_coreCommAt_comap_of_odd_central_ker ψ hψ hψker hoddψ hFourε hCoreε
  have hrU2 : rU ^ 2 = 1 := hFourU.2.2.1.2 rU hFourU.1
  have hRank : (mat SUσ m rU - 1).rank = 2 :=
    rank_eq_two_of_shortAt_of_central_cover hm hJ hoddJ ε hε hεker ψ hψ hψker
      hr1J hr2J hShort hrU2 hrUε
  obtain ⟨g, hgr, hgV⟩ := rckSU_exists_conj_suV_of_rank_two hm hFourU hCoreU hRank
  refine ⟨hrJ, g, ?_, ?_⟩
  · rw [← hgr]
    exact hrUε.symm
  · calc (V.subgroupOf J).map ε = VU.map ψ := hmapU.symm
      _ = ((suV hm).map (MulAut.conj g).toMonoidHom).map ψ := by rw [hgV]
      _ = (suV hm).map (ψ.comp (MulAut.conj g).toMonoidHom) := by rw [Subgroup.map_map]

theorem rckSU_exists_conj_suV_of_cover {X : Type} [Group X] [Finite X] {m : ℕ} (hm : 4 ≤ m)
    {J V : Subgroup X} {r : X} (ψ : SUG m →* X) (hψ : ψ.range = J)
    (hψker : ψ.ker ≤ Subgroup.center (SUG m))
    (hFour : FourAt J V r) (hCore : CoreCommAt J V r) (hShort : ShortAt J r) :
    ∃ g : SUG m, r = ψ (g * suR hm * g⁻¹) ∧
      V = (suV hm).map (ψ.comp (MulAut.conj g).toMonoidHom) := by
  have hAdm : StatedLieAdmissible .PSU m 2 1 :=
    ⟨Nat.prime_two, le_rfl, by omega, by intro h; have := (Prod.mk.inj h).1; omega⟩
  have hQ := isQuasisimple_SU rckSU_suF_card (by omega : 3 ≤ m) hAdm.2.2.2
  let ψ' : SUG m →* ↥J := ψ.codRestrict J (fun x => by
    rw [← hψ]
    exact ⟨x, rfl⟩)
  have hψ'surj : Function.Surjective ψ' := by
    intro j
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp (by rw [hψ]; exact j.2)
    exact ⟨x, Subtype.ext hx⟩
  have hψ'ker_eq : ψ'.ker = ψ.ker := by
    ext x
    constructor
    · intro hx
      exact congrArg Subtype.val hx
    · intro hx
      exact Subtype.ext hx
  have hψ'ker : ψ'.ker ≤ Subgroup.center (SUG m) := by
    rw [hψ'ker_eq]
    exact hψker
  have hJperf : Group.IsPerfect ↥J :=
    @Group.IsPerfect.ofSurjective (SUG m) ↥J _ _ ψ' hQ.1 hψ'surj
  have hle : (Subgroup.center ↥J).comap ψ' ≤ Subgroup.center (SUG m) := by
    intro x hx
    exact @mem_center_of_map_mem_center (SUG m) ↥J _ _ ψ' hψ'ker hQ.1 x hx
  have hoddJ : Odd (Nat.card (Subgroup.center ↥J)) := by
    have hodd := odd_natCard_of_le_center_SU SUσ hle
    have hmap : ((Subgroup.center ↥J).comap ψ').map ψ' = Subgroup.center ↥J :=
      Subgroup.map_comap_eq_self_of_surjective (f := ψ') hψ'surj _
    have hcard : Nat.card (Subgroup.center ↥J) =
        Nat.card (((Subgroup.center ↥J).comap ψ').map ψ') := by rw [hmap]
    have hdvd : Nat.card (Subgroup.center ↥J) ∣
        Nat.card ((Subgroup.center ↥J).comap ψ') := by
      rw [hcard]
      exact Subgroup.card_map_dvd _ ψ'
    exact Odd.of_dvd_nat hodd hdvd
  have hidker : (MonoidHom.id ↥J).ker ≤ Subgroup.center ↥J := by
    intro z hz
    rw [MonoidHom.mem_ker] at hz
    have hz1 : z = 1 := hz
    rw [hz1]
    exact Subgroup.one_mem _
  obtain ⟨hrJ, g, hεr, hVeq⟩ :=
    rckSU_exists_conj_suV_of_central_cover hm hJperf hoddJ (MonoidHom.id ↥J)
      Function.surjective_id hidker ψ' hψ'surj hψ'ker hFour hCore hShort
  have hsub : J.subtype.comp ψ' = ψ := MonoidHom.ext fun x => rfl
  refine ⟨g, ?_, ?_⟩
  · have h1 : (⟨r, hrJ⟩ : ↥J) = ψ' (g * suR hm * g⁻¹) := hεr
    exact congrArg Subtype.val h1
  · calc V = (V.subgroupOf J).map J.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hFour.2.1).symm
      _ = ((V.subgroupOf J).map (MonoidHom.id ↥J)).map J.subtype := by simp
      _ = ((suV hm).map (ψ'.comp (MulAut.conj g).toMonoidHom)).map J.subtype := by rw [hVeq]
      _ = (suV hm).map (J.subtype.comp (ψ'.comp (MulAut.conj g).toMonoidHom)) := by
          rw [Subgroup.map_map]
      _ = (suV hm).map (ψ.comp (MulAut.conj g).toMonoidHom) := by
          rw [← MonoidHom.comp_assoc, hsub]

end Short

end CFSG.StandardType.RCKC1
