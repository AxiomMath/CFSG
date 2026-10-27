module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyProof
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiftyFiveStepD
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyFourFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyOneProof
public import CFSG.Quasithin.H13.ZCentLieExc
public import CFSG.LocalAnalysis.GL83PartI.I713.ExceptionalCoprime
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U34FiveResidualHolds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.SU3
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped Pointwise Matrix commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem isCyclic_outer_of_isU3_two {Y : Type} [Group Y] (h : IsU3 Y 2) :
    IsCyclic (Outer Y) := by
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := (h.statedClassicalModel (by decide)).2
  letI : Field K := hKf
  have : Finite K := hKfin
  have hn1 : 1 ≤ 2 := by norm_num
  have hcard : Nat.card K = 2 ^ (2 * 2) := by
    rw [hKcard]
    norm_num
  have hdata : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 2 K :=
    ⟨Nat.prime_two, hn1, hcard⟩
  have hcyc : IsCyclic (Outer (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU hdata 3)) :=
    CFSG.ClassicalInvolution.Nobq.isCyclic_outer_unitaryPSU_of_gcd_eq_one hdata
      (n := 3) (by norm_num) (by decide) (by decide)
  exact GL83.I713.isCyclic_outer_congr
    (e.trans (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hdata (n := 3) (by norm_num)).symm)

theorem exists_scalar_of_centralizer_natImage_statedSU {K : Type} [Field K] [Finite K]
    [CharP K 2] (hK : Nat.card K = 16) {g : MulAut (StdMod (Fin 3) K)}
    (hg : ∀ γ : ↥(StatedSU 3 4 K), g * natAut (StatedSU 3 4 K) γ =
      natAut (StatedSU 3 4 K) γ * g) :
    ∃ c : K, ∀ v : Fin 3 → K, toAddMap g v = c • v := by
  have hsc : HasScalarCommutant (StatedSU 3 4 K) :=
    CFSG.Quasithin.H.SU3.hasScalarCommutant (K := K) (q := 4)
      (by rw [hK]; norm_num) (by norm_num)
  refine hsc { toFun := toAddMap g, map_zero' := toAddMap_zero g, map_add' := toAddMap_add g }
    ?_
  intro γ hγ v
  change toAddMap g (γ *ᵥ v) = γ *ᵥ toAddMap g v
  have hcomm := congrArg (fun φ : MulAut (StdMod (Fin 3) K) => toAddMap φ v)
    (hg ⟨γ, hγ⟩)
  simpa only [toAddMap_mul, toAddMap_natAut] using hcomm

theorem no_involution_centralizer_natImage_statedSU {K : Type} [Field K] [Finite K]
    [CharP K 2] (hK : Nat.card K = 16) {g : MulAut (StdMod (Fin 3) K)}
    (hg : ∀ γ : ↥(StatedSU 3 4 K), g * natAut (StatedSU 3 4 K) γ =
      natAut (StatedSU 3 4 K) γ * g)
    (hg2 : g ^ 2 = 1) : g = 1 := by
  obtain ⟨c, hc⟩ := exists_scalar_of_centralizer_natImage_statedSU hK hg
  have hcc : c * c = 1 := by
    have h1 := hc (Pi.single 0 1)
    have hgg : g * g = 1 := by rw [← pow_two]; exact hg2
    have h2 : toAddMap g (toAddMap g (Pi.single 0 1)) = Pi.single 0 1 := by
      rw [← toAddMap_mul, hgg, toAddMap_one]
    have h2' : toAddMap g (c • Pi.single 0 1) = Pi.single 0 1 := by rwa [h1] at h2
    have h3 : c • (c • (Pi.single 0 1 : Fin 3 → K)) = Pi.single 0 1 := by
      rw [← hc (c • Pi.single 0 1)]
      exact h2'
    have h4 := congrFun h3 0
    simpa [Pi.single_eq_same, smul_eq_mul] using h4
  have hc1 : c = 1 := CFSG.Quasithin.H.SU3.eq_one_of_mul_self_eq_one hcc
  refine toAddMap_injective fun v => ?_
  rw [hc v, hc1, toAddMap_one, one_smul]

theorem five_dvd_card_inf_normalizer_of_isSU3_two
    {L U : Subgroup G} (hSU3 : IsSU3 (Bar2 L) 2)
    (hSyl : CFSG.QuasithinUnique.IsSylowTwoOf U L) :
    5 ∣ Nat.card ↥(L ⊓ Subgroup.normalizer (U : Set G)) := by
  have hSU3bar : IsSU3 (borelQuotL L) 2 := isSU3_LBar hSU3
  have hperf : Group.IsPerfect ↥(borelQuotL L) := Group.IsPerfect.mk hSU3bar.1.1
  have hPSU : CFSG.Quasithin.IsPSU 3 2 2
      (↥(borelQuotL L) ⧸ Subgroup.center ↥(borelQuotL L)) :=
    (CFSG.Blueprint.LieModel.classical_iff (by decide)).1 hSU3bar.2
  have hUbar : CFSG.QuasithinUnique.IsSylowTwoOf (borelQuotU L U) (borelQuotL L) :=
    isSylowTwoOf_map_borelQuotPi hSyl
  obtain ⟨hZ, hcard, -, -, -⟩ :=
    CFSG.Quasithin.H13.P31X.u3BorelFacts_holds 2 (by norm_num) (borelQuotY L)
      (borelQuotL L) (borelQuotU L U) hperf hPSU hUbar
  have hZ1 : Nat.card (Subgroup.center ↥(borelQuotL L)) = 1 := by
    have h : Nat.card (Subgroup.center ↥(borelQuotL L)) ∣ 1 := by
      rwa [show Nat.gcd 3 (2 ^ 2 + 1) = 1 from by norm_num] at hZ
    exact Nat.dvd_one.mp h
  have hBeq : Nat.card ↥(borelQuotL L ⊓
      Subgroup.normalizer (borelQuotU L U : Set (borelQuotY L))) =
      Nat.card ↥(borelQuotU L U) * (4 ^ 2 - 1) := by
    simpa [hZ1] using hcard
  have hB5 : 5 ∣ Nat.card ↥(borelQuotL L ⊓
      Subgroup.normalizer (borelQuotU L U : Set (borelQuotY L))) := by
    rw [hBeq]
    exact Dvd.dvd.mul_left (by norm_num : 5 ∣ 4 ^ 2 - 1) _
  exact hB5.trans (card_inf_normalizer_bar2_dvd hSyl)

theorem conj_mem_inf_T_cStar_of_pCore_le (D : Data G) (L : Subgroup G)
    (hNL : D.M ≤ normalizer (L : Set G)) (hO2C : pCoreOf 2 L ≤ cStar1755 D L hNL)
    (hO2T : pCoreOf 2 L ≤ D.T) {y z : G} (hyL : y ∈ L)
    (hz : z ∈ D.T ⊓ cStar1755 D L hNL) :
    y * z * y⁻¹ ∈ D.T ⊓ cStar1755 D L hNL := by
  have hzT : z ∈ D.T := hz.1
  have hzC : z ∈ cStar1755 D L hNL := hz.2
  have hzM : z ∈ D.M := D.sylowM.le hzT
  have hzN : z ∈ normalizer (L : Set G) := hNL hzM
  have hρz : (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL L).comp
      (Subgroup.inclusion hNL) ⟨z, hzM⟩ = 1 := by
    obtain ⟨z', hz'ker, hz'val⟩ := Subgroup.mem_map.1 hzC
    have hz'eq : z' = ⟨z, hzM⟩ := Subtype.ext hz'val
    rw [MonoidHom.mem_ker] at hz'ker
    rwa [hz'eq] at hz'ker
  have hρz' : CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL L ⟨z, hzN⟩ = 1 := by
    have hincl : Subgroup.inclusion hNL ⟨z, hzM⟩ = ⟨z, hzN⟩ := Subtype.ext rfl
    simpa [MonoidHom.comp_apply, hincl] using hρz
  have hcomm : z * y * z⁻¹ * y⁻¹ ∈ pCoreOf 2 L :=
    (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL_fix_iff L ⟨z, hzN⟩ ⟨y, hyL⟩).1
      (by rw [hρz']; rfl)
  have hcomm' : y * z * y⁻¹ * z⁻¹ ∈ pCoreOf 2 L := by
    have := (pCoreOf 2 L).inv_mem hcomm
    simpa [mul_assoc] using this
  have hyzy : y * z * y⁻¹ = (y * z * y⁻¹ * z⁻¹) * z := by group
  rw [hyzy]
  exact Subgroup.mem_inf.mpr
    ⟨D.T.mul_mem (hO2T hcomm') hzT, (cStar1755 D L hNL).mul_mem (hO2C hcomm') hzC⟩

theorem exists_torus_mem_Q0_of_dvd_card (D : Data G) {L : Subgroup G} (hLM : L ≤ D.M)
    (hNL : D.M ≤ normalizer (L : Set G)) {p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ Nat.card ↥(L ⊓ Subgroup.normalizer ((L ⊓ D.T : Subgroup G) : Set G))) :
    ∃ h ∈ L ⊓ Q0_1755 D L hNL, orderOf h = p := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, -, hO2, -, -, -, -, -, -, -⟩ := cStar_T0_Q0_facts_1755 D hLM hNL
  obtain ⟨hO2C, hO2T⟩ := le_inf_iff.1 hO2
  obtain ⟨y, hyord⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(L ⊓ Subgroup.normalizer ((L ⊓ D.T : Subgroup G) : Set G))) p hdvd
  have hyL : (y : G) ∈ L := y.2.1
  have hyNT : (y : G) ∈ normalizer ((D.T ⊓ L : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have hy' : ∀ w : G, w ∈ (L ⊓ D.T : Subgroup G) ↔
        (y : G) * w * (y : G)⁻¹ ∈ (L ⊓ D.T : Subgroup G) :=
      Subgroup.mem_normalizer_iff.1 y.2.2
    constructor
    · rintro ⟨hzT, hzL⟩
      obtain ⟨h1, h2⟩ := (hy' z).1 ⟨hzL, hzT⟩
      exact ⟨h2, h1⟩
    · rintro ⟨hzT, hzL⟩
      obtain ⟨h1, h2⟩ := (hy' z).2 ⟨hzL, hzT⟩
      exact ⟨h2, h1⟩
  have hyNC : (y : G) ∈ normalizer ((D.T ⊓ cStar1755 D L hNL : Subgroup G) : Set G) := by
    have hkey : ∀ w : G, w ∈ D.T ⊓ cStar1755 D L hNL →
        (y : G) * w * (y : G)⁻¹ ∈ D.T ⊓ cStar1755 D L hNL := fun w hw =>
      conj_mem_inf_T_cStar_of_pCore_le D L hNL hO2C hO2T hyL hw
    have hkey' : ∀ w : G, w ∈ D.T ⊓ cStar1755 D L hNL →
        (y : G)⁻¹ * w * ((y : G)⁻¹)⁻¹ ∈ D.T ⊓ cStar1755 D L hNL := fun w hw =>
      conj_mem_inf_T_cStar_of_pCore_le D L hNL hO2C hO2T (L.inv_mem hyL) hw
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · exact hkey w
    · intro hw
      have h := hkey' ((y : G) * w * (y : G)⁻¹) hw
      simpa [mul_assoc] using h
  have hyT0 : (y : G) ∈ normalizer (T0_1755 D L hNL : Set G) := by
    rw [T0_eq_sup_1755 D hLM hNL]
    exact Subgroup.inf_normalizer_le_normalizer_sup (D.T ⊓ L)
      (D.T ⊓ cStar1755 D L hNL) ⟨hyNT, hyNC⟩
  have hyQ0 : (y : G) ∈ Q0_1755 D L hNL :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_left hyL, hyT0⟩
  exact ⟨(y : G), Subgroup.mem_inf.mpr ⟨hyL, hyQ0⟩, by
    rw [Subgroup.orderOf_coe, hyord]⟩

theorem exists_torus_mem_Q0_of_isSU3_two
    (D : Data G) {L : Subgroup G} (hLM : L ≤ D.M)
    (hNL : D.M ≤ normalizer (L : Set G)) (hSU3 : IsSU3 (Bar2 L) 2)
    (hSyl : CFSG.QuasithinUnique.IsSylowTwoOf (L ⊓ D.T) L) :
    ∃ h ∈ L ⊓ Q0_1755 D L hNL, orderOf h = 5 :=
  exists_torus_mem_Q0_of_dvd_card D hLM hNL (by norm_num)
    (five_dvd_card_inf_normalizer_of_isSU3_two hSU3 hSyl)

theorem u34FiveScalar_le_centralizer_statedSU {K : Type} [Field K] [Finite K] :
    u34FiveScalar K ≤ Subgroup.centralizer (natImage (StatedSU 3 4 K) : Set _) := by
  intro z hz
  have hzScal : z ∈ natImage (StatedScalars (Fin 3) K) :=
    CFSG.LieType.BorelTits.pCoreOf_le 5 _ hz
  obtain ⟨s, hs, hsz⟩ := by rwa [natImage_eq_map] at hzScal
  obtain ⟨u, rfl⟩ := hs
  rw [← hsz]
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  obtain ⟨t, ht, rfl⟩ := by rwa [natImage_eq_map] at hw
  rw [← map_mul, ← map_mul]
  rw [Matrix.GeneralLinearGroup.scalar_commute]

theorem eq_one_of_mem_centralizer_barSub_of_sq_eq_one {W : Type} [CommGroup W] [Finite W]
    {X : Subgroup (MulAut W)} (S : CNatModStructSU3 W X 2)
    {g : MulAut W} (hg : g ∈ Subgroup.centralizer (X : Set (MulAut W)))
    (hg2 : g ^ 2 = 1) : g = 1 := by
  let e := su3NatEquiv S
  have hK : Nat.card S.K = 16 := by
    have h := S.cardK
    norm_num at h ⊢
    exact h
  have : CharP S.K 2 := charP_cardK S
  have hge : ∀ γ : ↥(StatedSU 3 4 S.K),
      MulAut.congr e g * natAut (StatedSU 3 4 S.K) γ =
        natAut (StatedSU 3 4 S.K) γ * MulAut.congr e g := by
    intro γ
    have hγ : natAut (StatedSU 3 4 S.K) γ ∈ natImageX S := by
      rw [natImageX_eq S]
      exact ⟨γ, rfl⟩
    obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.mp hγ
    have hxeq' : MulAut.congr e x = natAut (StatedSU 3 4 S.K) γ := hxeq
    have hgx : x * g = g * x := Subgroup.mem_centralizer_iff.1 hg x hx
    calc MulAut.congr e g * natAut (StatedSU 3 4 S.K) γ
        = MulAut.congr e g * MulAut.congr e x := by rw [hxeq']
      _ = MulAut.congr e (g * x) := by rw [map_mul]
      _ = MulAut.congr e (x * g) := by rw [hgx]
      _ = MulAut.congr e x * MulAut.congr e g := by rw [map_mul]
      _ = natAut (StatedSU 3 4 S.K) γ * MulAut.congr e g := by rw [hxeq']
  have hge2 : (MulAut.congr e g) ^ 2 = 1 := by
    rw [← map_pow, hg2, map_one]
  have hone : MulAut.congr e g = 1 :=
    no_involution_centralizer_natImage_statedSU hK hge hge2
  exact (MulAut.congr e).injective (by rw [hone, map_one])

theorem cStar_le_M (D : Data G) (L : Subgroup G)
    (hNL : D.M ≤ normalizer (L : Set G)) : cStar1755 D L hNL ≤ D.M :=
  Subgroup.map_subtype_le _

theorem cStar_le_normalizer_inf_T_L (D : Data G) {L : Subgroup G} (hLM : L ≤ D.M)
    (hNL : D.M ≤ normalizer (L : Set G)) :
    cStar1755 D L hNL ≤ normalizer ((D.T ⊓ L : Subgroup G) : Set G) := by
  intro c hc
  obtain ⟨-, -, hO2, -, -, -, -, -, -, -⟩ := cStar_T0_Q0_facts_1755 D hLM hNL
  obtain ⟨hO2C, hO2T⟩ := le_inf_iff.1 hO2
  have hcM : c ∈ D.M := cStar_le_M D L hNL hc
  have hρc : CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL L ⟨c, hNL hcM⟩ = 1 := by
    obtain ⟨z', hz'ker, hz'val⟩ := Subgroup.mem_map.1 hc
    have hz'eq : z' = ⟨c, hcM⟩ := Subtype.ext hz'val
    rw [MonoidHom.mem_ker] at hz'ker
    rw [hz'eq] at hz'ker
    have hincl : Subgroup.inclusion hNL ⟨c, hcM⟩ = ⟨c, hNL hcM⟩ := Subtype.ext rfl
    rwa [MonoidHom.comp_apply, hincl] at hz'ker
  have hmap : (D.T ⊓ L).map (MulAut.conj c).toMonoidHom ≤ D.T ⊓ L := by
    rintro _ ⟨t, ht, rfl⟩
    change c * t * c⁻¹ ∈ D.T ⊓ L
    obtain ⟨htT, htL⟩ := ht
    have hcommO2 : c * t * c⁻¹ * t⁻¹ ∈ pCoreOf 2 L :=
      (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL_fix_iff L
        ⟨c, hNL hcM⟩ ⟨t, htL⟩).1 (by rw [hρc]; rfl)
    have heq : c * t * c⁻¹ = (c * t * c⁻¹ * t⁻¹) * t := by group
    rw [heq]
    exact ⟨D.T.mul_mem (hO2T hcommO2) htT,
      L.mul_mem (CFSG.LieType.BorelTits.pCoreOf_le 2 L hcommO2) htL⟩
  have hcard : Nat.card ↥((D.T ⊓ L).map (MulAut.conj c).toMonoidHom) = Nat.card ↥(D.T ⊓ L) :=
    Subgroup.card_map_of_injective (MulAut.conj c).injective
  exact CFSG.RankThree.GroupTheory.SteinbergBY.mem_normalizer_of_map_conj_eq
    (Subgroup.eq_of_le_of_card_ge hmap (by rw [hcard]))

theorem simpleGroup_and_center_bot_bar2_of_ctx17_40
    {D : Data G} {V L : Subgroup G} {n : ℕ} (c : Ctx17_40 D ⊥ V L n)
    (h35 : R17_35At D ⊥ V) :
    IsSimpleGroup (Bar2 L) ∧ Subgroup.center (Bar2 L) = ⊥ := by
  have hn : n = 2 := n_eq_two_of_ctx17_40 c h35
  have hU3q : IsU3 ((Bar2 L) ⧸ Subgroup.center (Bar2 L)) n := c.ctx.shape.2
  have hU3q2 : IsU3 ((Bar2 L) ⧸ Subgroup.center (Bar2 L)) 2 := hn ▸ hU3q
  have hZ : Subgroup.center (Bar2 L) = ⊥ :=
    uc22s13xc_center_eq_bot_of_isU3_quot (n := 2) c.ctx.mem_calC.2.2
      (by norm_num) hU3q2
  have hsimpleQuot : IsSimpleGroup ((Bar2 L) ⧸ Subgroup.center (Bar2 L)) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hU3q
  refine ⟨?_, hZ⟩
  exact CFSG.ABGLocalTools.isSimpleGroup_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm

theorem mem_cStar_of_centralizes_barSub (D : Data G) {V : Subgroup G}
    (hV : IsElemAbelian 2 V) (hMs : D.M ≤ stabTil (⊥ : Subgroup G) V)
    {L : Subgroup G} (hLM : L ≤ D.M) (hNL : D.M ≤ normalizer (L : Set G))
    (hsimple : IsSimpleGroup (Bar2 L))
    (h2 : barSub (⊥ : Subgroup G) V hV (pCoreOf 2 L) = ⊥)
    (hL1 : barSub (⊥ : Subgroup G) V hV L ≠ ⊥)
    {m : G} (hm : m ∈ D.M)
    (hcomm : actTil (⊥ : Subgroup G) V hV ⟨m, hMs hm⟩ ∈
      Subgroup.centralizer
        (barSub (⊥ : Subgroup G) V hV L : Set (MulAut (Vtil (⊥ : Subgroup G) V hV)))) :
    m ∈ cStar1755 D L hNL := by
  refine (actTil_mem_centralizer_iff_1755 D hV hMs hLM hNL hsimple h2 hL1 hm).2 ?_
  intro l hl
  exact (Subgroup.mem_centralizer_iff.1 hcomm l hl).symm

theorem not_isCyclic_of_isSylowOf_Q0_of_isU3_two (D : Data G) {V : Subgroup G}
    (hV : IsElemAbelian 2 V) (hMs : D.M ≤ stabTil (⊥ : Subgroup G) V)
    {L : Subgroup G} (hLM : L ≤ D.M) (hNL : D.M ≤ normalizer (L : Set G))
    (hU3 : IsU3 (barSub (⊥ : Subgroup G) V hV L) 2)
    (hsimple : IsSimpleGroup (Bar2 L))
    (h2 : barSub (⊥ : Subgroup G) V hV (pCoreOf 2 L) = ⊥)
    (hL1 : barSub (⊥ : Subgroup G) V hV L ≠ ⊥)
    (htor : ∃ x ∈ L ⊓ Q0_1755 D L hNL, orderOf x = 5)
    {c : MulAut (Vtil (⊥ : Subgroup G) V hV)}
    (hcQ : c ∈ barSub (⊥ : Subgroup G) V hV (Q0_1755 D L hNL))
    (hc1 : c ≠ 1) (hcp : c ^ 5 = 1)
    (hcL : ∀ l ∈ barSub (⊥ : Subgroup G) V hV L, c * l = l * c)
    {S : Subgroup G} (hS : CFSG.ABGLocalTools.IsSylowOf 5 S (Q0_1755 D L hNL)) :
    ¬ IsCyclic ↥S := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcOrd : orderOf c = 5 := orderOf_eq_prime hcp hc1
  obtain ⟨x, hxLQ, hxord⟩ := htor
  have hxL : x ∈ L := hxLQ.1
  have hxQ : x ∈ Q0_1755 D L hNL := hxLQ.2
  obtain ⟨-, -, -, -, -, -, -, -, hQM, -⟩ := cStar_T0_Q0_facts_1755 D hLM hNL
  have hxM : x ∈ D.M := hQM hxQ
  have hxp : x ^ 5 = 1 := by rw [← hxord]; exact pow_orderOf_eq_one x
  have hxbarNe : actTil (⊥ : Subgroup G) V hV ⟨x, hMs hxM⟩ ≠ 1 := by
    intro h1
    have hxO2 : x ∈ pCoreOf 2 L :=
      mem_pCoreOf_of_actTil_eq_one_of_isSimpleGroup hV (hLM.trans hMs) h2 hsimple hL1
        hxL (hMs hxM) h1
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) ⟨x, hxO2⟩
    have hk' : x ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have hdvd2 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have hdvdp : 5 ∣ 2 ^ k := by rwa [hxord] at hdvd2
    have hcop : Nat.Coprime 5 (2 ^ k) :=
      (by norm_num : Nat.Coprime 5 2).pow_right k
    exact absurd (Nat.Coprime.eq_one_of_dvd hcop hdvdp) (by norm_num)
  have hxbarOrd : orderOf (actTil (⊥ : Subgroup G) V hV ⟨x, hMs hxM⟩) = 5 := by
    refine orderOf_eq_prime ?_ hxbarNe
    rw [← map_pow]
    have hstp : (⟨x, hMs hxM⟩ : stabTil (⊥ : Subgroup G) V) ^ 5 = 1 := Subtype.ext hxp
    rw [hstp, map_one]
  have hxbarMemQ : actTil (⊥ : Subgroup G) V hV ⟨x, hMs hxM⟩ ∈
      barSub (⊥ : Subgroup G) V hV (Q0_1755 D L hNL) :=
    actTil_mem_barSub (⊥ : Subgroup G) V hV hxQ (hMs hxM)
  set A : Subgroup (MulAut (Vtil (⊥ : Subgroup G) V hV)) :=
    Subgroup.zpowers (actTil (⊥ : Subgroup G) V hV ⟨x, hMs hxM⟩) with hA
  set B : Subgroup (MulAut (Vtil (⊥ : Subgroup G) V hV)) := Subgroup.zpowers c with hB
  have hcCent : c ∈ Subgroup.centralizer (barSub (⊥ : Subgroup G) V hV L : Set _) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hcL y hy).symm
  have hBA : B ≤ Subgroup.centralizer (A : Set (MulAut (Vtil (⊥ : Subgroup G) V hV))) := by
    refine Subgroup.zpowers_le.mpr ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyL : y ∈ barSub (⊥ : Subgroup G) V hV L :=
      (Subgroup.zpowers_le.mpr (actTil_mem_barSub (⊥ : Subgroup G) V hV hxL (hMs hxM))) hy
    exact (hcL y hyL).symm
  have hxp_bar : (actTil (⊥ : Subgroup G) V hV ⟨x, hMs hxM⟩) ^ 5 = 1 := by
    rw [← map_pow]
    have hstp : (⟨x, hMs hxM⟩ : stabTil (⊥ : Subgroup G) V) ^ 5 = 1 := Subtype.ext hxp
    rw [hstp, map_one]
  have hEel : IsElementaryAbelian 5 ↥(A ⊔ B) := by
    have : IsElementaryAbelian 5 ↥A := IsElementaryAbelian.zpowers_of_pow_eq_one hxp_bar
    have : IsElementaryAbelian 5 ↥B := IsElementaryAbelian.zpowers_of_pow_eq_one hcp
    exact IsElementaryAbelian.sup_of_le_centralizer hBA
  have hcommAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
    intro a ha b hb
    have haL : a ∈ barSub (⊥ : Subgroup G) V hV L :=
      (Subgroup.zpowers_le.mpr (actTil_mem_barSub (⊥ : Subgroup G) V hV hxL (hMs hxM))) ha
    have hbCent : b ∈ Subgroup.centralizer (barSub (⊥ : Subgroup G) V hV L : Set _) :=
      (Subgroup.zpowers_le.mpr hcCent) hb
    exact Subgroup.mem_centralizer_iff.1 hbCent a haL
  have hinf : A ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    have hyL : y ∈ barSub (⊥ : Subgroup G) V hV L :=
      (Subgroup.zpowers_le.mpr (actTil_mem_barSub (⊥ : Subgroup G) V hV hxL (hMs hxM))) hy.1
    have hyCent : y ∈ Subgroup.centralizer (barSub (⊥ : Subgroup G) V hV L : Set _) :=
      (Subgroup.zpowers_le.mpr hcCent) hy.2
    have hyCenter : (⟨y, hyL⟩ : ↥(barSub (⊥ : Subgroup G) V hV L)) ∈
        Subgroup.center ↥(barSub (⊥ : Subgroup G) V hV L) := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.1 hyCent (g : _) g.2
    rw [center_eq_bot_of_isU3 hU3, Subgroup.mem_bot] at hyCenter
    exact congrArg Subtype.val hyCenter
  have hcardAB := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A B hcommAB).1
  have hcardA : Nat.card ↥A = 5 := by rw [hA, Nat.card_zpowers, hxbarOrd]
  have hcardB : Nat.card ↥B = 5 := by rw [hB, Nat.card_zpowers, hcOrd]
  have hcardInf : Nat.card ↥(A ⊓ B) = 1 := by rw [hinf]; simp
  have hcardE : Nat.card ↥(A ⊔ B) = 5 ^ 2 := by
    rw [hcardA, hcardB, hcardInf, mul_one] at hcardAB
    rw [hcardAB, sq]
  have : IsElementaryAbelian 5 ↥(A ⊔ B) := hEel
  have hEnc : ¬ IsCyclic ↥(A ⊔ B) :=
    CFSG.IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq hcardE
  have hEp : IsPGroup 5 ↥(A ⊔ B) := IsElementaryAbelian.isPGroup 5 ↥(A ⊔ B)
  have hE_le : A ⊔ B ≤ ((Q0_1755 D L hNL).subgroupOf
      (stabTil (⊥ : Subgroup G) V)).map (actTil (⊥ : Subgroup G) V hV) := by
    exact sup_le (Subgroup.zpowers_le.mpr hxbarMemQ) (Subgroup.zpowers_le.mpr hcQ)
  exact not_isCyclic_of_isSylowOf_of_le_map (actTil (⊥ : Subgroup G) V hV)
    (hQM.trans hMs) hS hEp hEnc hE_le

theorem pow_five_eq_one_of_mem_u34FiveScalar {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 16) {z : MulAut (StdMod (Fin 3) K)} (hz : z ∈ u34FiveScalar K) :
    z ^ 5 = 1 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hzScal : z ∈ natImage (StatedScalars (Fin 3) K) :=
    CFSG.LieType.BorelTits.pCoreOf_le 5 _ hz
  obtain ⟨s, hs, hsz⟩ := by rwa [natImage_eq_map] at hzScal
  obtain ⟨u, rfl⟩ := hs
  have hzu : z = matHom (Matrix.GeneralLinearGroup.scalar (Fin 3) u) := hsz.symm
  have hKunits : Nat.card Kˣ = 15 := by
    rw [Nat.card_units, hK]
  have hu15 : u ^ 15 = 1 := by
    have h := pow_card_eq_one' (G := Kˣ) (x := u)
    rwa [hKunits] at h
  have h15 : z ^ 15 = 1 := by
    rw [hzu, ← map_pow, ← map_pow, hu15, map_one, map_one]
  obtain ⟨k, hk⟩ :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 5 (natImage (StatedScalars (Fin 3) K)))
      ⟨z, hz⟩
  have hzk : z ^ (5 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_five).1 (orderOf_dvd_of_pow_eq_one hzk)
  have hm15 : 5 ^ m ∣ 15 := hm ▸ orderOf_dvd_of_pow_eq_one h15
  have hm1 : m ≤ 1 := by
    by_contra h
    have h2 : 25 ∣ 5 ^ m := by
      rw [show 25 = 5 ^ 2 by norm_num]
      exact pow_dvd_pow 5 (by omega)
    have : 25 ∣ 15 := h2.trans hm15
    norm_num at this
  interval_cases m
  · rw [pow_zero] at hm
    rw [orderOf_eq_one_iff] at hm
    rw [hm]
    exact one_pow 5
  · rw [pow_one] at hm
    rw [← hm]
    exact pow_orderOf_eq_one z

private theorem prime_eq_two_or_three_or_five_or_thirteen {p : ℕ} (hp : p.Prime)
    (h : p ∣ 2 ^ 8 * 3 ^ 2 * 5 ^ 3 * 13) : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 13 := by
  have h2 : p ∣ 2 ^ 8 ∨ p ∣ 3 ^ 2 ∨ p ∣ 5 ^ 3 ∨ p ∣ 13 := by
    rw [show 2 ^ 8 * 3 ^ 2 * 5 ^ 3 * 13 = 2 ^ 8 * (3 ^ 2 * (5 ^ 3 * 13)) by ring] at h
    rcases hp.dvd_mul.mp h with h | h
    · exact Or.inl h
    rcases hp.dvd_mul.mp h with h | h
    · exact Or.inr (Or.inl h)
    rcases hp.dvd_mul.mp h with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  rcases h2 with h | h | h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp (hp.dvd_of_dvd_pow h))
  · exact Or.inr (Or.inl
      ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp (hp.dvd_of_dvd_pow h)))
  · exact Or.inr (Or.inr (Or.inl
      ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp (hp.dvd_of_dvd_pow h))))
  · exact Or.inr (Or.inr (Or.inr
      ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h)))

theorem sig_eq_five_of_ctx17_40 {D : Data G} {V L : Subgroup G} {n : ℕ}
    (c : Ctx17_40 D ⊥ V L n) (h35 : R17_35At D ⊥ V)
    (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D)
    (hKU : K_U34NormalizerRanks)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D) :
    D.sig = {5} := by
  classical
  have hV := c.ctx.hyp125.isElemAbelian
  have hpf := c.ctx.hyp125.pairFacts
  have hMs : D.M ≤ stabTil (⊥ : Subgroup G) V := le_stabTil hpf.le_normalizer hpf.le_normalizer₀
  have hVin : InCalV D.M V := hyp123_inCalV c.ctx.hyp125.1
  have hTI : ¬ CFSG.CGT.Timmesfeld75.IsTI V := (twelve_nine D h127 c.ctx.hyp125).1
  obtain ⟨hS⟩ := cNatModSU3_two_of_ctx17_40 c h35 hx h61 h127 h1214
  have hLbarMbar : barSub (⊥ : Subgroup G) V hV L ≤ Mbar D.M ⊥ V hV :=
    barSub_mono (⊥ : Subgroup G) V hV c.ctx.mem_calC.1.le
  have hnormal : ((barSub (⊥ : Subgroup G) V hV L).subgroupOf (Mbar D.M ⊥ V hV)).Normal :=
    barSub_subgroupOf_mbar_normal_of_ctx17_40 c h35
  have hMbarNorm : Mbar D.M ⊥ V hV ≤
      normalizer (barSub (⊥ : Subgroup G) V hV L : Set (MulAut (Vtil (⊥ : Subgroup G) V hV))) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLbarMbar).mp hnormal
  have hImLe : (Mbar D.M ⊥ V hV).map (MulAut.congr (su3NatEquiv hS)).toMonoidHom ≤
      natNorm (StatedSU 3 4 hS.K) :=
    map_le_natNorm_of_cNatModSU3 hS hMbarNorm
  have h3not : 3 ∉ D.sig := three_not_mem_sig_of_ctx17_40 c h35 hSg
  have key : ∀ q : ℕ, q ∈ D.sig → q = 5 := by
    intro q hq
    have hqprime := (D.sig_prime q hq).1
    have hq2 := (D.sig_prime q hq).2
    have hq3 : 3 ≤ CFSG.Open.pRank q D.M := hSg.three_le q hq
    have hqMbar : 2 ≤ CFSG.Open.pRank q (Mbar D.M ⊥ V hV) := by
      have h115 := uc22p2251a_pRank_sub_one_le D h61 hVin hTI hq
      have : ((F11.CTilde D.M ⊥ V).subgroupOf D.M).Normal :=
        s15_Three_cTilde_normal hV hMs
      have heq : CFSG.pRank q (MBar D.M V) =
          CFSG.Open.pRank q (Mbar D.M ⊥ V hV) := by
        rw [UC22.pRank_mbar D.M V q, s15_Three_pRank_MBar11 hV hMs q,
          ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (Mbar D.M ⊥ V hV)]
      omega
    have hqNat : 2 ≤ CFSG.Open.pRank q (natNorm (StatedSU 3 4 hS.K)) := by
      have h1 : CFSG.Open.pRank q (Mbar D.M ⊥ V hV) ≤
          CFSG.Open.pRank q ((Mbar D.M ⊥ V hV).map
            (MulAut.congr (su3NatEquiv hS)).toMonoidHom) :=
        CFSG.SectionRank.pRank_le_map hqprime.one_lt _
          (MulAut.congr (su3NatEquiv hS)).injective _
      have h2 := CFSG.SectionRank.pRank_mono hqprime.one_lt hImLe
      omega
    have hqDvd : q ∣ Nat.card (natNorm (StatedSU 3 4 hS.K)) :=
      CFSG.GroupTheory.dvd_card_of_one_le_pRank hqprime (by omega)
    have hcardK : Nat.card hS.K = 16 := by
      have h := hS.cardK
      norm_num at h ⊢
      exact h
    have hcardNat : Nat.card (natNorm (StatedSU 3 4 hS.K)) = 2 ^ 8 * 3 ^ 2 * 5 ^ 3 * 13 :=
      (hKU hS.K hcardK).1
    have hqDvd' : q ∣ 2 ^ 8 * 3 ^ 2 * 5 ^ 3 * 13 := by rwa [hcardNat] at hqDvd
    rcases prime_eq_two_or_three_or_five_or_thirteen hqprime hqDvd' with h | h | h | h
    · exact absurd h hq2
    · exact absurd (h ▸ hq) h3not
    · exact h
    · exfalso
      have h13 : CFSG.Open.pRank 13 (natNorm (StatedSU 3 4 hS.K)) = 1 := by
        have h := (hKU hS.K hcardK).2.2.2.2
        rw [CFSG.SectionRank.pRank_coe_eq_openPRank] at h
        rwa [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (natNorm (StatedSU 3 4 hS.K))] at h
      rw [h] at hqNat
      omega
  ext q
  constructor
  · exact key q
  · intro hq
    rw [hq]
    obtain ⟨p, hp⟩ := hSg.nonempty
    rw [← key p hp]
    exact hp

theorem barSub_opp_eq_of_opp_mbar_map_eq {D : Data G} {V L : Subgroup G} {n : ℕ}
    (c : Ctx17_40 D ⊥ V L n)
    (hS : CNatModStructSU3 (Vtil (⊥ : Subgroup G) V c.ctx.hyp125.isElemAbelian)
      (barSub (⊥ : Subgroup G) V c.ctx.hyp125.isElemAbelian L) 2)
    (heq : Opp 5 ((Mbar D.M ⊥ V c.ctx.hyp125.isElemAbelian).map
        (MulAut.congr (su3NatEquiv hS)).toMonoidHom) =
      natImage (StatedSU 3 4 hS.K)) :
    barSub (⊥ : Subgroup G) V c.ctx.hyp125.isElemAbelian (Opp 5 D.M) =
      barSub (⊥ : Subgroup G) V c.ctx.hyp125.isElemAbelian L := by
  have hV := c.ctx.hyp125.isElemAbelian
  have hpf := c.ctx.hyp125.pairFacts
  have hMs : D.M ≤ stabTil (⊥ : Subgroup G) V := le_stabTil hpf.le_normalizer hpf.le_normalizer₀
  let f : MulAut (Vtil (⊥ : Subgroup G) V hV) →* MulAut (StdMod (Fin 3) hS.K) :=
    (MulAut.congr (su3NatEquiv hS)).toMonoidHom
  apply Subgroup.map_injective (f := f) (MulAut.congr (su3NatEquiv hS)).injective
  calc (barSub (⊥ : Subgroup G) V hV (Opp 5 D.M)).map f
      = (RankThree.PartOne.pElementSubgroup 5 (Mbar D.M ⊥ V hV)).map f := by
        rw [s1741_barSub_opp_eq D hV hMs]
    _ = RankThree.PartOne.pElementSubgroup 5 ((Mbar D.M ⊥ V hV).map f) :=
        s13_pElementSubgroup_map Nat.prime_five f _
    _ = natImage (StatedSU 3 4 hS.K) := heq
    _ = (barSub (⊥ : Subgroup G) V hV L).map f := (natImageX_eq hS).symm

theorem barSub_eq_opp_five_of_ctx17_40
    {D : Data G} {V L : Subgroup G} {n : ℕ} (c : Ctx17_40 D ⊥ V L n)
    (h35 : R17_35At D ⊥ V)
    (h1 : ∀ (hV : Hyp125 D ⊥ V), R17_1At D ⊥ V hV)
    (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D)
    (hKU : K_U34NormalizerRanks) (hKFR : K_U34FiveResidual)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D) :
    barSub (⊥ : Subgroup G) V c.ctx.hyp125.isElemAbelian L =
      barSub (⊥ : Subgroup G) V c.ctx.hyp125.isElemAbelian (Opp 5 D.M) := by
  classical
  have hV := c.ctx.hyp125.isElemAbelian
  letI : CommGroup (Vtil (⊥ : Subgroup G) V hV) :=
    QuotientGroup.Quotient.commGroup (modNull (⊥ : Subgroup G) V hV)
  have : Finite (Vtil (⊥ : Subgroup G) V hV) := inferInstance
  have hpf := c.ctx.hyp125.pairFacts
  have hMs : D.M ≤ stabTil (⊥ : Subgroup G) V := le_stabTil hpf.le_normalizer hpf.le_normalizer₀
  obtain ⟨hS⟩ := cNatModSU3_two_of_ctx17_40 c h35 hx h61 h127 h1214
  let e : Vtil (⊥ : Subgroup G) V hV ≃* StdMod (Fin 3) hS.K := su3NatEquiv hS
  have hNL : D.M ≤ normalizer (L : Set G) := by
    have hL_eq : L = UC22.conjClosure D.M L := (h35.2 L n c.ctx c.v0).2.2.2
    rw [hL_eq]
    exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyThree.le_normalizer_conjClosure
      D.M L
  have hLM : L ≤ D.M := c.ctx.mem_calC.1.le
  have hLbarMbar : barSub (⊥ : Subgroup G) V hV L ≤ Mbar D.M ⊥ V hV :=
    barSub_mono (⊥ : Subgroup G) V hV hLM
  have hnormal : ((barSub (⊥ : Subgroup G) V hV L).subgroupOf (Mbar D.M ⊥ V hV)).Normal :=
    barSub_subgroupOf_mbar_normal_of_ctx17_40 c h35
  have hMbarNorm : Mbar D.M ⊥ V hV ≤
      normalizer (barSub (⊥ : Subgroup G) V hV L : Set (MulAut (Vtil (⊥ : Subgroup G) V hV))) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLbarMbar).mp hnormal
  have hXn : (Mbar D.M ⊥ V hV).map (MulAut.congr e).toMonoidHom ≤
      natNorm (StatedSU 3 4 hS.K) :=
    map_le_natNorm_of_cNatModSU3 hS hMbarNorm
  have hcardK : Nat.card hS.K = 16 := by
    have h := hS.cardK
    norm_num at h ⊢
    exact h
  have hX : natImage (StatedSU 3 4 hS.K) ≤
      (Mbar D.M ⊥ V hV).map (MulAut.congr e).toMonoidHom := by
    have h := Subgroup.map_mono (f := (MulAut.congr e).toMonoidHom)
      (barSub_mono (⊥ : Subgroup G) V hV hLM)
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← natImageX_eq hS]
    exact h
  have hcases := @hKFR hS.K hS.fieldK hS.finiteK hcardK
    ((Mbar D.M ⊥ V hV).map (MulAut.congr e).toMonoidHom) hX hXn
  rcases hcases with hcase | hcase
  · exact (barSub_opp_eq_of_opp_mbar_map_eq c hS hcase).symm
  · by_cases hle : u34FiveScalar hS.K ≤ natImage (StatedSU 3 4 hS.K)
    · exact (barSub_opp_eq_of_opp_mbar_map_eq c hS
        (by rw [hcase, sup_eq_left.mpr hle])).symm
    · obtain ⟨z, hzFive, hzNotSU⟩ := Set.not_subset.mp hle
      have hz5 : z ^ 5 = 1 := pow_five_eq_one_of_mem_u34FiveScalar hcardK hzFive
      have hz1 : z ≠ 1 := by
        intro h
        exact hzNotSU (by rw [h]; exact Subgroup.one_mem _)
      have hzCent : z ∈ Subgroup.centralizer (natImage (StatedSU 3 4 hS.K) : Set _) :=
        u34FiveScalar_le_centralizer_statedSU hzFive
      have hzX : z ∈ (Mbar D.M ⊥ V hV).map (MulAut.congr e).toMonoidHom := by
        have hzOpp : z ∈ Opp 5 ((Mbar D.M ⊥ V hV).map
            (MulAut.congr e).toMonoidHom) := by
          rw [hcase]
          exact Subgroup.mem_sup_right hzFive
        refine (Subgroup.closure_le _).mpr ?_ hzOpp
        rintro x ⟨hx, -⟩
        exact hx
      obtain ⟨x, hxMbar, hxz⟩ := Subgroup.mem_map.mp hzX
      obtain ⟨⟨m, hms⟩, hmM, hmact⟩ := (mem_barSub (⊥ : Subgroup G) V hV D.M x).1 hxMbar
      have hmM' : m ∈ D.M := hmM
      have hxEq : actTil (⊥ : Subgroup G) V hV ⟨m, hMs hmM'⟩ = x := by
        rw [show (⟨m, hMs hmM'⟩ : stabTil (⊥ : Subgroup G) V) = ⟨m, hms⟩ from rfl]
        exact hmact
      have hfx : (MulAut.congr e) (actTil (⊥ : Subgroup G) V hV ⟨m, hMs hmM'⟩) = z := by
        rw [hxEq]
        exact hxz
      have hxCent : actTil (⊥ : Subgroup G) V hV ⟨m, hMs hmM'⟩ ∈
          Subgroup.centralizer (barSub (⊥ : Subgroup G) V hV L : Set _) := by
        rw [Subgroup.mem_centralizer_iff]
        intro l hl
        apply (MulAut.congr e).injective
        rw [map_mul, map_mul]
        have hlImg : (MulAut.congr e) l ∈ natImage (StatedSU 3 4 hS.K) := by
          have h : (MulAut.congr e) l ∈ natImageX hS :=
            Subgroup.mem_map_of_mem (MulAut.congr e).toMonoidHom hl
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← natImageX_eq hS]
          exact h
        have hcomm := Subgroup.mem_centralizer_iff.1 hzCent ((MulAut.congr e) l) hlImg
        change (MulAut.congr e) l * (MulAut.congr e) (actTil (⊥ : Subgroup G) V hV ⟨m, hMs hmM'⟩) =
          (MulAut.congr e) (actTil (⊥ : Subgroup G) V hV ⟨m, hMs hmM'⟩) * (MulAut.congr e) l
        rw [hfx]
        exact hcomm
      obtain ⟨hsimple, hZ⟩ := simpleGroup_and_center_bot_bar2_of_ctx17_40 c h35
      have h2 : barSub (⊥ : Subgroup G) V hV (pCoreOf 2 L) = ⊥ :=
        TwelveTwentyThree.barSub_pCoreOf_eq_bot_of_isSubnormal hV c.ctx.mem_calC.1
          (barSub_pCoreOf_eq_bot_of_hyp125 c.ctx.hyp125)
      have hL1 : barSub (⊥ : Subgroup G) V hV L ≠ ⊥ := barSub_ne_bot_of_ctx17_40 c h35
      have hmC : m ∈ cStar1755 D L hNL :=
        mem_cStar_of_centralizes_barSub D hV hMs hLM hNL hsimple h2 hL1 hmM' hxCent
      have hTCtilde : D.T ⊓ cStar1755 D L hNL ≤
          cStar1755 D L hNL ⊓ F11.CTilde D.M ⊥ V := by
        intro s hs
        have hsT : s ∈ D.T := hs.1
        have hsC : s ∈ cStar1755 D L hNL := hs.2
        have hsM : s ∈ D.M := D.sylowM.le hsT
        have hsCent : actTil (⊥ : Subgroup G) V hV ⟨s, hMs hsM⟩ ∈
            Subgroup.centralizer (barSub (⊥ : Subgroup G) V hV L : Set _) := by
          have h := (actTil_mem_centralizer_iff_1755 D hV hMs hLM hNL hsimple h2 hL1 hsM).1 hsC
          rw [Subgroup.mem_centralizer_iff]
          intro l hl
          exact (h l hl).symm
        have hsAct : actTil (⊥ : Subgroup G) V hV ⟨s, hMs hsM⟩ = 1 := by
          let u := actTil (⊥ : Subgroup G) V hV ⟨s, hMs hsM⟩
          change u = 1
          by_cases hu1 : u = 1
          · exact hu1
          obtain ⟨k, hk⟩ := D.sylowM.isPGroup ⟨s, hsT⟩
          have hk' : s ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
          have hmapk : u ^ (2 ^ k) = 1 := by
            rw [← map_pow]
            have hst : (⟨s, hMs hsM⟩ : stabTil (⊥ : Subgroup G) V) ^ (2 ^ k) = 1 :=
              Subtype.ext hk'
            rw [hst, map_one]
          obtain ⟨n, -, hn⟩ :=
            (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hmapk)
          have hj : orderOf (u ^ 2 ^ (n - 1)) = 2 :=
            CFSG.Quasithin.H13.ZCentLie.exists_pow_orderOf_eq_two hu1 hn
          have hw2 : (u ^ 2 ^ (n - 1)) ^ 2 = 1 := by
            have h := pow_orderOf_eq_one (u ^ 2 ^ (n - 1))
            rwa [hj] at h
          have hw1 : u ^ 2 ^ (n - 1) ≠ 1 := by
            intro h1
            rw [h1, orderOf_one] at hj
            exact (by norm_num : (2 : ℕ) ≠ 1) hj.symm
          have hwCent : u ^ 2 ^ (n - 1) ∈ Subgroup.centralizer
              (barSub (⊥ : Subgroup G) V hV L : Set _) :=
            Subgroup.pow_mem _ hsCent (2 ^ (n - 1))
          exfalso
          exact hw1 (eq_one_of_mem_centralizer_barSub_of_sq_eq_one hS hwCent hw2)
        refine Subgroup.mem_inf.mpr ⟨hsC, ?_⟩
        rw [uc22p22u_cTilde_bot]
        refine Subgroup.mem_inf.mpr ⟨hsM, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro v hv
        have h1 := (actTil_eq_one_iff (⊥ : Subgroup G) V hV ⟨s, hMs hsM⟩).1 hsAct v hv
        rw [Subgroup.mem_bot] at h1
        have h2 : s * v = v * s :=
          mul_inv_eq_one.1 (by simpa [mul_assoc, mul_inv_rev] using h1)
        exact h2.symm
      have hMc : D.M ≤ normalizer (cStar1755 D L hNL : Set G) := by
        let ρ : ↥D.M →* MulAut (Bar2 L) :=
          (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL L).comp (Subgroup.inclusion hNL)
        have hN : ρ.ker.Normal := MonoidHom.normal_ker ρ
        have h := CFSG.GroupTheory.map_subtype_le_normalizer (K := D.M) (X := ⊤) (L := ρ.ker)
          (by rw [Subgroup.normalizer_eq_top_iff.mpr hN])
        have htop : (⊤ : Subgroup ↥D.M).map D.M.subtype = D.M := by
          rw [Subgroup.map_top, Subgroup.range_subtype]
        change D.M ≤ normalizer (((((CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL L).comp
          (Subgroup.inclusion hNL)).ker).map D.M.subtype : Subgroup G) : Set G)
        simpa [Subgroup.map_top, Subgroup.range_subtype] using h
      have hN0le : cStar1755 D L hNL ⊓ F11.CTilde D.M ⊥ V ≤ cStar1755 D L hNL := inf_le_left
      have hN0norm : cStar1755 D L hNL ≤
          normalizer ((cStar1755 D L hNL ⊓ F11.CTilde D.M ⊥ V : Subgroup G) : Set G) := by
        have : ((F11.CTilde D.M ⊥ V).subgroupOf D.M).Normal :=
          s15_Three_cTilde_normal hV hMs
        have hCtN : D.M ≤ normalizer (F11.CTilde D.M ⊥ V : Set G) :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer
            (CFSG.LocalAnalysis.WeakClosure81.cTilde_le_M D.M ⊥ V)).mp
            (s15_Three_cTilde_normal hV hMs)
        have hcMle : cStar1755 D L hNL ≤ D.M := cStar_le_M D L hNL
        exact (le_inf (Subgroup.le_normalizer) (hcMle.trans hCtN)).trans
          Subgroup.inf_normalizer_le_normalizer_inf
      have hSylC : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ cStar1755 D L hNL)
          (cStar1755 D L hNL) := D.sylowM.inf_of_le_normalizer (cStar_le_M D L hNL) hMc
      have hSylN0 : CFSG.ABGLocalTools.IsSylowOf 2
          (D.T ⊓ cStar1755 D L hNL ⊓ (cStar1755 D L hNL ⊓ F11.CTilde D.M ⊥ V))
          (cStar1755 D L hNL ⊓ F11.CTilde D.M ⊥ V) :=
        hSylC.inf_of_le_normalizer hN0le hN0norm
      have hSinf : D.T ⊓ cStar1755 D L hNL ⊓
          (cStar1755 D L hNL ⊓ F11.CTilde D.M ⊥ V) = D.T ⊓ cStar1755 D L hNL :=
        inf_eq_left.mpr hTCtilde
      rw [hSinf] at hSylN0
      have hfr := UC6.frattini_of_isSylowOf hN0le hN0norm hSylN0
      have hmSupC : (⟨m, hmC⟩ : ↥(cStar1755 D L hNL)) ∈
          ((cStar1755 D L hNL ⊓ F11.CTilde D.M ⊥ V).subgroupOf (cStar1755 D L hNL)) ⊔
            ((cStar1755 D L hNL ⊓ normalizer
              (((D.T ⊓ cStar1755 D L hNL : Subgroup G) : Set G))).subgroupOf
                (cStar1755 D L hNL)) := by
        rw [← Subgroup.subgroupOf_sup hN0le inf_le_left, ← hfr]
        exact Subgroup.mem_subgroupOf.mpr hmC
      have : ((cStar1755 D L hNL ⊓ F11.CTilde D.M ⊥ V).subgroupOf
          (cStar1755 D L hNL)).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hN0le).2 hN0norm
      obtain ⟨kk, hkk, mm, hmm, hprod⟩ :=
        (Subgroup.mem_sup_of_normal_left (s := (cStar1755 D L hNL ⊓ F11.CTilde D.M ⊥ V).subgroupOf
          (cStar1755 D L hNL)) (t := (cStar1755 D L hNL ⊓ normalizer
            (((D.T ⊓ cStar1755 D L hNL : Subgroup G) : Set G))).subgroupOf
            (cStar1755 D L hNL))).1 hmSupC
      let k : G := kk
      let m' : G := mm
      have hkN0 : k ∈ cStar1755 D L hNL ⊓ F11.CTilde D.M ⊥ V := Subgroup.mem_subgroupOf.mp hkk
      have hm' : m' ∈ cStar1755 D L hNL ⊓ normalizer
          (((D.T ⊓ cStar1755 D L hNL : Subgroup G) : Set G)) := Subgroup.mem_subgroupOf.mp hmm
      have hkm' : k * m' = m := by
        have h1 := congrArg Subtype.val hprod
        simpa [k, m'] using h1
      have hkM : k ∈ D.M := (cStar_le_M D L hNL) hkN0.1
      have hkCt : k ∈ F11.CTilde D.M ⊥ V := hkN0.2
      have hkAct : actTil (⊥ : Subgroup G) V hV ⟨k, hMs hkM⟩ = 1 := by
        rw [actTil_eq_one_iff]
        intro v hv
        rw [uc22p22u_cTilde_bot] at hkCt
        have hcomm : v * k = k * v := Subgroup.mem_centralizer_iff.1 hkCt.2 v hv
        rw [Subgroup.mem_bot]
        calc k * v * k⁻¹ * v⁻¹ = (v * k) * k⁻¹ * v⁻¹ := by rw [hcomm]
          _ = 1 := by group
      have hm'C : m' ∈ cStar1755 D L hNL := hm'.1
      have hm'M : m' ∈ D.M := (cStar_le_M D L hNL) hm'C
      have hm'actEq : actTil (⊥ : Subgroup G) V hV ⟨m', hMs hm'M⟩ =
          actTil (⊥ : Subgroup G) V hV ⟨m, hMs hmM'⟩ := by
        have hprod' : (⟨m, hMs hmM'⟩ : stabTil (⊥ : Subgroup G) V) =
            ⟨k, hMs hkM⟩ * ⟨m', hMs hm'M⟩ := by
          apply Subtype.ext
          exact hkm'.symm
        rw [hprod', map_mul, hkAct, one_mul]
      have hm'Cent : actTil (⊥ : Subgroup G) V hV ⟨m', hMs hm'M⟩ ∈
          Subgroup.centralizer (barSub (⊥ : Subgroup G) V hV L : Set _) := by
        rw [hm'actEq]
        exact hxCent
      have hm'Notone : actTil (⊥ : Subgroup G) V hV ⟨m', hMs hm'M⟩ ≠ 1 := by
        intro h1
        apply hz1
        rw [← hfx, ← hm'actEq, h1, map_one]
      have hm'pow : (actTil (⊥ : Subgroup G) V hV ⟨m', hMs hm'M⟩) ^ 5 = 1 := by
        apply (MulAut.congr e).injective
        rw [map_pow, map_one]
        have hzEq : (MulAut.congr e) (actTil (⊥ : Subgroup G) V hV ⟨m', hMs hm'M⟩) = z := by
          rw [hm'actEq, hfx]
        rw [hzEq, hz5]
      have hm'NT : m' ∈ normalizer ((D.T ⊓ L : Subgroup G) : Set G) :=
        cStar_le_normalizer_inf_T_L D hLM hNL hm'C
      have hm'Q : m' ∈ Q0_1755 D L hNL := by
        refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_right hm'C, ?_⟩
        rw [T0_eq_sup_1755 D hLM hNL]
        exact Subgroup.inf_normalizer_le_normalizer_sup (D.T ⊓ L)
          (D.T ⊓ cStar1755 D L hNL) ⟨hm'NT, hm'.2⟩
      have hcQ : actTil (⊥ : Subgroup G) V hV ⟨m', hMs hm'M⟩ ∈
          barSub (⊥ : Subgroup G) V hV (Q0_1755 D L hNL) :=
        actTil_mem_barSub (⊥ : Subgroup G) V hV hm'Q (hMs hm'M)
      have hn : n = 2 := n_eq_two_of_ctx17_40 c h35
      have hSU3bar2 : IsSU3 (Bar2 L) 2 := hn ▸ c.ctx.shape
      have hU3bar : IsU3 (barSub (⊥ : Subgroup G) V hV L) 2 :=
        isU3_barSub_of_ctx17_40 c h35
      have hSylLT : CFSG.QuasithinUnique.IsSylowTwoOf (L ⊓ D.T) L := by
        have hM' : CFSG.QuasithinUnique.IsSylowTwoOf D.T D.M :=
          CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.2 D.sylowM
        have := CFSG.Quasithin.A4.isSylowTwoOf_inf_normal hM' hLM hNL
        rwa [inf_comm] at this
      obtain ⟨hh, hhLQ, hhord⟩ :=
        exists_torus_mem_Q0_of_isSU3_two D hLM hNL hSU3bar2 hSylLT
      have hnc : ∀ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 5 S (Q0_1755 D L hNL) →
          ¬ IsCyclic ↥S :=
        fun S hSyl => not_isCyclic_of_isSylowOf_Q0_of_isU3_two D hV hMs hLM hNL hU3bar hsimple h2
          hL1 ⟨hh, hhLQ, hhord⟩ hcQ hm'Notone hm'pow (fun l hl =>
            (Subgroup.mem_centralizer_iff.1 hm'Cent l hl).symm) hSyl
      obtain ⟨X, hXQ, hXp, hXexp, hXnc, hTX⟩ :=
        exists_X_1755 D hLM hNL (by norm_num) (by norm_num) hnc
      have hns : ¬ Group.IsSolvable ↥D.M :=
        CFSG.LocalAnalysis.UniquenessCase.UC6S846.not_solvable_of_mem_calC c.ctx.mem_calC
      have hsig : D.sig = {5} := sig_eq_five_of_ctx17_40 c h35 hSg hKU hx h61 h127 h1214
      have h5sig : 5 ∈ D.sig := by rw [hsig]; exact Set.mem_singleton 5
      have hstr : CFSG.RankThree.PartOne.IsStronglyPEmbedded 5 D.M :=
        CFSG.LocalAnalysis.UniquenessCase.UC6S846.sp_of_mem_sig hSg hns h5sig
      have hU3Bar2 : IsU3 (Bar2 L) 2 := by
        have hq : IsU3 ((Bar2 L) ⧸ Subgroup.center (Bar2 L)) 2 := hn ▸ c.ctx.shape.2
        have hqBot : IsU3 ((Bar2 L) ⧸ (⊥ : Subgroup (Bar2 L))) 2 :=
          CFSG.Blueprint.LieModel.of_mulEquiv
            (QuotientGroup.quotientMulEquivOfEq (G := Bar2 L) hZ) hq
        exact CFSG.Blueprint.LieModel.of_mulEquiv
          (QuotientGroup.quotientBot (G := Bar2 L)) hqBot
      have : Finite (CFSG.ComponentClassification.OuterAutomorphisms.Outer (Bar2 L)) :=
        CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22g_finite_outer (Bar2 L)
      have : IsCyclic (CFSG.ComponentClassification.OuterAutomorphisms.Outer (Bar2 L)) :=
        isCyclic_outer_of_isU3_two hU3Bar2
      obtain ⟨-, -, -, hT0T, hTT0, -, hQT0, -, hQM, -⟩ := cStar_T0_Q0_facts_1755 D hLM hNL
      have hP : InPStar D ⊥ X :=
        inPStar_of_strongly_of_le_normalizer_sup (by norm_num) (by norm_num) hstr
          (hXQ.trans hQM) hXp hXexp hXnc hT0T hTT0 (hXQ.trans hQT0) hTX
          (phi1755 D L hNL) (ker_phi_le_T0_1755 D hLM hNL)
      exfalso
      exact (h1 c.ctx.hyp125).1 X hP

theorem seventeen_forty
    {D : Data G} {V₀ V : Subgroup G}
    (h1 : ∀ (hV : Hyp125 D V₀ V), R17_1At D V₀ V hV)
    (h35 : R17_35At D V₀ V)
    (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D) :
    R17_40At D V₀ V := by
  have hKU : K_U34NormalizerRanks := Inputs1719.k_U34NormalizerRanks_holds
  have hKFR : K_U34FiveResidual := Inputs1719.k_U34FiveResidual_holds
  intro L n c
  obtain rfl : V₀ = ⊥ := c.v0
  refine ⟨?_, ?_, ?_⟩
  · exact barSub_eq_opp_five_of_ctx17_40 c h35 h1 hSg hKU hKFR hx h61 h127 h1214
  · exact isU3_barSub_of_ctx17_40 c h35
  · exact sig_eq_five_of_ctx17_40 c h35 hSg hKU hx h61 h127 h1214

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

end
