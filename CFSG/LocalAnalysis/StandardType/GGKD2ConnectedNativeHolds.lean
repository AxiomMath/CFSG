module

public import CFSG.LocalAnalysis.StandardType.GGKD2ConnectedPieces1615
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeAssemblyHolds
public import CFSG.LocalAnalysis.StandardType.GGTPNDefs
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonL2Holds
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRankOneCard
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.E6BadLift
public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151DiagDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeD4ThreeHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeE6KernelExitFacts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcAdj
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcInnerD4FixMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamChar2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInBCDCharTwo
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamTriAct
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamTriLang
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamTriMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeLinStatedInner
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeReeF4LargeRFHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeTwE6CompAct
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeTwE6Conn
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeTwSmall
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeUniInner
public import CFSG.Quasithin.Background.B1
public import CFSG.Quasithin.Background.B3Q
public import CFSG.Quasithin.Background.B3ThreeModel
public import CFSG.Quasithin.Background.B3ThreeStruct
public import CFSG.Quasithin.Background.G2Omega4PlusModule
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2CompO
public import CFSG.Quasithin.EmptyFaithful.R3c19B
public import CFSG.Quasithin.EmptyFaithful.S143FF
public import CFSG.Quasithin.EmptyFaithful.S143Final
public import CFSG.Quasithin.EmptyFaithful.S143HD
public import CFSG.Quasithin.EmptyFaithful.S143IG
public import CFSG.Quasithin.EmptyFaithful.S143JB
public import CFSG.Quasithin.EmptyFaithful.S143KO
public import CFSG.Quasithin.EmptyFaithful.S143KP
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15421
public import CFSG.RankThree.PartOne.N143.HighEvenU

public section

namespace CFSG.StandardType.KD2Pieces1615

open CFSG CFSG.Assembly CFSG.StandardType S2MathAs3_1615

private lemma ltrkna_absTag_exceptional (T : GGKacType) :
    GGK0MarkedKacIface1587.absTag T = .G2 ∨
      GGK0MarkedKacIface1587.absTag T = .F4 ∨
      GGK0MarkedKacIface1587.absTag T = .D4 ∨
      GGK0MarkedKacIface1587.absTag T = .E6 ∨
      GGK0MarkedKacIface1587.absTag T = .E7 ∨
      GGK0MarkedKacIface1587.absTag T = .E8 := by
  cases T <;> simp [GGK0MarkedKacIface1587.absTag]

private lemma ltrkna_absTag_ne_g2 (T : GGKacType) :
    GGK0MarkedKacIface1587.absTag T ≠ .G2 := by
  cases T <;> simp [GGK0MarkedKacIface1587.absTag]

private lemma ltrkna_map_center_eq {C Q : Type*} [Group C] [Group Q] (φ : C ≃* Q) :
    (Subgroup.center C).map (φ : C →* Q) = Subgroup.center Q := by
  apply le_antisymm
  · rintro q ⟨z, hz, rfl⟩
    have hz' : ∀ g : C, g * z = z * g := Subgroup.mem_center_iff.mp hz
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := φ.surjective y
    calc (φ : C →* Q) x * (φ : C →* Q) z = (φ : C →* Q) (x * z) :=
          (map_mul (φ : C →* Q) x z).symm
      _ = (φ : C →* Q) (z * x) := congrArg (φ : C →* Q) (hz' x)
      _ = (φ : C →* Q) z * (φ : C →* Q) x := map_mul (φ : C →* Q) z x
  · intro q hq
    have hq' : ∀ y : Q, y * q = q * y := Subgroup.mem_center_iff.mp hq
    refine Subgroup.mem_map.mpr ⟨φ.symm q, ?_, ?_⟩
    · rw [Subgroup.mem_center_iff]
      intro x
      apply φ.injective
      simp only [map_mul, MulEquiv.apply_symm_apply]
      exact hq' (φ x)
    · simp

private lemma ltrkna_congr_symm_apply {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (f : MulAut B) (x : A) :
    ((MulAut.congr e).symm f) x = e.symm (f (e x)) := by
  show (MulAut.congr e.symm f) x = e.symm (f (e x))
  rfl

private lemma ltrkna_card_quot_ne_360 {X : Type} [Group X]
    (hlab : GGHasLabel (⟨.A, 1, 3⟩ : LargeEvenLabel) X) : Nat.card X ≠ 360 := by
  classical
  simp only [GGHasLabel, CFSG.StandardType.LargeEvenRawDatum,
    CFSG.Assembly.LargeEvenRecipeLinear] at hlab
  obtain ⟨K, hF, hfin, hK, hQ⟩ := hlab
  letI : Field K := hF
  letI : Finite K := hfin
  obtain ⟨eK⟩ := hQ
  have hK' : Nat.card K = 2 ^ 3 := hK
  haveI : CharP K 2 := CFSG.StandardType.LayerCC.charP_two_of_natCard hK'
  have hbot : (LargeEvenScalars (Fin (1 + 1)) K).subgroupOf
      (LargeEvenSLGroup (Fin (1 + 1)) K) = ⊥ :=
    CFSG.LocalAnalysis.GLTheoremA.scalars_subgroupOf_eq_bot K
  have hQcard : Nat.card (LargeEvenProj (LargeEvenSLGroup (Fin (1 + 1)) K)) = 504 := by
    have e : LargeEvenProj (LargeEvenSLGroup (Fin (1 + 1)) K) ≃*
        (↥(LargeEvenSLGroup (Fin (1 + 1)) K)) := by
      change (↥(LargeEvenSLGroup (Fin (1 + 1)) K) ⧸
        (LargeEvenScalars (Fin (1 + 1)) K).subgroupOf (LargeEvenSLGroup (Fin (1 + 1)) K)) ≃* _
      exact (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
    rw [Nat.card_congr e.toEquiv]
    change Nat.card (↥(LargeEvenSLGroup (Fin 2) K)) = 504
    rw [Nat.card_congr (CFSG.LocalAnalysis.GLTheoremA.lsEquiv K).toEquiv,
      CFSG.StandardType.ggSL2_card K, hK]
    norm_num
  have hcard : Nat.card X = 504 := by
    rw [Nat.card_congr eK.toEquiv]
    convert hQcard using 2 <;> rfl
  rw [hcard]
  norm_num

private lemma ltrkna_map_eq_of_le_of_injective {G : Type*} [Group G] {H : Subgroup G}
    (f : G →* G) (hf : Function.Injective f) [Finite ↥H] (h : H.map f ≤ H) :
    H.map f = H :=
  Subgroup.eq_of_le_of_card_ge h (by rw [Subgroup.card_map_of_injective hf])

theorem connectedNativeAction_holds :
    ConnectedNativeAction := by
  intro Omega _ _ _ lab R _ I phi rho j hqs g hg hpres hlab
  let C : Subgroup R := E6Centralizer1585.component rho j
  let Q : Subgroup (CFSG.Blueprint.Chevalley.ModGL rho.tau Omega) :=
    CFSG.HardMathSupport.Timmesfeld.LangTorus.rationalComponent rho.setup.ρ rho.setup.Γ
      (CFSG.LieType.AlgebraicGroups.rootCharHom rho.a) (rho.repr j)
  have hCQ : C = Q.comap rho.iota := rfl
  haveI hfinModel : Finite ↥rho.setup.D.model := rho.setup.finite
  have hQle : Q ≤ rho.setup.Γ := by
    simp only [Q, CFSG.HardMathSupport.Timmesfeld.LangTorus.rationalComponent,
      CFSG.HardMathSupport.Timmesfeld.LangTorus.rationalSpan]
    exact (Subgroup.commutator_le_self _).trans inf_le_right
  have hQmodel : Q ≤ rho.setup.D.model := by
    refine hQle.trans ?_
    show ⁅rho.setup.D.model, rho.setup.D.model⁆ ≤ rho.setup.D.model
    exact Subgroup.commutator_le_self _
  haveI : Finite ↥Q :=
    Finite.of_injective (Subgroup.inclusion hQmodel) (Subgroup.inclusion_injective hQmodel)
  have hmap : C.map rho.iota = Q := by
    rw [hCQ]
    exact Subgroup.map_comap_eq_self (by rw [rho.iota_range]; exact hQle)
  let φ : C ≃* Q :=
    (Subgroup.equivMapOfInjective C rho.iota rho.iota_inj).trans (MulEquiv.subgroupCongr hmap)
  have hφ_coe : ∀ x : C,
      ((φ x : Q) : CFSG.Blueprint.Chevalley.ModGL rho.tau Omega) = rho.iota (x : R) :=
    fun x => rfl
  have hclosure : Subgroup.closure (Set.range (fun b : Fin rho.tau.rank → Omegaˣ =>
      CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit rho.tau b)) ≤
      CFSG.LieType.Chevalley.torusGroup rho.tau Omega :=
    (Subgroup.closure_le _).mpr (by
      rintro _ ⟨b, rfl⟩
      exact CFSG.LieType.Chevalley.rootDiagUnit_mem_torusGroup b)
  have hyZ := (sup_le_sup_right hclosure _) hg
  have hyF : rho.setup.D.step (g : CFSG.Blueprint.Chevalley.ModGL rho.tau Omega) =
      (g : CFSG.Blueprint.Chevalley.ModGL rho.tau Omega) := by
    have h := (CFSG.HardMathSupport.Timmesfeld.LangTorus.LangDatum.mem_model
      (D := rho.setup.D)).mp g.2
    rw [CFSG.HardMathSupport.Timmesfeld.LangTorus.LangDatum.step, MonoidHom.comp_apply]
    show rho.setup.D.n * rho.setup.D.Φ (g : CFSG.Blueprint.Chevalley.ModGL rho.tau Omega) *
      rho.setup.D.n⁻¹ = (g : CFSG.Blueprint.Chevalley.ModGL rho.tau Omega)
    exact h.2
  have ha3 : rho.a ^ 3 = 1 := by
    ext i
    simpa using congrArg (fun u : Omegaˣ => (u : Omega)) (rho.a_pow i)
  have hpow : CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit rho.tau
      rho.a ^ 3 = 1 := by
    rw [CFSG.LieType.Chevalley.rootDiagUnit_pow, ha3,
      CFSG.LieType.Chevalley.rootDiagUnit_one]
  have hτ : rho.tau = .G2 ∨ rho.tau = .F4 ∨ rho.tau = .D4 ∨ rho.tau = .E6 ∨
      rho.tau = .E7 ∨ rho.tau = .E8 := by
    rw [← rho.tau_eq]
    exact ltrkna_absTag_exceptional rho.row.T
  have hG2q : rho.tau = .G2 → 4 ≤ rho.setup.D.q := fun h => absurd h (by
    rw [← rho.tau_eq]
    exact ltrkna_absTag_ne_g2 rho.row.T)
  have hyStab : MulAut.conj (g : CFSG.Blueprint.Chevalley.ModGL rho.tau Omega) ∈
      CFSG.GroupActions.subgroupStabAut Q := by
    show Q.map (MulAut.conj (g : CFSG.Blueprint.Chevalley.ModGL rho.tau Omega)).toMonoidHom = Q
    have hle : Q.map
        (MulAut.conj (g : CFSG.Blueprint.Chevalley.ModGL rho.tau Omega)).toMonoidHom ≤ Q := by
      rw [Subgroup.map_le_iff_le_comap]
      intro x hx
      have hxΓ : x ∈ rho.setup.Γ := hQle hx
      rw [← rho.iota_range] at hxΓ
      obtain ⟨d, rfl⟩ := MonoidHom.mem_range.mp hxΓ
      have hdC : d ∈ C := by
        rw [hCQ]
        exact hx
      have h1 : (g : CFSG.Blueprint.Chevalley.ModGL rho.tau Omega) * rho.iota d *
          (g : CFSG.Blueprint.Chevalley.ModGL rho.tau Omega)⁻¹ ∈ Q := by
        have h2 : rho.iota (rho.modelAction g d) ∈ Q := hpres d hdC
        rwa [rho.modelAction_compat g d] at h2
      change (MulAut.conj (g : CFSG.Blueprint.Chevalley.ModGL rho.tau Omega)) (rho.iota d) ∈ Q
      exact h1
    exact ltrkna_map_eq_of_le_of_injective _
      (MulAut.conj (g : CFSG.Blueprint.Chevalley.ModGL rho.tau Omega)).injective hle
  have hlabC : GGHasLabel (⟨.A, 1, 3⟩ : LargeEvenLabel) (↥C ⧸ Subgroup.center ↥C) := hlab
  have hlabQ : GGHasLabel (⟨.A, 1, 3⟩ : LargeEvenLabel)
      (↥Q ⧸ Subgroup.center ↥Q) :=
    CFSG.StandardType.ggHasLabel_quotCenter_of_mulEquiv φ hlabC
  have h360 : Nat.card (↥Q ⧸ Subgroup.center ↥Q) ≠ 360 :=
    ltrkna_card_quot_ne_360 hlabQ
  let v : MulAut ↥Q := CFSG.GroupActions.subgroupStabRestrict Q
    ⟨MulAut.conj (g : CFSG.Blueprint.Chevalley.ModGL rho.tau Omega), hyStab⟩
  have hnat : CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥Q v ∈
      CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived
        (↥Q ⧸ Subgroup.center ↥Q) := by
    exact CFSG.LocalAnalysis.GLTheoremA.T171Sh.excKernelCompAction_holds rho.setup
      (by norm_num) (by norm_num) (p := 3) (by norm_num) (by norm_num)
      hτ (a := rho.a) rho.a_torus (fun i => rho.a_pow i) hpow rho.a_ne hG2q
      (i := rho.repr j) (rho.qs j hqs) h360 hyZ hyF hyStab
  let e : (↥C ⧸ Subgroup.center ↥C) ≃* (↥Q ⧸ Subgroup.center ↥Q) :=
    QuotientGroup.congr (Subgroup.center ↥C) (Subgroup.center ↥Q) φ (ltrkna_map_center_eq φ)
  let β : MulAut (↥C ⧸ Subgroup.center ↥C) :=
    (MulAut.congr e).symm
      (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥Q v)
  have hβ : β ∈ CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived
      (↥C ⧸ Subgroup.center ↥C) := by
    refine (CFSG.ComponentClassification.OuterAutomorphisms.mem_innAutDerived_congr e).mp ?_
    show MulAut.congr e β ∈ CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived
      (↥Q ⧸ Subgroup.center ↥Q)
    rw [show MulAut.congr e β =
        CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥Q v from
      MulEquiv.apply_symm_apply (MulAut.congr e)
        (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥Q v)]
    exact hnat
  change ∃ β ∈ CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived
      (↥C ⧸ Subgroup.center ↥C),
    ∀ d d' : C, rho.modelAction g (d : R) = (d' : R) →
      (d' : ↥C ⧸ Subgroup.center ↥C) = β (d : ↥C ⧸ Subgroup.center ↥C)
  refine ⟨β, hβ, ?_⟩
  intro d d' hdd'
  have hβ_d : β (QuotientGroup.mk' (Subgroup.center ↥C) d) =
      QuotientGroup.mk' (Subgroup.center ↥C) ⟨rho.modelAction g (d : R), hpres d d.2⟩ := by
    show ((MulAut.congr e).symm
        (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥Q v))
      (QuotientGroup.mk' (Subgroup.center ↥C) d) = _
    rw [ltrkna_congr_symm_apply]
    dsimp only [e]
    have hcm : (QuotientGroup.congr (Subgroup.center ↥C) (Subgroup.center ↥Q) φ
        (ltrkna_map_center_eq φ)) (QuotientGroup.mk' (Subgroup.center ↥C) d) =
        QuotientGroup.mk' (Subgroup.center ↥Q) (φ d) :=
      QuotientGroup.congr_mk (Subgroup.center ↥C) (Subgroup.center ↥Q) φ
        (ltrkna_map_center_eq φ) d
    rw [hcm]
    change (QuotientGroup.congr (Subgroup.center ↥C) (Subgroup.center ↥Q) φ
        (ltrkna_map_center_eq φ)).symm
      ((CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient v)
        (QuotientGroup.mk' (Subgroup.center ↥Q) (φ d))) = _
    rw [CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk]
    have hcm' : (QuotientGroup.congr (Subgroup.center ↥C) (Subgroup.center ↥Q) φ
        (ltrkna_map_center_eq φ)) (QuotientGroup.mk' (Subgroup.center ↥C)
          ⟨rho.modelAction g (d : R), hpres d d.2⟩) =
        QuotientGroup.mk' (Subgroup.center ↥Q)
          (φ ⟨rho.modelAction g (d : R), hpres d d.2⟩) :=
      QuotientGroup.congr_mk (Subgroup.center ↥C) (Subgroup.center ↥Q) φ
        (ltrkna_map_center_eq φ) ⟨rho.modelAction g (d : R), hpres d d.2⟩
    rw [MulEquiv.symm_apply_eq, hcm']
    congr 1
    apply Subtype.ext
    have hv : ((v (φ d) : Q) : CFSG.Blueprint.Chevalley.ModGL rho.tau Omega) =
        (g : CFSG.Blueprint.Chevalley.ModGL rho.tau Omega) * rho.iota (d : R) *
          (g : CFSG.Blueprint.Chevalley.ModGL rho.tau Omega)⁻¹ := by
      simp only [v, CFSG.GroupActions.subgroupStabRestrict_apply, hφ_coe d, MulAut.conj_apply]
    simp only [hv, hφ_coe, rho.modelAction_compat g (d : R)]
  have hd' : d' = ⟨rho.modelAction g (d : R), hpres d d.2⟩ := by
    ext
    exact hdd'.symm
  change (QuotientGroup.mk' (Subgroup.center ↥C) d') =
    β (QuotientGroup.mk' (Subgroup.center ↥C) d)
  rw [hβ_d, hd']

end CFSG.StandardType.KD2Pieces1615

end
