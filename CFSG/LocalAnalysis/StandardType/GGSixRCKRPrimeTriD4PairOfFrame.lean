module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeTriD4Model
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeReturnedFrame
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcD4
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.AmbientPairDescentPart1
public import CFSG.LieType.Chevalley.GraphFixedOrbitCollection
public import CFSG.LieType.Chevalley.SignKernelComponentBorel
public import CFSG.LieType.Steinberg.TwistedD4.Perfect
public import CFSG.LocalAnalysis.SectionRank.TrialityEvenCover
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TriD4BridgeLongRoot
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LemmaHTriD4

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.StandardType.GGFinModel
  CFSG.StandardType.S2MathFi1035Pos CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.SectionRank CFSG.StandardType.F4ExplicitPos.AmbientPairDescent
  CFSG.LieType.AlgebraicGroups
open CFSG.LieType.RootSystem (weylAction weylAction_mul_apply weylAction_apply_inv_apply
  weylAction_apply_injective)
open CFSG.LieType.Universal (LieUniversal)
open CFSG.SeitzReduction (highRoot isRoot_highRoot height_le_height_highRoot)
open scoped commutatorElement


theorem rckTriD4_coxeter_highRoot {K : Type} [Field K] (σ : K →+* K) :
    weylAction (twistedDatum σ).isFiniteType
      (simple .G2 (ng 1) * simple .G2 (ng 0)) (highRoot .G2) = Pi.single (ng 0) 1 := by
  change (simple .G2 (ng 1) * simple .G2 (ng 0)) •
    (highRoot .G2 : Fin (Tag.rank .G2) → ℤ) = Pi.single (ng 0) 1
  simp only [mul_smul, simple_smul]
  decide +kernel

theorem rckTriD4_rootGroup_eq_conj_single
    {K : Type} [Field K] (σ : K →+* K) (hσ : ∀ c, σ (σ (σ c)) = c)
    {β : Fin (Tag.rank .G2) → ℤ} (hl : GGLongRoot (twistedDatum σ) β) :
    ∃ u : twistedGroup σ,
      (twistedDatum σ).rootGroup β =
        ((twistedDatum σ).rootGroup (Pi.single (ng 0) 1)).map
          (MulAut.conj u).toMonoidHom ∧
      (twistedDatum σ).rootGroup (-β) =
        ((twistedDatum σ).rootGroup (-Pi.single (ng 0) 1)).map
          (MulAut.conj u).toMonoidHom := by
  classical
  obtain ⟨w, γ₀, hγ₀mem, hmax, rfl⟩ := hl
  have hγ₀root : IsRoot .G2 γ₀ := isRoot_of_mem_twistedDatum_roots σ hγ₀mem
  have hhigh : highRoot .G2 ∈ (twistedDatum σ).roots := by
    rw [twistedDatum_roots]
    exact isRoot_highRoot .G2
  have hle1 : height (τ := .G2) (highRoot .G2) ≤ height (τ := .G2) γ₀ := hmax _ hhigh
  have hle2 : height (τ := .G2) γ₀ ≤ height (τ := .G2) (highRoot .G2) :=
    height_le_height_highRoot (τ := .G2) hγ₀root
  have hγ₀ : γ₀ = highRoot .G2 :=
    CFSG.StandardType.LieKnownR2.TriD4.Bridge.eq_highRoot_G2_of_height_eq hγ₀root
      (le_antisymm hle2 hle1)
  have hm : weylAction (isFiniteType_cartan Tag.G2)
      (simple .G2 (ng 1) * simple .G2 (ng 0)) (highRoot .G2) = Pi.single (ng 0) 1 :=
    rckTriD4_coxeter_highRoot σ
  have hm' : weylAction (isFiniteType_cartan Tag.G2)
      (simple .G2 (ng 1) * simple .G2 (ng 0))⁻¹ (Pi.single (ng 0) 1) = highRoot .G2 := by
    apply weylAction_apply_injective (isFiniteType_cartan Tag.G2)
    rw [weylAction_apply_inv_apply, ← hm]
  let mD : GGWeyl (twistedDatum σ) :=
    show GGWeyl (twistedDatum σ) from (simple .G2 (ng 1) * simple .G2 (ng 0))⁻¹
  let W : GGWeyl (twistedDatum σ) := w * mD
  have hW : weylAction (twistedDatum σ).isFiniteType W (Pi.single (ng 0) 1) =
      weylAction (twistedDatum σ).isFiniteType w γ₀ := by
    rw [show W = w * mD from rfl, weylAction_mul_apply,
      show weylAction (twistedDatum σ).isFiniteType mD (Pi.single (ng 0) 1) = highRoot .G2
        from hm', hγ₀]
  let u : twistedGroup σ := nrep (twistedDatum_isCTGroupDatum σ hσ) W
  have hu : ActsAs (twistedDatum σ) u W := actsAs_nrep (twistedDatum_isCTGroupDatum σ hσ) W
  have hroot : Pi.single (ng 0) 1 ∈ (twistedDatum σ).roots := by
    rw [twistedDatum_roots]
    exact IsRoot.basis (ng 0)
  have hnegroot : -Pi.single (ng 0) 1 ∈ (twistedDatum σ).roots := by
    rw [twistedDatum_roots]
    exact IsRoot.neg (IsRoot.basis (ng 0))
  have hneg : weylAction (twistedDatum σ).isFiniteType W (-Pi.single (ng 0) 1) =
      -weylAction (twistedDatum σ).isFiniteType w γ₀ := by
    rw [show weylAction (twistedDatum σ).isFiniteType W (-Pi.single (ng 0) 1) =
        -weylAction (twistedDatum σ).isFiniteType W (Pi.single (ng 0) 1) from
      map_neg (weylAction (twistedDatum σ).isFiniteType W) (Pi.single (ng 0) 1)]
    rw [hW]
  refine ⟨u, ?_, ?_⟩
  · exact (congrArg (twistedDatum σ).rootGroup hW.symm).trans
      (hu (Pi.single (ng 0) 1) hroot).symm
  · exact (congrArg (twistedDatum σ).rootGroup hneg.symm).trans
      (hu (-Pi.single (ng 0) 1) hnegroot).symm

private theorem rckTriD4_base_pair_stable
    {τ : Tag} {p₀ : ℕ} (S : LangSetup τ GGL p₀) {Ψ : Set (Fin τ.rank → ℤ)}
    (hY : ∀ y ∈ rootSpan τ GGL Ψ, S.D.step y ∈ rootSpan τ GGL Ψ)
    (Ξ : ↥(rootSpan τ GGL Ψ) ≃* ↥(adjointGroup Tag.D4 GGL)) {h r : ℕ}
    (hΞeq : ∀ (y : ModGL τ GGL) (hy : y ∈ rootSpan τ GGL Ψ),
      (Ξ ⟨S.D.step y, hY y hy⟩ : ModGL Tag.D4 GGL) = triPsi h r (Ξ ⟨y, hy⟩ : ModGL Tag.D4 GGL))
    {γ : Fin τ.rank → ℤ} (z : ModGL τ GGL) {U : Subgroup (ModGL Tag.D4 GGL)}
    (hUA : U ≤ adjointGroup Tag.D4 GGL) (hUstable : U.map (triPsi h r) = U)
    (hYeq : ∀ y : ModGL τ GGL, y ∈ (rootSubgroup τ GGL γ).map (MulAut.conj z).toMonoidHom ↔
      ∃ hy : y ∈ rootSpan τ GGL Ψ, (Ξ ⟨y, hy⟩ : ModGL Tag.D4 GGL) ∈ U) :
    ((rootSubgroup τ GGL γ).map (MulAut.conj z).toMonoidHom).map S.D.step =
      (rootSubgroup τ GGL γ).map (MulAut.conj z).toMonoidHom := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hyV, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨hyY, hyU⟩ := (hYeq y).1 hyV
    refine (hYeq (S.D.step y)).2 ⟨hY y hyY, ?_⟩
    rw [hΞeq y hyY]
    have hmem := Subgroup.mem_map_of_mem (triPsi h r) hyU
    rwa [hUstable] at hmem
  · intro x hx
    obtain ⟨hxY, hxU⟩ := (hYeq x).1 hx
    have hmem : (Ξ ⟨x, hxY⟩ : ModGL Tag.D4 GGL) ∈ U.map (triPsi h r) := by
      rw [hUstable]; exact hxU
    obtain ⟨v, hvU, hv⟩ := Subgroup.mem_map.1 hmem
    have hvA : v ∈ adjointGroup Tag.D4 GGL := hUA hvU
    refine Subgroup.mem_map.2
      ⟨((Ξ.symm ⟨v, hvA⟩ : ↥(rootSpan τ GGL Ψ)) : ModGL τ GGL), ?_, ?_⟩
    · have hsub : ((Ξ.symm ⟨v, hvA⟩ : ↥(rootSpan τ GGL Ψ)) : ModGL τ GGL) ∈
          rootSpan τ GGL Ψ := (Ξ.symm ⟨v, hvA⟩).2
      refine (hYeq ((Ξ.symm ⟨v, hvA⟩ : ↥(rootSpan τ GGL Ψ)) : ModGL τ GGL)).2
        (Exists.intro hsub ?_)
      rw [MulEquiv.apply_symm_apply]
      exact hvU
    · let w : ↥(rootSpan τ GGL Ψ) := Ξ.symm ⟨v, hvA⟩
      have hwY0 : (w : ModGL τ GGL) ∈ rootSpan τ GGL Ψ := w.2
      have h2 : (Subtype.mk (S.D.step (w : ModGL τ GGL))
          (hY (w : ModGL τ GGL) hwY0) : ↥(rootSpan τ GGL Ψ)) = ⟨x, hxY⟩ := by
        apply Ξ.injective
        apply Subtype.ext
        refine (hΞeq (w : ModGL τ GGL) hwY0).trans ?_
        have hweq : (⟨(w : ModGL τ GGL), hwY0⟩ : ↥(rootSpan τ GGL Ψ)) = w := rfl
        have hwv : (Ξ w : ↥(adjointGroup Tag.D4 GGL)) = ⟨v, hvA⟩ :=
          MulEquiv.apply_symm_apply Ξ ⟨v, hvA⟩
        rw [hweq, hwv]
        exact hv
      exact congrArg Subtype.val h2

private theorem rckTriD4_map_conj_stable {G : Type*} [Group G] (F : G →* G) {r : G}
    (hr : F r = r) {V : Subgroup G} (hV : V.map F = V) :
    (V.map (MulAut.conj r).toMonoidHom).map F = V.map (MulAut.conj r).toMonoidHom := by
  have hcomm : F.comp (MulAut.conj r).toMonoidHom =
      (MulAut.conj r).toMonoidHom.comp F := by
    ext x
    change F (r * x * r⁻¹) = r * F x * r⁻¹
    rw [map_mul, map_mul, map_inv, hr]
  rw [Subgroup.map_map, hcomm, ← Subgroup.map_map, hV]

theorem rckFrameCoverPair_triD4_of_frame
    {τ : Tag} {p₀ : ℕ} (S : LangSetup τ GGL p₀) (a : Fin τ.rank → GGLˣ)
    (i : KernelComponent (rootCharHom a)) {h : ℕ} (hh : 1 ≤ h)
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (hF : RCKTriD4Frame S (componentRoots (rootCharHom a) i) h) :
    RCKFrameCoverPair S a i h (fun M g => ∃ (F : Type) (_ : Field F) (_ : Finite F)
      (σ : F →+* F), TriField F σ g ∧ M = triD4Universal F σ) := by
  classical
  set Ψ : Set (Fin τ.rank → ℤ) := componentRoots (rootCharHom a) i with hΨ
  have hfinΨ : Ψ.Finite :=
    (CFSG.Blueprint.Chevalley.finite_setOf_isRoot τ).subset fun γ hγ =>
      isRoot_of_mem_componentRoots hγ
  have hs1 : componentOrbitLength S.ρ Ψ = 1 := componentOrbitLength_eq_one hfinΨ hρ
  obtain ⟨r, hr, hY, Ξ, hΞeq, z, hzΨ, γ, hγΨ, hpairpos, hpairneg⟩ := hF
  obtain ⟨F, hFld, hFfin, σ, ι, hTri, hιinj, hιrange, hιUpos, hιUneg, hstablepos, hstableneg⟩ :=
    triD4_model_in_adjD4 hh hr
  letI : Field F := hFld
  letI : Finite F := hFfin
  haveI : CharP F 2 := CFSG.StandardType.RCKC1.charP_two_of_triField hTri
  have hσ3 : ∀ c, σ (σ (σ c)) = c := TwistedD4.sigma_three_of_card hTri.2.1 hTri.2.2
  have hq2 : 2 ≤ 2 ^ h := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) hh
  have hperf : Group.IsPerfect ↥(twistedGroup σ) :=
    TwistedD4.twistedGroup_isPerfect_of_card hq2 hTri.2.1 hTri.2.2
  have hsplit : CFSG.SeitzReduction.UnitaryPilot.OddCentralSplit ↥(twistedGroup σ) := by
    intro E _ _ π hπ hker hodd
    obtain ⟨s, hs, -, -⟩ :=
      CFSG.SectionRank.triality_even_central_odd_extension_splitting (σ := σ) hσ3 hπ hker hodd
    exact ⟨s, hs⟩
  let M : LieUniversal := triD4Universal F σ
  have hιadj : ι.range ≤ adjointGroup Tag.D4 GGL := hιrange.le.trans inf_le_left
  let eι : ↥(twistedGroup σ) →* ↥(adjointGroup Tag.D4 GGL) :=
    ι.codRestrict _ (fun x => hιadj (MonoidHom.mem_range.mpr ⟨x, rfl⟩))
  let φY : ↥(twistedGroup σ) →* ↥(rootSpan τ GGL Ψ) :=
    Ξ.symm.toMonoidHom.comp eι
  let φ : ↥(twistedGroup σ) →* ModGL τ GGL :=
    (rootSpan τ GGL Ψ).subtype.comp φY
  have hιfix : ∀ x, triPsi h r (ι x) = ι x := by
    intro x
    have hmem : ι x ∈ adjointGroup Tag.D4 GGL ⊓ (triPsi h r).eqLocus (MonoidHom.id _) := by
      rw [← hιrange]; exact MonoidHom.mem_range.mpr ⟨x, rfl⟩
    exact (Subgroup.mem_inf.1 hmem).2
  have hφY_range : φY.range =
      (S.D.step.eqLocus (MonoidHom.id _)).comap (rootSpan τ GGL Ψ).subtype := by
    ext x
    constructor
    · rintro ⟨c, rfl⟩
      show S.D.step ((φY c : ↥(rootSpan τ GGL Ψ)) : ModGL τ GGL) =
        ((φY c : ↥(rootSpan τ GGL Ψ)) : ModGL τ GGL)
      have h2 : (⟨S.D.step ((φY c : ↥(rootSpan τ GGL Ψ)) : ModGL τ GGL),
          hY _ (φY c).2⟩ : ↥(rootSpan τ GGL Ψ)) = φY c := by
        apply Ξ.injective
        apply Subtype.ext
        rw [hΞeq ((φY c : ↥(rootSpan τ GGL Ψ)) : ModGL τ GGL) (φY c).2]
        rw [show (⟨((φY c : ↥(rootSpan τ GGL Ψ)) : ModGL τ GGL),
          (φY c).2⟩ : ↥(rootSpan τ GGL Ψ)) = φY c from rfl]
        rw [show φY c = Ξ.symm (eι c) from rfl, MulEquiv.apply_symm_apply]
        exact hιfix c
      exact congrArg Subtype.val h2
    · intro hx
      have hstep : S.D.step (x : ModGL τ GGL) = (x : ModGL τ GGL) := hx
      have hfix : triPsi h r (Ξ x : ModGL Tag.D4 GGL) = (Ξ x : ModGL Tag.D4 GGL) := by
        have h1 := hΞeq (x : ModGL τ GGL) x.2
        have h2 : (⟨S.D.step (x : ModGL τ GGL), hY _ x.2⟩ : ↥(rootSpan τ GGL Ψ)) = x :=
          Subtype.ext hstep
        rw [h2] at h1
        exact h1.symm
      have hmem : (Ξ x : ModGL Tag.D4 GGL) ∈ ι.range := by
        rw [hιrange]; exact ⟨(Ξ x).2, hfix⟩
      obtain ⟨c, hc⟩ := MonoidHom.mem_range.1 hmem
      refine ⟨c, ?_⟩
      apply Ξ.injective
      rw [show Ξ (φY c) = eι c from MulEquiv.apply_symm_apply Ξ (eι c)]
      exact Subtype.ext hc
  have hφ_range : φ.range = rootSpan τ GGL Ψ ⊓ S.D.step.eqLocus (MonoidHom.id _) := by
    calc φ.range = (φY.range).map (rootSpan τ GGL Ψ).subtype := by
          rw [show φ = (rootSpan τ GGL Ψ).subtype.comp φY from rfl, MonoidHom.range_comp]
      _ = ((S.D.step.eqLocus (MonoidHom.id _)).comap (rootSpan τ GGL Ψ).subtype).map
            (rootSpan τ GGL Ψ).subtype := by rw [hφY_range]
      _ = (rootSpan τ GGL Ψ).subtype.range ⊓ S.D.step.eqLocus (MonoidHom.id _) :=
            Subgroup.map_comap_eq (rootSpan τ GGL Ψ).subtype (S.D.step.eqLocus (MonoidHom.id _))
      _ = rootSpan τ GGL Ψ ⊓ S.D.step.eqLocus (MonoidHom.id _) := by
            rw [Subgroup.range_subtype]
  have hφ_range_model : φ.range = rootSpan τ GGL Ψ ⊓ S.D.model := by
    rw [hφ_range]
    show rootSpan τ GGL Ψ ⊓ S.D.step.eqLocus (MonoidHom.id _) =
      rootSpan τ GGL Ψ ⊓ (adjointGroup τ GGL ⊓ S.D.step.eqLocus (MonoidHom.id _))
    rw [← inf_assoc, inf_eq_left.mpr (rootSpan_le_adjointGroup GGL Ψ)]
  have hφ_inj : Function.Injective φ := by
    intro x y hxy
    have h1 : (Ξ.symm (eι x) : ↥(rootSpan τ GGL Ψ)) = Ξ.symm (eι y) := Subtype.ext hxy
    have h2 := Ξ.symm.injective h1
    exact hιinj (congrArg Subtype.val h2)
  have hφ_ker : φ.ker ≤ Subgroup.center M.K := by
    rw [(MonoidHom.ker_eq_bot_iff φ).mpr hφ_inj]
    exact bot_le
  have hfinM : Finite M.K := by
    change Finite ↥(twistedGroup σ)
    have hfinA : Finite (adjointGroup d4 F) := generated_group_finite d4 F
    infer_instance
  have hperfM : Group.IsPerfect M.K := by
    change Group.IsPerfect ↥(twistedGroup σ)
    exact hperf
  have hsplitM : CFSG.SeitzReduction.UnitaryPilot.OddCentralSplit M.K := by
    change CFSG.SeitzReduction.UnitaryPilot.OddCentralSplit ↥(twistedGroup σ)
    exact hsplit
  have hφ_range_R : φ.range = rationalComponent S.ρ S.Γ (rootCharHom a) i := by
    have hPperf : ⁅φ.range, φ.range⁆ = φ.range := by
      have htop : ⁅(⊤ : Subgroup M.K), (⊤ : Subgroup M.K)⁆ = ⊤ := by
        haveI : Group.IsPerfect M.K := hperfM
        rw [← commutator_def]
        exact Group.IsPerfect.commutator_eq_top
      calc ⁅φ.range, φ.range⁆
          = ⁅(⊤ : Subgroup M.K).map φ, (⊤ : Subgroup M.K).map φ⁆ := by
            rw [MonoidHom.range_eq_map]
            rfl
        _ = (⁅(⊤ : Subgroup M.K), (⊤ : Subgroup M.K)⁆).map φ :=
            (Subgroup.map_commutator (⊤ : Subgroup M.K) (⊤ : Subgroup M.K) φ).symm
        _ = (⊤ : Subgroup M.K).map φ := by rw [htop]
        _ = φ.range := (MonoidHom.range_eq_map φ).symm
    have hPΓ : φ.range ≤ S.Γ := by
      rw [← hPperf]
      show ⁅φ.range, φ.range⁆ ≤ ⁅S.D.model, S.D.model⁆
      exact Subgroup.commutator_mono (by rw [hφ_range_model]; exact inf_le_right)
        (by rw [hφ_range_model]; exact inf_le_right)
    have hPleY : φ.range ≤ rootSpan τ GGL Ψ := by
      rw [hφ_range_model]; exact inf_le_left
    have hroots : rationalRoots S.ρ (rootCharHom a) i = Ψ := by
      ext δ
      constructor
      · rintro ⟨k, ε, hε, rfl⟩
        induction k generalizing ε with
        | zero => exact hε
        | succ k ih =>
          rw [Function.iterate_succ_apply]
          exact ih _ (hρ ε hε)
      · intro hδ; exact ⟨0, δ, hδ, rfl⟩
    have hspan : rationalSpan S.ρ S.Γ (rootCharHom a) i = rootSpan τ GGL Ψ ⊓ S.Γ := by
      rw [rationalSpan, hroots]
    have hR : rationalComponent S.ρ S.Γ (rootCharHom a) i =
        ⁅rootSpan τ GGL Ψ ⊓ S.Γ, rootSpan τ GGL Ψ ⊓ S.Γ⁆ := by
      rw [rationalComponent, hspan]
    have hle1 : φ.range ≤ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
      rw [hR]
      calc φ.range = ⁅φ.range, φ.range⁆ := hPperf.symm
        _ ≤ ⁅rootSpan τ GGL Ψ ⊓ S.Γ, rootSpan τ GGL Ψ ⊓ S.Γ⁆ :=
            Subgroup.commutator_mono (le_inf hPleY hPΓ) (le_inf hPleY hPΓ)
    have hle2 : rationalComponent S.ρ S.Γ (rootCharHom a) i ≤ φ.range := by
      rw [hR]
      calc ⁅rootSpan τ GGL Ψ ⊓ S.Γ, rootSpan τ GGL Ψ ⊓ S.Γ⁆
          ≤ ⁅rootSpan τ GGL Ψ ⊓ S.D.model, rootSpan τ GGL Ψ ⊓ S.D.model⁆ :=
            Subgroup.commutator_mono
              (inf_le_inf_left _ S.Γ_le_model) (inf_le_inf_left _ S.Γ_le_model)
        _ = φ.range := by rw [← hφ_range_model]; exact hPperf
    exact le_antisymm hle1 hle2
  have hMod : (fun M g => ∃ (F : Type) (_ : Field F) (_ : Finite F) (σ : F →+* F),
      TriField F σ g ∧ M = triD4Universal F σ) M (h * componentOrbitLength S.ρ Ψ) :=
    ⟨F, hFld, hFfin, σ, by rw [hs1, Nat.mul_one]; exact hTri, rfl⟩
  have hADE : RCKADEModel M (h * componentOrbitLength S.ρ Ψ) :=
    Or.inr ⟨F, hFld, hFfin, σ, by rw [hs1, Nat.mul_one]; exact hTri, rfl⟩
  refine ⟨M, φ, hMod, hADE, hφ_range_R, hφ_ker, hfinM, hperfM, hsplitM, ?_⟩
  rw [hs1]
  intro _ β hβ hlong
  have hlong' : GGLongRoot (twistedDatum σ) β := hlong
  obtain ⟨u, hXu, hXu'⟩ := rckTriD4_rootGroup_eq_conj_single σ hσ3 hlong'
  have hbasepos :
      ((twistedDatum σ).rootGroup (Pi.single (ng 0) 1)).map φ =
      (rootSubgroup τ GGL γ).map (MulAut.conj z).toMonoidHom ⊓
        S.D.step.eqLocus (MonoidHom.id _) := by
    ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      have hkU : (ι k : ModGL Tag.D4 GGL) ∈
          rootSubgroup Tag.D4 GGL (Pi.single (nd 2) 1) ⊓
            (triPsi h r).eqLocus (MonoidHom.id _) := by
        rw [← hιUpos]
        exact Subgroup.mem_map_of_mem ι hk
      have hxY : φ k ∈ rootSpan τ GGL Ψ := (φY k).2
      have hcoe : (Ξ ⟨φ k, hxY⟩ : ModGL Tag.D4 GGL) = ι k := by
        have e : (⟨φ k, hxY⟩ : ↥(rootSpan τ GGL Ψ)) = φY k := rfl
        rw [e, show φY k = Ξ.symm (eι k) from rfl, MulEquiv.apply_symm_apply]
        rfl
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · refine (hpairpos (φ k)).2 ⟨hxY, ?_⟩
        rw [hcoe]
        exact (Subgroup.mem_inf.1 hkU).1
      · have h1 := hΞeq (φ k) hxY
        have h2 : (⟨S.D.step (φ k), hY _ hxY⟩ : ↥(rootSpan τ GGL Ψ)) = φY k := by
          apply Ξ.injective
          apply Subtype.ext
          rw [h1, hcoe, (Subgroup.mem_inf.1 hkU).2]
          rw [show φY k = Ξ.symm (eι k) from rfl, MulEquiv.apply_symm_apply]
          rfl
        exact congrArg Subtype.val h2
    · intro hx
      obtain ⟨hxV, hxfix⟩ := Subgroup.mem_inf.1 hx
      obtain ⟨hxY, hxH⟩ := (hpairpos x).1 hxV
      have hxfixΨ : triPsi h r (Ξ ⟨x, hxY⟩) = Ξ ⟨x, hxY⟩ := by
        have h1 := hΞeq x hxY
        have h2 : (⟨S.D.step (x : ModGL τ GGL), hY _ hxY⟩ : ↥(rootSpan τ GGL Ψ)) = ⟨x, hxY⟩ :=
          Subtype.ext hxfix
        rw [h2] at h1
        exact h1.symm
      have hxU : (Ξ ⟨x, hxY⟩ : ModGL Tag.D4 GGL) ∈
          ((twistedDatum σ).rootGroup (Pi.single (ng 0) 1)).map ι := by
        rw [hιUpos]
        exact Subgroup.mem_inf.2 ⟨hxH, hxfixΨ⟩
      obtain ⟨k, hk, hkι⟩ := Subgroup.mem_map.1 hxU
      refine Subgroup.mem_map.2 ⟨k, hk, ?_⟩
      have hsub : (⟨x, hxY⟩ : ↥(rootSpan τ GGL Ψ)) = φY k := by
        apply Ξ.injective
        rw [show Ξ (φY k) = eι k from MulEquiv.apply_symm_apply Ξ (eι k)]
        exact Subtype.ext hkι.symm
      exact (congrArg Subtype.val hsub).symm
  have hbaseneg :
      ((twistedDatum σ).rootGroup (-Pi.single (ng 0) 1)).map φ =
      (rootSubgroup τ GGL (-γ)).map (MulAut.conj z).toMonoidHom ⊓
        S.D.step.eqLocus (MonoidHom.id _) := by
    ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      have hkU : (ι k : ModGL Tag.D4 GGL) ∈
          rootSubgroup Tag.D4 GGL (-Pi.single (nd 2) 1) ⊓
            (triPsi h r).eqLocus (MonoidHom.id _) := by
        rw [← hιUneg]
        exact Subgroup.mem_map_of_mem ι hk
      have hxY : φ k ∈ rootSpan τ GGL Ψ := (φY k).2
      have hcoe : (Ξ ⟨φ k, hxY⟩ : ModGL Tag.D4 GGL) = ι k := by
        have e : (⟨φ k, hxY⟩ : ↥(rootSpan τ GGL Ψ)) = φY k := rfl
        rw [e, show φY k = Ξ.symm (eι k) from rfl, MulEquiv.apply_symm_apply]
        rfl
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · refine (hpairneg (φ k)).2 ⟨hxY, ?_⟩
        rw [hcoe]
        exact (Subgroup.mem_inf.1 hkU).1
      · have h1 := hΞeq (φ k) hxY
        have h2 : (⟨S.D.step (φ k), hY _ hxY⟩ : ↥(rootSpan τ GGL Ψ)) = φY k := by
          apply Ξ.injective
          apply Subtype.ext
          rw [h1, hcoe, (Subgroup.mem_inf.1 hkU).2]
          rw [show φY k = Ξ.symm (eι k) from rfl, MulEquiv.apply_symm_apply]
          rfl
        exact congrArg Subtype.val h2
    · intro hx
      obtain ⟨hxV, hxfix⟩ := Subgroup.mem_inf.1 hx
      obtain ⟨hxY, hxH⟩ := (hpairneg x).1 hxV
      have hxfixΨ : triPsi h r (Ξ ⟨x, hxY⟩) = Ξ ⟨x, hxY⟩ := by
        have h1 := hΞeq x hxY
        have h2 : (⟨S.D.step (x : ModGL τ GGL), hY _ hxY⟩ : ↥(rootSpan τ GGL Ψ)) = ⟨x, hxY⟩ :=
          Subtype.ext hxfix
        rw [h2] at h1
        exact h1.symm
      have hxU : (Ξ ⟨x, hxY⟩ : ModGL Tag.D4 GGL) ∈
          ((twistedDatum σ).rootGroup (-Pi.single (ng 0) 1)).map ι := by
        rw [hιUneg]
        exact Subgroup.mem_inf.2 ⟨hxH, hxfixΨ⟩
      obtain ⟨k, hk, hkι⟩ := Subgroup.mem_map.1 hxU
      refine Subgroup.mem_map.2 ⟨k, hk, ?_⟩
      have hsub : (⟨x, hxY⟩ : ↥(rootSpan τ GGL Ψ)) = φY k := by
        apply Ξ.injective
        rw [show Ξ (φY k) = eι k from MulEquiv.apply_symm_apply Ξ (eι k)]
        exact Subtype.ext hkι.symm
      exact (congrArg Subtype.val hsub).symm
  have hstabpos : ((rootSubgroup τ GGL γ).map (MulAut.conj z).toMonoidHom).map S.D.step =
      (rootSubgroup τ GGL γ).map (MulAut.conj z).toMonoidHom :=
    rckTriD4_base_pair_stable S hY Ξ hΞeq z
      (rootSubgroup_le_adjointGroup (Pi.single (nd 2) 1)) hstablepos hpairpos
  have hstabneg : ((rootSubgroup τ GGL (-γ)).map (MulAut.conj z).toMonoidHom).map S.D.step =
      (rootSubgroup τ GGL (-γ)).map (MulAut.conj z).toMonoidHom :=
    rckTriD4_base_pair_stable S hY Ξ hΞeq z
      (rootSubgroup_le_adjointGroup (-Pi.single (nd 2) 1)) hstableneg hpairneg
  have hφu_mem : φ u ∈ rootSpan τ GGL Ψ := by
    have hmem : φ u ∈ φ.range := MonoidHom.mem_range.mpr ⟨u, rfl⟩
    rw [hφ_range_model] at hmem
    exact (Subgroup.mem_inf.1 hmem).1
  have hφu_fix : S.D.step (φ u) = φ u := by
    have h1 := hΞeq ((Ξ.symm (eι u) : ↥(rootSpan τ GGL Ψ)) : ModGL τ GGL) (Ξ.symm (eι u)).2
    have hιfixu : triPsi h r (eι u) = eι u := by
      have hmem : (eι u : ModGL Tag.D4 GGL) ∈ adjointGroup Tag.D4 GGL ⊓
          (triPsi h r).eqLocus (MonoidHom.id _) := by
        rw [← hιrange]
        exact MonoidHom.mem_range.mpr ⟨u, rfl⟩
      exact (Subgroup.mem_inf.1 hmem).2
    have h2 : (⟨S.D.step ((Ξ.symm (eι u) : ↥(rootSpan τ GGL Ψ)) : ModGL τ GGL),
        hY _ (Ξ.symm (eι u)).2⟩ : ↥(rootSpan τ GGL Ψ)) = Ξ.symm (eι u) := by
      apply Ξ.injective
      apply Subtype.ext
      rw [h1]
      simpa using hιfixu
    simpa [φ, φY] using congrArg Subtype.val h2
  have hmapconj_pos : (((twistedDatum σ).rootGroup (Pi.single (ng 0) 1)).map
        (MulAut.conj u).toMonoidHom).map φ =
      (((twistedDatum σ).rootGroup (Pi.single (ng 0) 1)).map φ).map
        (MulAut.conj (φ u)).toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
      map_inv]
  have hmapconj_neg : (((twistedDatum σ).rootGroup (-Pi.single (ng 0) 1)).map
        (MulAut.conj u).toMonoidHom).map φ =
      (((twistedDatum σ).rootGroup (-Pi.single (ng 0) 1)).map φ).map
        (MulAut.conj (φ u)).toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
      map_inv]
  have hconjz_pos : (rootSubgroup τ GGL γ).map (MulAut.conj (φ u * z)).toMonoidHom =
      ((rootSubgroup τ GGL γ).map (MulAut.conj z).toMonoidHom).map
        (MulAut.conj (φ u)).toMonoidHom := by
    have hcomp : (MulAut.conj (φ u * z)).toMonoidHom =
        ((MulAut.conj (φ u)).toMonoidHom).comp ((MulAut.conj z).toMonoidHom) := by
      rw [map_mul]
      ext x
      rfl
    rw [hcomp, Subgroup.map_map]
  have hconjz_neg : (rootSubgroup τ GGL (-γ)).map (MulAut.conj (φ u * z)).toMonoidHom =
      ((rootSubgroup τ GGL (-γ)).map (MulAut.conj z).toMonoidHom).map
        (MulAut.conj (φ u)).toMonoidHom := by
    have hcomp : (MulAut.conj (φ u * z)).toMonoidHom =
        ((MulAut.conj (φ u)).toMonoidHom).comp ((MulAut.conj z).toMonoidHom) := by
      rw [map_mul]
      ext x
      rfl
    rw [hcomp, Subgroup.map_map]
  have hβpos : ((twistedDatum σ).rootGroup β).map φ =
      (rootSubgroup τ GGL γ).map (MulAut.conj (φ u * z)).toMonoidHom ⊓
        S.D.step.eqLocus (MonoidHom.id _) := by
    rw [hconjz_pos]
    calc ((twistedDatum σ).rootGroup β).map φ
        = (((twistedDatum σ).rootGroup (Pi.single (ng 0) 1)).map
            (MulAut.conj u).toMonoidHom).map φ :=
          congrArg (fun S : Subgroup ↥(twistedGroup σ) => S.map φ) hXu
      _ = (((twistedDatum σ).rootGroup (Pi.single (ng 0) 1)).map φ).map
            (MulAut.conj (φ u)).toMonoidHom := hmapconj_pos
      _ = ((rootSubgroup τ GGL γ).map (MulAut.conj z).toMonoidHom ⊓
            S.D.step.eqLocus (MonoidHom.id _)).map (MulAut.conj (φ u)).toMonoidHom := by
            rw [hbasepos]
      _ = ((rootSubgroup τ GGL γ).map (MulAut.conj z).toMonoidHom).map
            (MulAut.conj (φ u)).toMonoidHom ⊓ S.D.step.eqLocus (MonoidHom.id _) := by
            rw [(map_conj_fixed_eq S.D.step hφu_fix
              ((rootSubgroup τ GGL γ).map (MulAut.conj z).toMonoidHom)).symm]
  have hβneg : ((twistedDatum σ).rootGroup (-β)).map φ =
      (rootSubgroup τ GGL (-γ)).map (MulAut.conj (φ u * z)).toMonoidHom ⊓
        S.D.step.eqLocus (MonoidHom.id _) := by
    rw [hconjz_neg]
    calc ((twistedDatum σ).rootGroup (-β)).map φ
        = (((twistedDatum σ).rootGroup (-Pi.single (ng 0) 1)).map
            (MulAut.conj u).toMonoidHom).map φ :=
          congrArg (fun S : Subgroup ↥(twistedGroup σ) => S.map φ) hXu'
      _ = (((twistedDatum σ).rootGroup (-Pi.single (ng 0) 1)).map φ).map
            (MulAut.conj (φ u)).toMonoidHom := hmapconj_neg
      _ = ((rootSubgroup τ GGL (-γ)).map (MulAut.conj z).toMonoidHom ⊓
            S.D.step.eqLocus (MonoidHom.id _)).map (MulAut.conj (φ u)).toMonoidHom := by
            rw [hbaseneg]
      _ = ((rootSubgroup τ GGL (-γ)).map (MulAut.conj z).toMonoidHom).map
            (MulAut.conj (φ u)).toMonoidHom ⊓ S.D.step.eqLocus (MonoidHom.id _) := by
            rw [(map_conj_fixed_eq S.D.step hφu_fix
              ((rootSubgroup τ GGL (-γ)).map (MulAut.conj z).toMonoidHom)).symm]
  refine ⟨γ, hγΨ, φ u * z, ?_, ?_, ?_, hβpos, hβneg⟩
  · exact Subgroup.mem_sup_right
      (rootSpan_mono (fun _ hδ => hδ.1) (Subgroup.mul_mem _ hφu_mem hzΨ))
  · rw [hconjz_pos]
    exact rckTriD4_map_conj_stable S.D.step hφu_fix hstabpos
  · rw [hconjz_neg]
    exact rckTriD4_map_conj_stable S.D.step hφu_fix hstabneg

end CFSG.StandardType.RCKRP

end
