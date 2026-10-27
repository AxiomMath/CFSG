module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveCompatJoinF4
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.ComponentRootSpan
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.RankThreeSources
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.GuardedComponentRank
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.SelectedLiteralPart2
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.RankThreeFrobeniusError
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.RootSL2LangConjugator
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp3SelectedImage
public import CFSG.LocalAnalysis.StandardType.GGSelectedF4
public import CFSG.LocalAnalysis.StandardType.GGSecFiveFieldTwoCommon
public import CFSG.LocalAnalysis.StandardType.GGOuterInvLangDatumThrough
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.CenterProofFastPart2
public import CFSG.LocalAnalysis.StandardType.GGTBJConfigFacts
public import CFSG.LocalAnalysis.StandardType.GGSpJoinLeviCount
public import CFSG.LocalAnalysis.StandardType.GGTriD4NoneMarking
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim

public noncomputable section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.Blueprint CFSG.LieType.AlgebraicGroups CFSG.LieType.RootSystem CFSG.Timmesfeld.LieEmbed
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.SeitzReduction.F4Pilot
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433


theorem f4_presentsG0_injective {G : Type} [Group G] {H : Subgroup G}
    {n f : ℕ} (ψ : (ggU .F4 n f).K →* G)
    (hpres : GGPresentsG0 H (ggU .F4 n f).D .F4 n f ψ) :
    Function.Injective ψ := by
  have hZ : Subgroup.center (ggU .F4 n f).K = ⊥ :=
    F4ExplicitPos.CenterProofFast.center_adjointGroup_F4_charTwo_eq_bot
  have hker : ψ.ker = ⊥ := eq_bot_iff.2 (by rw [← hZ]; exact hpres.2.1.2)
  exact (MonoidHom.ker_eq_bot_iff ψ).mp hker

theorem GGConfig.exists_f4_source_component {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J X : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) {n f : ℕ}
    (ψ : (ggU .F4 n f).K →* G)
    (hpres : GGPresentsG0 (ggG0 p B x L D J) (ggU .F4 n f).D .F4 n f ψ)
    (horigin : (X = L ∧ x ∈ ggG0 p B x L D J) ∨
      ∃ y : G, GGNbr p B x D J y X ∧ y ∈ ggG0 p B x L D J)
    (hq : CFSG.Assembly.IsQuasisimple ↥X) :
    ∃ u : (ggU .F4 n f).K, u ≠ 1 ∧ u ^ p = 1 ∧ Odd (orderOf u) ∧
      ∃ Q : Subgroup (ggU .F4 n f).K,
        IsComponentOf Q (Subgroup.centralizer ({u} : Set (ggU .F4 n f).K)) ∧
        Q.map ψ = X ∧ ∃ e : Q ≃* X, ∀ q : Q, (e q : G) = ψ q := by
  have hinj := f4_presentsG0_injective ψ hpres
  obtain ⟨u, huodd, hz, hQ, hQmap⟩ := ggActualMember_injective_model hcfg ψ hinj
    hpres.2.1.1 horigin hq
  have hpow : ψ u ^ p = 1 ∧ ψ u ≠ 1 := by
    rcases hz with ⟨-, hu⟩ | hNb
    · rw [hu]
      exact ⟨hcfg.data_L.2.2.1, hcfg.data_L.2.1⟩
    · exact ⟨hcfg.2.1.2.1.2 _ (hcfg.2.1.1 hNb.1.2.1), hNb.1.2.2.1⟩
  have hup : u ^ p = 1 := by
    apply hinj
    rw [map_pow, hpow.1, map_one]
  have hu1 : u ≠ 1 := by
    intro h
    apply hpow.2
    rw [h, map_one]
  let Q := X.comap ψ
  let e : Q ≃* X := (Q.equivMapOfInjective ψ hinj).trans (MulEquiv.subgroupCongr hQmap)
  exact ⟨u, hu1, hup, huodd, Q, hQ, hQmap, e, fun _ => rfl⟩

theorem GGConfig.exists_f4_source_langDatum {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J X : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) {n f : ℕ}
    (ψ : (ggU .F4 n f).K →* G)
    (hpres : GGPresentsG0 (ggG0 p B x L D J) (ggU .F4 n f).D .F4 n f ψ)
    (horigin : (X = L ∧ x ∈ ggG0 p B x L D J) ∨
      ∃ y : G, GGNbr p B x D J y X ∧ y ∈ ggG0 p B x L D J)
    (hq : CFSG.Assembly.IsQuasisimple ↥X) (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ u : (ggU .F4 n f).K, u ≠ 1 ∧ u ^ p = 1 ∧
      ∃ Q : Subgroup (ggU .F4 n f).K,
        IsComponentOf Q (Subgroup.centralizer ({u} : Set (ggU .F4 n f).K)) ∧
        Q.map ψ = X ∧ ∃ e : Q ≃* X, (∀ q : Q, (e q : G) = ψ q) ∧
          ∃ Δ : LangDatum .F4 (AlgebraicClosure (GaloisField 2 f)),
            Δ.Φ = Units.map (entrywiseHom (iterateFrobenius
              (AlgebraicClosure (GaloisField 2 f)) 2 f)) ∧ Δ.q = 2 ^ f ∧
            baseChangeGL (algebraMap (GaloisField 2 f) (AlgebraicClosure (GaloisField 2 f)))
              (Subtype.val (show adjointGroup .F4 (GaloisField 2 f) from u)) ∈
                Δ.torus.map (MulAut.conj Δ.g0).toMonoidHom := by
  obtain ⟨u, hu1, hup, _, Q, hQ, hQmap, e, he⟩ :=
    hcfg.exists_f4_source_component ψ hpres horigin hq
  have hf : 1 ≤ f := hpres.1.1.2.1
  have hcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  obtain ⟨Δ, hΦ, hqΔ, hT⟩ := f4_langDatum_through hf hcard hp hp2 u hup
  exact ⟨u, hu1, hup, Q, hQ, hQmap, e, he, Δ, hΦ, hqΔ, hT⟩

section NativePosition

variable {n f : ℕ}
variable [CharP (AlgebraicClosure (GaloisField 2 f)) 2] [Algebra (ZMod 2) (AlgebraicClosure (GaloisField 2 f))] [Algebra.IsAlgebraic (ZMod 2) (AlgebraicClosure (GaloisField 2 f))]

theorem f4_guarded_component_root_rank (hf : 1 ≤ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (Δ : LangDatum .F4 (AlgebraicClosure (GaloisField 2 f)))
    (hΦ : Δ.Φ = Units.map (entrywiseHom (iterateFrobenius (AlgebraicClosure (GaloisField 2 f)) 2 f))) (hq : Δ.q = 2 ^ f)
    (η : (ggU .F4 n f).K →* ModGL .F4 (AlgebraicClosure (GaloisField 2 f)))
    (hηpoint : ∀ u, η u = Δ.g0⁻¹ *
      ((F4ExplicitPos.AmbientAction.jF4 (K := (GaloisField 2 f)) (L := (AlgebraicClosure (GaloisField 2 f))) u : adjointGroup .F4 (AlgebraicClosure (GaloisField 2 f))) :
        ModGL .F4 (AlgebraicClosure (GaloisField 2 f))) * Δ.g0)
    (hη : Function.Injective η) (hrange : η.range = Δ.model)
    (a : Fin Tag.F4.rank → (AlgebraicClosure (GaloisField 2 f))ˣ) (hap : ∀ j, a j ^ p = 1) (ha1 : a ≠ 1)
    (haT : rootDiagUnit .F4 a ∈ Δ.torus) (w : WeylGroup .F4)
    (hρ : FrobRootMap Δ (MulAction.toPerm w)) (Q : Subgroup (ggU .F4 n f).K)
    (hmark : LargeEvenMarking Q (fun lab _ _ _ _ _ => GuardedLargeEvenLabel lab))
    (i : KernelComponent (rootCharHom a))
    (hQ : IsComponentOf (Q.map η) (Δ.Γ ⊓ Subgroup.centralizer {rootDiagUnit .F4 a}))
    (hle : Q.map η ≤ rootSpan .F4 (AlgebraicClosure (GaloisField 2 f)) (rationalRoots (MulAction.toPerm w) (rootCharHom a) i)) :
    3 ≤ compRank (componentRoots (rootCharHom a) i) := by
  haveI : Finite ((ggU .F4 n f).K) := by
    change Finite (adjointGroup .F4 (GaloisField 2 f))
    infer_instance
  have hfinRange : Finite η.range :=
    Finite.of_surjective (MonoidHom.ofInjective hη) (MonoidHom.ofInjective hη).surjective
  have hfin : Finite Δ.model := by rw [← hrange]; exact hfinRange
  obtain ⟨S, hSD, hSρ⟩ := LieCore.exists_langSetup_of_datum Δ (MulAction.toPerm w) hρ hfin hf hq
  have h1 : rootDiagUnit .F4 a ≠ 1 := by
    intro h
    apply ha1
    apply CFSG.LieType.Chevalley.rootDiagUnit_injective (τ := .F4)
    simpa only [CFSG.LieType.Chevalley.rootDiagUnit_one] using h
  have hpL : (p : (AlgebraicClosure (GaloisField 2 f))) ≠ 0 := by
    intro hzero
    have hd : 2 ∣ p := (CharP.cast_eq_zero_iff (AlgebraicClosure (GaloisField 2 f)) 2 p).1 hzero
    rcases (Nat.dvd_prime hp).1 hd with h | h
    · omega
    · exact hp2 h.symm
  have hTS : rootDiagUnit .F4 a ∈ S.D.torus := by rw [hSD]; exact haT
  have hQS : IsComponentOf (Q.map η) (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit .F4 a}) := by
    simpa only [LangSetup.Γ, hSD] using hQ
  have hspan : Q.map η ≤ rationalSpan S.ρ S.Γ (rootCharHom a) i := by
    change Q.map η ≤ rootSpan .F4 (AlgebraicClosure (GaloisField 2 f)) (rationalRoots S.ρ (rootCharHom a) i) ⊓ S.Γ
    rw [hSρ]
    refine le_inf hle ?_
    simpa only [LangSetup.Γ, hSD] using hQ.1.trans inf_le_left
  have hTame := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.langSetup_tame_of_prime
    S hp hpL (by intro h; cases h) hTS hap h1 i
  have hQSOpen : CFSG.Open.IsComponentOf (Q.map η)
      (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit .F4 a}) :=
    CFSG.Assembly.isComponentOf_iff_open.mp hQS
  obtain ⟨heq, hRq⟩ := eq_rationalComponent_of_isComponentOf_of_le_rationalSpan
    S hTS i hQSOpen hspan hTame
  have hmarkP : LargeEvenMarking (Q.map η)
      (fun lab _ _ _ _ _ => GuardedLargeEvenLabel lab) :=
    largeEvenMarking_of_mulEquiv (Q.equivMapOfInjective η hη).symm hmark
  have hmarkR : LargeEvenMarking (rationalComponent S.ρ S.Γ (rootCharHom a) i)
      (fun lab _ _ _ _ _ => GuardedLargeEvenLabel lab) := heq ▸ hmarkP
  have hqS : S.D.q = 2 ^ f := by rw [hSD]; exact hq
  exact f4_guarded_rationalComponent_root_rank S hf hqS hp hp2 a hap h1 hTS i hRq hmarkR


theorem f4_selected_models_of_rankThree_source (hf : 1 ≤ f)
    (Δ : LangDatum .F4 (AlgebraicClosure (GaloisField 2 f)))
    (hΦ : Δ.Φ = Units.map (entrywiseHom (iterateFrobenius (AlgebraicClosure (GaloisField 2 f)) 2 f))) (hq : Δ.q = 2 ^ f)
    (η : (ggU .F4 n f).K →* ModGL .F4 (AlgebraicClosure (GaloisField 2 f)))
    (hηpoint : ∀ u, η u = Δ.g0⁻¹ *
      ((F4ExplicitPos.AmbientAction.jF4 (K := (GaloisField 2 f)) (L := (AlgebraicClosure (GaloisField 2 f))) u : adjointGroup .F4 (AlgebraicClosure (GaloisField 2 f))) :
        ModGL .F4 (AlgebraicClosure (GaloisField 2 f))) * Δ.g0)
    (hη : Function.Injective η) (hrange : η.range = Δ.model)
    (a : Fin Tag.F4.rank → (AlgebraicClosure (GaloisField 2 f))ˣ) (i : KernelComponent (rootCharHom a))
    (σ : (AlgebraicClosure (GaloisField 2 f)) ≃+* (AlgebraicClosure (GaloisField 2 f))) (z : ModGL .F4 (AlgebraicClosure (GaloisField 2 f))) (v : WeylGroup .F4)
    (Φ : CFSG.Open.StatedSp 3 (GaloisField 2 f) →* ModGL .F4 (AlgebraicClosure (GaloisField 2 f))) (lam : CFSG.Open.StatedSp 3 (GaloisField 2 f) →* (ggU .F4 n f).K)
    (hσ : ∀ c, σ c = c ^ Δ.q) (hz : z ∈ F4ExplicitPos.NativePinFinal.Zsub (rootCharHom a))
    (hn : F4ExplicitPos.NativePinFinal.normalizesAll (rootCharHom a) z)
    (hstep : ∀ g ∈ rootSpan .F4 (AlgebraicClosure (GaloisField 2 f)) (componentRoots (rootCharHom a) i),
      Δ.step (z * g * z⁻¹) = z * frobGL σ g * z⁻¹)
    (hlam : Function.Injective lam) (hcomp : η.comp lam = Φ)
    (hformula :
      (componentRoots (rootCharHom a) i = (fun α => v • α) '' F4ExplicitPos.C3Range.c3RootSet ∧
        Φ = (((MulAut.conj z).toMonoidHom.comp
          (F4ExplicitPos.RationalC3.conjIM (AlgebraicClosure (GaloisField 2 f)) (canonicalRep (coxeterSystem .F4) (AlgebraicClosure (GaloisField 2 f)) v))).comp
          (statedSpMap (algebraMap (GaloisField 2 f) (AlgebraicClosure (GaloisField 2 f))) 3))) ∨
      (componentRoots (rootCharHom a) i = (fun α => v • α) '' b3LeviRoots ∧
        Φ = F4ExplicitPos.RationalB3.PhiB (K := (GaloisField 2 f)) (AlgebraicClosure (GaloisField 2 f))
          (canonicalRep (coxeterSystem .F4) (AlgebraicClosure (GaloisField 2 f)) v) z)) :
    ∃ (δ : Fin (ggU .PSp 3 f).D.rank → ℤ)
      (model' : SelectedRoot.SelectedSL2Model (ggU .PSp 3 f).D (GaloisField 2 f) δ)
      (γ : Fin (ggU .F4 n f).D.rank → ℤ)
      (model : SelectedRoot.SelectedSL2Model (ggU .F4 n f).D (GaloisField 2 f) γ) (u₀ : (ggU .F4 n f).K),
      ((MulAut.conj u₀).toMonoidHom.comp model.phi).range = (lam.comp model'.phi).range := by
  classical
  let K := GaloisField 2 f
  let Ω := AlgebraicClosure K
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  change (adjointGroup .F4 K →* ModGL .F4 Ω) at η
  change (CFSG.Open.StatedSp 3 K →* adjointGroup .F4 K) at lam
  change η.comp lam = Φ at hcomp
  change ∃ (δ : Fin 3 → ℤ)
      (model' : SelectedRoot.SelectedSL2Model (CFSG.LieType.Universal.Symplectic.rootDatum 3 K) K δ)
      (γ : Fin Tag.F4.rank → ℤ)
      (model : SelectedRoot.SelectedSL2Model (CFSG.LieType.Steinberg.Adjoint.f4Datum K) K γ)
      (u₀ : adjointGroup .F4 K),
      ((MulAut.conj u₀).toMonoidHom.comp model.phi).range = (lam.comp model'.phi).range
  let nV := canonicalRep (coxeterSystem .F4) Ω v
  let a₀ := Δ.g0 * z * nV
  let Fr := iterateFrobenius Ω 2 f
  let j : adjointGroup .F4 K →* ModGL .F4 Ω :=
    (adjointGroup .F4 Ω).subtype.comp (F4ExplicitPos.AmbientAction.jF4 (K := K) (L := Ω))
  change ∀ u : adjointGroup .F4 K, η u = Δ.g0⁻¹ * j u * Δ.g0 at hηpoint
  have hcard : Nat.card K = 2 ^ f := GaloisField.card 2 f (by omega)
  have ha₀ : a₀ ∈ adjointGroup .F4 Ω :=
    mul_mem (mul_mem Δ.g0_mem (F4ExplicitPos.NativePinFinal.Zsub_le_adjointGroup _ hz))
      (canonicalRep_mem_adjointGroup (coxeterSystem .F4) Ω v)
  have hfinish (k : Fin Tag.F4.rank)
      (model' : SelectedRoot.SelectedSL2Model (CFSG.LieType.Universal.Symplectic.rootDatum 3 K) K (Pi.single (0 : Fin 3) 1))
      (H : Subgroup (ModGL .F4 Ω)) (β : Fin Tag.F4.rank → ℤ) (hβ : IsRoot .F4 β)
      (herror : a₀⁻¹ * Units.map (entrywiseHom Fr) a₀ ∈ (rootSL2 .F4 Ω β).range)
      (hcentralizer : (rootSL2 .F4 Ω β).range ≤ Subgroup.centralizer (H : Set (ModGL .F4 Ω)))
      (hrootH : (CFSG.LieType.CurtisTits.rankOne (CFSG.LieType.Steinberg.Adjoint.f4Datum K).rootGroup k).map j ≤ H)
      (hsource : (lam.comp model'.phi).range.map η =
        ((CFSG.LieType.CurtisTits.rankOne (CFSG.LieType.Steinberg.Adjoint.f4Datum K).rootGroup k).map j).map
          (MulAut.conj (z * nV)).toMonoidHom) :
      ∃ (δ : Fin 3 → ℤ)
        (model' : SelectedRoot.SelectedSL2Model (CFSG.LieType.Universal.Symplectic.rootDatum 3 K) K δ)
        (γ : Fin Tag.F4.rank → ℤ)
        (model : SelectedRoot.SelectedSL2Model (CFSG.LieType.Steinberg.Adjoint.f4Datum K) K γ)
        (u₀ : adjointGroup .F4 K),
        ((MulAut.conj u₀).toMonoidHom.comp model.phi).range = (lam.comp model'.phi).range := by
    obtain ⟨u₀, hu₀⟩ := F4ExplicitPos.exists_finite_conjugator_of_rootSL2_error
      f hf hcard β hβ H a₀ ha₀ herror hcentralizer
    obtain ⟨model, hmodel⟩ := SelectedRoot.exists_model_f4 K k
    refine ⟨Pi.single (0 : Fin 3) 1, model', Pi.single k 1, model, u₀, ?_⟩
    apply Subgroup.map_injective (f := η) hη
    have hmap :
        ((CFSG.LieType.CurtisTits.rankOne (CFSG.LieType.Steinberg.Adjoint.f4Datum K).rootGroup k).map
          (MulAut.conj u₀).toMonoidHom).map η =
        ((CFSG.LieType.CurtisTits.rankOne (CFSG.LieType.Steinberg.Adjoint.f4Datum K).rootGroup k).map j).map
          (MulAut.conj (z * nV)).toMonoidHom := by
      simp only [Subgroup.map_map]
      have hpoint (u : adjointGroup .F4 K)
          (hu : u ∈ CFSG.LieType.CurtisTits.rankOne (CFSG.LieType.Steinberg.Adjoint.f4Datum K).rootGroup k) :
          (η.comp (MulAut.conj u₀).toMonoidHom) u =
            ((MulAut.conj (z * nV)).toMonoidHom.comp j) u := by
        have hact : j u₀ * j u * (j u₀)⁻¹ = a₀ * j u * a₀⁻¹ :=
          hu₀ (j u) (hrootH (Subgroup.mem_map_of_mem j hu))
        change η (u₀ * u * u₀⁻¹) = (z * nV) * j u * (z * nV)⁻¹
        rw [hηpoint]
        change Δ.g0⁻¹ * j (u₀ * u * u₀⁻¹) * Δ.g0 = _
        rw [map_mul, map_mul, map_inv, hact]
        dsimp only [a₀]
        group
      apply le_antisymm
      · intro x hx
        obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
        exact Subgroup.mem_map.mpr ⟨u, hu, (hpoint u hu).symm⟩
      · intro x hx
        obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
        exact Subgroup.mem_map.mpr ⟨u, hu, hpoint u hu⟩
    calc
      (((MulAut.conj u₀).toMonoidHom.comp model.phi).range).map η =
          (model.phi.range.map (MulAut.conj u₀).toMonoidHom).map η := by
        rw [MonoidHom.range_comp]
      _ = ((CFSG.LieType.CurtisTits.rankOne (CFSG.LieType.Steinberg.Adjoint.f4Datum K).rootGroup k).map
          (MulAut.conj u₀).toMonoidHom).map η := by rw [hmodel]
      _ = ((CFSG.LieType.CurtisTits.rankOne (CFSG.LieType.Steinberg.Adjoint.f4Datum K).rootGroup k).map j).map
          (MulAut.conj (z * nV)).toMonoidHom := hmap
      _ = (lam.comp model'.phi).range.map η := hsource.symm
  rcases hformula with ⟨hshape, hformula⟩ | ⟨hshape, hformula⟩
  · obtain ⟨hβ, _, herror, hcentralizer⟩ :=
      F4ExplicitPos.frobenius_error_rootSL2_data_of_c3 Δ hΦ hq σ hσ (rootCharHom a) i z hz hstep v hshape
    rw [hΦ] at herror
    obtain ⟨model', hsource⟩ := F4ExplicitPos.Sp3Selected.exists_sp3Model_rankOne_c3
      η lam nV z (hcomp.trans hformula) (0 : Fin 3)
    exact hfinish (c3Node (0 : Fin 3)) model' (F4ExplicitPos.RationalC3.conjIM Ω 1).range
      rootR hβ herror hcentralizer
      (F4ExplicitPos.Sp3Selected.map_rankOne_jF4_le_range_conjIM (K := K) (Ω := Ω) (0 : Fin 3)) hsource
  · obtain ⟨hβ, _, herror, hcentralizer⟩ :=
      F4ExplicitPos.frobenius_error_rootSL2_data_of_b3 Δ hΦ hq σ hσ (rootCharHom a) i z hz hstep v hshape
    rw [hΦ] at herror
    obtain ⟨model', hsource⟩ := F4ExplicitPos.Sp3Selected.exists_sp3Model_rankOne_b3
      η lam nV z (hcomp.trans hformula) (0 : Fin 3)
    exact hfinish (Fin.castSucc (0 : Fin 3)) model' (F4ExplicitPos.RationalB3.conjBM Ω 1).range
      rootS hβ herror hcentralizer
      (F4ExplicitPos.Sp3Selected.map_rankOne_jF4_le_range_conjBM (K := K) (Ω := Ω) (0 : Fin 3)) hsource

end NativePosition

theorem f4_native_component_selected {n f p : ℕ} (hf : 1 ≤ f)
    (hp : p.Prime) (hp2 : p ≠ 2) (u : (ggU .F4 n f).K) (hup : u ^ p = 1)
    (hu : u ≠ 1) (Q : Subgroup (ggU .F4 n f).K)
    (hQ : IsComponentOf Q (Subgroup.centralizer ({u} : Set (ggU .F4 n f).K)))
    (hmark : LargeEvenMarking Q (fun lab _ _ _ _ _ => GuardedLargeEvenLabel lab))
    (Δ : LangDatum .F4 (AlgebraicClosure (GaloisField 2 f)))
    (hΦ : Δ.Φ = Units.map (entrywiseHom (iterateFrobenius
      (AlgebraicClosure (GaloisField 2 f)) 2 f))) (hq : Δ.q = 2 ^ f)
    (hT : baseChangeGL (algebraMap (GaloisField 2 f) (AlgebraicClosure (GaloisField 2 f)))
      (Subtype.val (show adjointGroup .F4 (GaloisField 2 f) from u)) ∈
        Δ.torus.map (MulAut.conj Δ.g0).toMonoidHom) :
    ∃ S : Subgroup (ggU .F4 n f).K, MemberSelectedSL2At Q S ∧
      PresentedSelectedSL2At (t := .F4) (n := n) (f := f)
        (MonoidHom.id (ggU .F4 n f).K) S := by
  classical
  let K := GaloisField 2 f
  let Ω := AlgebraicClosure K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  letI : Algebra (ZMod 2) Ω := ZMod.algebra Ω 2
  letI : Algebra.IsAlgebraic (ZMod 2) Ω :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.isAlgebraic_zmod_algebraicClosure_of_finite K 2
  let Fr := iterateFrobenius Ω 2 f
  have hcard : Nat.card K = 2 ^ f := GaloisField.card 2 f (by omega)
  have hFr : ∀ c, Fr c = c ^ Nat.card K := by
    intro c
    change iterateFrobenius Ω 2 f c = c ^ Nat.card K
    rw [iterateFrobenius_def, hcard]
  have hFrsurj : Function.Surjective Fr :=
    (bijective_iterateFrobenius (R := Ω) (p := 2) (n := f)).2
  change ((F4ExplicitPos.AmbientAction.jF4 (K := K) (L := Ω) u :
    adjointGroup .F4 Ω) : ModGL .F4 Ω) ∈ Δ.torus.map (MulAut.conj Δ.g0).toMonoidHom at hT
  obtain ⟨η, hηpoint, hη, hrange, a, _, hap, ha1, haT, w, _, hρ, i, hQΓ, hle⟩ :=
    F4ExplicitPos.component_le_rationalRootSpan_of_frobenius Fr hFr hFrsurj Δ hΦ
      (hq.trans hcard.symm) hp hp2 u hup hu Q hQ hT
  have h3 := f4_guarded_component_root_rank (n := n) (f := f) hf hp hp2 Δ hΦ hq η hηpoint hη hrange
    a hap ha1 haT w hρ Q hmark i hQΓ hle
  have hpodd : p % 2 = 1 := by
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
    omega
  have hpΩ : (p : Ω) ≠ 0 := by
    intro hzero
    have hd : 2 ∣ p := (CharP.cast_eq_zero_iff Ω 2 p).mp hzero
    rcases (Nat.dvd_prime hp).mp hd with he | he
    · norm_num at he
    · exact hp2 he.symm
  have haDiag : rootDiagUnit .F4 a ≠ 1 := by
    intro h
    exact ha1 (CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_injective
      (h.trans rootDiagUnit_one.symm))
  obtain ⟨v, J, hJ, hshape, hr3, h18⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.f4_rank_ge_three_component_is_levi_odd_of_coord
      hp.pos hpodd hpΩ hap haDiag i h3
  obtain ⟨hstable, _⟩ :=
    F4ExplicitPos.JointRankOrbit.f4_cyclic_componentOrbitLength_eq_one_of_rank_ge_two
      Δ (MulAction.toPerm w) hρ a haT i (by omega)
  have hker : ∀ γ ∈ kernelRoots (rootCharHom a), (MulAction.toPerm w) γ ∈ kernelRoots (rootCharHom a) := by
    rintro γ ⟨hγroot, hγ⟩
    change rootChar a γ = 1 at hγ
    refine ⟨(hρ.isRoot_iff γ).2 hγroot, ?_⟩
    show rootChar a ((MulAction.toPerm w) γ) = 1
    rw [hρ.rootChar_eq a haT γ hγroot, hγ, one_pow]
  have hrat := F4ExplicitPos.OddKernelOrbit.rationalRoots_eq_componentRoots_of_image_eq (MulAction.toPerm w) (rootCharHom a) i hstable
  have hleH : Q.map η ≤ rootSpan .F4 Ω (componentRoots (rootCharHom a) i) := by
    rwa [hrat] at hle
  have hHC : rootSpan .F4 Ω (componentRoots (rootCharHom a) i) ≤
      Subgroup.centralizer ({rootDiagUnit .F4 a} : Set (ModGL .F4 Ω)) :=
    (CFSG.HardMathSupport.Timmesfeld.CrossChar.componentRootSpan_le_toralCentralizer a i).trans inf_le_right
  have hshapes : (∃ v : WeylGroup .F4, componentRoots (rootCharHom a) i =
      (fun α => v • α) '' F4ExplicitPos.C3Range.c3RootSet) ∨
      ∃ v : WeylGroup .F4, componentRoots (rootCharHom a) i = (fun α => v • α) '' b3LeviRoots := by
    rcases hJ with hb | hc
    · right
      refine ⟨v, ?_⟩
      simpa only [hb, F4ExplicitPos.SelectedLiteral.parabolicRoots_f4LeviB3_eq_b3LeviRoots] using hshape
    · left
      refine ⟨v, ?_⟩
      simpa only [hc, F4ExplicitPos.SelectedLiteral.parabolicRoots_f4LeviC3_eq_c3RootSet] using hshape
  obtain ⟨σ, z, v', Φ, lam, hσ, hz, hn, hstep, hlam, hlamrange, hcomp, hformula⟩ :=
    F4ExplicitPos.exists_sp6_source_of_rankThree η hη Q (rootCharHom a) Δ f hf hq hcard
      (MulAction.toPerm w) hρ i hker hstable hr3 h18 hshapes
      (Subgroup.centralizer ({rootDiagUnit .F4 a} : Set (ModGL .F4 Ω))) hHC hQΓ hleH
  obtain ⟨δ, model', γ, model, u₀, hmatch⟩ :=
    f4_selected_models_of_rankThree_source (n := n) (f := f) hf Δ hΦ hq η hηpoint hη hrange a i
      σ z v' Φ lam hσ hz hn hstep hlam hcomp hformula
  have hadm : StatedLieAdmissible .PSp 3 2 f :=
    ⟨Nat.prime_two, hf, by decide, by simp⟩
  have hkerlam : lam.ker ≤ Subgroup.center (ggU .PSp 3 f).K := by
    rw [(MonoidHom.ker_eq_bot_iff lam).mpr hlam]
    exact bot_le
  refine ⟨(lam.comp model'.phi).range, ?_, ?_⟩
  · refine ⟨.PSp, 3, f, lam, hadm, ?_, hkerlam, hlamrange, K,
      inferInstance, inferInstance, inferInstance, δ, model', rfl⟩
    change 2 ≤ 3
    decide
  · refine ⟨K, inferInstance, inferInstance, inferInstance, γ, model, u₀, ?_⟩
    change ((MulAut.conj u₀).toMonoidHom.comp model.phi).range = (lam.comp model'.phi).range
    exact hmatch

theorem ggActualMember_F4_selected
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs L D J X : Subgroup G} {x : G}
    (hcfg : GGConfig p B Bs x L D J) {n f : ℕ} (ψ : (ggU .F4 n f).K →* G)
    (hpres : GGPresentsG0 (ggG0 p B x L D J) (ggU .F4 n f).D .F4 n f ψ)
    (horigin : (X = L ∧ x ∈ ggG0 p B x L D J) ∨
      ∃ y : G, GGNbr p B x D J y X ∧ y ∈ ggG0 p B x L D J)
    (hmark : LargeEvenMarking ↥X (fun lab _ _ _ _ _ => GuardedLargeEvenLabel lab)) :
    ∃ S : Subgroup G, MemberSelectedSL2At X S ∧ PresentedSelectedSL2At ψ S := by
  obtain ⟨hp, hp2, -⟩ := (hcfg.1.2.2.2.2.2.1 : p ∈ CFSG.Assembly.LargeEvenBeta 4 G)
  obtain ⟨u, hu1, hup, Q, hQ, hQmap, eQ, -, Δ, hΦ, hq, hT⟩ :=
    hcfg.exists_f4_source_langDatum ψ hpres horigin (isQuasisimple_of_largeEvenMarking hmark)
      hp hp2
  have hmarkQ : LargeEvenMarking Q (fun lab _ _ _ _ _ => GuardedLargeEvenLabel lab) :=
    largeEvenMarking_of_mulEquiv eQ hmark
  obtain ⟨S, hSQ, hSP⟩ := f4_native_component_selected hpres.1.1.2.1 hp hp2
    u hup hu1 Q hQ hmarkQ Δ hΦ hq hT
  refine ⟨S.map ψ, ?_, ?_⟩
  · have h := hSQ.map_of_injective ψ (f4_presentsG0_injective ψ hpres)
    exact hQmap ▸ h
  · have h := hSP.map ψ
    simpa only [MonoidHom.comp_id] using h

theorem GGSecFiveRouteCfg.exists_selected_F4_of_guarded
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {n f : ℕ} (ψ : (ggU .F4 n f).K →* G)
    (hpres : GGPresentsG0 (ggG0 p B x L D J) (ggU .F4 n f).D .F4 n f ψ)
    (hx : x ∈ ggG0 p B x L D J)
    (hmark : LargeEvenMarking ↥L (fun lab _ _ _ _ _ => GuardedLargeEvenLabel lab)) :
    ∃ S : Subgroup G, MemberSelectedSL2At L S ∧ PresentedSelectedSL2At ψ S :=
  ggActualMember_F4_selected hcfg.1.1 ψ hpres (Or.inl ⟨rfl, hx⟩) hmark

theorem ggF4Join_selectedAt_originalL
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (_hReg : ¬ GGSecFiveTier1Region p B Bs x L D J)
    {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (_hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (_hF4 : GGIsWeylMatrixF4 M)
    (_hB3 : GGWeylOfType p (CoxeterMatrix.B 3) (ggAutomizer L Bs))
    {n f : ℕ} (ψ : (ggU .F4 n f).K →* G)
    (hpres : GGPresentsG0 (ggG0 p B x L D J) (ggU .F4 n f).D .F4 n f ψ)
    (hx : x ∈ ggG0 p B x L D J)
    (hmark : LargeEvenMarking ↥L (fun lab _ _ _ _ _ => GuardedLargeEvenLabel lab)) :
    ∃ S : Subgroup G, MemberSelectedSL2At L S ∧ PresentedSelectedSL2At ψ S :=
  hcfg.exists_selected_F4_of_guarded ψ hpres hx hmark

theorem ggF4JoinMemberAt_F4 : GGF4JoinMemberAt .F4 := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hReg _ _ ι M e hP hF4 _ hB3 n f ψ hpres _ hx hmark
  exact ggF4Join_selectedAt_originalL hcfg hReg hP hF4 hB3 ψ hpres hx hmark

end CFSG.StandardType
