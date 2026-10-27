module

public import CFSG.LocalAnalysis.StandardType.GGL45NtDefs
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyClosedLang
public import CFSG.LieType.AlgebraicGroups.RationalCentralizerCocycle
public import CFSG.LieType.Ree.Endo
public import CFSG.LocalAnalysis.StandardType.GGTableBExcBasic
public import CFSG.LieType.Chevalley.CoordinateFieldBaseChange
public import CFSG.RankThree.Chevalley.EvenPinnedRootSL2
public import CFSG.RankThree.Chevalley.G2F4FiniteFieldFixedMatrices
public import CFSG.LieType.SeitzGeneration.ExcHigh.E8FivePurityLang
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotAlignTori
public import CFSG.LieType.Chevalley.GraphFixedF4GroupDescent
public import CFSG.LieType.Chevalley.GraphFixedData
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE7Data
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE8Rank1
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.MPart
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Transport
public import CFSG.HardMathSupport.Lang.AnisoE6.CatBridge
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerResiduals
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.LieType.SeitzGeneration.ExcHighThree.Pilot
public import CFSG.LieType.SeitzGeneration.ExtSeitzReeF4Cyclic
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.Chevalley.SteinbergBNNoninnerComponentNodes
public import CFSG.RankThree.Chevalley.SteinbergCFOddE7E8NoninnerComponent
public import CFSG.RankThree.PartOne.BRANCH.RankRee
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.UnitaryHigherCrossPrimeTorus
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
public import CFSG.RankThree.PartOne.KE.A1Fixed
public import CFSG.RankThree.PartOne.KE.Basic
public import CFSG.RankThree.PartOne.KE.D4LayerAlgebraic
public import CFSG.RankThree.PartOne.KE.E8FourA1Family
public import CFSG.RankThree.PartOne.KE.E8NineData
public import CFSG.RankThree.PartOne.KE.NativeCyclicMain
public import CFSG.RankThree.PartOne.KF4.EvenDescent
public import CFSG.RankThree.PartOne.KGD.D4QA1
public import CFSG.RankThree.PartOne.N143.Weyl613Defs
public import CFSG.RankThree.PartOne.N143X.KF64WSimple
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

namespace CFSG.HardMathSupport.C14ExcBridgeU

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType CFSG.Assembly

noncomputable section

@[expose] def castGLS {r : ℕ} {S S' : (Fin r → ℤ) → Prop} (h : S = S') (K : Type) [Field K] :
    MarkChev.GLS S K ≃* MarkChev.GLS S' K := by
  subst h; exact MulEquiv.refl _

theorem mem_chevH_iff_castGLS {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) {S S' : (Fin r → ℤ) → Prop}
    (h : S = S') (K : Type) [Field K] (d : Bool) (g : MarkChev.GLS S K) :
    g ∈ MarkChev.chevH A S K d ↔ castGLS h K g ∈ MarkChev.chevH A S' K d := by
  subst h; exact Iff.rfl

theorem castGLS_symm_entrywise {r : ℕ} {S S' : (Fin r → ℤ) → Prop} (h : S = S') (K : Type)
    [Field K] (f : K → K) (hf : f 0 = 0) (g g' : MarkChev.GLS S' K)
    (hg : (g' : Module.End K (MarkChev.Space S' K)) = MarkChev.entrywise S' K f hf g) :
    ((castGLS h K).symm g' : Module.End K (MarkChev.Space S K)) =
      MarkChev.entrywise S K f hf ((castGLS h K).symm g) := by
  subst h; exact hg

@[expose] def kappa (τ : Tag) (K : Type) [Field K] : LargeEvenChevGL τ.cartan K ≃* ModGL τ K :=
  castGLS (largeEvenIsRoot_eq_isRoot τ) K

theorem mem_chevH_iff_kappa (τ : Tag) (K : Type) [Field K] (g : LargeEvenChevGL τ.cartan K) :
    g ∈ LargeEvenChevH τ.cartan K false ↔ kappa τ K g ∈ adjointGroup τ K := by
  rw [largeEvenChevH_eq, mem_chevH_iff_castGLS τ.cartan (largeEvenIsRoot_eq_isRoot τ),
    chevH_false_eq_adjointGroup]
  rfl

theorem map_kappa_chevH (τ : Tag) (K : Type) [Field K] :
    (LargeEvenChevH τ.cartan K false).map (kappa τ K).toMonoidHom = adjointGroup τ K := by
  ext g
  constructor
  · rintro ⟨g', hg', rfl⟩
    exact (mem_chevH_iff_kappa τ K g').1 hg'
  · intro hg
    refine ⟨(kappa τ K).symm g, ?_, by simp⟩
    show (kappa τ K).symm g ∈ LargeEvenChevH τ.cartan K false
    rw [mem_chevH_iff_kappa]
    simpa using hg

theorem kappa_symm_entrywise (τ : Tag) (K : Type) [Field K] (σ : K →+* K) (g : ModGL τ K) :
    ((kappa τ K).symm (Units.map (entrywiseHom σ) g) :
        Module.End K (LargeEvenChevModule τ.cartan K)) =
      LargeEvenEntrywise τ.cartan K σ σ.map_zero ((kappa τ K).symm g : Module.End K _) :=
  castGLS_symm_entrywise (largeEvenIsRoot_eq_isRoot τ) K σ σ.map_zero g _ rfl

@[expose] def eH (τ : Tag) (K : Type) [Field K] :
    LargeEvenChevH τ.cartan K false ≃* adjointGroup τ K :=
  ((kappa τ K).subgroupMap _).trans (MulEquiv.subgroupCongr (map_kappa_chevH τ K))

@[simp] theorem eH_apply (τ : Tag) (K : Type) [Field K]
     (h : LargeEvenChevH τ.cartan K false) :
    (eH τ K h : ModGL τ K) = kappa τ K h := rfl

theorem center_chevH_eq_bot (τ : Tag) (K : Type) [Field K]
     [Finite K] :
    Subgroup.center (LargeEvenChevH τ.cartan K false) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hx' : eH τ K x ∈ Subgroup.center (adjointGroup τ K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := (eH τ K).surjective g
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hx) y]
  rw [CFSG.LieType.Chevalley.center_adjointGroup_eq_bot, Subgroup.mem_bot] at hx'
  rw [Subgroup.mem_bot, ← (eH τ K).map_eq_one_iff]
  exact hx'

@[expose] def eR (τ : Tag) (K : Type) [Field K]
    [Finite K] : TableBExc.RecipeGroup τ K ≃* adjointGroup τ K :=
  ((QuotientGroup.quotientMulEquivOfEq (center_chevH_eq_bot τ K)).trans
    QuotientGroup.quotientBot).trans (eH τ K)

@[simp] theorem eR_mk (τ : Tag) (K : Type) [Field K]
     [Finite K] (h : LargeEvenChevH τ.cartan K false) :
    eR τ K (LargeEvenCenterMk _ h) = eH τ K h := rfl

theorem eR_fieldAut (τ : Tag) (K : Type) [Field K]
    [Finite K] (σ : K ≃+* K) (φ : MulAut (TableBExc.RecipeGroup τ K))
    (hφ : LargeEvenGraphAut (LargeEvenCenterMk (LargeEvenChevH τ.cartan K false))
      (fun h h' => ((h' : LargeEvenChevGL τ.cartan K) : Module.End K _) =
        LargeEvenEntrywise τ.cartan K σ (map_zero σ)
          ((h : LargeEvenChevGL τ.cartan K) : Module.End K _)) φ)
    (r : TableBExc.RecipeGroup τ K) :
    (eR τ K (φ r) : ModGL τ K) = Units.map (entrywiseHom (σ : K →+* K)) (eR τ K r) := by
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective r
  set x : ModGL τ K := Units.map (entrywiseHom (σ : K →+* K)) (kappa τ K h)
  have hx : x ∈ adjointGroup τ K := baseChangeGL_mem_adjointGroup (σ : K →+* K)
    ((mem_chevH_iff_kappa τ K h).1 h.2)
  have hmem : (kappa τ K).symm x ∈ LargeEvenChevH τ.cartan K false := by
    rw [mem_chevH_iff_kappa]; simpa using hx
  have hrel := hφ h ⟨_, hmem⟩
    ((kappa_symm_entrywise τ K (σ : K →+* K) (kappa τ K h)).trans
      (by rw [MulEquiv.symm_apply_apply]; rfl))
  change (eR τ K (φ (LargeEvenCenterMk _ h)) : ModGL τ K) = _
  rw [hrel, eR_mk, eH_apply, MulEquiv.apply_symm_apply]
  rfl

section Fixed

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Chevalley

theorem mem_map_baseChange_of_frobenius_fixed_E7_of_bijective
    {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L]
    [CharP K 2] (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ Nat.card K) (hbij : Function.Bijective Fr) {g : ModGL Tag.E7 L}
    (hg : g ∈ adjointGroup Tag.E7 L) (hfix : Units.map (entrywiseHom Fr) g = g) :
    g ∈ (adjointGroup Tag.E7 K).map (baseChangeGL (algebraMap K L)) := by
  set σ : L ≃+* L := RingEquiv.ofBijective Fr hbij
  have hσ : σ.toRingHom = Fr := RingHom.ext fun _ => rfl
  have hσfix : ∀ c, σ c = c → c ∈ Set.range (algebraMap K L) := fun c hc =>
    CFSG.RankThree.PartOne.KE.mem_range_algebraMap_of_pow_card_eq (by rw [← hFr]; exact hc)
  have hg' : g ∈ entrywiseFixedGroup Tag.E7 σ := ⟨hg, by
    change Units.map (entrywiseHom σ.toRingHom) g = g
    rw [hσ]
    exact hfix⟩
  obtain ⟨h, hh, j, hj, rfl⟩ := mem_mul_of_mem_entrywiseFixedGroup hg'
  obtain ⟨hhT, -, hhF⟩ := hh
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hhT
  have hbσ : (fun i => Units.map σ.toRingHom.toMonoidHom (b i)) = b := by
    apply rootDiagUnit_injective (τ := Tag.E7) (K := L)
    rw [← baseChangeGL_rootDiagUnit, ← units_map_entrywiseHom_eq_baseChangeGL]
    exact hhF
  have hbK : ∀ i, ∃ c : Kˣ, Units.map (algebraMap K L).toMonoidHom c = b i := by
    intro i
    obtain ⟨c, hc⟩ := hσfix (b i : L) (by
      have := congrArg Units.val (congrFun hbσ i)
      simpa using this)
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [map_zero] at hc
      exact (b i).ne_zero hc.symm
    exact ⟨Units.mk0 c hc0, Units.ext (by simpa using hc)⟩
  choose bK hbK using hbK
  have hjK : j ∈ (adjointGroup Tag.E7 K).map (baseChangeGL (algebraMap K L)) := by
    rw [fixedFieldImage_eq_closure] at hj
    refine (Subgroup.closure_le _).2 ?_ hj
    rintro _ ⟨i, c, hc, rfl | rfl⟩
    · obtain ⟨c', rfl⟩ := hσfix c hc
      exact ⟨xUnit Tag.E7 K i c', xUnit_mem_adjointGroup i c', baseChangeGL_xUnit _ i c'⟩
    · obtain ⟨c', rfl⟩ := hσfix c hc
      exact ⟨yUnit Tag.E7 K i c', yUnit_mem_adjointGroup i c', baseChangeGL_yUnit _ i c'⟩
  obtain ⟨jK, hjKC, rfl⟩ := hjK
  have hb : rootDiagUnit Tag.E7 b = baseChangeGL (algebraMap K L) (rootDiagUnit Tag.E7 bK) := by
    rw [baseChangeGL_rootDiagUnit]
    congr 1
    funext i
    exact (hbK i).symm
  rw [hb]
  exact ⟨rootDiagUnit Tag.E7 bK * jK, mul_mem
    (CFSG.SeitzReduction.E7Pilot.rootDiagUnit_mem_adjointGroup_of_ringChar_eq_two
      (ringChar.eq K 2) bK) hjKC, map_mul _ _ _⟩

theorem fixed_eq_map
    {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L]
    {τ : Tag} (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E7 ∨ τ = .E8) [CharP K 2]
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K) (hbij : Function.Bijective Fr) :
    adjointGroup τ L ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) =
      (adjointGroup τ K).map (baseChangeGL (algebraMap K L)) := by
  rcases hτ with rfl | rfl | rfl | rfl
  · exact CFSG.RankThree.Chevalley.frobenius_fixed_eq_map_of_bijective (Or.inl rfl) Fr hFr hbij
  · exact CFSG.RankThree.Chevalley.frobenius_fixed_eq_map_of_bijective (Or.inr rfl) Fr hFr hbij
  all_goals refine le_antisymm (fun g hg => ?_) ?_
  · exact mem_map_baseChange_of_frobenius_fixed_E7_of_bijective Fr hFr hbij hg.1 hg.2
  · rintro _ ⟨g, hg, rfl⟩
    exact ⟨CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup _ hg, units_map_entrywiseHom_baseChangeGL_algebraMap Fr hFr g⟩
  · exact CFSG.LieType.SeitzGeneration.ExcHigh.mem_map_baseChange_of_frobenius_fixed_E8_of_bijective
      Fr hFr hbij hg.1 hg.2
  · rintro _ ⟨g, hg, rfl⟩
    exact ⟨CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup _ hg, units_map_entrywiseHom_baseChangeGL_algebraMap Fr hFr g⟩

end Fixed

@[expose] def endPowU {G : Type*} [Monoid G] (S : G →* G) (n : ℕ) : G →* G :=
  @HPow.hPow (Monoid.End G) ℕ (Monoid.End G) _ S n

section Frob

open CFSG.LieType.AlgebraicGroups

theorem iterateFrobenius_comp

     {L : Type} [Field L] (p a b : ℕ) [ExpChar L p] :
    (iterateFrobenius L p a).comp (iterateFrobenius L p b) = iterateFrobenius L p (a + b) := by
  ext c
  simp only [RingHom.comp_apply, iterateFrobenius_def, ← pow_mul, ← pow_add, add_comm a b]

theorem endPow_zero'

     {G : Type*} [Monoid G] (S : G →* G) (x : G) :
    endPowU S 0 x = x := by
  change (((show Monoid.End G from S) ^ 0 : Monoid.End G) : G → G) x = x
  rw [pow_zero]; rfl

theorem endPow_succ'

     {G : Type*} [Monoid G] (S : G →* G) (m : ℕ) (x : G) :
    endPowU S (m + 1) x = S (endPowU S m x) := by
  change (((show Monoid.End G from S) ^ (m + 1) : Monoid.End G) : G → G) x = _
  rw [pow_succ']; rfl

theorem endPow_frobTwist_one

    {τ : Tag} {L : Type} [Field L] [CharP L 2] (e m : ℕ)
    (g : ModGL τ L) :
    endPowU (frobTwistGL τ L 2 e 1) m g =
      Units.map (entrywiseHom (iterateFrobenius L 2 (e * m))) g := by
  induction m with
  | zero =>
    rw [mul_zero, endPow_zero']
    ext : 1
    change _ = entrywise _ _
    rw [iterateFrobenius_zero, entrywise_id]
  | succ m ih =>
    rw [endPow_succ', ih, frobTwistGL_apply, one_mul, inv_one, mul_one]
    change baseChangeGL _ (baseChangeGL _ g) = baseChangeGL _ g
    rw [baseChangeGL_baseChangeGL, iterateFrobenius_comp, mul_add_one, add_comm]

end Frob

section Bridge

open CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus

theorem frob_pow_apply

     {K : Type} [Field K] (σ₀ : K ≃+* K) (h : ∀ c, σ₀ c = c ^ 2) (a : ℕ)
    (c : K) : (σ₀ ^ a) c = c ^ 2 ^ a := by
  induction a generalizing c with
  | zero => rw [pow_zero, pow_zero, pow_one]; rfl
  | succ a ih =>
    rw [pow_succ]
    change (σ₀ ^ a) (σ₀ c) = _
    rw [ih, h, ← pow_mul, pow_succ']

theorem exists_e_j

     {n a p : ℕ} (hp : p.Prime) (hn : 0 < n) (h1 : n ∣ a * p) (h2 : ¬ n ∣ a) :
    p ∣ n ∧ ∃ j, a = n / p * j ∧ ¬ p ∣ j := by
  have hg0 : 0 < Nat.gcd n a := Nat.gcd_pos_of_pos_left _ hn
  have hcop := Nat.coprime_div_gcd_div_gcd (m := n) (n := a) hg0
  have hn' := (Nat.mul_div_cancel' (Nat.gcd_dvd_left n a)).symm
  have ha' := (Nat.mul_div_cancel' (Nat.gcd_dvd_right n a)).symm
  generalize Nat.gcd n a = g at hg0 hcop hn' ha'
  generalize n / g = n' at hcop hn'
  generalize a / g = a' at hcop ha'
  subst hn' ha'
  have hdvd : n' ∣ p :=
    hcop.dvd_of_dvd_mul_left (Nat.dvd_of_mul_dvd_mul_left hg0 (by rwa [mul_assoc] at h1))
  rcases (Nat.dvd_prime hp).1 hdvd with h | h
  · exfalso; apply h2; rw [h, mul_one]; exact dvd_mul_right g a'
  · rw [h] at hcop ⊢
    refine ⟨dvd_mul_left _ _, a', by rw [Nat.mul_div_cancel _ hp.pos], fun hpa => ?_⟩
    exact hp.one_lt.ne' (hcop.eq_one_of_dvd hpa)

theorem fieldImage_frob

    {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) {p : ℕ} (hp : p.Prime)
    (f : MulAut (TableBExc.RecipeGroup τ K))
    (hf : f ∈ LargeEvenChevFieldImage τ.cartan K (LargeEvenChevH τ.cartan K false))
    (hfp : orderOf f = p) :
    p ∣ n ∧ ∃ j, ¬ p ∣ j ∧ ∀ r, (eR τ K (f r) : ModGL τ K) =
      baseChangeGL (iterateFrobenius K 2 (n / p * j)) (eR τ K r) := by
  obtain ⟨σ, hσ⟩ := hf
  obtain ⟨σ₀, hσ₀, hord, hzp, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two hn hK
  have hfin₀ : IsOfFinOrder σ₀ := by
    rw [← orderOf_pos_iff, hord]; omega
  obtain ⟨a, ha⟩ : ∃ a : ℕ, σ₀ ^ a = σ := by
    have : σ ∈ Subgroup.zpowers σ₀ := hzp ▸ Subgroup.mem_top σ
    rw [← hfin₀.mem_powers_iff_mem_zpowers] at this
    exact this
  have hσa : ∀ c, σ c = c ^ 2 ^ a := fun c => by rw [← ha, frob_pow_apply σ₀ hσ₀]
  have hfk : ∀ (k : ℕ) (r : TableBExc.RecipeGroup τ K),
      (eR τ K ((f ^ k) r) : ModGL τ K) =
        baseChangeGL (iterateFrobenius K 2 (a * k)) (eR τ K r) := by
    intro k
    induction k with
    | zero =>
      intro r
      rw [mul_zero, iterateFrobenius_zero, pow_zero]
      exact (CFSG.LieType.Chevalley.baseChangeGL_id _ _).symm
    | succ k ih =>
      intro r
      rw [pow_succ', MulAut.mul_apply, eR_fieldAut τ K σ f hσ, ih]
      change baseChangeGL _ (baseChangeGL _ _) = _
      rw [baseChangeGL_baseChangeGL]
      have : (σ : K →+* K).comp (iterateFrobenius K 2 (a * k)) =
          iterateFrobenius K 2 (a * (k + 1)) := by
        ext c
        change σ (iterateFrobenius K 2 (a * k) c) = _
        rw [hσa, iterateFrobenius_def, iterateFrobenius_def, ← pow_mul, ← pow_add, mul_add_one]
      rw [this]
  have hrank : 0 < τ.rank := by cases τ <;> decide
  have hfix : ∀ m, (∀ r, (eR τ K ((f ^ m) r) : ModGL τ K) = eR τ K r) → n ∣ a * m := by
    intro m hm
    have hc : ∀ c : K, c ^ 2 ^ (a * m) = c := by
      intro c
      have := hm ((eR τ K).symm ⟨xUnit τ K ⟨0, hrank⟩ c, xUnit_mem_adjointGroup _ c⟩)
      rw [hfk, MulEquiv.apply_symm_apply] at this
      change baseChangeGL _ (xUnit τ K ⟨0, hrank⟩ c) = xUnit τ K ⟨0, hrank⟩ c at this
      rw [baseChangeGL_xUnit] at this
      have := xOp_injective _ (congrArg Units.val this)
      rwa [iterateFrobenius_def] at this
    have : σ₀ ^ (a * m) = 1 := RingEquiv.ext fun c => by
      rw [frob_pow_apply σ₀ hσ₀, hc]; rfl
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one this
  have h1 : n ∣ a * p := hfix p fun r => by
    rw [← hfp, pow_orderOf_eq_one]; rfl
  have h2 : ¬ n ∣ a := by
    intro hna
    have hσ1 : σ₀ ^ a = 1 := orderOf_dvd_iff_pow_eq_one.1 (hord ▸ hna)
    have hid : iterateFrobenius K 2 (a * 1) = RingHom.id K := RingHom.ext fun c => by
      rw [iterateFrobenius_def, mul_one, ← frob_pow_apply σ₀ hσ₀, hσ1]; rfl
    have hf1 : f = 1 := by
      ext r
      apply (eR τ K).injective
      apply Subtype.ext
      have := hfk 1 r
      rw [pow_one, hid, CFSG.LieType.Chevalley.baseChangeGL_id] at this
      exact this
    rw [hf1, orderOf_one] at hfp
    exact hp.one_lt.ne hfp
  obtain ⟨hpn, j, haj, hpj⟩ := exists_e_j hp (by omega) h1 h2
  refine ⟨hpn, j, hpj, fun r => ?_⟩
  have := hfk 1 r
  rwa [pow_one, mul_one, haj] at this

theorem bridge_untwisted

    {τ : Tag} (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hT : TableB.torusSubgroup τ.cartan K = ⊤)
    {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] {p : ℕ} (hp : p.Prime) :
    (∃ f ∈ LargeEvenChevFieldImage τ.cartan K (LargeEvenChevH τ.cartan K false), orderOf f = p) →
    ∃ (e : ℕ) (Q : ModGL τ L),
      1 ≤ e ∧ IsDiagramTwistMatrix τ L Q ∧
      ((∀ g ∈ adjointGroup τ L, frobTwistGL τ L 2 e Q g ∈ adjointGroup τ L) ∧
       ∃ (ρ : TableBExc.RecipeGroup τ K →* ModGL τ L)
        (Θ : ↥(adjointGroup τ L ⊓ (endPowU (frobTwistGL τ L 2 e Q) p).eqLocus (MonoidHom.id _)) →*
          MulAut (TableBExc.RecipeGroup τ K)),
        Function.Injective ρ ∧
        (∀ r, ρ r ∈ adjointGroup τ L ⊓ (endPowU (frobTwistGL τ L 2 e Q) p).eqLocus (MonoidHom.id _)) ∧
        Function.Injective Θ ∧ (∀ φ, φ ∈ TableBExc.RecipeID τ K ↔ ∃ g, Θ g = φ) ∧
        (∀ g r, ρ (Θ g r) = g * ρ r * (g : ModGL τ L)⁻¹) ∧
        ∀ f ∈ LargeEvenChevFieldImage τ.cartan K (LargeEvenChevH τ.cartan K false), orderOf f = p →
          ∃ j : ℕ, ¬ p ∣ j ∧ ∀ r, ρ (f r) = (endPowU (frobTwistGL τ L 2 e Q) j) (ρ r)) ∧
      IsSteinbergEnd τ L ((2 ^ e) ^ p) (endPowU (frobTwistGL τ L 2 e Q) p) ∧
      Finite ↥(adjointGroup τ L ⊓ (endPowU (frobTwistGL τ L 2 e Q) p).eqLocus (MonoidHom.id _)) := by
  classical
  rintro ⟨f, hfF, hfp⟩
  obtain ⟨hpn, -⟩ := fieldImage_frob hn hK hp f hfF hfp
  set e := n / p with he
  have hnpe : n = e * p := (Nat.div_mul_cancel hpn).symm
  have he1 : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · rw [h, zero_mul] at hnpe; omega
    · exact h
  let _ : Algebra (ZMod 2) K := ZMod.algebra K 2
  let _ : Algebra (ZMod 2) L := ZMod.algebra L 2
  obtain ⟨φ⟩ : Nonempty (K →ₐ[ZMod 2] L) := ⟨IsAlgClosed.lift⟩
  let _ : Algebra K L := φ.toRingHom.toAlgebra
  have hFr : ∀ c : L, iterateFrobenius L 2 (e * p) c = c ^ Nat.card K := fun c => by
    rw [iterateFrobenius_def, hK, hnpe]
  have hbij : Function.Bijective (iterateFrobenius L 2 (e * p)) := by
    rw [← coe_iterateFrobeniusEquiv]; exact (iterateFrobeniusEquiv L 2 (e * p)).bijective
  have hrat : (adjointGroup τ L ⊓ (endPowU (frobTwistGL τ L 2 e 1) p).eqLocus (MonoidHom.id _)) =
      (adjointGroup τ K).map (baseChangeGL (algebraMap K L)) := by
    rw [← fixed_eq_map hτ _ hFr hbij]
    ext g
    change g ∈ adjointGroup τ L ∧ endPowU (frobTwistGL τ L 2 e 1) p g = g ↔
      g ∈ adjointGroup τ L ∧ Units.map (entrywiseHom (iterateFrobenius L 2 (e * p))) g = g
    rw [endPow_frobTwist_one]
  let ρ : TableBExc.RecipeGroup τ K →* ModGL τ L :=
    (baseChangeGL (algebraMap K L)).comp ((adjointGroup τ K).subtype.comp (eR τ K).toMonoidHom)
  have hρ : ∀ r, ρ r = baseChangeGL (algebraMap K L) (eR τ K r) := fun r => rfl
  have hρinj : Function.Injective ρ := fun r r' h =>
    (eR τ K).injective (Subtype.ext (baseChangeGL_injective (algebraMap K L) h))
  have hρmem : ∀ r, ρ r ∈ (adjointGroup τ L ⊓ (endPowU (frobTwistGL τ L 2 e 1) p).eqLocus (MonoidHom.id _)) := fun r => by
    rw [hrat]; exact ⟨_, (eR τ K r).2, rfl⟩
  have hρsurj : ∀ g ∈ (adjointGroup τ L ⊓ (endPowU (frobTwistGL τ L 2 e 1) p).eqLocus (MonoidHom.id _)), ∃ r, ρ r = g := by
    intro g hg
    rw [hrat] at hg
    obtain ⟨x, hx, rfl⟩ := hg
    exact ⟨(eR τ K).symm ⟨x, hx⟩, by rw [hρ, MulEquiv.apply_symm_apply]⟩
  let ψ : TableBExc.RecipeGroup τ K ≃* ↥(adjointGroup τ L ⊓ (endPowU (frobTwistGL τ L 2 e 1) p).eqLocus (MonoidHom.id _)) :=
    MulEquiv.ofBijective (ρ.codRestrict _ hρmem) ⟨fun r r' h => hρinj (congrArg Subtype.val h),
      fun g => by obtain ⟨r, hr⟩ := hρsurj g g.2; exact ⟨r, Subtype.ext hr⟩⟩
  have hψ : ∀ g, ρ (ψ.symm g) = g := fun g => congrArg Subtype.val (ψ.apply_symm_apply g)
  have hconj : Function.Injective
      (MulAut.conj : TableBExc.RecipeGroup τ K →* MulAut (TableBExc.RecipeGroup τ K)) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    rw [← TableBExc.center_recipeGroup_eq_bot τ K, Subgroup.mem_center_iff]
    intro h
    have := congrArg (fun φ : MulAut (TableBExc.RecipeGroup τ K) => φ h) (MonoidHom.mem_ker.1 hg)
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  let Θ := (MulAut.conj : TableBExc.RecipeGroup τ K →* MulAut (TableBExc.RecipeGroup τ K)).comp
    ψ.symm.toMonoidHom
  refine ⟨e, 1, he1, Or.inl rfl, ⟨fun g hg => ?_, ρ, Θ, hρinj, hρmem, hconj.comp ψ.symm.injective, ?_, ?_, ?_⟩,
    ⟨iterateFrobenius L 2 (e * p), fun c => by rw [iterateFrobenius_def, pow_mul], 1, Or.inl rfl,
      fun g => ?_⟩, ?_⟩
  · rw [frobTwistGL_apply, one_mul, inv_one, mul_one]
    exact CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup _ hg
  · intro φ'
    constructor
    · intro hφ'
      obtain ⟨s, rfl⟩ := TableBExc.idImage_subset_inn_of_top τ K hT hφ'
      refine ⟨ψ s, ?_⟩
      show MulAut.conj (ψ.symm (ψ s)) = MulAut.conj s
      rw [ψ.symm_apply_apply]
    · rintro ⟨g, rfl⟩
      exact Subgroup.subset_closure (Set.mem_union_left _ ⟨ψ.symm g, rfl⟩)
  · intro g r
    show ρ (ψ.symm g * r * (ψ.symm g)⁻¹) = _
    rw [map_mul, map_mul, map_inv, hψ]
  · intro f' hf' hf'p
    obtain ⟨-, j, hpj, hj⟩ := fieldImage_frob hn hK hp f' hf' hf'p
    refine ⟨j, hpj, fun r => ?_⟩
    rw [hρ, hρ, hj, baseChangeGL_baseChangeGL, endPow_frobTwist_one]
    change _ = baseChangeGL _ (baseChangeGL (algebraMap K L) _)
    rw [baseChangeGL_baseChangeGL]
    have hc : (algebraMap K L).comp (iterateFrobenius K 2 (e * j)) =
        (iterateFrobenius L 2 (e * j)).comp (algebraMap K L) := by
      ext c
      simp only [RingHom.comp_apply, iterateFrobenius_def, map_pow]
    rw [hc]
  · rw [endPow_frobTwist_one, one_mul, inv_one, mul_one]
  · rw [hrat]
    haveI : Finite (adjointGroup τ K) := CFSG.LieType.Chevalley.generated_group_finite τ K
    exact Finite.of_surjective _ (MonoidHom.subgroupMap_surjective
      (baseChangeGL (algebraMap K L)) (adjointGroup τ K))

end Bridge

end

end CFSG.HardMathSupport.C14ExcBridgeU
