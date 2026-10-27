module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29ExcRankGen
public import CFSG.HardMathSupport.Timmesfeld.Torality.PlanesToralF4Three
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest8b
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylCompDefs
public import CFSG.RankThree.Chevalley.G2SplitPrimeToralCentralizers
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCharF4
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyClosedLang
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.F4ThreeSigma
public import CFSG.HardMathSupport.Timmesfeld.Torality.LangAssembly
public import CFSG.LieType.Chevalley.GraphFixedF4GroupDescent
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAut
public import CFSG.LieType.SeitzGeneration.UnitaryNonabLift
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeA3pSurvivor
public import CFSG.LocalAnalysis.AGLEmbedding.GapROneBS
public import CFSG.LocalAnalysis.AGLEmbedding.J3InSitu
public import CFSG.LocalAnalysis.AGLEmbedding.J3MSide
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3CoverGenAssembly
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3FourGenData
public import CFSG.LocalAnalysis.AGLEmbedding.MonomialWeightsOne
public import CFSG.LocalAnalysis.AGLEmbedding.ReeData
public import CFSG.LocalAnalysis.AGLEmbedding.SurvivorTransfer
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1Frontier3
public import CFSG.RankThree.PartOne.KLR.SL2Gen
public import CFSG.RankThree.PartOne.N143.LowTwoRankSplit
public import CFSG.RankThree.PartOne.N143.SectionCenter
public import CFSG.RankThree.PartOne.N143.SectionRankBound
public import CFSG.RankThree.PartOne.N143.SectionRankProof
public import CFSG.RankThree.PartOne.N143.SectionRankSplit
public import CFSG.RankThree.PartTwo.KFacts.AutPSUDet
public import CFSG.RankThree.PartTwo.Sec14.Item148RankProofField
public import CFSG.RankThree.PartTwo.Sec14.Item148Steps
public import CFSG.RankThree.PartTwo.Sec19.Item19Res5ProofFaithNF
public import CFSG.RankThree.PartTwo.Sec19.Step1914Split
public import CFSG.RankThree.PartTwo.Sec19.Step1914TriSeitz434
public import CFSG.RankThree.PartTwo.Sec19.Step199Proof
public import CFSG.RankThree.PartTwo.Sec4.Census.Open43

public section

namespace CFSG.StandardType

namespace Irred937

open CFSG CFSG.Open CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Group

theorem not_ggFixCompCyclic_of_two_components {p : ℕ} [Fact p.Prime] {H : Type} [Group H]
    [Finite H] (a : MulAut H) {J₁ J₂ P₁ P₂ : Subgroup H}
    (hJ₁ : CFSG.Assembly.IsComponentOf J₁ (ggFix a))
    (hJ₂ : CFSG.Assembly.IsComponentOf J₂ (ggFix a)) (hne : J₁ ≠ J₂)
    (hP₁ : P₁ ≤ J₁) (hP₂ : P₂ ≤ J₂) (hp₁ : IsPGroup p P₁) (hp₂ : IsPGroup p P₂)
    (hc₁ : ¬ IsCyclic P₁) (hc₂ : ¬ IsCyclic P₂) : ¬ GGFixCompCyclic p a := by
  have hdvd : ∀ {J P : Subgroup H}, P ≤ J → IsPGroup p P → ¬ IsCyclic P → p ∣ Nat.card J := by
    intro J P hPJ hpP hcP
    have hnt : P ≠ ⊥ := by
      rintro rfl
      exact hcP inferInstance
    obtain ⟨k, hk⟩ := hpP.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hnt (Subgroup.eq_bot_of_card_eq P (by simpa using hk))
    have h1 : p ∣ Nat.card P := by rw [hk]; exact dvd_pow_self p hk0
    exact h1.trans (Subgroup.card_dvd_of_le hPJ)
  rintro ⟨J, -, hcyc⟩
  by_cases hJ : J = J₁
  · subst hJ
    refine hc₂ (hcyc P₂ hp₂ (le_trans hP₂ ?_))
    exact le_iSup₂_of_le (f := fun (J₂ : Subgroup H)
      (_ : CFSG.Assembly.IsComponentOf J₂ (ggFix a) ∧ J₂ ≠ J ∧ p ∣ Nat.card J₂) => J₂) J₂
      ⟨hJ₂, fun h => hne h.symm, hdvd hP₂ hp₂ hc₂⟩ le_rfl
  · refine hc₁ (hcyc P₁ hp₁ (le_trans hP₁ ?_))
    exact le_iSup₂_of_le (f := fun (J₂ : Subgroup H)
      (_ : CFSG.Assembly.IsComponentOf J₂ (ggFix a) ∧ J₂ ≠ J ∧ p ∣ Nat.card J₂) => J₂) J₁
      ⟨hJ₁, fun h => hJ (h.symm), hdvd hP₁ hp₁ hc₁⟩ le_rfl

end Group

section Inputs

@[expose] def F4ThreeKernelDichotomy : Prop :=
  ∀ (L : Type) [Field L] (a : Fin Tag.F4.rank → Lˣ), (∀ i, a i ^ 3 = 1) → a ≠ 1 →
    (rootCharKernel (τ := Tag.F4) a).ncard = 12 ∨ (rootCharKernel (τ := Tag.F4) a).ncard = 18

@[expose] def F4ThreeEighteenToral :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K], ¬ 3 ∣ Nat.card K →
    ∀ A : Subgroup (ModGL Tag.F4 (AlgebraicClosure K)),
      A ≤ adjointGroup Tag.F4 (AlgebraicClosure K) → Finite A →
      (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) → (∀ x ∈ A, x ^ 3 = 1) →
      ∀ g ∈ adjointGroup Tag.F4 (AlgebraicClosure K), ∀ a : Fin Tag.F4.rank → (AlgebraicClosure K)ˣ,
        (∀ i, a i ^ 3 = 1) → (rootCharKernel (τ := Tag.F4) a).ncard = 18 →
        g * rootDiagUnit Tag.F4 a * g⁻¹ ∈ A →
        ∃ C ∈ adjointGroup Tag.F4 (AlgebraicClosure K), ∀ x ∈ A,
          C⁻¹ * x * C ∈ torusGroup Tag.F4 (AlgebraicClosure K)

@[expose] def F4ThreeA2A2TwoComponents :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 3 ∣ Nat.card K + 1 → 2 < Nat.card K →
    ∀ e : adjointGroup Tag.F4 K,
    ∀ g ∈ adjointGroup Tag.F4 (AlgebraicClosure K), ∀ a : Fin Tag.F4.rank → (AlgebraicClosure K)ˣ,
      (∀ i, a i ^ 3 = 1) → (rootCharKernel (τ := Tag.F4) a).ncard = 12 →
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL Tag.F4 K) =
        g * rootDiagUnit Tag.F4 a * g⁻¹ →
      ∃ J₁ J₂ P₁ P₂ : Subgroup (adjointGroup Tag.F4 K),
        CFSG.Assembly.IsComponentOf J₁ (ggFix (MulAut.conj e)) ∧
        CFSG.Assembly.IsComponentOf J₂ (ggFix (MulAut.conj e)) ∧
        J₁ ≠ J₂ ∧ P₁ ≤ J₁ ∧ P₂ ≤ J₂ ∧ IsElemAbelian 3 P₁ ∧ IsElemAbelian 3 P₂ ∧
        Nat.card P₁ = 9 ∧ Nat.card P₂ = 9

end Inputs

section F1

open CFSG.HardMathSupport.Timmesfeld.Steinberg in
theorem f4ThreeKernelDichotomy_holds :
    F4ThreeKernelDichotomy := by
  intro L _ a h3 ha1
  classical
  obtain ⟨χ', hker⟩ := exists_triChar_ker_eq (rootCharHom3 a) (rootCharHom3_pow_three a h3)
  have hK : rootCharKernel (τ := Tag.F4) a = kernelRoots χ' := by
    rw [← kernelRoots_congr_ker hker]
    rfl
  obtain ⟨ρ, hρ, t, ht⟩ := exists_isCharConj_of_orbitCheck3 f4ThreeOrbit_check χ'
  have himg : kernelRoots χ' =
      (fun α => t • α) '' kernelRoots (triChar (vec3 (τ := Tag.F4) (f4ThreeReps.getD ρ []))) := by
    ext α
    rw [kernelRoots_iff_of_isCharConj ht]
    constructor
    · intro h
      exact ⟨t⁻¹ • α, h, smul_inv_smul t α⟩
    · rintro ⟨β, hβ, rfl⟩
      rwa [inv_smul_smul]
  rw [hK, himg, Set.ncard_image_of_injective _ (MulAction.injective t)]
  have hlen : f4ThreeReps.length = 4 := rfl
  rw [hlen] at hρ
  interval_cases ρ
  ·
    exfalso
    apply ha1
    funext i
    have hv0 : vec3 (τ := Tag.F4) [0, 0, 0, 0] = 0 := by
      funext j
      fin_cases j <;> rfl
    have hz : ∀ v : Fin Tag.F4.rank → ℤ,
        triChar (vec3 (τ := Tag.F4) [0, 0, 0, 0]) (Multiplicative.ofAdd v) = 1 := fun v => by
      rw [triChar_apply, hv0]
      simp [triPairing, Z3.ofAdd_zero]
    have h0 : χ' (Multiplicative.ofAdd (Pi.single i 1)) = 1 := by
      rw [ht]
      exact hz _
    have := (hker _).2 h0
    change rootChar a (Pi.single i 1) = 1 at this
    rwa [CFSG.LieType.Chevalley.rootChar_single] at this
  · exact Or.inr f4_kernelSizes_C3.1
  · exact Or.inl f4_kernelSizes_A2A2t.1
  · exact Or.inr f4_kernelSizes_B3.1

end F1

section F3

open CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest8bAux

theorem ncard_kernelRoots_of_isCharConj
    {M : Type*} [CommGroup M] {χ χ' : Multiplicative (Fin Tag.F4.rank → ℤ) →* M}
    {t : WeylGroup Tag.F4} (h : IsCharConj χ χ' t) :
    (kernelRoots χ').ncard = (kernelRoots χ).ncard := by
  have himg : kernelRoots χ' = (fun α => t • α) '' kernelRoots χ := by
    ext α
    rw [kernelRoots_iff_of_isCharConj h]
    constructor
    · intro hα
      exact ⟨t⁻¹ • α, hα, smul_inv_smul t α⟩
    · rintro ⟨β, hβ, rfl⟩
      rwa [inv_smul_smul]
  rw [himg, Set.ncard_image_of_injective _ (MulAction.injective t)]

theorem kp_commonRoot_one : ∀ a b c d : ZMod 3, ∃ t ∈ kpTuples,
    kpPair (kpVec 1 0 0 0) (kpOfCoords t) = 0 ∧ kpPair (kpVec a b c d) (kpOfCoords t) = 0 := by
  decide +kernel

theorem kp_commonRoot_three : ∀ a b c d : ZMod 3, ∃ t ∈ kpTuples,
    kpPair (kpVec 1 0 1 0) (kpOfCoords t) = 0 ∧ kpPair (kpVec a b c d) (kpOfCoords t) = 0 := by
  decide +kernel

end F3

section B0

theorem toralRootGroup_eq_familyGroup
    {τ : Tag} {K : Type} [Field K] (a : Fin τ.rank → Kˣ) :
    toralRootGroup τ K a = familyGroup (fun _ : Unit => a) := by
  have : familyKernel (fun _ : Unit => a) = rootCharKernel a := by
    ext α
    simp [familyKernel, rootCharKernel]
  rw [toralRootGroup, familyGroup, this]

open CFSG.LieType.AlgebraicGroups in
theorem exists_lang_w0_F4_three
    {K : Type} [Field K] [Finite K]
  {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] (hq : Nat.card K = ℓ ^ f) (hf : 1 ≤ f) (h3q : 3 ∣ Nat.card K + 1)
    (w₀ : WeylGroup Tag.F4) (hw₀ : ∀ v : Fin Tag.F4.rank → ℤ, w₀ • v = -v)
    (e : adjointGroup Tag.F4 K) {g : ModGL Tag.F4 (AlgebraicClosure K)}
    (hg : g ∈ adjointGroup Tag.F4 (AlgebraicClosure K))
    (a : Fin Tag.F4.rank → (AlgebraicClosure K)ˣ) (ha : ∀ i, a i ^ 3 = 1)
    (hga : baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL Tag.F4 K) =
      g * rootDiagUnit Tag.F4 a * g⁻¹) :
    ∃ g' ∈ adjointGroup Tag.F4 (AlgebraicClosure K),
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL Tag.F4 K) =
        g' * rootDiagUnit Tag.F4 a * g'⁻¹ ∧
      g'⁻¹ * entrywiseFrobGL Tag.F4 (AlgebraicClosure K) ℓ f g' =
        canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) w₀ := by
  classical
  set L := AlgebraicClosure K
  set ι : K →+* L := algebraMap K L
  haveI : CharP L ℓ := charP_of_injective_algebraMap ι.injective _
  set F : ModGL Tag.F4 L →* ModGL Tag.F4 L := entrywiseFrobGL Tag.F4 L ℓ f with hF
  set n₀ := canonicalRep (coxeterSystem Tag.F4) L w₀ with hn₀
  set d := rootDiagUnit Tag.F4 a with hd
  have hFix : F (baseChangeGL ι (e : ModGL Tag.F4 K)) = baseChangeGL ι (e : ModGL Tag.F4 K) :=
    CFSG.LieType.Chevalley.units_map_entrywiseHom_baseChangeGL_algebraMap
      (iterateFrobenius L ℓ f) (fun c => by rw [iterateFrobenius_def, hq]) _
  have hpow : ∀ x : Lˣ, x ^ 3 = 1 → x ^ ℓ ^ f = x⁻¹ := by
    intro x hx
    obtain ⟨k, hk⟩ := h3q
    rw [hq] at hk
    have h1 : x ^ ℓ ^ f * x = 1 := by
      rw [← pow_succ, hk, pow_mul, hx, one_pow]
    exact eq_inv_of_mul_eq_one_left h1
  have hneg : ∀ v : Fin Tag.F4.rank → ℤ, rootChar a (-v) = (rootChar a v)⁻¹ := by
    intro v
    have := rootChar_add a (-v) v
    rw [neg_add_cancel, rootChar_zero] at this
    exact eq_inv_of_mul_eq_one_left this.symm
  have hw : ∀ v, rootChar a (w₀ • v) = rootChar a v ^ ℓ ^ f := by
    intro v
    rw [hw₀, hneg, hpow _ (CFSG.HardMathSupport.Timmesfeld.Torality.rootChar_pow_eq_one a ha v)]
  have hdconj : d = n₀ * F d * n₀⁻¹ :=
    CFSG.HardMathSupport.Timmesfeld.Torality.rootDiagUnit_eq_conj_frob ℓ hw
  have h1 : g * d * g⁻¹ = F g * F d * (F g)⁻¹ := by
    have := congrArg F hga
    rw [hFix, map_mul, map_mul, map_inv] at this
    rw [← hga]
    exact this
  have hn : (g⁻¹ * F g) * F d * (g⁻¹ * F g)⁻¹ = d := by
    calc (g⁻¹ * F g) * F d * (g⁻¹ * F g)⁻¹ = g⁻¹ * (F g * F d * (F g)⁻¹) * g := by group
      _ = g⁻¹ * (g * d * g⁻¹) * g := by rw [← h1]
      _ = d := by group
  have hnG : g⁻¹ * F g ∈ adjointGroup Tag.F4 L := mul_mem (inv_mem hg) (entrywiseFrobGL_mem ℓ f hg)
  have hn₀G : n₀ ∈ adjointGroup Tag.F4 L := canonicalRep_mem_adjointGroup _ L w₀
  have hmd : ((g⁻¹ * F g) * n₀⁻¹) * d * ((g⁻¹ * F g) * n₀⁻¹)⁻¹ = d := by
    have h2 : n₀⁻¹ * d * n₀ = F d := by
      calc n₀⁻¹ * d * n₀ = n₀⁻¹ * (n₀ * F d * n₀⁻¹) * n₀ := by rw [← hdconj]
        _ = F d := by group
    calc ((g⁻¹ * F g) * n₀⁻¹) * d * ((g⁻¹ * F g) * n₀⁻¹)⁻¹
        = (g⁻¹ * F g) * (n₀⁻¹ * d * n₀) * (g⁻¹ * F g)⁻¹ := by group
      _ = d := by rw [h2, hn]
  have hcomm : ((g⁻¹ * F g) * n₀⁻¹) * d = d * ((g⁻¹ * F g) * n₀⁻¹) := by
    calc ((g⁻¹ * F g) * n₀⁻¹) * d
        = (((g⁻¹ * F g) * n₀⁻¹) * d * ((g⁻¹ * F g) * n₀⁻¹)⁻¹) * ((g⁻¹ * F g) * n₀⁻¹) := by group
      _ = d * ((g⁻¹ * F g) * n₀⁻¹) := by rw [hmd]
  have hm : (g⁻¹ * F g) * n₀⁻¹ ∈ toralCentralizer Tag.F4 L a := by
    rw [toralCentralizer, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    refine ⟨mul_mem hnG (inv_mem hn₀G), ?_⟩
    first
      | exact hcomm
      | exact hcomm.symm
  rw [CFSG.HardMathSupport.Timmesfeld.Steinberg.toralCentralizer_eq_toralRootGroup_F4_three _ a ha,
    toralRootGroup_eq_familyGroup] at hm
  have hpq : Nat.Coprime 3 (ℓ ^ f) := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three, ← hq]
    intro h
    have : 3 ∣ 1 := (Nat.dvd_add_right h).1 h3q
    omega
  have himg := CFSG.HardMathSupport.Timmesfeld.Torality.image_familyKernel_of_pow ℓ hpq
    (fun _ : Unit => a) (fun _ i => ha i) (fun _ v => hw v)
  have hQ := CFSG.HardMathSupport.Timmesfeld.Torality.canonicalRep_mem_normalizer_of_image
    (K := L) himg
  obtain ⟨z, hz, hzF⟩ := CFSG.HardMathSupport.Timmesfeld.Torality.exists_mem_lang_conj F
    (M := familyGroup (K := L) (fun _ : Unit => a)) hm
    (by group : g⁻¹ * F g = ((g⁻¹ * F g) * n₀⁻¹) * n₀)
    (CFSG.HardMathSupport.Timmesfeld.Torality.lang_familyGroup ℓ _ f hf _ hQ)
  obtain ⟨hzG, hzc⟩ := mem_familyCentralizer.1
    (CFSG.HardMathSupport.Timmesfeld.Torality.familyGroup_le_familyCentralizer (K := L) _ hz)
  have hzd : z * d * z⁻¹ = d := by
    have h := hzc ()
    rw [← hd] at h
    have h' : d * z = z * d := by
      calc d * z = (d * z * d⁻¹) * d := by group
        _ = z * d := by rw [h]
    calc z * d * z⁻¹ = d * z * z⁻¹ := by rw [h']
      _ = d := by group
  refine ⟨g * z, mul_mem hg hzG, ?_, hzF⟩
  rw [hga]
  calc g * d * g⁻¹ = g * (z * d * z⁻¹) * g⁻¹ := by rw [hzd]
    _ = (g * z) * d * (g * z)⁻¹ := by group

end B0

section Assembly

private theorem isCyclic_false_of_elemAbelian_nine {H : Type} [Group H] {P : Subgroup H}
    (hP : IsElemAbelian 3 P) (h9 : Nat.card P = 9) : ¬ IsCyclic P := by
  intro hc
  haveI : Finite P := Nat.finite_of_card_ne_zero (by rw [h9]; norm_num)
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := P)
  have h3 : g ^ 3 = 1 := Subtype.ext (by simpa using hP.2 g g.2)
  have := orderOf_dvd_of_pow_eq_one h3
  rw [hg, h9] at this
  norm_num at this

theorem not_fixCompCyclic_of_a2a2
    (hB : F4ThreeA2A2TwoComponents)
    (K : Type) [Field K] [Finite K] [CharP K 2] (hq : 3 ∣ Nat.card K + 1) (hq2 : 2 < Nat.card K)
    (e : adjointGroup Tag.F4 K) (g : ModGL Tag.F4 (AlgebraicClosure K))
    (hg : g ∈ adjointGroup Tag.F4 (AlgebraicClosure K))
    (a : Fin Tag.F4.rank → (AlgebraicClosure K)ˣ)
    (ha : ∀ i, a i ^ 3 = 1) (h12 : (rootCharKernel (τ := Tag.F4) a).ncard = 12)
    (hga : baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL Tag.F4 K) =
      g * rootDiagUnit Tag.F4 a * g⁻¹) :
    ¬ GGFixCompCyclic 3 (MulAut.conj e) := by
  haveI : Finite (adjointGroup Tag.F4 K) := Subtype.finite
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨J₁, J₂, P₁, P₂, hJ₁, hJ₂, hne, hP₁, hP₂, hE₁, hE₂, h₁, h₂⟩ :=
    hB K hq hq2 e g hg a ha h12 hga
  have hp : ∀ {P : Subgroup (adjointGroup Tag.F4 K)}, IsElemAbelian 3 P → IsPGroup 3 P :=
    fun hE x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  exact not_ggFixCompCyclic_of_two_components (MulAut.conj e) hJ₁ hJ₂ hne hP₁ hP₂ (hp hE₁)
    (hp hE₂) (isCyclic_false_of_elemAbelian_nine hE₁ h₁)
    (isCyclic_false_of_elemAbelian_nine hE₂ h₂)

theorem toral_of_fixCompCyclic
    (hF1 : F4ThreeKernelDichotomy) (hA : F4ThreeEighteenToral)
    (hB : F4ThreeA2A2TwoComponents)
    (K : Type) [Field K] [Finite K] [CharP K 2] (hq : 3 ∣ Nat.card K + 1) (hq2 : 2 < Nat.card K)
    (E : Subgroup (adjointGroup Tag.F4 K)) (hE : IsElemAbelian 3 E)
    (e : adjointGroup Tag.F4 K) (he : e ∈ E) (he1 : e ≠ 1)
    (hfix : GGFixCompCyclic 3 (MulAut.conj e)) :
    ∃ g ∈ adjointGroup Tag.F4 (AlgebraicClosure K), ∀ x ∈ E,
      g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) ((x : adjointGroup Tag.F4 K) :
        ModGL Tag.F4 K) * g ∈ torusGroup Tag.F4 (AlgebraicClosure K) := by
  classical
  set L := AlgebraicClosure K
  have hK3 : ¬ 3 ∣ Nat.card K := by
    intro h
    have h1 : 3 ∣ 1 := (Nat.dvd_add_right h).1 hq
    omega
  have hmon : MonomialToralAt Tag.F4 3 := monomialToralAt_three_of_block a2BlockToral_F4
  have he3 : (e : ModGL Tag.F4 K) ^ 3 = 1 := by
    have := hE.2 e he
    exact congrArg Subtype.val this
  obtain ⟨g, hg, a, ha3, hga⟩ :=
    CFSG.LocalAnalysis.RankFourTheoremC.ExcRank.exists_toral_conj_gen Nat.prime_three hmon K hK3
      e.2 he3
  have ha1 : a ≠ 1 := by
    rintro rfl
    apply he1
    apply Subtype.ext
    apply baseChangeGL_injective (algebraMap K L)
    rw [hga, CFSG.LieType.Chevalley.rootDiagUnit_one, mul_one, mul_inv_cancel]
    exact (map_one _).symm
  rcases hF1 L a ha3 ha1 with h12 | h18
  · exact absurd hfix (not_fixCompCyclic_of_a2a2 hB K hq hq2 e g hg a ha3 h12 hga)
  ·
    let φ : adjointGroup Tag.F4 K →* ModGL Tag.F4 L :=
      (baseChangeGL (algebraMap K L)).comp (adjointGroup Tag.F4 K).subtype
    let A : Subgroup (ModGL Tag.F4 L) := E.map φ
    have hAle : A ≤ adjointGroup Tag.F4 L := by
      rintro _ ⟨x, -, rfl⟩
      exact CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup _ x.2
    haveI : Finite (adjointGroup Tag.F4 K) := Subtype.finite
    have hAfin : Finite A := by
      change Finite ↥(E.map φ)
      exact Finite.Set.finite_image _ _
    have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      have := congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
      rw [← map_mul, ← map_mul]
      exact congrArg φ this
    have hAexp : ∀ x ∈ A, x ^ 3 = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hE.2 x hx, map_one]
    have hmem : g * rootDiagUnit Tag.F4 a * g⁻¹ ∈ A := ⟨e, he, hga⟩
    obtain ⟨C, hC, hCT⟩ := hA K hK3 A hAle hAfin hAcomm hAexp g hg a ha3 h18 hmem
    exact ⟨C, hC, fun x hx => hCT _ ⟨x, hx, rfl⟩⟩

end Assembly

end Irred937

end CFSG.StandardType

end
