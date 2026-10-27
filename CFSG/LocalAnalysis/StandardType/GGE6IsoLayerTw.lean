module

public import CFSG.LocalAnalysis.StandardType.GGE6IsoOrbit
public import CFSG.LocalAnalysis.StandardType.GGTwE6D4GammaLayer
public import CFSG.LocalAnalysis.StandardType.GGTwE6RawFrame
public import CFSG.LocalAnalysis.StandardType.GGTwE6D4RootFacts
public import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourCover
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
public import CFSG.LocalAnalysis.StandardType.GGLangLatSolv
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddToral
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24A2CubeClass
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LangQuasisimpleOfNotSmallSolv
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Inner

public section

namespace CFSG.StandardType.KGL

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.StandardType.TableBExc CFSG.StandardType.TableBExc.E6Three
  CFSG.StandardType.NoOffRest CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.KGL
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.StandardType.KGL.TwLayer
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three (e6LineRoots card_biUnion_e6LineRoots
  e6LineChar e6LineChar_kacNode e6KacNode)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem ncard_kernelRoots_iso {L : Type} [Field L]
    {ζ : Lˣ} (hζ : ζ ^ 3 = 1) (h1 : ζ ≠ 1) :
    (kernelRoots (rootCharHom (zetaVec (τ := Tag.E6) ζ hζ ggE6IsoBase))).ncard = 18 := by
  have h2 : kernelRoots (rootCharHom (zetaVec (τ := Tag.E6) ζ hζ ggE6IsoBase)) =
      CFSG.RankThree.PartOne.KE8F.famKernel {zetaVec (τ := Tag.E6) ζ hζ ggE6IsoBase} := by
    ext γ
    constructor
    · rintro ⟨hγ, h⟩
      exact ⟨hγ, fun b hb => by
        rw [Set.mem_singleton_iff] at hb
        subst hb
        exact h⟩
    · rintro ⟨hγ, h⟩
      exact ⟨hγ, h _ rfl⟩
  have h3 : (⋃ i, (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ))) =
      ↑(Finset.univ.biUnion e6LineRoots) := by
    simp [Finset.coe_biUnion]
  rw [h2, famKernel_zetaVec_ggE6IsoBase hζ h1, h3, Set.ncard_coe_finset]
  exact card_biUnion_e6LineRoots

private theorem rootDiagUnit_iso_ne_one
    {L : Type} [Field L] {ζ : Lˣ} (hζ : ζ ^ 3 = 1)
    (h1 : ζ ≠ 1) : rootDiagUnit Tag.E6 (zetaVec (τ := Tag.E6) ζ hζ ggE6IsoBase) ≠ 1 := by
  intro h
  have h' : rootDiagUnit Tag.E6 (zetaVec (τ := Tag.E6) ζ hζ ggE6IsoBase) =
      rootDiagUnit Tag.E6 1 := by
    rw [h]
    exact (map_one (rootDiagUnitHom Tag.E6 L)).symm
  have h4 := congrFun (CFSG.LieType.Chevalley.rootDiagUnit_injective h') e6KacNode
  rw [zetaVec_ggE6IsoBase, e6LineChar_kacNode] at h4
  exact h1 h4

private theorem rationalRoots_eq_of_neg
    {L : Type} [Field L] {ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)}
    {a : Fin Tag.E6.rank → Lˣ} (hρ : ∀ γ, IsRoot Tag.E6 γ → ρ γ = -γ)
    (i : KernelComponent (rootCharHom a)) :
    rationalRoots ρ (rootCharHom a) i = componentRoots (rootCharHom a) i := by
  refine LangRat.rationalRoots_eq_componentRoots_of_mapsTo ρ _ i fun γ hγ => ?_
  obtain ⟨⟨hr, -⟩, -⟩ := id hγ
  rw [hρ γ hr]
  exact CFSG.ComponentClassification.ExcSelector.neg_mem_componentRoots hγ

private theorem isComponentOf_rationalComponent
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hq : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    IsComponentOf (rationalComponent S.ρ S.Γ (rootCharHom a) i)
      (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a}) := by
  obtain ⟨hle, hsub⟩ := langSubnormal_of_mem_torus S hT i
  exact ⟨hle, (CFSG.Assembly.IsSubnormal.iff_subgroupOf hle).2 hsub,
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2 hq⟩

open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24
  (kernel_classes_of_ncard_eighteen disjoint_componentRoots) in
private theorem exists_two_isComponentOf
    {L : Type} [Field L] [IsAlgClosed L] (h3 : ((3 : ℕ) : L) ≠ 0) {p₀ : ℕ}
    (S : LangSetup Tag.E6 L p₀) {a : Fin Tag.E6.rank → Lˣ} (hap : ∀ i, a i ^ 3 = 1)
    (h1 : rootDiagUnit Tag.E6 a ≠ 1) (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (h18 : (kernelRoots (rootCharHom a)).ncard = 18) (hρ : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = -γ)
    (hq : 4 ≤ S.D.q) :
    ∃ R₁ R₂ : Subgroup (ModGL Tag.E6 L), R₁ ≠ R₂ ∧
      IsComponentOf R₁ (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 a}) ∧
      IsComponentOf R₂ (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 a}) := by
  classical
  obtain ⟨c, hc, h6⟩ := kernel_classes_of_ncard_eighteen h3 hap h18
  have hQ : ∀ k, CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) (c k)) := by
    intro k
    refine langQuasisimpleOfNotSmallSolv Tag.E6 L p₀ 3 S (by decide) Nat.prime_three h3 a hT
      hap h1 (c k) ?_
    rintro (⟨-, h2⟩ | ⟨hs, -, -⟩)
    · rw [h6 k] at h2
      exact absurd h2 (by decide)
    · rcases Nat.eq_zero_or_pos
        (componentOrbitLength S.ρ (componentRoots (rootCharHom a) (c k))) with h0 | hpos
      · rw [h0, pow_zero] at hs
        exact absurd hs (by decide)
      · have h4 : 4 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) (c k)) :=
          hq.trans (Nat.le_self_pow hpos.ne' _)
        omega
  have hne01 : c 0 ≠ c 1 := fun h => absurd (hc.1 h) (by decide)
  have hrr : rationalRoots S.ρ (rootCharHom a) (c 0) ≠
      rationalRoots S.ρ (rootCharHom a) (c 1) := by
    rw [rationalRoots_eq_of_neg hρ, rationalRoots_eq_of_neg hρ]
    intro h
    have hd := disjoint_componentRoots (χ := rootCharHom a) hne01
    rw [h, disjoint_self] at hd
    have h61 := h6 1
    rw [hd, Set.bot_eq_empty, Set.ncard_empty] at h61
    exact absurd h61 (by decide)
  have hcomm := commute_rootSpan_rationalRoots (rho_mem_kernelRoots_of_mem_torus S hT)
    S.frob.iform_eq hrr
  refine ⟨_, _, fun heq => ?_, isComponentOf_rationalComponent S hT (c 0) (hQ 0),
    isComponentOf_rationalComponent S hT (c 1) (hQ 1)⟩
  have hle : ∀ k, rationalComponent S.ρ S.Γ (rootCharHom a) (c k) ≤
      rootSpan Tag.E6 L (rationalRoots S.ρ (rootCharHom a) (c k)) := fun k => by
    unfold rationalComponent rationalSpan
    exact (Subgroup.commutator_le_self _).trans inf_le_left
  obtain ⟨-, -, x, y, hxy⟩ := hQ 0
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
  have hy1 : (y : ModGL Tag.E6 L) ∈ rationalComponent S.ρ S.Γ (rootCharHom a) (c 1) :=
    heq ▸ y.2
  refine hxy ?_
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  exact congrArg _ (Subtype.ext (hcomm _ (hle 0 x.2) _ (hle 1 hy1)).eq)

open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24
  (kernel_classes_of_ncard_eighteen) in
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  (perfect_le_iSup_rationalComponent_of_prime) in
private theorem eq_bot_of_perfect
    {L : Type} [Field L] [IsAlgClosed L] (h3 : ((3 : ℕ) : L) ≠ 0) {p₀ : ℕ}
    (S : LangSetup Tag.E6 L p₀) {a : Fin Tag.E6.rank → Lˣ} (hap : ∀ i, a i ^ 3 = 1)
    (h1 : rootDiagUnit Tag.E6 a ≠ 1) (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (h18 : (kernelRoots (rootCharHom a)).ncard = 18) (hρ : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = -γ)
    (hq : S.D.q = 2) {P : Subgroup (ModGL Tag.E6 L)}
    (hP : P ≤ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 a}) (hperf : ⁅P, P⁆ = P) :
    P = ⊥ := by
  classical
  obtain ⟨c, hc, h6⟩ := kernel_classes_of_ncard_eighteen h3 hap h18
  have hρ' : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = (-1 : ℤ) • latPerm 1 γ := by
    intro γ hγ
    rw [hρ γ hγ]
    exact (neg_one_smul ℤ (latPerm 1 γ)).symm
  have hsolv : ∀ i, Group.IsSolvable ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
    intro i
    obtain ⟨k, rfl⟩ := hc.2 i
    refine LangRat.isSolvable_rationalComponent_of_latSolv S (f := 1) (p := 3)
      (hq.trans (pow_one 2).symm) Nat.prime_three h3 1 (-1) (Or.inr rfl) (by rw [hq]; norm_num)
      hρ' hT hap (c k) ⟨rfl, Or.inr ⟨?_, fun α _ => rfl⟩⟩
    rw [rationalRoots_eq_of_neg hρ]
    exact h6 k
  have hnq : ∀ i, ¬ CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
    intro i hqs
    haveI := hsolv i
    obtain ⟨x, y, hxy⟩ := hqs.2.2
    obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
    haveI : Nontrivial ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
      ⟨⟨x', y', fun h => hxy (by rw [h])⟩⟩
    exact (Group.IsSolvable.commutator_lt_top_of_nontrivial _).ne (Group.isPerfect_def.mp hqs.1)
  have hle := perfect_le_iSup_rationalComponent_of_prime S Nat.prime_three hT hap h1
    (fun i => Or.inr (hsolv i)) P hP hperf
  haveI : IsEmpty {i : KernelComponent (rootCharHom a) //
      CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)} := ⟨fun i => hnq i.1 i.2⟩
  rw [iSup_of_empty] at hle
  exact le_bot_iff.1 hle

private theorem ne_bot_of_isComponentOf {G : Type*} [Group G] {J C : Subgroup G}
    (h : IsComponentOf J C) : J ≠ ⊥ := by
  rintro rfl
  obtain ⟨x, y, hxy⟩ := h.2.2.2.toNontrivial.exists_pair_ne
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
  exact hxy (congrArg _ (Subsingleton.elim x y))

theorem kgTwAdjNonIso :
    ∀ (n : ℕ), 1 ≤ n → 3 ∣ 2 ^ n + 1 → ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K),
      Nat.card K = (2 ^ n) ^ 2 → (∀ c, σ c = c ^ 2 ^ n) →
      ∀ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ 2 ^ n) →
      ∀ v : WeylGroup TwistTag.E6.tag,
        (∀ γ : Fin TwistTag.E6.tag.rank → ℤ, v • permLattice TwistTag.E6.perm γ = -γ) →
      ∀ g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K),
        twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
          g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v →
      ∀ (ζ : (AlgebraicClosure K)ˣ) (hζ : ζ ^ 3 = 1), ζ ≠ 1 →
      ∀ t ∈ twistedE6InndiagGL K σ,
        g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) t * g0 =
          rootDiagUnit TwistTag.E6.tag (zetaVec (τ := Tag.E6) ζ hζ ggE6IsoBase) →
      ∀ J : Subgroup ↥(twistedE6RootGroup K σ),
        IsComponentOf J ((Subgroup.centralizer ({t} : Set (ModGL TwistTag.E6.tag K))).subgroupOf
          (twistedE6RootGroup K σ)) →
        ∃ J' : Subgroup ↥(twistedE6RootGroup K σ),
          IsComponentOf J' ((Subgroup.centralizer ({t} : Set (ModGL TwistTag.E6.tag K))).subgroupOf
            (twistedE6RootGroup K σ)) ∧ J' ≠ J := by
  intro n hn _ K _ _ σ hK hσ Fr hFr v hv g0 hg0C hg0 ζ hζ hζ1 t ht ht' J hJ
  classical
  haveI : CharP K 2 := CFSG.StandardType.charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have h3L : ((3 : ℕ) : AlgebraicClosure K) ≠ 0 := by
    rw [show ((3 : ℕ) : AlgebraicClosure K) = 1 + 2 by norm_num, CharTwo.two_eq_zero, add_zero]
    exact one_ne_zero
  obtain ⟨S, hSD⟩ := exists_ennolaSetup_five hn hK hσ (rawTwLang (σ := σ) Fr hFr v g0 hg0C hg0)
  set D := LangDatum.ofTwist TwistTag.E6 Fr (2 ^ n) hFr v hg0C hg0 with hD
  have hΓS : S.Γ = D.Γ := by
    show S.D.Γ = D.Γ
    rw [hSD] <;> rfl
  set a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ := zetaVec (τ := Tag.E6) ζ hζ ggE6IsoBase
    with ha
  have hdt : rootDiagUnit Tag.E6 a = twThetaHom g0 t := by
    rw [twThetaHom_apply, ht'] <;> rfl
  have hap : ∀ i, a i ^ 3 = 1 := fun i => zetaVec_apply_pow_three hζ _ i
  have h1 : rootDiagUnit Tag.E6 a ≠ 1 := rootDiagUnit_iso_ne_one hζ hζ1
  have h18 : (kernelRoots (rootCharHom a)).ncard = 18 := ncard_kernelRoots_iso hζ hζ1
  have hρ : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = -γ := fun γ hγ =>
    CFSG.StandardType.TwE6EltSmall.ennola_rho_eq_neg (rawTwLang (σ := σ) Fr hFr v g0 hg0C hg0)
      hv S hSD hγ
  have hT : rootDiagUnit Tag.E6 a ∈ S.D.torus := by
    have hmodel : twThetaHom g0 t ∈ D.model :=
      twThetaHom_mem_model hσ Fr hFr v g0 hg0C hg0 ht
    have htor : twThetaHom g0 t ∈ torusGroup Tag.E6 (AlgebraicClosure K) := by
      rw [← hdt]
      exact rootDiagUnit_mem_torusGroup a
    rw [hdt, hSD]
    exact CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.2 ⟨htor, (D.mem_model.1 hmodel).2⟩
  let Θ : ↥(twistedE6RootGroup K σ) →* ModGL TwistTag.E6.tag (AlgebraicClosure K) :=
    (twThetaHom g0).comp (twistedE6RootGroup K σ).subtype
  have hΘinj : Function.Injective Θ :=
    (twThetaHom_injective g0).comp (Subgroup.subtype_injective _)
  have hmap : ((Subgroup.centralizer ({t} : Set (ModGL TwistTag.E6.tag K))).subgroupOf
      (twistedE6RootGroup K σ)).map Θ = S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 a} := by
    rw [hΓS]
    exact map_centralizer_twThetaHom hn hK hσ Fr hFr v g0 hg0C hg0 hdt
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  ·
    exfalso
    have hq2 : S.D.q = 2 := by
      rw [hSD]
      show 2 ^ n = 2
      rw [show n = 1 by omega, pow_one]
    have hJle : J.map Θ ≤ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 a} := by
      rw [← hmap]
      exact Subgroup.map_mono hJ.1
    have hJperf : ⁅J.map Θ, J.map Θ⁆ = J.map Θ := by
      rw [← Subgroup.map_commutator, SCFourCover.commutator_eq_self_of_isComponentOf hJ]
    have hbot := eq_bot_of_perfect h3L S hap h1 hT h18 hρ hq2 hJle hJperf
    exact ne_bot_of_isComponentOf hJ ((Subgroup.map_eq_bot_iff_of_injective _ hΘinj).1 hbot)
  ·
    have hq4 : 4 ≤ S.D.q := by
      rw [hSD]
      show 4 ≤ 2 ^ n
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    obtain ⟨R₁, R₂, hne, hR₁, hR₂⟩ := exists_two_isComponentOf h3L S hap h1 hT h18 hρ hq4
    have hR : ∀ R, IsComponentOf R (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 a}) →
        IsComponentOf R (((Subgroup.centralizer ({t} : Set (ModGL TwistTag.E6.tag K))).subgroupOf
          (twistedE6RootGroup K σ)).map Θ) := fun R hR => by
      rw [hmap]
      exact hR
    obtain ⟨hC₁, hm₁⟩ := isComponentOf_comap_of_injective Θ hΘinj (hR R₁ hR₁)
    obtain ⟨hC₂, hm₂⟩ := isComponentOf_comap_of_injective Θ hΘinj (hR R₂ hR₂)
    by_cases h : R₁.comap Θ = J
    · refine ⟨R₂.comap Θ, hC₂, fun h2 => hne ?_⟩
      rw [← hm₁, ← hm₂, h, h2]
    · exact ⟨R₁.comap Θ, hC₁, h⟩

end CFSG.StandardType.KGL

end
