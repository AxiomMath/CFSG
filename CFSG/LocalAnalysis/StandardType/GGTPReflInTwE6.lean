module

public import CFSG.LocalAnalysis.StandardType.GGTPDefs
public import CFSG.LocalAnalysis.StandardType.GGTwKGLayerDefs
public import CFSG.LocalAnalysis.StandardType.GGKGAutDict
public import CFSG.LocalAnalysis.StandardType.GGKGWeylRootFacts
public import CFSG.LocalAnalysis.StandardType.GGTPLayerTwE6
public import CFSG.LocalAnalysis.StandardType.GGE6DepBlockLift
public import CFSG.LocalAnalysis.StandardType.GGKGTwFrame
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Delta
public import CFSG.LocalAnalysis.StandardType.GGTwE6D4E0Data
public import CFSG.LocalAnalysis.StandardType.GGTwE6D4RootFacts

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.StandardType.TableBExc
  CFSG.StandardType.TableBExc.E6Three CFSG.StandardType.NoOffRest
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.KGL
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.StandardType.TwE6EltSmall
  CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KE CFSG.StandardType.LayerSixE
  CFSG.StandardType.LayerExc CFSG.RankThree.PartOne.KE8F CFSG.StandardType.KGL.TwLayer
open scoped MatrixGroups commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem ggTP_a3_E0_data_cent
    {n : ℕ} {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    (v : WeylGroup TwistTag.E6.tag)
    (hv : ∀ γ : Fin TwistTag.E6.tag.rank → ℤ, v • permLattice TwistTag.E6.perm γ = -γ)
    (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K))
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
    (ζ : (AlgebraicClosure K)ˣ) (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3)
    {α β : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α) (hβ : IsRoot Tag.E6 β)
    (hαβ : iform α β = 0) :
    ∃ E0 : Subgroup (ModGL Tag.E6 (AlgebraicClosure K)), CFSG.IsQuasisimple E0 ∧
      E0 ≤ (LangDatum.ofTwist TwistTag.E6 Fr (2 ^ n) hFr v hg0C hg0).Γ ∧
      E0 ≤ Subgroup.centralizer
        {rootDiagUnit Tag.E6 (zetaVec ζ hζ (kgExpVec β))} ∧
      ∀ μ : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 μ → iform μ α = 0 → iform μ β = 0 →
        rootSL2 Tag.E6 (AlgebraicClosure K) μ WSL ∈ E0 := by
  classical
  haveI : CharP K 2 := CFSG.StandardType.charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set L := AlgebraicClosure K with hL
  set D := LangDatum.ofTwist TwistTag.E6 Fr (2 ^ n) hFr v hg0C hg0 with hD
  obtain ⟨u, hUeq, hlayer⟩ := ggLayerOf_pair_A3 ζ hζ hζo hα hβ hαβ
  have hstep : ∀ γ, IsRoot Tag.E6 γ → ∀ c,
      D.step (pinnedX Tag.E6 L γ c) = pinnedX Tag.E6 L (-γ) (Fr c) := fun γ hγ c =>
    ennola_step_pinnedX (rawTwLang (σ := σ) Fr hFr v g0 hg0C hg0) hv hK hγ c
  let σ' : L ≃+* L := twFrobEquiv Fr hFr
  have hσ'1 : σ'.toRingHom = Fr := RingHom.ext fun _ => rfl
  have hσ' : ∀ c, σ' c = c ^ 2 ^ n := hFr
  have hfixq : CFSG.IsQuasisimple (fixSubgroup (stdUnitaryEquiv (ν := 4) σ')) :=
    (stdUnitary_fixSubgroup (ν := 4) Nat.prime_two (f := n) hn σ' hσ' (by norm_num)).2.1
      (by simp)
  set U := rootSpan Tag.E6 L
    (famKernel {zetaVec ζ hζ (kgExpVec α), zetaVec ζ hζ (kgExpVec β)}) with hU
  set E0 := U ⊓ D.step.eqLocus (MonoidHom.id _) with hE0
  have hE0eq : E0 = (fixSubgroup (stdUnitaryEquiv (ν := 4) σ')).map (rhoSigmaE6A3 L u) := by
    rw [hE0, hUeq]
    exact inf_eqLocus_eq_map_fix Fr D.step hstep u σ' hσ'1
  have hE0q : CFSG.IsQuasisimple E0 := by
    rw [hE0eq]
    exact (CFSG.IsQuasisimple.congr (Subgroup.equivMapOfInjective _ _
      (rhoSigmaE6A3_injective u))).mp hfixq
  have hE0model : E0 ≤ D.model := fun x hx =>
    D.mem_model.2 ⟨rootSpan_le_adjointGroup L _ hx.1, hx.2⟩
  have hE0Γ : E0 ≤ D.Γ := by
    have h1 : ⁅E0, E0⁆ = E0 := Subgroup.isPerfect_iff.mp hE0q.1
    have h2 := Subgroup.commutator_mono hE0model hE0model
    rw [h1] at h2
    exact h2
  have hΓmodel : D.Γ ≤ D.model := by
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    rw [commutatorElement_def]
    exact D.model.mul_mem (D.model.mul_mem (D.model.mul_mem ha hb) (D.model.inv_mem ha))
      (D.model.inv_mem hb)
  have hΓfix : D.Γ ≤ D.step.eqLocus (MonoidHom.id _) := fun x hx => (D.mem_model.1 (hΓmodel hx)).2
  refine ⟨E0, hE0q, hE0Γ, ?_, ?_⟩
  · intro x hx
    obtain ⟨g, hg, rfl⟩ := hlayer.1 hx.1
    have hgβ := mem_famCentralizer.1 hg (zetaVec ζ hζ (kgExpVec β))
      (Set.mem_insert_of_mem _ rfl)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact mul_inv_eq_iff_eq_mul.1 hgβ
  · intro μ hμ hμα hμβ
    have hS := famKernel_kgExpVec_pair hζo hζ hα hβ
    have hμS : μ ∈ famKernel {zetaVec ζ hζ (kgExpVec α), zetaVec ζ hζ (kgExpVec β)} := by
      rw [hS]
      exact ⟨hμ, hμα, hμβ⟩
    have hnα : iform (τ := Tag.E6) (-μ) α = 0 := by
      rw [iform_neg_left (τ := Tag.E6) μ α, hμα, neg_zero]
    have hnβ : iform (τ := Tag.E6) (-μ) β = 0 := by
      rw [iform_neg_left (τ := Tag.E6) μ β, hμβ, neg_zero]
    have hnμS : -μ ∈ famKernel {zetaVec ζ hζ (kgExpVec α), zetaVec ζ hζ (kgExpVec β)} := by
      rw [hS]
      exact ⟨IsRoot.neg hμ, hnα, hnβ⟩
    have hmemU : rootSL2 Tag.E6 L μ WSL ∈ U :=
      rootRankOneGroup_le_rootSpan hμ hμS hnμS (MonoidHom.mem_range.2 ⟨WSL, rfl⟩)
    have hmemΓ : rootSL2 Tag.E6 L μ WSL ∈ D.Γ :=
      rootSL2_WSL_mem_Γ_raw hn hK hσ Fr hFr v hv g0 hg0C hg0 hμ
    exact ⟨hmemU, hΓfix hmemΓ⟩

private theorem ggTP_map_conj_eq {M N : Type} [Group M] [Group N] (φ : M →* N) (x y : M) :
    φ (MulAut.conj x y) = MulAut.conj (φ x) (φ y) := by
  rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]

private theorem ggTP_mulEquiv_conj_apply {M N : Type} [Group M] [Group N] (e : M ≃* N) (x y : M) :
    e (MulAut.conj x y) = MulAut.conj (e x) (e y) := by
  rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]

private theorem ggTP_conjAut_apply
    {n : ℕ} {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    {R : Type} [Group R] {Θ : R ≃* ↥(twistedE6RootGroup K σ)}
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} {ζ : (AlgebraicClosure K)ˣ}
    {hζ : ζ ^ 3 = 1} {L' : Type} [Group L'] {ψ : L' →* R}
    {A : Subgroup (MulAut L')} {v : WeylGroup TwistTag.E6.tag}
    {g : ModGL TwistTag.E6.tag (AlgebraicClosure K)} {κ : A →* Multiplicative (Fin 6 → ZMod 3)}
    {t : (Fin 6 → ZMod 3) → ModGL TwistTag.E6.tag K}
    (hF : KGTwFrame n σ Θ Fr ζ hζ ψ A v g κ t) {l₀ : L'}
    {j : ↥(twistedE6RootGroup K σ)} (hl₀ : Θ (ψ l₀) = j) (a' : A) (l : L') :
    ((Θ (ψ ((MulAut.conj l₀ * (a' : MulAut L') * (MulAut.conj l₀)⁻¹) l)) :
        ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) =
      (((j : ModGL TwistTag.E6.tag K) * t (Multiplicative.toAdd (κ a')) *
          (j : ModGL TwistTag.E6.tag K)⁻¹) *
        ((Θ (ψ l) : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) *
        ((j : ModGL TwistTag.E6.tag K) * t (Multiplicative.toAdd (κ a')) *
          (j : ModGL TwistTag.E6.tag K)⁻¹)⁻¹) := by
  have harg : (MulAut.conj l₀ * (a' : MulAut L') * (MulAut.conj l₀)⁻¹) l =
      MulAut.conj l₀ ((a' : MulAut L') ((MulAut.conj l₀)⁻¹ l)) := by
    rw [MulAut.mul_apply, MulAut.mul_apply]
  have hinv : (MulAut.conj l₀)⁻¹ = MulAut.conj l₀⁻¹ := by
    ext y
    rw [MulAut.conj_inv_apply, MulAut.conj_apply, inv_inv]
  have hw : ((Θ (ψ ((MulAut.conj l₀)⁻¹ l)) : ↥(twistedE6RootGroup K σ)) :
        ModGL TwistTag.E6.tag K) =
      (j : ModGL TwistTag.E6.tag K)⁻¹ *
        ((Θ (ψ l) : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) *
        (j : ModGL TwistTag.E6.tag K) := by
    rw [hinv, MulAut.conj_apply]
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hl₀]
    group
  rw [harg, ggTP_map_conj_eq ψ, ggTP_mulEquiv_conj_apply Θ]
  simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, hl₀]
  rw [hF.conj a' ((MulAut.conj l₀)⁻¹ l), hw]
  group

private theorem ggTP_conj_mem_normalizer {L' : Type} [Group L'] {A : Subgroup (MulAut L')} [Finite A]
    (m : L') (h : ∀ a : A, ∃ b : A,
      MulAut.conj m * (a : MulAut L') * (MulAut.conj m)⁻¹ = (b : MulAut L')) :
    MulAut.conj m ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
  let c : MulAut L' := MulAut.conj m
  rw [Subgroup.mem_set_normalizer_iff]
  intro v
  constructor
  · intro hv
    obtain ⟨b, hb⟩ := h ⟨v, hv⟩
    rw [hb]
    exact b.2
  · intro hv
    have hmaple : A.map (MulAut.conj c).toMonoidHom ≤ A := by
      rintro _ ⟨w, hw, rfl⟩
      obtain ⟨b, hb⟩ := h ⟨w, hw⟩
      rw [show (MulAut.conj c).toMonoidHom w = c * w * c⁻¹ from MulAut.conj_apply c w, hb]
      exact b.2
    have hcard : Nat.card (A.map (MulAut.conj c).toMonoidHom) = Nat.card A :=
      Subgroup.card_map_of_injective (MulAut.conj c).injective
    have hEq : A.map (MulAut.conj c).toMonoidHom = A :=
      Subgroup.eq_of_le_of_card_ge hmaple (le_of_eq hcard.symm)
    have hmem : (MulAut.conj c).toMonoidHom v ∈ A.map (MulAut.conj c).toMonoidHom := by
      rw [hEq]
      exact hv
    obtain ⟨u, hu, huv⟩ := Subgroup.mem_map.1 hmem
    have huv' : u = v := (MulAut.conj c).injective huv
    rwa [← huv']

theorem ggTPReflIn_TwE6
    {n : ℕ} (hn : 1 ≤ n) (h3 : 3 ∣ 2 ^ n + 1) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) {L' : Type} [Group L'] [Finite L']
    (ψ : L' →* TwE6Delta.RecipeR K n) (A : Subgroup (MulAut L'))
    (hTB : GGTorusTBGroup 3 5 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) L' ψ A)
    (hA : Nat.card A = 3 ^ 5) {c : ↥A} (hc : GGCorootPt 3 (ggTorusAut A) c) {J : Subgroup L'}
    (hJ : IsComponentOf J (ggFix (c : MulAut L'))) :
    ∃ (κ : A →* Multiplicative (Fin 6 → ZMod 3)) (β : Fin Tag.E6.rank → ℤ),
      KGL.KGAutFrame A κ ∧ IsRoot Tag.E6 β ∧ Multiplicative.toAdd (κ c) = KGL.kgExpVec β ∧
        ∀ γ : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 γ → iform γ β = 0 →
          ∃ m ∈ J, MulAut.conj m ∈ Subgroup.normalizer (A : Set (MulAut L')) ∧
            ∀ a b : ↥A, (b : MulAut L') = MulAut.conj m * (a : MulAut L') * (MulAut.conj m)⁻¹ →
              Multiplicative.toAdd (κ b) = KGL.rootRefl γ (Multiplicative.toAdd (κ a)) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := by
    obtain ⟨m, hprime, hm⟩ := FiniteField.card K (ringChar K)
    have hcard : Fintype.card K = 2 ^ (2 * n) := by
      rw [← Nat.card_eq_fintype_card, hK, ← pow_mul, Nat.mul_comm]
    rw [hcard] at hm
    have hdvd : ringChar K ∣ 2 ^ (2 * n) := by
      rw [hm]
      exact dvd_pow_self _ m.pos.ne'
    have hrc : ringChar K = 2 :=
      (Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).mp
        (Nat.Prime.dvd_of_dvd_pow hprime hdvd)
    exact hrc ▸ ringChar.charP K
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  haveI : IsAlgClosed (AlgebraicClosure K) := AlgebraicClosure.isAlgClosed K
  have hinj : Function.Injective (iterateFrobenius K 2 n) := (iterateFrobenius K 2 n).injective
  set σ : K ≃+* K := RingEquiv.ofBijective (iterateFrobenius K 2 n)
    ⟨hinj, Finite.surjective_of_injective hinj⟩ with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
  set Fr : AlgebraicClosure K →+* AlgebraicClosure K := iterateFrobenius (AlgebraicClosure K) 2 n
    with hFrdef
  have hFr : ∀ c, Fr c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
  have h30 : (3 : AlgebraicClosure K) ≠ 0 :=
    CFSG.HardMathSupport.Lang.E6Descent.three_ne_zero_of_dvd_card_add_one (ℓ := 2) hn h3
  obtain ⟨ζ, hζ, hζo⟩ :=
    CFSG.HardMathSupport.Lang.E6Descent.TwistedDiag.exists_cube_root
      (Ω := AlgebraicClosure K) h30
  obtain ⟨ε, hε⟩ := TwE6DD2.exists_recipeEquiv hn hK σ hσ
  obtain ⟨v, g, κ, t, hF⟩ :=
    ggTwKGFrame_holds n hn h3 K hK σ hσ ε hε Fr hFr ζ hζ hζo L' ψ A hTB hA
  have hψ : Function.Surjective ψ := hTB.1
  have hker : ψ.ker ≤ Subgroup.center L' := hTB.2.1
  have hperf : commutator L' = ⊤ := hTB.2.2.1
  have hind := hTB.2.2.2.2.1
  obtain ⟨β, hβ, hκc⟩ := hF.aut.corootPt hc
  obtain ⟨ER, X, _, hER, -, -, -⟩ := ggTPLayerModel_TwE6 hn h3 hK ψ A hTB hA hc
  have hFaut : ∀ f ∈ ({(c : MulAut L')} : Set (MulAut L')), ∃ φ : MulAut (TwE6Delta.RecipeR K n),
      ∀ l, φ (ψ l) = ψ (f l) := by
    intro f hf
    rw [Set.mem_singleton_iff] at hf
    subst hf
    obtain ⟨φ, -, hφ⟩ := hind (c : MulAut L') c.2
    exact ⟨φ, hφ⟩
  have hC : ∀ l : L', l ∈ ggFix (c : MulAut L') ↔ ∀ f ∈ ({(c : MulAut L')} : Set (MulAut L')), f l = l := by
    intro l
    rw [mem_ggFix]
    constructor
    · intro h f hf
      rw [Set.mem_singleton_iff] at hf
      subst hf
      exact h
    · intro h
      exact h (c : MulAut L') rfl
  obtain ⟨E', hE'comp, hE'uniq, hE'max, hE'map⟩ :=
    ggLayerOf_lift ψ hψ hker ({(c : MulAut L')} : Set (MulAut L')) hFaut (ggFix (c : MulAut L')) hC hER
  have hJeq : J = E' := hE'uniq J hJ
  haveI : Finite A := Nat.finite_of_card_ne_zero (by rw [hF.aut.card_eq]; norm_num)
  refine ⟨κ, β, hF.aut, hβ, hκc, fun γ hγ hγβ => ?_⟩
  obtain ⟨δ, α, hδ, hα, -, -, hαγ, hαβ, -⟩ := exists_root_pair_kgL4 hγ hβ hγβ
  have hγα : iform γ α = 0 := by rw [iform_comm]; exact hαγ
  obtain ⟨E0, hE0q, hE0Γ, hE0Cβ, hE0n⟩ :=
    ggTP_a3_E0_data_cent hn hK hσ Fr hFr v hF.hv g hF.hg hF.hgF ζ hζ hζo hα hβ hαβ
  let nγ : ModGL Tag.E6 (AlgebraicClosure K) :=
    rootSL2 Tag.E6 (AlgebraicClosure K) γ WSL
  have ht_apply : ∀ x : Fin Tag.E6.rank → ZMod 3,
      twThetaHom g (t x) = rootDiagUnit Tag.E6 (zetaVec ζ hζ x) := by
    intro x
    rw [twThetaHom_apply, (hF.ht x).2]
    group
    rfl
  have hnγΓ : (nγ : ModGL TwistTag.E6.tag (AlgebraicClosure K)) ∈
      ((twThetaHom g).comp (twistedE6RootGroup K σ).subtype).range := by
    rw [range_twThetaHom_eq_Γ hn hK hσ Fr hFr v g hF.hg hF.hgF]
    exact rootSL2_WSL_mem_Γ_raw hn hK hσ Fr hFr v hF.hv g hF.hg hF.hgF hγ
  obtain ⟨c0sub, hc0sub⟩ := MonoidHom.mem_range.1 hnγΓ
  have hc0E : (c0sub : ModGL TwistTag.E6.tag K) ∈ E0.comap (twThetaHom g) := by
    change twThetaHom g (c0sub : ModGL TwistTag.E6.tag K) ∈ E0
    rw [show twThetaHom g (c0sub : ModGL TwistTag.E6.tag K) =
        (nγ : ModGL TwistTag.E6.tag (AlgebraicClosure K)) from hc0sub]
    exact hE0n γ hγ hγα hγβ
  have hE0range : E0 ≤ (twThetaHom g).range := by
    refine hE0Γ.trans ?_
    rw [← range_twThetaHom_eq_Γ hn hK hσ Fr hFr v g hF.hg hF.hgF]
    rintro y ⟨c', rfl⟩
    exact ⟨(twistedE6RootGroup K σ).subtype c', rfl⟩
  have hP0le : E0.comap (twThetaHom g) ≤ twistedE6RootGroup K σ := by
    intro x hx
    change twThetaHom g x ∈ E0 at hx
    have hxr : twThetaHom g x ∈ ((twThetaHom g).comp (twistedE6RootGroup K σ).subtype).range := by
      rw [range_twThetaHom_eq_Γ hn hK hσ Fr hFr v g hF.hg hF.hgF]
      exact hE0Γ hx
    obtain ⟨c', hc'⟩ := MonoidHom.mem_range.1 hxr
    have hxeq : x = (c' : ModGL TwistTag.E6.tag K) := twThetaHom_injective g (by
      simp only [MonoidHom.comp_apply] at hc'
      exact hc'.symm)
    rw [hxeq]
    exact c'.2
  have hP0perf : ⁅E0.comap (twThetaHom g), E0.comap (twThetaHom g)⁆ =
      E0.comap (twThetaHom g) := by
    have hmap : (E0.comap (twThetaHom g)).map (twThetaHom g) = E0 :=
      Subgroup.map_comap_eq_self hE0range
    have h1 : (⁅E0.comap (twThetaHom g), E0.comap (twThetaHom g)⁆).map (twThetaHom g) =
        (E0.comap (twThetaHom g)).map (twThetaHom g) := by
      rw [Subgroup.map_commutator (H₁ := E0.comap (twThetaHom g))
        (H₂ := E0.comap (twThetaHom g)) (f := twThetaHom g), hmap]
      exact Subgroup.isPerfect_iff.mp hE0q.1
    exact Subgroup.map_injective (twThetaHom_injective g) h1
  let f : TwE6Delta.RecipeR K n →* ModGL TwistTag.E6.tag K :=
    (twistedE6RootGroup K σ).subtype.comp ε.symm.toMonoidHom
  have hfr : f.range = twistedE6RootGroup K σ := by
    apply le_antisymm
    · rintro y ⟨y₀, rfl⟩
      exact (ε.symm y₀).2
    · intro y hy
      refine ⟨ε ⟨y, hy⟩, ?_⟩
      change (ε.symm (ε ⟨y, hy⟩) : ModGL TwistTag.E6.tag K) = y
      rw [MulEquiv.symm_apply_apply]
  let P : Subgroup (TwE6Delta.RecipeR K n) := (E0.comap (twThetaHom g)).comap f
  have hPmap : P.map f = E0.comap (twThetaHom g) :=
    Subgroup.map_comap_eq_self (by rw [hfr]; exact hP0le)
  have hfinj : Function.Injective f := by
    intro a b hab
    apply ε.symm.injective
    apply Subtype.ext
    exact hab
  have hPperf : ⁅P, P⁆ = P := by
    have h1 : (⁅P, P⁆).map f = P.map f := by
      rw [Subgroup.map_commutator (H₁ := P) (H₂ := P) (f := f), hPmap]
      exact hP0perf
    exact Subgroup.map_injective hfinj h1
  have hPle : P ≤ ggRFix ψ ({(c : MulAut L')} : Set (MulAut L')) := by
    intro r hr
    have hr' : f r ∈ E0.comap (twThetaHom g) := hr
    change twThetaHom g (f r) ∈ E0 at hr'
    have hcent := hE0Cβ hr'
    have htc : twThetaHom g (t (Multiplicative.toAdd (κ c))) =
        rootDiagUnit Tag.E6 (zetaVec ζ hζ (kgExpVec β)) := by
      rw [hκc]
      exact ht_apply (kgExpVec β)
    have hcomm : t (Multiplicative.toAdd (κ c)) * ε.symm r =
        ε.symm r * t (Multiplicative.toAdd (κ c)) := by
      apply twThetaHom_injective g
      rw [map_mul, map_mul, htc]
      exact Subgroup.mem_centralizer_iff.1 hcent
        (rootDiagUnit Tag.E6 (zetaVec ζ hζ (kgExpVec β))) rfl
    obtain ⟨l, hl⟩ := hψ r
    refine ⟨l, hl, ?_⟩
    intro f' hf'
    rw [Set.mem_singleton_iff] at hf'
    subst hf'
    apply ε.symm.injective
    apply Subtype.ext
    rw [hF.conj c l, hl, hcomm]
    group
  have hPER : P ≤ ER := hER.2.2.2 P hPle hPperf
  have hrP : ε.symm.symm c0sub ∈ P := by
    change f (ε.symm.symm c0sub) ∈ E0.comap (twThetaHom g)
    rw [MulEquiv.symm_symm]
    change twThetaHom g (f (ε c0sub)) ∈ E0
    rw [show f (ε c0sub) = (c0sub : ModGL TwistTag.E6.tag K) from by
      change (ε.symm (ε c0sub) : ModGL TwistTag.E6.tag K) = (c0sub : ModGL TwistTag.E6.tag K)
      rw [MulEquiv.symm_apply_apply]]
    exact hc0E
  have hrER : ε.symm.symm c0sub ∈ ER := hPER hrP
  obtain ⟨l, hlE', hlψ⟩ := Subgroup.mem_map.1 (by rw [hE'map]; exact hrER)
  have hl₀ : ε.symm (ψ l) = c0sub := by
    rw [hlψ, MulEquiv.symm_symm, MulEquiv.symm_apply_apply]
  have hmonoγ : nγ ∈ monomialSubgroup Tag.E6 (AlgebraicClosure K) :=
    (rootSL2_WSL_monomial_mapsRootLines (L := AlgebraicClosure K) hγ).1
  have hmapsγ : MapsRootLines nγ (rootReflection γ) :=
    (rootSL2_WSL_monomial_mapsRootLines (L := AlgebraicClosure K) hγ).2
  have ht_conj : ∀ x : Fin Tag.E6.rank → ZMod 3,
      ((c0sub : ModGL TwistTag.E6.tag K) * t x * (c0sub : ModGL TwistTag.E6.tag K)⁻¹ :
        ModGL TwistTag.E6.tag K) =
        (t (rootRefl γ x) : ModGL TwistTag.E6.tag K) := by
    intro x
    apply twThetaHom_injective g
    rw [map_mul, map_mul, map_inv, ht_apply x, ht_apply (rootRefl γ x)]
    rw [show twThetaHom g (c0sub : ModGL TwistTag.E6.tag K) =
        (nγ : ModGL TwistTag.E6.tag (AlgebraicClosure K)) from hc0sub]
    have h := monomial_conj_rootDiagUnit_zetaVec hζ hmonoγ hmapsγ x
    rw [adAct_rootReflection_eq_rootRefl hγ x] at h
    exact h
  have hact : ∀ a : ↥A, ∃ b' : ↥A,
      MulAut.conj l * (a : MulAut L') * (MulAut.conj l)⁻¹ = (b' : MulAut L') ∧
      Multiplicative.toAdd (κ b') = KGL.rootRefl γ (Multiplicative.toAdd (κ a)) := by
    intro a
    obtain ⟨b', hb'κ⟩ :=
      hF.aut.exists_of_mem_hypE6 (rootRefl_mem_hypE6 hγ (hF.aut.toAdd_mem_hypE6 a))
    refine ⟨b', ?_, hb'κ⟩
    refine mulAut_eq_of_comp_eq ψ hker hperf (fun z => ?_)
    apply ε.symm.injective
    apply Subtype.ext
    have h1 := ggTP_conjAut_apply hF hl₀ a z
    have h2 := hF.conj b' z
    have hkey : t (Multiplicative.toAdd (κ b')) =
        (c0sub : ModGL TwistTag.E6.tag K) * t (Multiplicative.toAdd (κ a)) *
          (c0sub : ModGL TwistTag.E6.tag K)⁻¹ := by
      rw [hb'κ]
      exact (ht_conj (Multiplicative.toAdd (κ a))).symm
    rw [h1, h2, hkey]
  have hnorm : MulAut.conj l ∈ Subgroup.normalizer (A : Set (MulAut L')) :=
    ggTP_conj_mem_normalizer l (fun a => by obtain ⟨b', hb', -⟩ := hact a; exact ⟨b', hb'⟩)
  refine ⟨l, ?_, hnorm, ?_⟩
  · rw [hJeq]
    exact hlE'
  · intro a b hb
    obtain ⟨b', hbeq, hb'κ⟩ := hact a
    have hbb' : b = b' := Subtype.ext (hb.trans hbeq)
    rw [hbb', hb'κ]
end CFSG.StandardType

end
