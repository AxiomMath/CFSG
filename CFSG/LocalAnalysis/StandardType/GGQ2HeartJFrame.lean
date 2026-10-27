module

public import CFSG.LocalAnalysis.StandardType.GGQ2HeartJLang
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRootGenFrame
public import CFSG.LocalAnalysis.StandardType.GGQTwoE6Realization
public import CFSG.LocalAnalysis.StandardType.GGQTwoCavQuotient
public import CFSG.LocalAnalysis.StandardType.GGQTwoHeartJInput
public import CFSG.LocalAnalysis.StandardType.GGLangExhaust

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem ggQ2HeartJFrameAux_card_bs {G : Type} [Group G] [Finite G] {Bs L : Subgroup G}
    {x : G} {labL : LargeEvenLabel} (htag : labL.tag = .twE6) (M : GGQ2LDatum 3 Bs L x)
    (hW : GGQ2LabelWeyl labL M.coxeter) (hB : M.ShapeB) : Nat.card Bs = 3 ^ 6 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e, -⟩ : ∃ e : Fin 6 ≃ M.Λ, M.coxeter = CoxeterMatrix.E₆.reindex e := by
    simpa only [GGQ2LabelWeyl, htag] using hW
  have hΛ : Fintype.card M.Λ = 6 := by rw [← Fintype.card_congr e, Fintype.card_fin]
  have : Finite M.V := Finite.of_equiv (Additive ↥Bs) M.model.toEquiv
  have : Module.Finite (ZMod 3) M.V := Module.Finite.of_finite
  have hx0 : M.xV ≠ 0 := by
    intro h
    exact hB.2.2.1 (h ▸ M.coSpan.zero_mem)
  have hdisj : Disjoint M.coSpan (Submodule.span (ZMod 3) {M.xV}) := by
    rw [Submodule.disjoint_span_singleton' hx0]
    exact hB.2.2.1
  have hfin : Module.finrank (ZMod 3) M.V = 6 := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq M.coSpan (Submodule.span (ZMod 3) {M.xV})
    rw [hB.2.2.2, finrank_top, hdisj.eq_bot, finrank_bot, add_zero,
      finrank_span_singleton hx0] at h1
    rw [h1, hB.2.1, hΛ]
  have hcardV : Nat.card M.V = 3 ^ 6 := by
    rw [← FiniteField.pow_finrank_eq_natCard 3 M.V, hfin]
  rw [← hcardV]
  exact Nat.card_congr ((Additive.ofMul.trans M.model.toEquiv))

private theorem ggQ2HeartJFrameAux_cent {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) (hxBs : x ∈ Bs) :
    Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSS : LargeEvenSStar 3 B x L := hS.1.1.1.2.2.2.2.2.2.1
  obtain ⟨-, -, hx1, hLC, hcyc⟩ := hSS
  have hBs : IsElemAbelian 3 Bs := hS.1.1.2.1.2.1
  have hxC := mem_centralizer_of_le_centralizer hLC.1
  have hE : IsElemAbelian 3 (Bs ⊓ Subgroup.centralizer (L : Set G)) :=
    TableB.isElemAbelian_mono hBs inf_le_left
  have hcE := hcyc _ inf_le_right (TableB.isPGroup_of_isElemAbelian hE)
  have hx3 : x ^ 3 = 1 := hBs.2 x hxBs
  have hle : Subgroup.zpowers x ≤ Bs ⊓ Subgroup.centralizer (L : Set G) :=
    (Subgroup.zpowers_le).mpr ⟨hxBs, hxC⟩
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1]
  exact TableB.card_le_of_isCyclic (by norm_num) hcE hE.2

private theorem ggQ2HeartJFrameAux_zetaVec_eq_one {Ω : Type} [Field Ω] {ζ : Ωˣ} (hζ : ζ ^ 3 = 1)
    (hζo : orderOf ζ = 3) {v : Fin Tag.E6.rank → ZMod 3}
    (h : TableBExc.E6Three.zetaVec (τ := Tag.E6) ζ hζ v = 1) : v = 0 := by
  funext i
  have hi := congrFun h i
  rw [TableBExc.E6Three.zetaVec_apply, Pi.one_apply] at hi
  have hdvd : 3 ∣ (v i).val := by
    have h1 := orderOf_dvd_of_pow_eq_one hi
    rwa [hζo] at h1
  have hlt : (v i).val < 3 := ZMod.val_lt (v i)
  have h0 : (v i).val = 0 := by omega
  exact (ZMod.val_eq_zero (v i)).1 h0

private theorem ggQ2HeartJFrameAux_labQTwo
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) {labL : LargeEvenLabel}
    (htag : labL.tag = .twE6) (hmark : LargeEvenMarking L (fun lab _ _ _ _ _ => lab = labL)) :
    GGLabQTwo 3 labL := by
  obtain ⟨-, lab₀, hlab₀, hraw₀⟩ := hS.2.1
  obtain ⟨-, lab₁, hlab₁, hraw₁⟩ := hmark
  have hq₀ : GGLabQTwo 3 lab₀ := by
    obtain ⟨_, _, _, _, _, _, _, h, -⟩ := largeEvenRawDatum_exists hraw₀
    exact h
  have hEq₁ : lab₁ = labL := by
    obtain ⟨_, _, _, _, _, _, _, h⟩ := largeEvenRawDatum_exists hraw₁
    exact h
  have has₀ : GGHasLabel lab₀ (L ⧸ Subgroup.center L) := by
    unfold GGHasLabel
    exact largeEvenRawDatum_mono (fun _ _ _ _ ⟨_, _, θ, _⟩ => ⟨θ⟩) hraw₀
  have has₁ : GGHasLabel lab₁ (L ⧸ Subgroup.center L) := by
    unfold GGHasLabel
    exact largeEvenRawDatum_mono (fun _ _ _ _ ⟨_, _, θ, _⟩ => ⟨θ⟩) hraw₁
  have hiso := ggLabelRigidInput_holds lab₀ lab₁ (L ⧸ Subgroup.center L) hlab₀ hlab₁ has₀ has₁
  have htag₁ : lab₁.tag = .twE6 := hEq₁ ▸ htag
  have h01 : lab₀ = lab₁ := by
    rcases hiso with h | ⟨-, h, -⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · rcases h with h | h <;> rw [h] at htag₁ <;> cases htag₁
    all_goals first
      | (rw [h] at htag₁; cases htag₁)
  rw [← hEq₁, ← h01]
  exact hq₀


theorem ggQ2HeartJ_frame {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) {labL : LargeEvenLabel}
    (htag : labL.tag = .twE6) (hmark : LargeEvenMarking L (fun lab _ _ _ _ _ => lab = labL))
    (M : GGQ2LDatum 3 Bs L x) (hW : GGQ2LabelWeyl labL M.coxeter) (hB : M.ShapeB)
    (yB : ↥Bs) (hyB : (yB : G) ∈ D) (hyx : (yB : G) ∉ Subgroup.zpowers x) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (S : LangSetup Tag.E6 (AlgebraicClosure K) 5)
      (ζ : (AlgebraicClosure K)ˣ) (hζ : ζ ^ 3 = 1)
      (κ : ↥Bs →* Multiplicative (Fin Tag.E6.rank → ZMod 3))
      (i : KernelComponent (rootCharHom
        (TableBExc.E6Three.zetaVec (τ := Tag.E6) ζ hζ (Multiplicative.toAdd (κ yB))))),
      orderOf ζ = 3 ∧ (∀ α, S.ρ α = -α) ∧ S.D.q = 2 ∧ S.IsAlgebraic ∧
      (∀ a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ,
        rootDiagUnit Tag.E6 a ∈ S.D.torus ↔ ∀ j, a j ^ 3 = 1) ∧
      (∀ b, κ b = 1 ↔ (b : G) ∈ Subgroup.zpowers x) ∧
      (∀ v, Multiplicative.ofAdd v ∈ κ.range ↔ v ∈ NoOffRest.hypE6) ∧
      (∀ φ ∈ ggAutomizer L Bs, ∃ u : WeylGroup Tag.E6, ∀ b : ↥Bs,
        Multiplicative.toAdd (κ (φ b)) =
          TableBExc.E6Three.adAct Tag.E6 3 u (Multiplicative.toAdd (κ b))) ∧
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom
        (TableBExc.E6Three.zetaVec (τ := Tag.E6) ζ hζ (Multiplicative.toAdd (κ yB)))) i) ∧
      ∀ b : ↥Bs, (∀ j ∈ J, (b : G) * j = j * (b : G)) →
        rationalComponent S.ρ S.Γ (rootCharHom
          (TableBExc.E6Three.zetaVec (τ := Tag.E6) ζ hζ (Multiplicative.toAdd (κ yB)))) i ≤
          Subgroup.centralizer {(rootDiagUnit Tag.E6
            (TableBExc.E6Three.zetaVec (τ := Tag.E6) ζ hζ (Multiplicative.toAdd (κ b))))} := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBsE : IsElemAbelian 3 Bs := hS.1.1.2.1.2.1
  have hSS : LargeEvenSStar 3 B x L := hS.1.1.1.2.2.2.2.2.2.1
  have hL : commutator L = ⊤ := hSS.2.2.2.1.2.2.1
  have hstd : LargeEvenStdSubPre 3 B x L D J := hS.1.1.2.2.1
  have hDB : D ≤ B := hstd.1
  have hBBs : B ≤ Bs := hS.1.1.2.1.1
  have hJ : CFSG.Assembly.IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hstd.2.2.2.2.2.1
  have hxBs : x ∈ Bs := M.hx
  have hcent := ggQ2HeartJFrameAux_cent hS hxBs
  have hidx : ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index = 3 ^ 5 := by
    have h1 := Subgroup.relIndex_mul_card (Subgroup.centralizer (L : Set G)) Bs
    rw [inf_comm, hcent, Nat.card_zpowers, orderOf_eq_prime (hBsE.2 x hxBs) hSS.2.2.1,
      ggQ2HeartJFrameAux_card_bs htag M hW hB] at h1
    change ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index * 3 = 3 ^ 6 at h1
    omega
  have hq2 := ggQ2HeartJFrameAux_labQTwo hS htag hmark
  have hmarkI : GGInnerDiagOnLabel (fun _ lab' => lab' = labL) 3 Bs L :=
    QTwoCav.innerDiagOnLabel_of_setting hS hmark
  obtain ⟨K, instF, instFin, σ, θ, hN, Simg, hK4, hσ, hSdef, -, -, hSrange, -, -, -⟩ :=
    QTwoE6.actual_beta_image_of_marking hS rfl hq2 htag hmarkI hidx
  have hK1 : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK4]; norm_num
  have hσ1 : ∀ c, σ c = c ^ 2 ^ 1 := by simpa using hσ
  have : CharP K 2 := charP_two_of_card (m := 2) (by rw [hK4]; norm_num)
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  have : ExpChar (AlgebraicClosure K) 2 := ExpChar.prime Nat.prime_two
  obtain ⟨ζ, hζp⟩ := CFSG.LieType.SeitzGeneration.exists_primitiveRoot_units
    (L := AlgebraicClosure K) (ℓ := 2) Nat.prime_two Nat.prime_three (by norm_num)
  have hζ : ζ ^ 3 = 1 := hζp.pow_eq_one
  have hζo : orderOf ζ = 3 := hζp.eq_orderOf.symm
  let Fr : AlgebraicClosure K →+* AlgebraicClosure K := iterateFrobenius (AlgebraicClosure K) 2 1
  have hFr : ∀ c, Fr c = c ^ 2 ^ 1 := fun c => iterateFrobenius_def (R := AlgebraicClosure K) 2 1 c
  let eR : LargeEvenCenterQuot (twistedE6RootGroup K σ) ≃* ↥(twistedE6RootGroup K σ) :=
    centerQuotEquivOfBot (exceptional_fixed_center_trivial TwistTag.E6 K σ)
  let ψ₀ : ↥L →* ↥(twistedE6RootGroup K σ) := eR.toMonoidHom.comp (ggQuotHom θ)
  have hψ₀ : Function.Surjective ψ₀ := eR.surjective.comp (ggQuotHom_surjective θ)
  have hker : ψ₀.ker ≤ Subgroup.center ↥L := by
    intro l hl
    rw [MonoidHom.mem_ker] at hl
    have h1 : ggQuotHom θ l = 1 := eR.map_eq_one_iff.mp hl
    rw [← ker_ggQuotHom θ]
    exact h1
  let A : Subgroup (MulAut ↥L) := (ggGamma L hN).range
  obtain ⟨hA, hsc⟩ := QTwoCav.gamma_hyps hS hN
  have hcardA : Nat.card A = 3 ^ 5 := (QTwoCav.gamma_card hN).trans hidx
  have h5 : 3 ^ 5 ≤ Nat.card A := hcardA.ge
  have hβψ : ∀ (b : ↥Bs) (l : ↥L),
      MulAut.congr eR (ggBeta L θ hN b) (ψ₀ l) = ψ₀ (ggGamma L hN b l) := by
    intro b l
    rw [MulAut.congr_apply]
    change eR (ggBeta L θ hN b (eR.symm (eR (ggQuotHom θ l)))) = eR (ggQuotHom θ (ggGamma L hN b l))
    rw [MulEquiv.symm_apply_apply, ggQuotHom_apply, ggQuotHom_apply, ggBeta_eq, ggLAut_apply]
    rfl
  have hAH : ∀ a ∈ A, ∃ φ ∈ (RecipeExcLang.twConj K σ).range, ∀ l, φ (ψ₀ l) = ψ₀ (a l) := by
    rintro _ ⟨b, rfl⟩
    have hφS : MulAut.congr eR (ggBeta L θ hN b) ∈ Simg := by
      rw [hSdef]
      exact ⟨_, ⟨b, rfl⟩, rfl⟩
    exact ⟨_, hSrange hφS, fun l => hβψ b l⟩
  obtain ⟨g, κ, t, -, hg, hgF, hκinj, hκrange, ht, hconj, -, -, -, hinner⟩ :=
    TwE6ThreeRootGen.exists_frame_torus (n := 1) le_rfl hK1 σ hσ1 (by norm_num) hFr hζ hζo
      hψ₀ hker hL hA hAH h5 hsc
  obtain ⟨S, e, he, hρ, hq, hAlg, htor⟩ :=
    ggQ2HeartJ_langSetup (K := K) (σ := σ) (n := 1) le_rfl hK1 hσ1 Fr hFr g hg hgF
  have htor3 : ∀ a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ,
      rootDiagUnit Tag.E6 a ∈ S.D.torus ↔ ∀ j, a j ^ 3 = 1 := fun a => htor a
  let κB : ↥Bs →* Multiplicative (Fin Tag.E6.rank → ZMod 3) := κ.comp (ggGamma L hN).rangeRestrict
  let dB : ↥Bs → ModGL Tag.E6 (AlgebraicClosure K) := fun b =>
    rootDiagUnit Tag.E6 (TableBExc.E6Three.zetaVec (τ := Tag.E6) ζ hζ (Multiplicative.toAdd (κB b)))
  let f : LargeEvenCenterQuot (twistedE6RootGroup K σ) →* ModGL Tag.E6 (AlgebraicClosure K) :=
    S.Γ.subtype.comp (e.toMonoidHom.comp eR.toMonoidHom)
  have hf : Function.Injective f :=
    Subtype.val_injective.comp (e.injective.comp eR.injective)
  have hfrange : ∀ r, f r ∈ S.Γ := fun r => (e (eR r)).2
  have hact : ∀ (b : ↥Bs) (r : LargeEvenCenterQuot (twistedE6RootGroup K σ)),
      f (ggBeta L θ hN b r) = dB b * f r * (dB b)⁻¹ := by
    intro b r
    obtain ⟨l, rfl⟩ := ggQuotHom_surjective θ r
    have h1 : ggBeta L θ hN b (ggQuotHom θ l) = ggQuotHom θ (ggGamma L hN b l) := by
      rw [ggQuotHom_apply, ggQuotHom_apply, ggBeta_eq, ggLAut_apply]
      rfl
    have h2 := hconj ((ggGamma L hN).rangeRestrict b) l
    have h3 : (((ggGamma L hN).rangeRestrict b : A) : MulAut ↥L) = ggGamma L hN b := rfl
    rw [h3] at h2
    have h4 : (g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((ψ₀ (ggGamma L hN b l) : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) * g :
            ModGL TwistTag.E6.tag (AlgebraicClosure K)) =
        rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec (τ := Tag.E6) ζ hζ
            (Multiplicative.toAdd (κ ((ggGamma L hN).rangeRestrict b)))) *
          (g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((ψ₀ l : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) * g) *
          (rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec (τ := Tag.E6) ζ hζ
            (Multiplicative.toAdd (κ ((ggGamma L hN).rangeRestrict b)))))⁻¹ := by
      rw [h2, map_mul, map_mul, map_inv, ht]
      group
      rfl
    rw [h1, show f (ggQuotHom θ (ggGamma L hN b l)) = _ from he (ψ₀ (ggGamma L hN b l)),
      show f (ggQuotHom θ l) = _ from he (ψ₀ l)]
    exact h4
  have hκB1 : ∀ b, κB b = 1 ↔ (b : G) ∈ Subgroup.zpowers x := by
    intro b
    constructor
    · intro h
      have h1 : (ggGamma L hN).rangeRestrict b = 1 := hκinj (h.trans (map_one κ).symm)
      have h2 : ggGamma L hN b = 1 := congrArg Subtype.val h1
      have h3 := (ggGamma_eq_one_iff L hN b).1 h2
      rw [← hcent]
      exact ⟨b.2, h3⟩
    · intro h
      have h3 : (b : G) ∈ Subgroup.centralizer (L : Set G) := by
        rw [← hcent] at h
        exact h.2
      have h1 : (ggGamma L hN).rangeRestrict b = 1 := Subtype.ext ((ggGamma_eq_one_iff L hN b).2 h3)
      change κ ((ggGamma L hN).rangeRestrict b) = 1
      rw [h1, map_one]
  have hκBrange : ∀ w, w ∈ κB.range ↔ w ∈ κ.range := by
    intro w
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨a, rfl⟩
      obtain ⟨b, hb⟩ := (ggGamma L hN).rangeRestrict_surjective a
      exact ⟨b, by rw [← hb]; rfl⟩
  have hκhyp : ∀ v, Multiplicative.ofAdd v ∈ κB.range ↔ v ∈ NoOffRest.hypE6 := by
    rcases hκrange with htop | hhyp
    · exfalso
      have h1 : Nat.card κ.range = Nat.card A := by
        rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hκinj, Subgroup.card_top]
      rw [htop, Subgroup.card_top, hcardA] at h1
      have h2 : Nat.card (Multiplicative (Fin 6 → ZMod 3)) = 3 ^ 6 := by
        rw [Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card, Fintype.card_fun,
          ZMod.card, Fintype.card_fin]
      rw [h2] at h1
      norm_num at h1
    · intro v
      rw [hκBrange]
      exact hhyp v
  have hnormκ : ∀ φ ∈ ggAutomizer L Bs, ∃ u : WeylGroup Tag.E6, ∀ b : ↥Bs,
      Multiplicative.toAdd (κB (φ b)) =
        TableBExc.E6Three.adAct Tag.E6 3 u (Multiplicative.toAdd (κB b)) := by
    intro φ hφ
    obtain ⟨g', hg'L, -, hg'⟩ := mem_ggAutomizer_iff.1 hφ
    obtain ⟨m, hm⟩ : ∃ m : ↥L, (m : G) = g' := ⟨⟨g', hg'L⟩, rfl⟩
    have hconjγ : ∀ b : ↥Bs,
        MulAut.conj m * ggGamma L hN b * (MulAut.conj m)⁻¹ = ggGamma L hN (φ b) := by
      intro b
      refine MulEquiv.ext fun l => Subtype.ext ?_
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply,
        Subgroup.coe_mul, Subgroup.coe_mul, ggGamma_coe, ggGamma_coe, hg' b, Subgroup.coe_mul,
        Subgroup.coe_mul]
      simp only [Subgroup.coe_inv, hm]
      group
    have hmN : MulAut.conj m ∈ Subgroup.normalizer (A : Set (MulAut ↥L)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro a
      constructor
      · rintro ⟨b, rfl⟩
        exact ⟨φ b, (hconjγ b).symm⟩
      · rintro ⟨b', hb'⟩
        refine ⟨φ.symm b', ?_⟩
        have h1 := hconjγ (φ.symm b')
        rw [MulEquiv.apply_symm_apply, hb'] at h1
        exact mul_left_cancel (mul_right_cancel h1)
    obtain ⟨u, hu⟩ := hinner m hmN
    exact ⟨u, fun b => hu ((ggGamma L hN).rangeRestrict b) ((ggGamma L hN).rangeRestrict (φ b))
      (hconjγ b).symm⟩
  have hdT : ∀ b, rootDiagUnit Tag.E6 (TableBExc.E6Three.zetaVec (τ := Tag.E6) ζ hζ
      (Multiplicative.toAdd (κB b))) ∈ S.D.torus := by
    intro b
    refine (htor3 _).2 fun j => ?_
    rw [TableBExc.E6Three.zetaVec_apply, ← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  have hap : ∀ j, TableBExc.E6Three.zetaVec (τ := Tag.E6) ζ hζ (Multiplicative.toAdd (κB yB)) j ^ 3
      = 1 := by
    intro j
    rw [TableBExc.E6Three.zetaVec_apply, ← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  have hdy1 : dB yB ≠ 1 := by
    intro h
    have h1 := CFSG.LieType.Chevalley.rootDiagUnit_injective (τ := Tag.E6)
      (h.trans (rootDiagUnit_one (τ := Tag.E6)).symm)
    have h2 := ggQ2HeartJFrameAux_zetaVec_eq_one hζ hζo h1
    exact hyx ((hκB1 yB).1 (by simpa using congrArg Multiplicative.ofAdd h2))
  have hpL : ((3 : ℕ) : AlgebraicClosure K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (AlgebraicClosure K) 2]
    norm_num
  let hDL : D ≤ Subgroup.normalizer (L : Set G) := QTwoCav.d_le_normalizer hS hN
  have hcompR := QTwoCav.isComponentOf_quotient_image hDL θ hJ
  have hcompF := isComponentOf_map_of_injective f hf hcompR
  have hβD : ∀ d : ↥D, ggBeta L θ hDL d = ggBeta L θ hN ⟨d, hBBs (hDB d.2)⟩ := fun d => rfl
  let yD : ↥D := ⟨yB, hyB⟩
  have hβy1 : ggBeta L θ hDL yD ≠ 1 := by
    intro h
    have h1 : yD ∈ (ggBeta L θ hDL).ker := h
    rw [QTwoCav.beta_ker hL θ hDL, Subgroup.mem_subgroupOf] at h1
    exact hyx (hcent ▸ ⟨yB.2, h1⟩)
  have hβcard := QTwoCav.beta_d_card θ Nat.prime_three hS hN
  have hgen : ∀ d : ↥D, ggBeta L θ hDL d ∈ Subgroup.zpowers (ggBeta L θ hDL yD) := by
    intro d
    have : Finite (ggBeta L θ hDL).range :=
      Nat.finite_of_card_ne_zero (by rw [hβcard]; norm_num)
    have hne : (⟨ggBeta L θ hDL yD, yD, rfl⟩ : (ggBeta L θ hDL).range) ≠ 1 := fun h =>
      hβy1 (congrArg Subtype.val h)
    have htopz := zpowers_eq_top_of_prime_card hβcard hne
    have hmem : (⟨ggBeta L θ hDL d, d, rfl⟩ : (ggBeta L θ hDL).range) ∈
        Subgroup.zpowers (⟨ggBeta L θ hDL yD, yD, rfl⟩ : (ggBeta L θ hDL).range) := by
      rw [htopz]
      exact Subgroup.mem_top _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    exact Subgroup.mem_zpowers_iff.2 ⟨k, by
      have h1 := congrArg Subtype.val hk
      simpa using h1⟩
  have hfix : (⨅ d : ↥D, ggFix (ggBeta L θ hDL d)).map f =
      S.Γ ⊓ Subgroup.centralizer {dB yB} := by
    ext z
    constructor
    · rintro ⟨r, hr, rfl⟩
      refine ⟨hfrange r, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      have hry : ggBeta L θ hDL yD r = r := (Subgroup.mem_iInf.1 hr) yD
      have h1 := hact yB r
      rw [← hβD yD, hry] at h1
      calc f r * dB yB = (dB yB * f r * (dB yB)⁻¹) * dB yB := by rw [← h1]
        _ = dB yB * f r := by group
    · rintro ⟨hzΓ, hzc⟩
      obtain ⟨c, hc⟩ := e.surjective ⟨z, hzΓ⟩
      obtain ⟨r, rfl⟩ := eR.surjective c
      have hfr : f r = z := congrArg Subtype.val hc
      refine ⟨r, ?_, hfr⟩
      have hry : ggBeta L θ hDL yD r = r := by
        apply hf
        rw [hβD yD, hact yB r, hfr]
        have hzc' := Subgroup.mem_centralizer_singleton_iff.1 hzc
        calc dB yB * z * (dB yB)⁻¹ = (z * dB yB) * (dB yB)⁻¹ := by rw [hzc']
          _ = z := by group
      refine Subgroup.mem_iInf.2 fun d => ?_
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hgen d)
      change ggBeta L θ hDL d r = r
      rw [← hk]
      have hpow : ∀ n : ℕ, (ggBeta L θ hDL yD ^ n) r = r := by
        intro n
        induction n with
        | zero => rfl
        | succ n ih => rw [pow_succ, MulAut.mul_apply, hry, ih]
      rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
      · rw [zpow_natCast, hpow n]
      · rw [zpow_neg, zpow_natCast]
        conv_lhs => rw [← hpow n]
        exact (ggBeta L θ hDL yD ^ n).symm_apply_apply r
  rw [hfix] at hcompF
  have hcompO : CFSG.Open.IsComponentOf
      (((J.subgroupOf L).map (ggQuotHom θ)).map f) (S.Γ ⊓ Subgroup.centralizer {dB yB}) :=
    CFSG.Assembly.isComponentOf_iff_open.1 hcompF
  obtain ⟨i, hqi, hJi⟩ := LangRat.exists_rationalComponent_eq_of_isComponentOf_of_ne_G2 S
    (fun h => by cases h) Nat.prime_three hpL (hdT yB) hap hdy1 hcompO
  refine ⟨K, instF, instFin, S, ζ, hζ, κB, i, hζo, hρ, by rw [hq]; norm_num, hAlg, htor3, hκB1,
    hκhyp, hnormκ, hqi, ?_⟩
  intro b hb
  rw [← hJi]
  rintro _ ⟨r, ⟨l, hl, rfl⟩, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hlJ : (l : G) ∈ J := hl
  have hγl : ggGamma L hN b l = l := Subtype.ext (by
    rw [ggGamma_coe, hb l hlJ, mul_inv_cancel_right])
  have h1 := hact b (ggQuotHom θ l)
  have h2 : ggBeta L θ hN b (ggQuotHom θ l) = ggQuotHom θ l := by
    rw [ggQuotHom_apply, ggBeta_eq, ggLAut_apply]
    exact congrArg (fun l' : ↥L => θ (l' : L ⧸ Subgroup.center L)) hγl
  rw [h2] at h1
  calc f (ggQuotHom θ l) * dB b = (dB b * f (ggQuotHom θ l) * (dB b)⁻¹) * dB b := by rw [← h1]
    _ = dB b * f (ggQuotHom θ l) := by group

end CFSG.StandardType

end
