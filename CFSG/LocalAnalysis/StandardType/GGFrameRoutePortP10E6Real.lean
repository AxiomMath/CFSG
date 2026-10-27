module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP10E6Pos
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP10E6Model
public import CFSG.LocalAnalysis.StandardType.GGQTwoE6Realization
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryDesc

public section

namespace CFSG.StandardType.FrameRoute

open CFSG CFSG.Assembly CFSG.Open CFSG.StandardType CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Lang.E6Descent CFSG.RankThree.Classical2

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def P10ModelReal (C : Type) [Group C] (S : Subgroup (MulAut C)) : Prop :=
  ∃ e : ↥S ≃* Multiplicative (Fin TwistTag.E6.tag.rank → ZMod 3),
    ∀ α : MulAut C, ∀ hα : α ∈ Subgroup.normalizer (S : Set (MulAut C)),
      ∃ (w : WeylGroup TwistTag.E6.tag) (ε : ZMod 3), (ε = 1 ∨ ε = -1) ∧
        ∀ s : ↥S, Multiplicative.toAdd (e (ggConjAut S hα s)) =
          ε • TwE6NormThree.weylDual w (Multiplicative.toAdd (e s))

theorem p10real_transfer {K C : Type} [Group K] [Group C] (D : MulAut K →* MulAut C)
    (hD : Function.Injective D) (A : Subgroup (MulAut K)) (hS : P10ModelReal C (A.map D)) :
    ∃ e : ↥A ≃* Multiplicative (Fin TwistTag.E6.tag.rank → ZMod 3),
      ∀ α : MulAut K, ∀ hα : α ∈ Subgroup.normalizer (A : Set (MulAut K)),
        ∃ (w : WeylGroup TwistTag.E6.tag) (ε : ZMod 3), (ε = 1 ∨ ε = -1) ∧
          ∀ a : ↥A, Multiplicative.toAdd (e (ggConjAut A hα a)) =
            ε • TwE6NormThree.weylDual w (Multiplicative.toAdd (e a)) := by
  obtain ⟨eS, hM⟩ := hS
  let ι : ↥A ≃* ↥(A.map D) := Subgroup.equivMapOfInjective A D hD
  refine ⟨ι.trans eS, fun α hα => ?_⟩
  have hDα : D α ∈ Subgroup.normalizer ((A.map D : Subgroup (MulAut C)) : Set (MulAut C)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro s
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨α * a * α⁻¹, (Subgroup.mem_normalizer_iff.mp hα a).mp ha, by simp⟩
    · rintro ⟨a', ha', h⟩
      have hs : s = D (α⁻¹ * a' * α) := by
        rw [map_mul, map_mul, map_inv, h]
        group
      have hmem : α⁻¹ * a' * α ∈ A := by
        have e : α * (α⁻¹ * a' * α) * α⁻¹ = a' := by group
        have := (Subgroup.mem_normalizer_iff.mp hα (α⁻¹ * a' * α)).mpr (by
          rw [e]
          exact ha')
        exact this
      exact ⟨α⁻¹ * a' * α, hmem, hs.symm⟩
  obtain ⟨w, ε, hε, hrel⟩ := hM (D α) hDα
  refine ⟨w, ε, hε, fun a => ?_⟩
  have hι : ι (ggConjAut A hα a) = ggConjAut (A.map D) hDα (ι a) := by
    apply Subtype.ext
    simp [ι, ggConjAut_apply]
  show Multiplicative.toAdd (eS (ι (ggConjAut A hα a))) = _
  rw [hι, hrel]
  rfl


theorem p10real_isElemAbelian_map {A B : Type} [Group A] [Group B] (f : A →* B) {E : Subgroup A}
    (hE : IsElemAbelian 3 E) : IsElemAbelian 3 (E.map f) := by
  refine ⟨⟨⟨?_⟩⟩, ?_⟩
  · rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩
    apply Subtype.ext
    show f a * f b = f b * f a
    rw [← map_mul, ← map_mul, TableB.IsElemAbelian.comm hE ha hb]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hE.2 a ha, map_one]

theorem p10real_descent {G : Type} [Group G] {Bs K : Subgroup G} {C : Type} [Group C]
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) (hperf : commutator ↥K = ⊤)
    (θ' : ↥K ⧸ Subgroup.center ↥K ≃* C) :
    ∃ D : MulAut ↥K →* MulAut C, Function.Injective D ∧
      ∀ b : ↥Bs, D (ggGamma K hN b) = ggBeta K θ' hN b := by
  let ψ : ↥K →* C := (θ' : ↥K ⧸ Subgroup.center ↥K →* C).comp
    (QuotientGroup.mk' (Subgroup.center ↥K))
  have hψ : Function.Surjective ψ := fun c => by
    obtain ⟨q, rfl⟩ := θ'.surjective c
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨l, rfl⟩
  have hZ : ψ.ker = Subgroup.center ↥K := by
    ext x
    simp only [MonoidHom.mem_ker, ψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      MulEquiv.coe_toMonoidHom]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have h1 : (QuotientGroup.mk x : ↥K ⧸ Subgroup.center ↥K) = 1 :=
        θ'.injective (h.trans (map_one θ').symm)
      exact (QuotientGroup.eq_one_iff x).mp h1
    · have h1 : (QuotientGroup.mk x : ↥K ⧸ Subgroup.center ↥K) = 1 :=
        (QuotientGroup.eq_one_iff x).mpr h
      exact (congrArg θ' h1).trans (map_one θ')
  refine ⟨BstarDesc.descAut hψ hZ, BstarDesc.descAut_injective hψ hZ hperf, fun b => ?_⟩
  ext c
  obtain ⟨l, rfl⟩ := hψ c
  rw [BstarDesc.descAut_apply hψ hZ]
  exact (ggLAut_apply K θ' ⟨b, hN b.2⟩ l).symm


theorem p10real_legacy_to_canonical {lab : LargeEvenLabel} (htag : lab.tag = .twE6)
    {Q : LargeEvenRawCont} (h : CFSG.Assembly.LargeEvenRawDatumLegacy lab Q) :
    CFSG.Assembly.LargeEvenRawDatum lab Q := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag
  subst htag
  dsimp only [CFSG.Assembly.LargeEvenRawDatum, CFSG.Assembly.LargeEvenRawDatumLegacy] at h ⊢
  exact h

theorem p10real_unpack
    {G : Type} [Group G] [Finite G] {Bs K : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hK : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twE6, 0, 1⟩) 3 Bs K) :
    commutator ↥K = ⊤ ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F) (σ : F ≃+* F)
      (θ : ↥K ⧸ Subgroup.center ↥K ≃* LargeEvenCenterQuot (twistedE6RootGroup F σ)),
      Nat.card F = (2 ^ 1) ^ 2 ∧ (∀ c, σ c = c ^ 2 ^ 1) ∧
        (ggBeta K θ hN).range ≤
          RecipeExcLang.markIDImage (IsRoot TwistTag.E6.tag) F (twistedE6RootGroup F σ) := by
  unfold GGInnerDiagOnLabel at hK
  obtain ⟨hperf, labM, hlab2M, hrawM⟩ := hK
  let Qmark : LargeEvenRawCont := fun R _ I F => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
    ∃ θ : ↥K ⧸ Subgroup.center ↥K ≃* R, (labM = ⟨.twE6, 0, 1⟩) ∧
      Bs ≤ Subgroup.normalizer (K : Set G) ∧
      ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = (b : G)⁻¹ * l * (b : G)) φ
  obtain ⟨R, _, I, Fd, hQraw⟩ := CFSG.StandardType.largeEvenRawDatum_exists hrawM
  obtain ⟨-, -, θR, hlabEq, -, -⟩ := hQraw
  have htagM : labM.tag = .twE6 := by rw [hlabEq]
  have hn1 : labM.n = 1 := by rw [hlabEq]
  have hnM : 1 ≤ labM.n := by omega
  have hrawCanon : CFSG.Assembly.LargeEvenRawDatum labM Qmark :=
    p10real_legacy_to_canonical htagM hrawM
  obtain ⟨F, instF, instFin, σ, hFcard, hσpow, hQ0⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.K155X.excTwE6_raw_of_label (lab := labM) (Q := Qmark) htagM hnM
      hrawCanon
  obtain ⟨-, -, θ, -, hN', hact⟩ := hQ0
  rw [hn1] at hFcard hσpow
  refine ⟨hperf, F, instF, instFin, σ, θ, hFcard, hσpow, ?_⟩
  rintro _ ⟨b, rfl⟩
  simpa only [ggBeta_eq] using ggLAut_mem_of_induces (L := K) (θ := θ) (B := Bs) hN hact b.2

theorem p10real_langCube
    {G : Type} [Group G] [Finite G] {Bs K : Subgroup G} {z : G}
    {n : ℕ} (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ n) (hn : 7 ≤ n) (hz : z ∈ Bs)
    (hz1 : z ≠ 1) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z)
    (hBstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hK : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twE6, 0, 1⟩) 3 Bs K) :
    n = 7 ∧ commutator ↥K = ⊤ ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (σ : F ≃+* F)
        (hF : Nat.card F = (2 ^ 1) ^ 2) (hσ : ∀ c, σ c = c ^ 2 ^ 1)
        (Fr : AlgebraicClosure F →+* AlgebraicClosure F) (hFr : ∀ c, Fr c = c ^ 2 ^ 1)
        (θ : ↥K ⧸ Subgroup.center ↥K ≃* ↥(twistedE6RootGroup F σ))
        (D : MulAut ↥K →* MulAut ↥(twistedE6RootGroup F σ)) (g : ModGL Tag.E6 (AlgebraicClosure F)),
        Function.Injective D ∧ (∀ b : ↥Bs, D (ggGamma K hN b) = ggBeta K θ hN b) ∧
        g ∈ adjointGroup Tag.E6 (AlgebraicClosure F) ∧
        g⁻¹ * twistE6 (AlgebraicClosure F) Fr g = TwistedDiag.n0 (AlgebraicClosure F) ∧
        (ggGamma K hN).range.map D = TwE6DD2.langCube le_rfl hF σ hσ Fr hFr g := by
  obtain ⟨hn7, hA6, -⟩ := p10h_twE6_full_adjoint hBs hcard hn hz hz1 hN hker hBstar hK
  obtain ⟨hperf, F, instF, instFin, σ, θ, hFcard, hσpow, hβI⟩ := p10real_unpack hN hK
  let eR := centerQuotEquivOfBot (exceptional_fixed_center_trivial TwistTag.E6 F σ)
  let θ' : ↥K ⧸ Subgroup.center ↥K ≃* ↥(twistedE6RootGroup F σ) := θ.trans eR
  obtain ⟨D, hDinj, hDγ⟩ := p10real_descent hN hperf θ'
  have hβθ : ∀ b : ↥Bs, ggBeta K θ' hN b = MulAut.congr eR (ggBeta K θ hN b) := by
    intro b
    refine MulEquiv.ext fun c => ?_
    obtain ⟨q, rfl⟩ := θ'.surjective c
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    have h1 := ggLAut_apply K θ' ⟨b, hN b.2⟩ l
    have h2 := ggLAut_apply K θ ⟨b, hN b.2⟩ l
    rw [MulAut.congr_apply]
    have e1 : eR.symm (θ' (l : ↥K ⧸ Subgroup.center ↥K)) = θ (l : ↥K ⧸ Subgroup.center ↥K) :=
      eR.symm_apply_apply _
    show ggBeta K θ' hN b (θ' (l : ↥K ⧸ Subgroup.center ↥K)) =
      eR ((ggBeta K θ hN b) (eR.symm (θ' (l : ↥K ⧸ Subgroup.center ↥K))))
    rw [e1]
    change ggLAut K θ' ⟨b, hN b.2⟩ (θ' (l : ↥K ⧸ Subgroup.center ↥K)) =
      eR (ggLAut K θ ⟨b, hN b.2⟩ (θ (l : ↥K ⧸ Subgroup.center ↥K)))
    rw [h1, h2]
    rfl
  have hSrange : (ggGamma K hN).range.map D ≤ (RecipeExcLang.twConj F σ).range := by
    rintro _ ⟨a, ⟨b, rfl⟩, rfl⟩
    rw [hDγ b, hβθ b]
    obtain ⟨w, hw⟩ := CFSG.LocalAnalysis.GLTheoremA.K155X.excTwE6_exists_twConj_of_mem_markID σ
      (hβI ⟨b, rfl⟩)
    exact ⟨w, hw.symm⟩
  have hSEA : IsElemAbelian 3 ((ggGamma K hN).range.map D) :=
    p10real_isElemAbelian_map D (p8dAct_isElemAbelian_range_ggGamma hBs hN)
  have hScard : Nat.card ((ggGamma K hN).range.map D) = 3 ^ 6 := by
    rw [Subgroup.card_map_of_injective hDinj]
    exact hA6
  have hF1 : Nat.card F = (2 ^ 1) ^ 2 := hFcard
  have hσ1 : ∀ c, σ c = c ^ 2 ^ 1 := hσpow
  haveI : CharP F 2 := charP_two_of_card (m := 2) (by rw [hF1]; norm_num)
  haveI : CharP (AlgebraicClosure F) 2 :=
    charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective 2
  haveI : ExpChar (AlgebraicClosure F) 2 := ExpChar.prime Nat.prime_two
  let Fr : AlgebraicClosure F →+* AlgebraicClosure F := iterateFrobenius (AlgebraicClosure F) 2 1
  have hFr : ∀ c, Fr c = c ^ 2 ^ 1 := fun _ => rfl
  obtain ⟨g, hg, hgn, hSlang⟩ := TwE6DD2.exists_eq_langCube (n := 1) le_rfl hF1 σ hσ1
    (by norm_num) Fr hFr hSEA hSrange hScard
  exact ⟨hn7, hperf, F, instF, instFin, σ, hF1, hσ1, Fr, hFr, θ', D, g, hDinj, hDγ, hg, hgn,
    hSlang⟩

theorem p10_twE6_realization
    {G : Type} [Group G] [Finite G] {Bs K : Subgroup G} {z : G}
    {n : ℕ} (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ n) (hn : 7 ≤ n) (hz : z ∈ Bs)
    (hz1 : z ≠ 1) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z)
    (hBstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hK : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twE6, 0, 1⟩) 3 Bs K) :
    ∃ e : ↥(ggGamma K hN).range ≃* Multiplicative (Fin TwistTag.E6.tag.rank → ZMod 3),
      ∀ α : MulAut ↥K, ∀ hα : α ∈ Subgroup.normalizer ((ggGamma K hN).range : Set (MulAut ↥K)),
        ∃ (w : WeylGroup TwistTag.E6.tag) (ε : ZMod 3), (ε = 1 ∨ ε = -1) ∧
          ∀ a : ↥(ggGamma K hN).range,
            Multiplicative.toAdd (e (ggConjAut (ggGamma K hN).range hα a)) =
              ε • TwE6NormThree.weylDual w (Multiplicative.toAdd (e a)) := by
  obtain ⟨-, -, F, instF, instFin, σ, hF, hσ, Fr, hFr, _, D, g, hDinj, -, hg, hgn, hS⟩ :=
    p10real_langCube hBs hcard hn hz hz1 hN hker hBstar hK
  haveI : CharP F 2 := charP_two_of_card (m := 2) (by rw [hF]; norm_num)
  haveI : CharP (AlgebraicClosure F) 2 :=
    charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective 2
  have hM := p10_twE6_model_realization hF σ hσ Fr hFr hg hgn
  have hS' : P10ModelReal ↥(twistedE6RootGroup F σ) ((ggGamma K hN).range.map D) := by
    rw [hS]
    exact hM
  exact p10real_transfer D hDinj _ hS'

end CFSG.StandardType.FrameRoute

end
