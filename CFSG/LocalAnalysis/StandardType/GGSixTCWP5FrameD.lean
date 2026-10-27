module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UE6
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Inputs2
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5Act
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnLang
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Defs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwCoreAssembly
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnLine
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24Plane
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24Red
public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltMain
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Certs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang.TwE6
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Down
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
public import CFSG.LieType.SeitzGeneration.SeitzStatus
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A3A3Perm
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Statements
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyU3Top
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCTFieldCenter
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotClassesRoots
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotMainSetup
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotSwapCoverConj
public import CFSG.Quasithin.Background.A3Structure314Defs
public import CFSG.Quasithin.Background.C1PackS15212C
public import CFSG.Quasithin.Background.C1PackS1531Top
public import CFSG.Quasithin.Background.E3
public import CFSG.Quasithin.Background.F918H5
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
public import CFSG.Quasithin.Background.GoldschmidtS146RBend1
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructFieldExt
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructPGL
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructSimple
public import CFSG.Quasithin.EmptyFaithful.S14610Q1
public import CFSG.Quasithin.EmptyFaithful.S14610Top
public import CFSG.Quasithin.EmptyFaithful.S146F4
public import CFSG.Quasithin.EmptyFaithful.S152UGen
public import CFSG.Quasithin.EmptyFaithful.S152Y15
public import CFSG.Quasithin.EmptyFaithful.S152Y19
public import CFSG.Quasithin.EmptyFaithful.S153E59A
public import CFSG.Quasithin.EmptyFaithful.T1531Final
public import CFSG.Quasithin.Recognition.ModelBridges
public import CFSG.Quasithin.Vol2.Ch10SecB4
public import CFSG.Quasithin.Vol2.Ch1EightFourChar2
public import CFSG.Quasithin.Vol2.Ch3Sec3InspF618Tools
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3315R
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3323B
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3324X
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcTw

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Assembly CFSG.Blueprint CFSG.StandardType CFSG.Open CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.Blueprint.Chevalley (Tag TwistTag ModGL adjointGroup IsRoot permLattice twistHom
  entrywiseHom diagramMap rootSubgroup)

section FrameD

variable {X : Type} [Group X] {G₀ B : Subgroup X} {f : ℕ}

theorem w5F_rho_eq_smul {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup Tag.E6 L p) {Fr : L →+* L}
    (hΦ : ∀ g, S.D.Φ g = e6Diagram L * Units.map (entrywiseHom Fr) g * (e6Diagram L)⁻¹)
    {w : WeylGroup Tag.E6} (hn : S.D.n = canonicalRep (coxeterSystem Tag.E6) L w)
    (hFrs : Function.Surjective Fr) :
    ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = w • permLattice e6Graph γ := by
  intro γ hγ
  have hst : S.D.step = twFrob TwistTag.E6 (canonicalRep (coxeterSystem TwistTag.E6.tag) L w)
      Fr := by
    ext1 g
    change S.D.n * S.D.Φ g * S.D.n⁻¹ = canonicalRep (coxeterSystem Tag.E6) L w *
      (e6Diagram L * Units.map (entrywiseHom Fr) g * (e6Diagram L)⁻¹) *
        (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹
    rw [hΦ, hn]
  have h2 := map_twFrob_rootSubgroup TwistTag.E6 hFrs w hγ
  have h3 : rootSubgroup Tag.E6 L (S.ρ γ) =
      rootSubgroup Tag.E6 L (w • permLattice e6Graph γ) := by
    rw [← S.frob.map_rootSubgroup γ hγ, hst]
    exact h2
  have hr : IsRoot Tag.E6 (w • permLattice e6Graph γ) :=
    IsRoot.smul (hγ.permLattice e6Graph_cartan) w
  exact eq_of_rootSubgroup_eq ((S.frob.isRoot_iff γ).2 hγ) hr h3


private theorem w5F_exists_langDatum_of_toral_twisted_subgroup
    (t : TwistTag) {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime]
    [CharP L ℓ] (f : ℕ) (hf : 1 ≤ f) {A : Subgroup (ModGL t.tag L)}
    (hfix : ∀ x ∈ A, twistHom t L (iterateFrobenius L ℓ f) x = x)
    (hconj : ∃ g ∈ adjointGroup t.tag L, ∀ x ∈ A, g⁻¹ * x * g ∈ torusGroup t.tag L) :
    ∃ D : LangDatum t.tag L, D.Φ = twistHom t L (iterateFrobenius L ℓ f) ∧
      D.q = ℓ ^ f ∧ ∀ x ∈ A, x ∈ D.torus.map (MulAut.conj D.g0).toMonoidHom := by
  obtain ⟨g, hg, hgu⟩ := hconj
  obtain ⟨w, g0, hg0, hF, hmem⟩ :=
    exists_lang_torus_of_conj_torus_twisted ℓ t f hf hfix hg hgu
  exact ⟨LangDatum.ofTwist t (iterateFrobenius L ℓ f) (ℓ ^ f)
    (iterateFrobenius_def ℓ f) w hg0 hF, rfl, rfl, hmem⟩

theorem exists_frameO_twE6_sub
    (hf : 1 ≤ f) (act : TwE6Act G₀ B hf) {D : Subgroup X} (hDB : D ≤ B)
    (htor : ∃ g ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure (GaloisField 2 (2 * f))),
      ∀ d : ↥D, g⁻¹ * baseChangeGL
          (algebraMap (GaloisField 2 (2 * f)) (AlgebraicClosure (GaloisField 2 (2 * f))))
          ((act.lam ⟨d, hDB d.2⟩ : ↥(RecipeExcLang.twInndiagGroup (GaloisField 2 (2 * f))
            (frobQEquiv hf))) : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) * g ∈
        torusGroup TwistTag.E6.tag (AlgebraicClosure (GaloisField 2 (2 * f)))) :
    ∃ S : LangSetup Tag.E6 (AlgebraicClosure (GaloisField 2 (2 * f))) 5, S.D.q = 2 ^ f ∧
      (∃ w : WeylGroup Tag.E6, ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = w • permLattice e6Graph γ) ∧
      ∃ fr : GGTCUFrameO G₀ B (ModGL Tag.E6 (AlgebraicClosure (GaloisField 2 (2 * f)))),
        fr.Θ.range = S.Γ ∧ fr.BimgO ≤ S.D.model ∧ fr.DimgO D ≤ S.D.torus ∧
        ∃ g₀ ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure (GaloisField 2 (2 * f))),
          ∀ b : ↥B,
          fr.ν b = g₀⁻¹ * baseChangeGL
            (algebraMap (GaloisField 2 (2 * f)) (AlgebraicClosure (GaloisField 2 (2 * f))))
            ((act.lam b : ↥(RecipeExcLang.twInndiagGroup (GaloisField 2 (2 * f))
              (frobQEquiv hf))) : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) * g₀ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := GaloisField 2 (2 * f) with hKdef
  have : Fintype K := Fintype.ofFinite K
  have hK : Nat.card K = (2 ^ f) ^ 2 := by
    rw [hKdef]
    exact CFSG.LieType.Universal.card_galoisField_two_mul 2 f hf
  set L := AlgebraicClosure K with hLdef
  let σ : K ≃+* K := frobQEquiv hf
  have hσ : ∀ c : K, σ c = c ^ 2 ^ f := fun c =>
    CFSG.LieType.Steinberg.Exceptional.frobQ_apply 2 f c
  have : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  set j : K →+* L := algebraMap K L with hj
  let φ : ↥B →* ModGL TwistTag.E6.tag L :=
    (baseChangeGL j).comp ((RecipeExcLang.twInndiagGroup K σ).subtype.comp act.lam)
  set A : Subgroup (ModGL TwistTag.E6.tag L) := (D.subgroupOf B).map φ with hA
  have hfixed_all : ∀ y : ↥(RecipeExcLang.twInndiagGroup K σ),
      baseChangeGL j (y : ModGL TwistTag.E6.tag K) ∈
        twistedFixedGroup TwistTag.E6 L (iterateFrobenius L 2 f) := by
    intro y
    have hyI : (y : ModGL TwistTag.E6.tag K) ∈ twistedE6InndiagGL K σ :=
      CFSG.StandardType.NoOffTwE6Three.twInndiagGroup_le_twistedE6InndiagGL σ y.2
    have hF := map_twistedE6InndiagGL_le_twistedFixedGroup Nat.prime_two hf hK σ hσ
      (iterateFrobenius L 2 f) (fun c => iterateFrobenius_def 2 f c)
    exact hF (Subgroup.mem_map.mpr ⟨(y : ModGL TwistTag.E6.tag K), hyI, rfl⟩)
  have hAfix : ∀ x ∈ A, twistHom TwistTag.E6 L (iterateFrobenius L 2 f) x = x := by
    intro x hx
    rw [hA, Subgroup.mem_map] at hx
    obtain ⟨b, _hb, hbx⟩ := hx
    rw [← hbx]
    exact (hfixed_all (act.lam b)).2
  have hAconj : ∃ g ∈ adjointGroup TwistTag.E6.tag L,
      ∀ x ∈ A, g⁻¹ * x * g ∈ torusGroup TwistTag.E6.tag L := by
    obtain ⟨g, hg, hgD⟩ := htor
    refine ⟨g, hg, fun x hx => ?_⟩
    rw [hA, Subgroup.mem_map] at hx
    obtain ⟨b, hb, hbx⟩ := hx
    have hbD : (b : X) ∈ D := Subgroup.mem_subgroupOf.mp hb
    have hbb : (⟨(b : X), hDB hbD⟩ : ↥B) = b := Subtype.ext rfl
    have hg1 := hgD ⟨(b : X), hbD⟩
    rw [hbb] at hg1
    rw [← hbx]
    exact hg1
  obtain ⟨Dd, hDΦ, hDq, hDmem⟩ :=
    w5F_exists_langDatum_of_toral_twisted_subgroup (ℓ := 2) TwistTag.E6 f hf hAfix hAconj
  obtain ⟨ρ, hρ⟩ := frobeniusOnRoots_proved TwistTag.E6.tag L Dd
  have hFr : ∀ c : L, iterateFrobenius L 2 f c = c ^ 2 ^ f := fun c =>
    iterateFrobenius_def 2 f c
  have hfin : Finite Dd.model :=
    finite_model_twistedE6 Nat.prime_two hf hK hσ hFr Dd hDΦ
  have hqpow : IsPrimePow Dd.q ∧ ((Dd.q : ℕ) : L) = 0 := by
    rw [hDq]
    exact ⟨Nat.prime_two.isPrimePow.pow (by omega),
      (CharP.cast_eq_zero_iff L 2 (2 ^ f)).2 (dvd_pow_self 2 (by omega))⟩
  have hpq : ¬ 5 ∣ Dd.q := by
    rw [hDq]
    intro h
    exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_five Nat.prime_two).1
      (Nat.prime_five.dvd_of_dvd_pow h)) (by norm_num)
  let S : LangSetup TwistTag.E6.tag L 5 :=
    Dd.toSetup 5 ρ hρ Nat.prime_five (Or.inl le_rfl) hqpow hpq hfin
  have hΦ : ∀ g : ModGL TwistTag.E6.tag L, S.D.Φ g =
      diagramMap TwistTag.E6 L * Units.map (entrywiseHom (iterateFrobenius L 2 f)) g *
        (diagramMap TwistTag.E6 L)⁻¹ := by
    intro g
    change Dd.Φ g = diagramMap TwistTag.E6 L *
      Units.map (entrywiseHom (iterateFrobenius L 2 f)) g * (diagramMap TwistTag.E6 L)⁻¹
    rw [hDΦ, twistHom_apply]
  have hFrs : Function.Surjective (iterateFrobenius L 2 f) := fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (n := 2 ^ f) (by positivity)
    exact ⟨x, by rw [iterateFrobenius_def]; exact hx⟩
  obtain ⟨w, hw⟩ : ∃ w : WeylGroup Tag.E6,
      ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = w • permLattice e6Graph γ := by
    obtain ⟨w, hn⟩ := S.D.n_weyl
    exact ⟨w, w5F_rho_eq_smul S hΦ hn hFrs⟩
  let ι₀ : ↥(twistedE6RootGroup K σ) →* ModGL TwistTag.E6.tag L :=
    (baseChangeGL j).comp (twistedE6RootGroup K σ).subtype
  let ι : ↥(twistedE6RootGroup K σ) →* ModGL TwistTag.E6.tag L :=
    (MulAut.conj Dd.g0⁻¹).toMonoidHom.comp ι₀
  let ν : ↥B →* ModGL TwistTag.E6.tag L := (MulAut.conj Dd.g0⁻¹).toMonoidHom.comp φ
  have hιinj : Function.Injective ι :=
    (MulAut.conj Dd.g0⁻¹).injective.comp
      ((baseChangeGL_injective j).comp (Subgroup.subtype_injective _))
  have hνinj : Function.Injective ν :=
    (MulAut.conj Dd.g0⁻¹).injective.comp
      ((baseChangeGL_injective j).comp ((Subgroup.subtype_injective _).comp act.lam_inj))
  have hι₀range : ι₀.range = (twistedE6RootGroup K σ).map (baseChangeGL j) := by
    simp only [ι₀]
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hΓ : Dd.Γ = ι₀.range.map (MulAut.conj Dd.g0⁻¹).toMonoidHom := by
    rw [hι₀range, hj]
    exact Γ_eq_map_twistedE6RootGroup Nat.prime_two hf hK hσ hFr Dd hDΦ
  have hrange : ι.range = S.Γ := by
    show ι.range = Dd.Γ
    simp only [ι]
    rw [MonoidHom.range_comp]
    exact hΓ.symm
  have hΘrange : (ι.comp act.θ.toMonoidHom).range = S.Γ := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 act.θ.surjective, Subgroup.map_top,
      hrange]
  have hconjlaw : ∀ (b : ↥B) (c c' : ↥(twistedE6RootGroup K σ)),
      (c' : ModGL TwistTag.E6.tag K) =
        (act.lam b : ModGL TwistTag.E6.tag K) * c *
          (act.lam b : ModGL TwistTag.E6.tag K)⁻¹ →
      ι c' = ν b * ι c * (ν b)⁻¹ := by
    intro b c c' hc
    have hιc : ∀ d : ↥(twistedE6RootGroup K σ),
        ι d = Dd.g0⁻¹ * baseChangeGL j (d : ModGL TwistTag.E6.tag K) * Dd.g0 := by
      intro d
      change (MulAut.conj Dd.g0⁻¹) (baseChangeGL j (d : ModGL TwistTag.E6.tag K)) =
        Dd.g0⁻¹ * baseChangeGL j (d : ModGL TwistTag.E6.tag K) * Dd.g0
      rw [MulAut.conj_apply, inv_inv]
    have hνb : ν b = Dd.g0⁻¹ * baseChangeGL j (act.lam b : ModGL TwistTag.E6.tag K) *
        Dd.g0 := by
      change (MulAut.conj Dd.g0⁻¹) (baseChangeGL j
        (act.lam b : ModGL TwistTag.E6.tag K)) = _
      rw [MulAut.conj_apply, inv_inv]
    rw [hιc c', hιc c, hνb, hc]
    simp only [map_mul, map_inv]
    group
  have hBimg : ν.range ≤ Dd.model := by
    rintro _ ⟨b, rfl⟩
    have hmem := hfixed_all (act.lam b)
    rw [model_eq_map_twistedFixedGroup Dd hDΦ]
    exact Subgroup.mem_map.mpr
      ⟨baseChangeGL j (act.lam b : ModGL TwistTag.E6.tag K), hmem, rfl⟩
  have hDimg : (D.subgroupOf B).map ν ≤ Dd.torus := by
    rintro _ ⟨b, hb, rfl⟩
    have hxA : φ b ∈ A := by
      rw [hA]
      exact Subgroup.mem_map.mpr ⟨b, hb, rfl⟩
    have hmem := hDmem (φ b) hxA
    rw [Subgroup.mem_map] at hmem
    obtain ⟨y, hy, hyx⟩ := hmem
    have hνy : ν b = y := by
      change (MulAut.conj Dd.g0⁻¹) (φ b) = y
      rw [← hyx]
      change (MulAut.conj Dd.g0⁻¹) ((MulAut.conj Dd.g0) y) = y
      rw [MulAut.conj_apply, MulAut.conj_apply, inv_inv]
      group
    rw [hνy]
    exact hy
  refine ⟨S, hDq, ⟨w, hw⟩, ?_⟩
  refine ⟨⟨ι.comp act.θ.toMonoidHom, hιinj.comp act.θ.injective, ν, hνinj, ?_⟩,
    hΘrange, hBimg, hDimg, Dd.g0, Dd.g0_mem, ?_⟩
  · intro b y y' hy'
    exact hconjlaw b (act.θ (QuotientGroup.mk y)) (act.θ (QuotientGroup.mk y'))
      (act.act b y y' hy')
  · intro b
    change (MulAut.conj Dd.g0⁻¹) (baseChangeGL j
      (act.lam b : ModGL TwistTag.E6.tag K)) =
      Dd.g0⁻¹ * baseChangeGL j (act.lam b : ModGL TwistTag.E6.tag K) * Dd.g0
    rw [MulAut.conj_apply, inv_inv]

end FrameD

end CFSG.StandardType.TableCRes

end
