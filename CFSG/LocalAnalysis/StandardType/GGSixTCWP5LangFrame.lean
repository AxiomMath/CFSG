module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UStd
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UFrameO
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UE6
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Inputs2
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnLang
public import CFSG.LocalAnalysis.StandardType.GGTwInndiagRootBridge
import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRankFiveAmbient
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
public import CFSG.Quasithin.Background.E3Nprime
public import CFSG.Quasithin.Background.E3Uniq
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

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.Open
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.Blueprint.Chevalley (Tag TwistTag ModGL adjointGroup twistHom)

section LangFrame

private theorem w7L_exists_langDatum_of_toral_twisted_subgroup
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

theorem exists_langFrame_twE6
    {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ f) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {N : Type} [Group N] [Nontrivial N] (lam : N →* ↥(RecipeExcLang.twInndiagGroup K σ))
    (hlam : Function.Injective lam)
    (htor : ∃ g ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K), ∀ n : N,
      g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((lam n : ↥(RecipeExcLang.twInndiagGroup K σ)) : ModGL TwistTag.E6.tag K) * g ∈
        torusGroup TwistTag.E6.tag (AlgebraicClosure K)) :
    ∃ (S : LangSetup Tag.E6 (AlgebraicClosure K) 5)
      (ι : ↥(twistedE6RootGroup K σ) →* ModGL Tag.E6 (AlgebraicClosure K))
      (ν : N →* ModGL Tag.E6 (AlgebraicClosure K)),
      S.D.q = 2 ^ f ∧ Function.Injective ι ∧ ι.range = S.Γ ∧ Function.Injective ν ∧
      (∀ n, ν n ∈ S.D.torus) ∧
      ∀ (n : N) (c c' : ↥(twistedE6RootGroup K σ)),
        (c' : ModGL TwistTag.E6.tag K) =
          ((lam n : ↥(RecipeExcLang.twInndiagGroup K σ)) : ModGL TwistTag.E6.tag K) * c *
            ((lam n : ↥(RecipeExcLang.twInndiagGroup K σ)) : ModGL TwistTag.E6.tag K)⁻¹ →
        ι c' = ν n * ι c * (ν n)⁻¹ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  set L := AlgebraicClosure K with hLdef
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  set j : K →+* L := algebraMap K L with hj
  set A : Subgroup (ModGL TwistTag.E6.tag L) :=
    lam.range.map ((baseChangeGL j).comp (RecipeExcLang.twInndiagGroup K σ).subtype) with hA
  have hAfix : ∀ x ∈ A, twistHom TwistTag.E6 L (iterateFrobenius L 2 f) x = x := by
    intro x hx
    rw [hA, Subgroup.mem_map] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have hyI : (y : ModGL TwistTag.E6.tag K) ∈ twistedE6InndiagGL K σ :=
      CFSG.StandardType.NoOffTwE6Three.twInndiagGroup_le_twistedE6InndiagGL σ y.2
    have hF := (map_twistedE6InndiagGL_le_twistedFixedGroup Nat.prime_two hf hK σ hσ
      (iterateFrobenius L 2 f) (fun c => iterateFrobenius_def 2 f c)) ⟨y, hyI, hyx⟩
    exact hF.2
  have hAconj : ∃ g ∈ adjointGroup TwistTag.E6.tag L,
      ∀ x ∈ A, g⁻¹ * x * g ∈ torusGroup TwistTag.E6.tag L := by
    obtain ⟨g, hg, hgA⟩ := htor
    refine ⟨g, hg, fun x hx => ?_⟩
    rw [hA, Subgroup.mem_map] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    obtain ⟨n, rfl⟩ := hy
    rw [← hyx]
    exact hgA n
  obtain ⟨D, hDΦ, hDq, hDmem⟩ :=
    w7L_exists_langDatum_of_toral_twisted_subgroup (ℓ := 2) TwistTag.E6 f hf hAfix hAconj
  obtain ⟨ρ, hρ⟩ := frobeniusOnRoots_proved TwistTag.E6.tag L D
  have hFr : ∀ c : L, iterateFrobenius L 2 f c = c ^ 2 ^ f := fun c =>
    iterateFrobenius_def 2 f c
  have hfin : Finite D.model :=
    finite_model_twistedE6 Nat.prime_two hf hK hσ hFr D hDΦ
  have hqpow : IsPrimePow D.q ∧ ((D.q : ℕ) : L) = 0 := by
    rw [hDq]
    exact ⟨Nat.prime_two.isPrimePow.pow (by omega),
      (CharP.cast_eq_zero_iff L 2 (2 ^ f)).2 (dvd_pow_self 2 (by omega))⟩
  have hpq : ¬ 5 ∣ D.q := by
    rw [hDq]
    intro h
    exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_five Nat.prime_two).1
      (Nat.prime_five.dvd_of_dvd_pow h)) (by norm_num)
  let S : LangSetup TwistTag.E6.tag L 5 :=
    D.toSetup 5 ρ hρ Nat.prime_five (Or.inl le_rfl) hqpow hpq hfin
  let ι₀ : ↥(twistedE6RootGroup K σ) →* ModGL TwistTag.E6.tag L :=
    (baseChangeGL j).comp (twistedE6RootGroup K σ).subtype
  let ι : ↥(twistedE6RootGroup K σ) →* ModGL TwistTag.E6.tag L :=
    (MulAut.conj D.g0⁻¹).toMonoidHom.comp ι₀
  let ν : N →* ModGL TwistTag.E6.tag L :=
    (MulAut.conj D.g0⁻¹).toMonoidHom.comp
      ((baseChangeGL j).comp ((RecipeExcLang.twInndiagGroup K σ).subtype.comp lam))
  have hιinj : Function.Injective ι :=
    (MulAut.conj D.g0⁻¹).injective.comp
      ((baseChangeGL_injective j).comp (Subgroup.subtype_injective _))
  have hι₀range : ι₀.range = (twistedE6RootGroup K σ).map (baseChangeGL j) := by
    simp only [ι₀]
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hΓ : D.Γ = ι₀.range.map (MulAut.conj D.g0⁻¹).toMonoidHom := by
    rw [hι₀range, hj]
    exact Γ_eq_map_twistedE6RootGroup Nat.prime_two hf hK hσ hFr D hDΦ
  have hrange : ι.range = S.Γ := by
    show ι.range = D.Γ
    simp only [ι]
    rw [MonoidHom.range_comp]
    exact hΓ.symm
  have hνinj : Function.Injective ν :=
    (MulAut.conj D.g0⁻¹).injective.comp
      ((baseChangeGL_injective j).comp ((Subgroup.subtype_injective _).comp hlam))
  have hνmem : ∀ n, ν n ∈ S.D.torus := by
    intro n
    have hxA : baseChangeGL j
        ((lam n : ↥(RecipeExcLang.twInndiagGroup K σ)) : ModGL TwistTag.E6.tag K) ∈ A :=
      Subgroup.mem_map.mpr ⟨lam n, ⟨n, rfl⟩, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hDmem (baseChangeGL j ↑(lam n)) hxA
    have hνeq : ν n = D.g0⁻¹ * baseChangeGL j ↑(lam n) * D.g0 := by
      change (MulAut.conj D.g0⁻¹) (baseChangeGL j ↑(lam n)) =
        D.g0⁻¹ * baseChangeGL j ↑(lam n) * D.g0
      rw [MulAut.conj_apply, inv_inv]
    have hyeq : y = D.g0⁻¹ * baseChangeGL j ↑(lam n) * D.g0 := by
      have h1 := hyx
      change (MulAut.conj D.g0) y = baseChangeGL j ↑(lam n) at h1
      rw [MulAut.conj_apply] at h1
      calc y = D.g0⁻¹ * (D.g0 * y * D.g0⁻¹) * D.g0 := by group
        _ = D.g0⁻¹ * baseChangeGL j ↑(lam n) * D.g0 := by rw [h1]
    have hνy : ν n = y := by rw [hνeq, ← hyeq]
    rw [hνy]
    exact hy
  have hconjlaw : ∀ (n : N) (c c' : ↥(twistedE6RootGroup K σ)),
      (c' : ModGL TwistTag.E6.tag K) =
        ((lam n : ↥(RecipeExcLang.twInndiagGroup K σ)) : ModGL TwistTag.E6.tag K) * c *
          ((lam n : ↥(RecipeExcLang.twInndiagGroup K σ)) : ModGL TwistTag.E6.tag K)⁻¹ →
      ι c' = ν n * ι c * (ν n)⁻¹ := by
    intro n c c' hc
    have hιc : ∀ d : ↥(twistedE6RootGroup K σ),
        ι d = D.g0⁻¹ * baseChangeGL j (d : ModGL TwistTag.E6.tag K) * D.g0 := by
      intro d
      change (MulAut.conj D.g0⁻¹) (baseChangeGL j (d : ModGL TwistTag.E6.tag K)) =
        D.g0⁻¹ * baseChangeGL j (d : ModGL TwistTag.E6.tag K) * D.g0
      rw [MulAut.conj_apply, inv_inv]
    have hνn : ν n = D.g0⁻¹ * baseChangeGL j
        ((lam n : ↥(RecipeExcLang.twInndiagGroup K σ)) : ModGL TwistTag.E6.tag K) * D.g0 := by
      change (MulAut.conj D.g0⁻¹) (baseChangeGL j
        ((lam n : ↥(RecipeExcLang.twInndiagGroup K σ)) : ModGL TwistTag.E6.tag K)) =
        D.g0⁻¹ * baseChangeGL j
          ((lam n : ↥(RecipeExcLang.twInndiagGroup K σ)) : ModGL TwistTag.E6.tag K) * D.g0
      rw [MulAut.conj_apply, inv_inv]
    rw [hιc c', hιc c, hνn, hc]
    simp only [map_mul, map_inv]
    group
  exact ⟨S, ι, ν, hDq, hιinj, hrange, hνinj, hνmem, hconjlaw⟩

end LangFrame

end CFSG.StandardType.TableCRes

end
