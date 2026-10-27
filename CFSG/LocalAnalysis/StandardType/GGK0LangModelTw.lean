module

public import CFSG.LocalAnalysis.StandardType.GGK0LangModel
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTwE6Conj
import CFSG.LocalAnalysis.StandardType.GGLangUniform
import CFSG.LocalAnalysis.StandardType.GGL45NtExcBridgeTwE6
import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtTwE6
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcRoots
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwFrob
import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRankFiveAmbient
import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtUntw

public section

namespace CFSG.StandardType.GGK0MarkedKacIface1587

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.StandardType.GGFinModel CFSG.StandardType.RecipeExcLang
  CFSG.HardMathSupport.Timmesfeld.CrossChar

theorem exists_k0LangModel_tw
    {K : Type} [Field K] [Finite K] [Algebra K GGL] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    {w : WeylGroup TwistTag.E6.tag} {g : ModGL TwistTag.E6.tag GGL}
    (hg : g ∈ adjointGroup TwistTag.E6.tag GGL)
    (hgw : twistHom TwistTag.E6 GGL (ggFrobT n) g =
      g * canonicalRep (coxeterSystem TwistTag.E6.tag) GGL w) :
    ∃ (S : LangSetup TwistTag.E6.tag GGL 5)
      (iota : graphFixedRootGroup TwistTag.E6 K σ.toRingHom →* ModGL TwistTag.E6.tag GGL)
      (act : S.D.model →* MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
      (hmem : ∀ y : twInndiagGroup K σ,
        g⁻¹ * baseChangeGL (algebraMap K GGL) (y : ModGL TwistTag.E6.tag K) * g ∈ S.D.model),
      S.D.q = 2 ^ n ∧ (∀ x, S.D.Φ x = twistHom TwistTag.E6 GGL (ggFrobT n) x) ∧
      S.D.n = canonicalRep (coxeterSystem TwistTag.E6.tag) GGL w ∧
      Function.Injective iota ∧ iota.range = S.Γ ∧
      Function.Injective act ∧ Set.range (fun x => act x) = Set.range (twConj K σ) ∧
      (∀ x r, iota (act x r) =
        (x : ModGL TwistTag.E6.tag GGL) * iota r * (x : ModGL TwistTag.E6.tag GGL)⁻¹) ∧
      (∀ y, act ⟨_, hmem y⟩ = twConj K σ y) ∧
      ∀ γ, IsRoot TwistTag.E6.tag γ → S.ρ γ = w • permLattice TwistTag.E6.perm γ := by
  classical
  have : CharP K 2 := RingHom.charP (algebraMap K GGL) (algebraMap K GGL).injective 2
  have : IsAlgClosure K GGL := isAlgClosure_ggl K
  have hFrs : Function.Surjective (ggFrobT n) := (bijective_iterateFrobenius GGL 2 n).2
  let D : LangDatum TwistTag.E6.tag GGL :=
    LangDatum.ofTwist TwistTag.E6 (ggFrobT n) (2 ^ n) (ggFrobT_apply n) w hg hgw
  let ι₀ : graphFixedRootGroup TwistTag.E6 K σ.toRingHom →* ModGL TwistTag.E6.tag GGL :=
    (baseChangeGL (algebraMap K GGL)).comp (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subtype
  have hdesc : LangDescent D 7 ι₀ :=
    langDescent_twE6 (ℓ := 2) (f := n) Nat.prime_two hn hK σ hσ (ggFrobT_apply n) D rfl
      Nat.prime_seven (by norm_num)
  obtain ⟨S, ι, hSD, hιeq, hιinj, hιrange, -⟩ :=
    CFSG.StandardType.LangRat.exists_langSetup_of_toral_datum_uniform
      (τ := TwistTag.E6.tag) (L := GGL) (ℓ := 2) (f := n) Nat.prime_two hn D rfl Nat.prime_five
      (by norm_num) (Or.inl le_rfl) hdesc.finite_model ι₀
      ((baseChangeGL_injective (algebraMap K GGL)).comp (Subgroup.subtype_injective _))
      hdesc.Γ_eq
  have hq : S.D.q = 2 ^ n := by rw [hSD]; rfl
  have hΦf : S.D.Φ = twistHom TwistTag.E6 GGL (ggFrobT n) := by rw [hSD]; rfl
  have hΦ : ∀ x, S.D.Φ x = twistHom TwistTag.E6 GGL (ggFrobT n) x := fun x => by rw [hΦf]
  have hn' : S.D.n = canonicalRep (coxeterSystem TwistTag.E6.tag) GGL w := by rw [hSD]; rfl
  have hDg0 : D.g0 = g := rfl
  have hfix : D.fix = (twInndiagGroup K σ).map (baseChangeGL (algebraMap K GGL)) := by
    rw [← CFSG.HardMathSupport.C14ExcBridgeTwE6.twisted_fixed_eq_map hn hK σ hσ (ggFrobT n)
      (ggFrobT_apply n)]
    ext x
    rw [LangDatum.mem_fix]
    rfl
  have hmodel : ∀ x : ModGL TwistTag.E6.tag GGL, x ∈ S.D.model ↔ ∃ y : twInndiagGroup K σ,
      x = g⁻¹ * baseChangeGL (algebraMap K GGL) (y : ModGL TwistTag.E6.tag K) * g := by
    intro x
    rw [hSD, LangDescent.model_eq, hfix, Subgroup.map_map, hDg0]
    constructor
    · rintro ⟨y, hy, hxy⟩
      exact ⟨⟨y, hy⟩, by simpa [MulAut.conj_apply] using hxy.symm⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, y.2, by simp⟩
  have hρ : ∀ γ, IsRoot TwistTag.E6.tag γ → S.ρ γ = w • permLattice TwistTag.E6.perm γ := by
    intro γ hγ
    have hst : S.D.step =
        twFrob TwistTag.E6 (canonicalRep (coxeterSystem TwistTag.E6.tag) GGL w) (ggFrobT n) := by
      ext1 x
      change S.D.n * S.D.Φ x * S.D.n⁻¹ = canonicalRep (coxeterSystem TwistTag.E6.tag) GGL w *
        twistHom TwistTag.E6 GGL (ggFrobT n) x *
          (canonicalRep (coxeterSystem TwistTag.E6.tag) GGL w)⁻¹
      rw [hΦ, hn']
    have h2 := map_twFrob_rootSubgroup TwistTag.E6 hFrs w hγ
    have h3 : rootSubgroup TwistTag.E6.tag GGL (S.ρ γ) =
        rootSubgroup TwistTag.E6.tag GGL (w • permLattice TwistTag.E6.perm γ) := by
      rw [← S.frob.map_rootSubgroup γ hγ, hst]
      exact h2
    have hr : IsRoot TwistTag.E6.tag (w • permLattice TwistTag.E6.perm γ) :=
      IsRoot.smul (hγ.permLattice TwistTag.E6.cartan_perm) w
    exact eq_of_rootSubgroup_eq ((S.frob.isRoot_iff γ).2 hγ) hr h3
  obtain ⟨act, hmem, hactinj, hactrange, hactcompat, hacteq⟩ :=
    exists_langModel_action_of S (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subtype
      (twConj K σ) (NoOffTwE6Three.twConj_injective hn hK σ hσ) (fun y r => coe_twConj σ y r) ι
      hmodel hιeq
  exact ⟨S, ι, act, hmem, hq, hΦ, hn', hιinj, hιrange, hactinj, hactrange, hactcompat, hacteq,
    hρ⟩

end CFSG.StandardType.GGK0MarkedKacIface1587

end
