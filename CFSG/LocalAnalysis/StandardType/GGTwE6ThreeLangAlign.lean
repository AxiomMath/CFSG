module

public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRootGenFrame
public import CFSG.LocalAnalysis.StandardType.GGTBE6IndTwistWeyl
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTwE6Lang
import CFSG.LieType.Chevalley.DiagramCoordinateFixedStructure
import CFSG.LieType.Chevalley.OddDiagramFrobeniusFixedDerived
import CFSG.LieType.Chevalley.CLSOddE7RationalDerivedIndex
import CFSG.LieType.Chevalley.CoordinateFieldBaseChange

public noncomputable section

namespace CFSG.StandardType.TwE6ThreeLang

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.TwistedE6 CFSG.StandardType.TwE6Lang CFSG.StandardType.TBE6IndTwist
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.TableBExc.E6Three

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


theorem frameLongest_eq_twE6W0 : frameLongest = CFSG.HardMathSupport.Lang.E6Descent.twE6W0 := by
  refine ext_single fun i => ?_
  have h := frameLongest_rho (rho (Pi.single i 1 : Fin Tag.E6.rank → ℤ))
  rw [rho_rho] at h
  rw [h, CFSG.HardMathSupport.Lang.E6Descent.twE6W0_smul]
  rfl

@[expose] def langIso {K : Type} [Field K] [Finite K] (σ : K ≃+* K) (l : K) :
    ModGL TwistTag.E6.tag K :=
  (e6Isogeny K (langG K σ.toRingHom l) : ModGL .E6 K)

theorem langIso_mem_adjointGroup {K : Type} [Field K] [Finite K] (σ : K ≃+* K) (l : K) :
    langIso σ l ∈ adjointGroup TwistTag.E6.tag K :=
  (e6Isogeny K (langG K σ.toRingHom l)).2

theorem twistHom_langIso {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)
    (hσ2 : ∀ c, σ.toRingHom (σ.toRingHom c) = c) {l : K} (hl : σ.toRingHom l = l + 1) :
    twistHom TwistTag.E6 K σ.toRingHom (langIso σ l) =
      langIso σ l * canonicalRep (coxeterSystem TwistTag.E6.tag) K
        CFSG.HardMathSupport.Lang.E6Descent.twE6W0 := by
  have hln : σ.toRingHom l ≠ l := by rw [hl]; exact add_ne_left.mpr one_ne_zero
  have hd : negDelta σ.toRingHom hln = 1 := by
    apply Units.ext
    change -(l - σ.toRingHom l) = (1 : K)
    rw [hl]
    ring
  have hs : sigma K σ.toRingHom (langG K σ.toRingHom l) =
      langG K σ.toRingHom l * weylHom K frameLongest := by
    rw [sigma_langG σ.toRingHom hσ2 hln, hd, langMM_one]
  have h1 : twistHom TwistTag.E6 K σ.toRingHom (langIso σ l) =
      (e6Isogeny K (sigma K σ.toRingHom (langG K σ.toRingHom l)) : ModGL .E6 K) := by
    rw [e6Isogeny_sigma]
    rfl
  rw [h1, hs, map_mul, Subgroup.coe_mul, weylHom_isogeny, frameLongest_eq_twE6W0]
  rfl

theorem exists_twInndiag_mul_eq {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ n)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ 2 ^ n) {l : K}
    (hl : σ.toRingHom l = l + 1) {g : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (hg : g ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hgF : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g =
      g * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K)
        CFSG.HardMathSupport.Lang.E6Descent.twE6W0) :
    ∃ r ∈ RecipeExcLang.twInndiagGroup K σ,
      baseChangeGL (algebraMap K (AlgebraicClosure K)) r *
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (langIso σ l) = g := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * n)
    (by rw [Fintype.card_eq_nat_card, hK, ← pow_mul, mul_comm])
  let ι := algebraMap K (AlgebraicClosure K)
  have hσ2 : ∀ c, σ.toRingHom (σ.toRingHom c) = c := by
    intro c
    change σ (σ c) = c
    rw [hσ, hσ, ← pow_mul, ← sq, ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hcomm : ι.comp σ.toRingHom = Fr.comp ι := by
    ext c
    change ι (σ c) = Fr (ι c)
    rw [hσ, hFr, map_pow]
  have hG : twistHom TwistTag.E6 (AlgebraicClosure K) Fr (baseChangeGL ι (langIso σ l)) =
      baseChangeGL ι (langIso σ l) * canonicalRep (coxeterSystem TwistTag.E6.tag)
        (AlgebraicClosure K) CFSG.HardMathSupport.Lang.E6Descent.twE6W0 := by
    rw [twistHom_baseChangeGL ι hcomm, twistHom_langIso σ hσ2 hl, map_mul,
      baseChangeGL_canonicalRep (τ := TwistTag.E6.tag) ι
        CFSG.HardMathSupport.Lang.E6Descent.twE6W0]
  have hadj : baseChangeGL ι (langIso σ l) ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) := by
    have hle : (adjointGroup TwistTag.E6.tag K).map (baseChangeGL ι) ≤
        adjointGroup TwistTag.E6.tag (AlgebraicClosure K) := by
      rw [map_baseChangeGL_adjointGroup, Subgroup.closure_le]
      rintro _ ⟨i, c, rfl | rfl⟩
      exacts [xUnit_mem_adjointGroup i _, yUnit_mem_adjointGroup i _]
    exact hle ⟨_, langIso_mem_adjointGroup σ l, rfl⟩
  have hr : g * (baseChangeGL ι (langIso σ l))⁻¹ ∈
      adjointGroup TwistTag.E6.tag (AlgebraicClosure K) :=
    mul_mem hg (inv_mem hadj)
  have hrF : twistHom TwistTag.E6 (AlgebraicClosure K) Fr (g * (baseChangeGL ι (langIso σ l))⁻¹) =
      g * (baseChangeGL ι (langIso σ l))⁻¹ := by
    rw [map_mul, map_inv, hgF, hG]
    group
  obtain ⟨r, hr, hre⟩ := RecipeExcLang.exists_mem_twInndiag_of_twist_fixed hn hK hσ hFr hr hrF
  refine ⟨r, hr, ?_⟩
  change baseChangeGL ι r * baseChangeGL ι (langIso σ l) = g
  rw [hre]
  group

@[expose] def langFrameMat {K : Type} [Field K] [Finite K] (σ : K ≃+* K) (l : K) (ζ : Kˣ) (hζ : ζ ^ 3 = 1)
    (x : Fin 6 → ZMod 3) : ModGL TwistTag.E6.tag K :=
  langIso σ l * rootDiagUnit TwistTag.E6.tag (zetaVec (τ := Tag.E6) ζ hζ x) * (langIso σ l)⁻¹

theorem exists_aligned_three {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (h3 : 3 ∣ 2 ^ n + 1) {l : K} (hl : σ.toRingHom l = l + 1) {ζ : Kˣ} (hζ : ζ ^ 3 = 1)
    (hζo : orderOf ζ = 3) {L' : Type} [Group L'] [Finite L']
    {ψ₀ : L' →* ↥(twistedE6RootGroup K σ)} (hψ₀ : Function.Surjective ψ₀)
    (hker : ψ₀.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian 3 A)
    (hAH : ∀ a ∈ A, ∃ φ ∈ (RecipeExcLang.twConj K σ).range, ∀ l, φ (ψ₀ l) = ψ₀ (a l))
    (h5 : 3 ^ 5 ≤ Nat.card A) (hsc : GGTorusSelfCent 3 A) :
    ∃ (r : ↥(RecipeExcLang.twInndiagGroup K σ)) (κ : A →* Multiplicative (Fin 6 → ZMod 3)),
      Function.Injective κ ∧
      (κ.range = ⊤ ∨ ∀ x, Multiplicative.ofAdd x ∈ κ.range ↔ x ∈ NoOffRest.hypE6) ∧
      ∀ (a : A) (y : L'),
        ((RecipeExcLang.twConj K σ r⁻¹ (ψ₀ ((a : MulAut L') y)) : ↥(twistedE6RootGroup K σ)) :
            ModGL TwistTag.E6.tag K) =
          langFrameMat σ l ζ hζ (Multiplicative.toAdd (κ a)) *
            ((RecipeExcLang.twConj K σ r⁻¹ (ψ₀ y) : ↥(twistedE6RootGroup K σ)) :
              ModGL TwistTag.E6.tag K) *
            (langFrameMat σ l ζ hζ (Multiplicative.toAdd (κ a)))⁻¹ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * n)
    (by rw [Fintype.card_eq_nat_card, hK, ← pow_mul, mul_comm])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  let Fr : AlgebraicClosure K →+* AlgebraicClosure K := iterateFrobenius (AlgebraicClosure K) 2 n
  have hFr : ∀ c, Fr c = c ^ 2 ^ n := fun c =>
    iterateFrobenius_def (R := AlgebraicClosure K) (p := 2) (n := n) (x := c)
  let ζΩ : (AlgebraicClosure K)ˣ := Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom ζ
  have hζΩ : ζΩ ^ 3 = 1 := by
    change Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom ζ ^ 3 = 1
    rw [← map_pow, hζ, map_one]
  have hζΩo : orderOf ζΩ = 3 := by
    rw [← hζo]
    exact orderOf_injective (Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom) (Units.map_injective (algebraMap K (AlgebraicClosure K)).injective) ζ
  obtain ⟨g, κ, t, -, hg, hgF, hκinj, hκrange, ht, hconj, -⟩ :=
    TwE6ThreeRootGen.exists_frame_torus hn hK σ hσ h3 hFr hζΩ hζΩo hψ₀ hker hperf hA hAH h5 hsc
  obtain ⟨r, hr, hrg⟩ := exists_twInndiag_mul_eq hn hK hσ hFr hl hg hgF
  have hbc : ∀ x : Fin 6 → ZMod 3,
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (rootDiagUnit TwistTag.E6.tag (zetaVec (τ := Tag.E6) ζ hζ x)) =
        rootDiagUnit TwistTag.E6.tag (zetaVec (τ := Tag.E6) ζΩ hζΩ x) := by
    intro x
    rw [baseChangeGL_rootDiagUnit (τ := TwistTag.E6.tag) (algebraMap K (AlgebraicClosure K)) (zetaVec (τ := Tag.E6) ζ hζ x)]
    congr 1
    funext i
    exact map_pow (Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom) ζ (x i).val
  have htx : ∀ x, t x = r * langFrameMat σ l ζ hζ x * r⁻¹ := by
    intro x
    apply baseChangeGL_injective (algebraMap K (AlgebraicClosure K))
    rw [ht x, ← hrg, langFrameMat, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, hbc]
    group
  refine ⟨⟨r, hr⟩, κ, hκinj, hκrange, fun a y => ?_⟩
  rw [RecipeExcLang.coe_twConj, RecipeExcLang.coe_twConj, hconj, htx]
  simp only [Subgroup.coe_inv]
  group

end CFSG.StandardType.TwE6ThreeLang

end
