module

public import CFSG.Assembly.Defs
public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveF4
public import Certificates.Certificate3007
public import Certificates.Certificate10005
import CFSG.Quasithin.Background.SL3SmallNat
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Basic
import CFSG.LocalAnalysis.StandardType.GGSixE6TwoSL3Section
import CFSG.LocalAnalysis.StandardType.GGSixE6TwoSchur
public import CFSG.Certificates.CosetTableShort
public import CFSG.LieType.Multipliers.ProductKernel
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldNaturalAction
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57SL
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57Sp4
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftSaturate
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesAlt5Split
import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalFamily
import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearStrong
import CFSG.Quasithin.Background.A3Structure312Iso
import CFSG.Quasithin.Background.FFC4Pair
import CFSG.Quasithin.Background.FFC4Tr2
import CFSG.Quasithin.Background.SmithB42L2L32
import CFSG.Quasithin.Background.SmithB42L2Nat
import CFSG.Quasithin.Background.SmithB42SL3Aut
import CFSG.Quasithin.Background.SmithB42SL3Base
import CFSG.Quasithin.Background.SmithB51LnRealB
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.StandardType.GGSixE6Two

open CFSG.Blueprint CFSG.StandardType.GGHalf Matrix

section Core

theorem sl3_four_core {G : Type} [Group G] [Finite G] (hq : CFSG.Assembly.IsQuasisimple G)
    (hP : LieModel (G ⧸ Subgroup.center G) .PSL 3 2 2)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) G V) (hρ : Function.Injective ρ)
    (hdim : Module.finrank (ZMod 2) V = 6) :
    ∃ (θ : Matrix.SpecialLinearGroup (Fin 3) F4 ≃* G) (E : V ≃+ (Fin 3 → F4)), ∀ g v,
      E (ρ (θ g) v) =
        ((g : Matrix.SpecialLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) *ᵥ E v := by
  classical
  have hnt : ∃ g v, ρ g v ≠ v := by
    obtain ⟨x, y, hxy⟩ := hq.2.exists_pair_ne
    obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) x
    obtain ⟨b, hb⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) y
    have hgne : a * b⁻¹ ≠ 1 := by
      intro h
      apply hxy
      have hab : a = b := by
        calc a = a * b⁻¹ * b := by group
          _ = 1 * b := by rw [h]
          _ = b := by rw [one_mul]
      have hqab : (a : G ⧸ Subgroup.center G) = (b : G ⧸ Subgroup.center G) := by rw [hab]
      exact ha.symm.trans (hqab.trans hb)
    have hρg : ρ (a * b⁻¹) ≠ 1 := by
      intro h
      exact hgne (hρ (by rw [h, map_one]))
    have h : ¬ ∀ v, ρ (a * b⁻¹) v = v := by
      intro hall
      exact hρg (LinearMap.ext fun v => by simpa using hall v)
    push Not at h
    exact ⟨a * b⁻¹, h⟩
  obtain ⟨U, U', hUU', hU'inv, hUtriv, hmax, g₀, v₀, hv₀, hg₀v₀⟩ :=
    CFSG.Quasithin.SL3Small.exists_section hq.1 hnt
  have hUinv : ∀ g, ∀ u ∈ U, ρ g u ∈ U := fun g u hu => by rw [hUtriv g u hu]; exact hu
  let W := ↥U' ⧸ U.comap U'.subtype
  let σ : Representation (ZMod 2) G W := CFSG.Quasithin.SL3Small.sectRep ρ hU'inv hUinv
  have hσmk : ∀ g (w : ↥U'), σ g (Submodule.Quotient.mk w) =
      Submodule.Quotient.mk (CFSG.Quasithin.SL3Small.resRep ρ hU'inv g w) :=
    fun g w => CFSG.Quasithin.SL3Small.sectRep_mk ρ hU'inv hUinv g w
  have hirr : σ.IsIrreducible :=
    CFSG.Quasithin.SL3Small.sectRep_isIrreducible ρ hU'inv hUinv hUU' hmax
  have hσg0ne : σ g₀ ≠ 1 := by
    intro h1
    apply hg₀v₀
    have hfix : σ g₀ (Submodule.Quotient.mk ⟨v₀, hv₀⟩) =
        Submodule.Quotient.mk ⟨v₀, hv₀⟩ := by rw [h1, Module.End.one_apply]
    have hmem : CFSG.Quasithin.SL3Small.resRep ρ hU'inv g₀ ⟨v₀, hv₀⟩ -
        (⟨v₀, hv₀⟩ : ↥U') ∈ U.comap U'.subtype := by
      rw [← Submodule.Quotient.eq, ← hσmk g₀ ⟨v₀, hv₀⟩]
      exact hfix
    have hmem2 : (U'.subtype (CFSG.Quasithin.SL3Small.resRep ρ hU'inv g₀ ⟨v₀, hv₀⟩ -
        (⟨v₀, hv₀⟩ : ↥U')) : V) ∈ U := Submodule.mem_comap.mp hmem
    have h2 : U'.subtype (CFSG.Quasithin.SL3Small.resRep ρ hU'inv g₀ ⟨v₀, hv₀⟩ -
        (⟨v₀, hv₀⟩ : ↥U')) = ρ g₀ v₀ - v₀ := by
      rw [Submodule.subtype_apply, Submodule.coe_sub,
        CFSG.Quasithin.SL3Small.coe_resRep ρ hU'inv]
    rwa [h2] at hmem2
  let K : Subgroup G := σ.ker
  haveI hKnormal : K.Normal := MonoidHom.normal_ker σ
  have hKne : K ≠ ⊤ := by
    intro htop
    have hmem : g₀ ∈ K := by rw [htop]; exact Subgroup.mem_top g₀
    exact hσg0ne ((MonoidHom.mem_ker (f := σ)).mp hmem)
  have hK : K ≤ Subgroup.center G := le_center_of_normal_ne_top hq hKne
  let X := G ⧸ K
  have hperfX : commutator X = ⊤ := commutator_quotient_eq_top hq.1 K
  let σhat : Representation (ZMod 2) X W := QuotientGroup.lift K σ (fun _ h => h)
  have hσhatmk : ∀ g : G, σhat (g : X) = σ g :=
    fun g => QuotientGroup.lift_mk K (fun _ h => h) g
  have hirrHat : σhat.IsIrreducible := by
    rw [CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff] at hirr ⊢
    refine ⟨hirr.1, fun U hU => hirr.2 U (fun g u hu => ?_)⟩
    have h := hU (g : X) u hu
    rwa [hσhatmk g] at h
  have hntHat : ∃ x : X, σhat x ≠ 1 := by
    refine ⟨(g₀ : X), ?_⟩
    rw [hσhatmk g₀]
    exact hσg0ne
  have hoddX : ∀ z ∈ Subgroup.center X, ∀ k : ℕ, z ^ 2 ^ k = 1 → z = 1 := by
    intro z hz k hzk
    obtain ⟨g, hgcenter, hgz⟩ := exists_mem_center_of_mem_center_quotient hq hK hz
    have hmemK : g ^ 2 ^ k ∈ K := by
      have h1 : (g ^ 2 ^ k : X) = 1 := by rw [hgz, hzk]
      exact (QuotientGroup.eq_one_iff (N := K) (g ^ 2 ^ k)).mp h1
    have hσpow : σ (g ^ 2 ^ k) = 1 := (MonoidHom.mem_ker (f := σ)).mp hmemK
    have hσg : σ g = 1 := rep_eq_one_of_central_pow_two hirr hgcenter hσpow
    have hgK : g ∈ K := (MonoidHom.mem_ker (f := σ)).mpr hσg
    rw [← hgz]
    exact (QuotientGroup.eq_one_iff (N := K) g).mpr hgK
  have hPX : LieModel (X ⧸ Subgroup.center X) .PSL 3 2 2 := by
    obtain ⟨e⟩ := nonempty_quotient_center_mulEquiv hq hK
    exact LieModel.of_mulEquiv e.symm hP
  have hdimW : Module.finrank (ZMod 2) W ≤ 6 := by
    have hsum : Module.finrank (ZMod 2) W +
        Module.finrank (ZMod 2) ↥(U.comap U'.subtype) = Module.finrank (ZMod 2) ↥U' :=
      Submodule.finrank_quotient_add_finrank _
    have hle := Submodule.finrank_le (U' : Submodule (ZMod 2) V)
    omega
  obtain ⟨θ', E₀, hE₀⟩ := sl3_section_natural hperfX hoddX hPX σhat hirrHat hntHat hdimW
  have hcardF4 : Nat.card F4 = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]; norm_num
  have hcard3 : Nat.card (Fin 3) = 3 := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]
  have hWdim : Module.finrank (ZMod 2) W = 6 := by
    have hcardW : Nat.card W = Nat.card (Fin 3 → F4) := Nat.card_congr E₀.toEquiv
    have h1 : Nat.card W = 2 ^ Module.finrank (ZMod 2) W := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    have h2 : Nat.card (Fin 3 → F4) = 2 ^ 6 := by
      rw [Nat.card_fun, hcardF4, hcard3]; norm_num
    have h3 : 2 ^ Module.finrank (ZMod 2) W = 2 ^ 6 := by rw [← h1, hcardW, h2]
    exact Nat.pow_right_injective (by norm_num) h3
  have hsum : Module.finrank (ZMod 2) W +
      Module.finrank (ZMod 2) ↥(U.comap U'.subtype) = Module.finrank (ZMod 2) ↥U' :=
    Submodule.finrank_quotient_add_finrank _
  have hle := Submodule.finrank_le (U' : Submodule (ZMod 2) V)
  have hcomap0 : Module.finrank (ZMod 2) ↥(U.comap U'.subtype) = 0 := by omega
  have hU'dim : Module.finrank (ZMod 2) ↥U' = 6 := by omega
  have hU'top : U' = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [hU'dim, hdim])
  have hcomapbot : U.comap U'.subtype = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hforall : ∀ y : ↥(U.comap U'.subtype), y = 0 :=
      (finrank_zero_iff_forall_zero (K := ZMod 2) (V := ↥(U.comap U'.subtype))).mp hcomap0
    exact congrArg Subtype.val (hforall ⟨x, hx⟩)
  have hUbot : U = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro u hu
    have hmem : (⟨u, hUU'.le hu⟩ : ↥U') ∈ U.comap U'.subtype := hu
    rw [hcomapbot, Submodule.mem_bot] at hmem
    exact Subtype.ext_iff.mp hmem
  let toU' : V →ₗ[ZMod 2] ↥U' :=
    { toFun := fun v => ⟨v, by rw [hU'top]; exact Submodule.mem_top⟩
      map_add' := fun v w => rfl
      map_smul' := fun c v => rfl }
  let ι : V →ₗ[ZMod 2] W := (U.comap U'.subtype).mkQ.comp toU'
  have hι_apply : ∀ v : V, ι v =
      Submodule.Quotient.mk (⟨v, by rw [hU'top]; exact Submodule.mem_top⟩ : ↥U') :=
    fun v => rfl
  have hker : LinearMap.ker ι = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    have hxmem : (⟨x, by rw [hU'top]; exact Submodule.mem_top⟩ : ↥U') ∈
        U.comap U'.subtype := by
      rw [← Submodule.Quotient.mk_eq_zero, ← hι_apply x]
      exact hx
    rw [hcomapbot, Submodule.mem_bot] at hxmem
    exact Subtype.ext_iff.mp hxmem
  have hinj : Function.Injective ι := LinearMap.ker_eq_bot.mp hker
  have hrange : LinearMap.range ι = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h1 : Module.finrank (ZMod 2) ↥(LinearMap.range ι) +
        Module.finrank (ZMod 2) ↥(LinearMap.ker ι) = Module.finrank (ZMod 2) V :=
      LinearMap.finrank_range_add_finrank_ker ι
    rw [hker, finrank_bot (ZMod 2) V] at h1
    omega
  have hsurj : Function.Surjective ι := LinearMap.range_eq_top.mp hrange
  have hbij : Function.Bijective ι := ⟨hinj, hsurj⟩
  have hι_equiv : ∀ (g : G) (v : V), ι (ρ g v) = σ g (ι v) := by
    intro g v
    rw [hι_apply (ρ g v), hι_apply v,
      hσmk g ⟨v, by rw [hU'top]; exact Submodule.mem_top⟩]
    exact congrArg Submodule.Quotient.mk
      (Subtype.ext (by rw [CFSG.Quasithin.SL3Small.coe_resRep ρ hU'inv]))
  have hKbot : K = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro g hg
    have hσg : σ g = 1 := (MonoidHom.mem_ker (f := σ)).mp hg
    have hρg : ρ g = 1 := by
      apply LinearMap.ext
      intro v
      have hv : ι (ρ g v) = ι v := by rw [hι_equiv g v, hσg, Module.End.one_apply]
      exact hinj hv
    exact hρ (by rw [hρg, map_one])
  have hinjK : Function.Injective (QuotientGroup.mk' K) :=
    (MonoidHom.ker_eq_bot_iff (QuotientGroup.mk' K)).mp (by rw [QuotientGroup.ker_mk', hKbot])
  have hbijK : Function.Bijective (QuotientGroup.mk' K) :=
    ⟨hinjK, QuotientGroup.mk'_surjective K⟩
  let eG : G ≃* X := MulEquiv.ofBijective (QuotientGroup.mk' K) hbijK
  let θ : Matrix.SpecialLinearGroup (Fin 3) F4 ≃* G := θ'.trans eG.symm
  refine ⟨θ, (AddEquiv.ofBijective ι hbij).trans E₀, fun g v => ?_⟩
  have hθg : eG (θ g) = θ' g := by
    show eG (eG.symm (θ' g)) = θ' g
    rw [MulEquiv.apply_symm_apply]
  have hσθ : σhat (θ' g) = σ (θ g) := by
    have h1 : (θ' g : X) = (θ g : X) := by
      rw [← hθg]
      rfl
    rw [h1, hσhatmk (θ g)]
  calc ((AddEquiv.ofBijective ι hbij).trans E₀) (ρ (θ g) v)
      = E₀ ((AddEquiv.ofBijective ι hbij) (ρ (θ g) v)) := rfl
    _ = E₀ (ι (ρ (θ g) v)) := by rw [AddEquiv.ofBijective_apply]
    _ = E₀ (σ (θ g) (ι v)) := by rw [hι_equiv]
    _ = E₀ (σhat (θ' g) (ι v)) := by rw [← hσθ]
    _ = ((g : Matrix.SpecialLinearGroup (Fin 3) F4) :
          Matrix (Fin 3) (Fin 3) F4) *ᵥ E₀ (ι v) := hE₀ g (ι v)
    _ = ((g : Matrix.SpecialLinearGroup (Fin 3) F4) :
          Matrix (Fin 3) (Fin 3) F4) *ᵥ
          ((AddEquiv.ofBijective ι hbij).trans E₀) v := rfl

end Core

end CFSG.StandardType.GGSixE6Two
