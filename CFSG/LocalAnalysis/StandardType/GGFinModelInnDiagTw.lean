module

public import CFSG.LocalAnalysis.StandardType.GGFinModelRootCompatDefs
public import CFSG.LocalAnalysis.StandardType.GGFinModelAct
public import CFSG.LocalAnalysis.StandardType.GGFinModelExists
import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdE6Core
import CFSG.LocalAnalysis.StandardType.GGRootDetectTwE6
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTwE6
import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.CoverTwE6

public section

namespace CFSG.StandardType.GGFinModel

open CFSG.StandardType CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Universal CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Steinberg.Isogeny
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private lemma g4bConj_injective {C : Type*} [Group C] (hZ : Subgroup.center C = ⊥) :
    Function.Injective (MulAut.conj : C →* MulAut C) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  rw [Subgroup.mem_bot]
  have hxc : x ∈ Subgroup.center C := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h := congrArg (fun f : MulAut C => f y) hx
    rw [MulAut.conj_apply, MulAut.one_apply] at h
    calc y * x = (x * y * x⁻¹) * x := by rw [h]
      _ = x * y := by group
  rw [hZ] at hxc
  simpa using hxc

private lemma g4bConj_conj {C : Type*} [Group C] (κ : MulAut C) (g : C) :
    κ⁻¹ * MulAut.conj g * κ = MulAut.conj (κ⁻¹ g) := by
  ext x
  change κ⁻¹ (g * κ x * g⁻¹) = κ⁻¹ g * x * (κ⁻¹ g)⁻¹
  rw [map_mul, map_mul, map_inv, MulAut.inv_apply_self]

private lemma g4bConj_mul_conj {C : Type*} [Group C] (f : MulAut C) (c : C) :
    f * MulAut.conj c * f⁻¹ = MulAut.conj (f c) := by
  ext y
  change f (c * f⁻¹ y * c⁻¹) = f c * y * (f c)⁻¹
  rw [map_mul, map_mul, map_inv, MulAut.apply_inv_self]

private lemma g4bConj_range_normal {C : Type*} [Group C] :
    (MulAut.conj : C →* MulAut C).range.Normal := by
  rw [Subgroup.normal_iff_map_conj_eq]
  intro f
  apply le_antisymm
  · rintro _ ⟨x, ⟨c, rfl⟩, rfl⟩
    exact ⟨f c, (g4bConj_mul_conj f c).symm⟩
  · rintro _ ⟨c, rfl⟩
    refine ⟨MulAut.conj (f.symm c), ⟨f.symm c, rfl⟩, ?_⟩
    show f * MulAut.conj (f.symm c) * f⁻¹ = MulAut.conj c
    rw [g4bConj_mul_conj, MulEquiv.apply_symm_apply]

theorem ggFixGp_conj_innDiagU_twE6
    {n f : ℕ} (hf : 1 ≤ f)
    (hinj : Function.Injective (ggIota .twistedE6 n f hf)) (m : ModGL (langTag .twistedE6) GGL)
    (hm : m ∈ ggFixGp .twistedE6 f)
    (hmN : m ∈ Subgroup.normalizer
      ((ggIota .twistedE6 n f hf).range : Set (ModGL (langTag .twistedE6) GGL))) :
    GGInnDiagU .twistedE6 n f (ggConjAut (ggIota .twistedE6 n f hf) hinj ⟨m, hmN⟩) := by
  classical
  let F := GaloisField 2 (2 * f)
  let S := (ggU .twistedE6 n f).K
  let ZS := Subgroup.center S
  let Cq := S ⧸ ZS
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Algebra F GGL := (ggRatEmb (2 * f)).toAlgebra
  haveI : IsScalarTower (ZMod 2) F GGL :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  haveI : Algebra.IsAlgebraic F GGL :=
    Algebra.IsAlgebraic.tower_top (K := ZMod 2) (L := F) (A := GGL)
  haveI : IsAlgClosure F GGL := ⟨IsAlgClosure.isAlgClosed (ZMod 2), inferInstance⟩
  have hσsurj : Function.Surjective (frobQ 2 f) :=
    Finite.surjective_of_injective (frobQ 2 f).injective
  let σE : F ≃+* F := RingEquiv.ofBijective (frobQ 2 f) ⟨(frobQ 2 f).injective, hσsurj⟩
  set κ : MulAut Cq := ggConjAut (ggIota .twistedE6 n f hf) hinj ⟨m, hmN⟩ with hκdef
  have hcardF : Nat.card F = (2 ^ f) ^ 2 := card_galoisField_two_mul 2 f hf
  let m' : ModGL TwistTag.E6.tag GGL := m
  have hmR : m' ∈ twistedFixedGroup TwistTag.E6 GGL (ggFrobT f) := hm
  have hdecomp := (CFSG.RankThree.Classical2.twisted_E6_full_rational_fixed_group_order
    (ℓ := 2) (f := f) Nat.prime_two hf F hcardF (frobQ 2 f) (frobQ_apply 2 f)
    GGL (ggFrobT f) (ggFrobT_apply f)).2.1
  have hmRset : m' ∈ (twistedFixedGroup TwistTag.E6 GGL (ggFrobT f) :
      Set (ModGL TwistTag.E6.tag GGL)) := hmR
  rw [hdecomp, Set.mem_mul] at hmRset
  obtain ⟨d, hd, e, hemap, hdc⟩ := hmRset
  obtain ⟨e, he, rfl⟩ := hemap
  obtain ⟨a, ha, hda⟩ := RecipeExcLang.exists_compat_of_mem_graphFixedTorus
    (K := F) (L := GGL) (n := f) hcardF σE (fun c => frobQ_apply 2 f c)
    (ggFrobT f) (ggFrobT_apply f) hd
  have hm_eq : baseChangeGL (algebraMap F GGL) (rootDiagUnit TwistTag.E6.tag a * e) = m' := by
    rw [map_mul, hda]
    exact hdc
  have he' : e⁻¹ ∈ ⁅twistedFixedGroup TwistTag.E6 F (frobQ 2 f),
      twistedFixedGroup TwistTag.E6 F (frobQ 2 f)⁆ := by
    rw [CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.derived_eq (f := f) hf hcardF
      (frobQ 2 f) (frobQ_apply 2 f)]
    exact inv_mem he
  obtain ⟨a₀, ha₀⟩ :=
    twistedE6Isogeny_surjective (p := 2) (f := f) hf (⟨e⁻¹, he'⟩ : ↥⁅twistedFixedGroup
      TwistTag.E6 F (frobQ 2 f), twistedFixedGroup TwistTag.E6 F (frobQ 2 f)⁆)
  have ha₀val : (twistedE6Isogeny 2 f hf a₀ : ModGL TwistTag.E6.tag F) = e⁻¹ :=
    congrArg Subtype.val ha₀
  have hcenterC : Subgroup.center Cq = ⊥ := by
    have hcg : Subgroup.center (graphFixedRootGroup TwistTag.E6 F (frobQ 2 f)) = ⊥ :=
      center_graphFixedRootGroup_eq_bot (t := TwistTag.E6) (K := F) (σ := frobQ 2 f) hσsurj
    have hmap := Subgroup.map_center_eq (ggKbEquivTwE6 n f hf)
    rw [hcg] at hmap
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hxmap : (ggKbEquivTwE6 n f hf) x ∈ (⊥ : Subgroup _) := by
      rw [← hmap]
      exact ⟨x, hx, rfl⟩
    rw [Subgroup.mem_bot] at hxmap
    exact (ggKbEquivTwE6 n f hf).injective (by simpa using hxmap)
  have hconj_inj : Function.Injective (MulAut.conj : Cq →* MulAut Cq) :=
    g4bConj_injective hcenterC
  have hψy : ∀ z : S, ggPsiU .twistedE6 n f z =
      MulAut.conj (QuotientGroup.mk z : Cq) := fun z => rfl
  have hmk : ∀ y y' : S, ggPsiU .twistedE6 n f y' = κ⁻¹ * ggPsiU .twistedE6 n f y * κ →
      (QuotientGroup.mk y' : Cq) = κ⁻¹ (QuotientGroup.mk y : Cq) := by
    intro y y' h
    apply hconj_inj
    change MulAut.conj (QuotientGroup.mk y' : Cq) =
      MulAut.conj (κ⁻¹ (QuotientGroup.mk y : Cq))
    rw [← hψy y', h, hψy y]
    exact g4bConj_conj κ (QuotientGroup.mk y)
  have hκinv : ∀ z : Cq, (ggIota .twistedE6 n f hf) (κ⁻¹ z) =
      m⁻¹ * (ggIota .twistedE6 n f hf) z * m := by
    intro z
    have h := ggConjAut_apply (ggIota .twistedE6 n f hf) hinj ⟨m, hmN⟩ (κ⁻¹ z)
    rw [← hκdef] at h
    rw [MulAut.apply_inv_self] at h
    calc (ggIota .twistedE6 n f hf) (κ⁻¹ z) =
        m⁻¹ * (m * (ggIota .twistedE6 n f hf) (κ⁻¹ z) * m⁻¹) * m := by group
      _ = m⁻¹ * (ggIota .twistedE6 n f hf) z * m := by rw [← h]
  have hleft : ∀ y y' : S, ggPsiU .twistedE6 n f y' = κ⁻¹ * ggPsiU .twistedE6 n f y * κ →
      baseChangeGL (algebraMap F GGL)
          (twistedE6Isogeny 2 f hf y' : ModGL TwistTag.E6.tag F) =
        m'⁻¹ * baseChangeGL (algebraMap F GGL)
          (twistedE6Isogeny 2 f hf y : ModGL TwistTag.E6.tag F) * m' := by
    intro y y' h
    have h1 : (ggIota .twistedE6 n f hf) (QuotientGroup.mk y' : Cq) =
        m⁻¹ * (ggIota .twistedE6 n f hf) (QuotientGroup.mk y : Cq) * m := by
      rw [hmk y y' h, hκinv]
    rw [ggIota_twistedE6_mk n f hf y', ggIota_twistedE6_mk n f hf y] at h1
    exact h1
  have hact : ∀ y y' : S, ggPsiU .twistedE6 n f y' = κ⁻¹ * ggPsiU .twistedE6 n f y * κ →
      (twistedE6Isogeny 2 f hf y' : ModGL TwistTag.E6.tag F) =
        (twistedE6Isogeny 2 f hf a₀ : ModGL TwistTag.E6.tag F) * rootDiagUnit TwistTag.E6.tag a⁻¹ *
          (twistedE6Isogeny 2 f hf y : ModGL TwistTag.E6.tag F) *
            (rootDiagUnit TwistTag.E6.tag a⁻¹)⁻¹ *
              (twistedE6Isogeny 2 f hf a₀ : ModGL TwistTag.E6.tag F)⁻¹ := by
    intro y y' h
    apply baseChangeGL_injective (algebraMap F GGL)
    rw [hleft y y' h]
    rw [map_mul, map_mul, map_mul, map_mul, map_inv, map_inv]
    rw [show baseChangeGL (algebraMap F GGL)
          (twistedE6Isogeny 2 f hf a₀ : ModGL TwistTag.E6.tag F) =
        (baseChangeGL (algebraMap F GGL) e)⁻¹ from by rw [ha₀val, map_inv]]
    rw [show baseChangeGL (algebraMap F GGL) (rootDiagUnit TwistTag.E6.tag a⁻¹) =
        (baseChangeGL (algebraMap F GGL) (rootDiagUnit TwistTag.E6.tag a))⁻¹ from by
          rw [← MpStdE6.rootDiagUnit_inv, map_inv]]
    rw [hda]
    rw [← hdc, mul_inv_rev]
    group
  have hdiag : ∀ δ ∈ (twistedE6Datum 2 f).roots,
      ∃ h ∈ ggTorus (twistedE6Datum 2 f),
        ∀ z ∈ (twistedE6Datum 2 f).rootGroup δ,
          (twistedE6Isogeny 2 f hf (h * z * h⁻¹) : ModGL TwistTag.E6.tag F) =
            rootDiagUnit TwistTag.E6.tag a⁻¹ *
              (twistedE6Isogeny 2 f hf z : ModGL TwistTag.E6.tag F) *
                (rootDiagUnit TwistTag.E6.tag a⁻¹)⁻¹ := by
    intro δ hδ
    obtain ⟨h, hh, hz⟩ := RootDetectTwE6.hdiag_twisted (frobQ 2 f) (frobQ_frobQ 2 f hf)
      a⁻¹ (fun i => RecipeExcLang.IsCompatE6.inv ha i) δ hδ
    exact ⟨h, hh, fun z hz' => hz z hz'⟩
  have hψrange : (ggPsiU .twistedE6 n f).range =
      (MulAut.conj : Cq →* MulAut Cq).range := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨QuotientGroup.mk z, rfl⟩
    · rintro ⟨z, rfl⟩
      obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective ZS z
      exact ⟨s, rfl⟩
  have hc : κ ∈ Subgroup.normalizer ((ggPsiU .twistedE6 n f).range : Set (MulAut Cq)) := by
    rw [hψrange, Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top _
  refine MpStdE6.ggPsiInnerDiag_of_conj_diag (twistedE6Datum 2 f)
    (RootDetectTwE6.ker_le_center f (twistedE6Isogeny 2 f hf) (coe_twistedE6Isogeny 2 f hf))
    (RootDetectTwE6.odd_card_ker f (twistedE6Isogeny 2 f hf) (coe_twistedE6Isogeny 2 f hf))
    (RootDetectTwE6.twistedRootGroup_mul_self f) a⁻¹ hdiag hc a₀ hact

end CFSG.StandardType.GGFinModel
