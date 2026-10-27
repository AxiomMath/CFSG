module

public import CFSG.LocalAnalysis.StandardType.GGFinModelRootCompatDefs
public import CFSG.LocalAnalysis.StandardType.GGFinModelAct
public import CFSG.LocalAnalysis.StandardType.GGFinModelExists
public import CFSG.LocalAnalysis.StandardType.GGFinModelCore
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdE6Core
public import CFSG.LocalAnalysis.StandardType.GGExcElemToralFrobeniusFixed
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.FiniteCentralizerRegular

public section

namespace CFSG.StandardType.GGFinModel

open CFSG.StandardType CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Universal CFSG.LieType.Steinberg.Isogeny
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus

section Helpers

open CFSG.LieType.Steinberg.Minuscule

private theorem g4bMulAut_conj_conj {G : Type*} [Group G] (φ : MulAut G) (y : G) :
    φ * MulAut.conj y * φ⁻¹ = MulAut.conj (φ y) := by
  ext z
  simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply]
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

private theorem g4bConj_range_normal (G : Type*) [Group G] :
    (MulAut.conj : G →* MulAut G).range.Normal where
  conj_mem := by
    intro x hx g
    obtain ⟨y, rfl⟩ := hx
    refine ⟨g y, ?_⟩
    rw [g4bMulAut_conj_conj]

private theorem g4bMulAut_conj_injective_of_center_bot {G : Type*} [Group G]
    (h : Subgroup.center G = ⊥) :
    Function.Injective (MulAut.conj : G →* MulAut G) := by
  intro u v huv
  have h1 : MulAut.conj (v⁻¹ * u) = 1 := by
    rw [map_mul, map_inv, huv, inv_mul_cancel]
  have h2 : v⁻¹ * u ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro w
    have h3 := congrArg (fun f : MulAut G => f w) h1
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.one_apply] at h3
    have h4 : (v⁻¹ * u) * w = w * (v⁻¹ * u) := by
      have h5 := congrArg (fun t => t * (v⁻¹ * u)) h3
      simpa [mul_assoc] using h5
    exact h4.symm
  rw [h, Subgroup.mem_bot] at h2
  have h6 : v = u := inv_mul_eq_one.mp h2
  exact h6.symm

private theorem g4bE6FrobFixBaseChange
    {f : ℕ} (hf : 1 ≤ f)
    (g : ModGL Tag.E6 (GaloisField 2 f)) :
    Units.map (entrywiseHom (ggFrobT f)) (baseChangeGL (ggRatEmb f) g) =
      baseChangeGL (ggRatEmb f) g := by
  have hcomp : (ggFrobT f).comp (ggRatEmb f) = ggRatEmb f := by
    ext c
    rw [RingHom.comp_apply, ggFrobT_apply]
    have hmem : ggRatEmb f c ∈ Set.range (ggRatEmb f) := ⟨c, rfl⟩
    rw [ggRatEmb_range hf] at hmem
    exact hmem
  rw [CFSG.LieType.Chevalley.units_map_entrywiseHom_eq_baseChangeGL,
    CFSG.LieType.Chevalley.baseChangeGL_baseChangeGL, hcomp]

private theorem g4bE6RootInv
    {f : ℕ} :
    ∀ δ ∈ (e6Datum (GaloisField 2 f)).roots,
      ∀ z ∈ (e6Datum (GaloisField 2 f)).rootGroup δ, z * z = 1 := by
  intro δ _ z hz
  obtain ⟨t, rfl⟩ := (e6Data_valid.mem_rootGroup (GaloisField 2 f)).mp hz
  rw [← e6Data_valid.xm_add, CharTwo.add_self_eq_zero, e6Data_valid.xm_zero]

private theorem g4bE6Center
    {n f : ℕ} (hf : 1 ≤ f) (hinj : Function.Injective (ggIota .E6 n f hf)) :
    Subgroup.center (GGKb .E6 n f) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (ggU .E6 n f).K) z
  have hzadj : ggIota .E6 n f hf (QuotientGroup.mk' (Subgroup.center (ggU .E6 n f).K) k) ∈
      adjointGroup Tag.E6 GGL := by
    rw [QuotientGroup.mk'_apply, ggIota_E6_mk]
    exact CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup _
      (e6Isogeny (GaloisField 2 f) k).2
  have hcent : ggIota .E6 n f hf (QuotientGroup.mk' (Subgroup.center (ggU .E6 n f).K) k) = 1 := by
    refine eq_one_of_commute_image (K := GaloisField 2 f) (L := GGL) (ggRatEmb f) hzadj ?_
    rintro h ⟨g, hg, rfl⟩
    obtain ⟨k', hk'⟩ := e6Isogeny_surjective (GaloisField 2 f) ⟨g, hg⟩
    have hιk : ggIota .E6 n f hf (QuotientGroup.mk' (Subgroup.center (ggU .E6 n f).K) k') =
        baseChangeGL (ggRatEmb f) g :=
      (ggIota_E6_mk n f hf k').trans (by rw [hk']; rfl)
    rw [← hιk, ← map_mul, ← map_mul]
    congr 1
    exact (Subgroup.mem_center_iff.mp hz
      (QuotientGroup.mk' (Subgroup.center (ggU .E6 n f).K) k')).symm
  refine hinj ?_
  rw [hcent, map_one]

private theorem g4bE6Decomp
    {f : ℕ} (hf : 1 ≤ f) (m : ModGL Tag.E6 GGL)
    (hmAdj : m ∈ adjointGroup Tag.E6 GGL)
    (hmFix : Units.map (entrywiseHom (ggFrobT f)) m = m) :
    ∃ a : Fin (Tag.rank .E6) → (GaloisField 2 f)ˣ,
      ∃ j : adjointGroup Tag.E6 (GaloisField 2 f),
        m = baseChangeGL (ggRatEmb f)
          (rootDiagUnit Tag.E6 a * (j : ModGL Tag.E6 (GaloisField 2 f))) := by
  classical
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  have hKcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hFr : ∀ c : GGL, ggFrobT f c = c ^ Nat.card (GaloisField 2 f) := fun c => by
    rw [hKcard]
    exact ggFrobT_apply f c
  letI : Algebra (GaloisField 2 f) GGL := (ggRatEmb f).toAlgebra
  have hcomm : ∀ r : ZMod 2,
      ggRatEmb f (algebraMap (ZMod 2) (GaloisField 2 f) r) = algebraMap (ZMod 2) GGL r :=
    fun r => (IsAlgClosed.lift (R := ZMod 2) (S := GaloisField 2 f) (M := GGL)).commutes r
  haveI : Module.IsTorsionFree (GaloisField 2 f) GGL := {
    isSMulRegular := by
      intro r hr
      have hr0 : r ≠ 0 := hr.ne_zero
      have hfr0 : ggRatEmb f r ≠ 0 :=
        fun h => hr0 ((ggRatEmb f).injective (by rw [h, map_zero]))
      intro x y hxy
      change ggRatEmb f r * x = ggRatEmb f r * y at hxy
      exact mul_left_cancel₀ hfr0 hxy }
  have hcomp : RingHom.comp (algebraMap (GaloisField 2 f) GGL)
        (algebraMap (ZMod 2) (GaloisField 2 f)) =
      RingHom.comp (RingHom.id GGL) (algebraMap (ZMod 2) GGL) := by
    ext r
    exact hcomm r
  haveI : IsAlgClosure (GaloisField 2 f) GGL :=
    { isAlgClosed := inferInstance
      isAlgebraic := Algebra.IsAlgebraic.ringHom_of_comp_eq
        (f := algebraMap (ZMod 2) (GaloisField 2 f)) (g := RingHom.id GGL)
        (algebraMap (ZMod 2) (GaloisField 2 f)).injective Function.surjective_id hcomp }
  obtain ⟨D, hD, j, hj, hmj⟩ :=
    ExcElemToral.exists_mem_torusGroup_mul_baseChangeGL_of_frobenius_fixed
      (τ := Tag.E6) (K := GaloisField 2 f) (L := GGL) (ggFrobT f) hFr hmAdj hmFix
  have halg : algebraMap (GaloisField 2 f) GGL = ggRatEmb f :=
    RingHom.algebraMap_toAlgebra (ggRatEmb f)
  rw [halg] at hmj
  have hB : Units.map (entrywiseHom (ggFrobT f)) (baseChangeGL (ggRatEmb f) j) =
      baseChangeGL (ggRatEmb f) j := g4bE6FrobFixBaseChange hf j
  have hDfix : Units.map (entrywiseHom (ggFrobT f)) D = D := by
    have h2 : D * baseChangeGL (ggRatEmb f) j =
        Units.map (entrywiseHom (ggFrobT f)) D * baseChangeGL (ggRatEmb f) j := by
      calc D * baseChangeGL (ggRatEmb f) j = m := hmj.symm
        _ = Units.map (entrywiseHom (ggFrobT f)) m := hmFix.symm
        _ = Units.map (entrywiseHom (ggFrobT f)) (D * baseChangeGL (ggRatEmb f) j) := by
              rw [hmj]
        _ = Units.map (entrywiseHom (ggFrobT f)) D *
            Units.map (entrywiseHom (ggFrobT f)) (baseChangeGL (ggRatEmb f) j) := by
              rw [map_mul]
        _ = Units.map (entrywiseHom (ggFrobT f)) D * baseChangeGL (ggRatEmb f) j := by
              rw [hB]
    exact (mul_right_cancel h2).symm
  obtain ⟨b, hb⟩ := CFSG.LieType.Chevalley.exists_rootDiagUnit_eq_of_mem_torusGroup hD
  have hbfix : (fun i => Units.map (ggFrobT f).toMonoidHom (b i)) = b := by
    have h1 : Units.map (entrywiseHom (ggFrobT f)) (rootDiagUnit Tag.E6 b) =
        rootDiagUnit Tag.E6 b := by
      rw [← hb]
      exact hDfix
    rw [CFSG.LieType.Chevalley.units_map_entrywiseHom_eq_baseChangeGL,
      CFSG.LieType.Chevalley.baseChangeGL_rootDiagUnit] at h1
    exact CFSG.LieType.Chevalley.rootDiagUnit_injective h1
  have hrange : ∀ i, ∃ a : (GaloisField 2 f)ˣ, Units.map (ggRatEmb f).toMonoidHom a = b i := by
    intro i
    have hbi : ((b i : GGLˣ) : GGL) ^ 2 ^ f = ((b i : GGLˣ) : GGL) := by
      have h2 := congrArg (fun u : GGLˣ => (u : GGL)) (congrFun hbfix i)
      simp only [Units.coe_map, MonoidHom.coe_coe, ggFrobT_apply] at h2
      exact h2
    have hmem : ((b i : GGLˣ) : GGL) ∈ Set.range (algebraMap (GaloisField 2 f) GGL) :=
      CFSG.LieType.Chevalley.mem_range_algebraMap_of_pow_card_eq (k := GaloisField 2 f)
        (L := GGL) (by rw [hKcard]; exact hbi)
    obtain ⟨a, ha⟩ := hmem
    have ha' : ggRatEmb f a = ((b i : GGLˣ) : GGL) := by
      rw [← halg]
      exact ha
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [map_zero] at ha'
      exact (b i).ne_zero ha'.symm
    exact ⟨Units.mk0 a ha0, Units.ext ha'⟩
  choose a ha using hrange
  have hb' : b = fun i => Units.map (ggRatEmb f).toMonoidHom (a i) := by
    funext i
    exact (ha i).symm
  have hmain : m = baseChangeGL (ggRatEmb f) (rootDiagUnit Tag.E6 a * j) := by
    calc m = D * baseChangeGL (ggRatEmb f) j := hmj
      _ = rootDiagUnit Tag.E6 b * baseChangeGL (ggRatEmb f) j := by rw [hb]
      _ = rootDiagUnit Tag.E6 (fun i => Units.map (ggRatEmb f).toMonoidHom (a i)) *
            baseChangeGL (ggRatEmb f) j := by rw [hb']
      _ = baseChangeGL (ggRatEmb f) (rootDiagUnit Tag.E6 a) *
            baseChangeGL (ggRatEmb f) j := by
            rw [← CFSG.LieType.Chevalley.baseChangeGL_rootDiagUnit]
      _ = baseChangeGL (ggRatEmb f) (rootDiagUnit Tag.E6 a * j) := by rw [map_mul]
  exact ⟨a, ⟨j, hj⟩, hmain⟩

end Helpers

theorem ggFixGp_conj_innDiagU_E6
    {n f : ℕ} (hf : 1 ≤ f)
    (hinj : Function.Injective (ggIota .E6 n f hf)) (m : ModGL (langTag .E6) GGL)
    (hm : m ∈ ggFixGp .E6 f)
    (hmN : m ∈ Subgroup.normalizer ((ggIota .E6 n f hf).range : Set (ModGL (langTag .E6) GGL))) :
    GGInnDiagU .E6 n f (ggConjAut (ggIota .E6 n f hf) hinj ⟨m, hmN⟩) := by
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  haveI : CharP (GaloisField 2 f) 2 := inferInstance
  have hmAdj : m ∈ adjointGroup Tag.E6 GGL := by
    have hm' := hm
    rw [ggFixGp] at hm'
    exact (Subgroup.mem_inf.1 hm').1
  have hmFix : Units.map (entrywiseHom (ggFrobT f)) m = m := by
    have hm' := hm
    rw [ggFixGp] at hm'
    have h := MonoidHom.mem_eqLocusM.1 (Subgroup.mem_inf.1 hm').2
    change Units.map (entrywiseHom (ggFrobT f)) m = m at h
    exact h
  obtain ⟨a, j, hmj⟩ := g4bE6Decomp hf m hmAdj hmFix
  set x : ModGL Tag.E6 (GaloisField 2 f) :=
    rootDiagUnit Tag.E6 a * (j : ModGL Tag.E6 (GaloisField 2 f)) with hx
  have hmjx : m = baseChangeGL (ggRatEmb f) x := by
    rw [hx]
    exact hmj
  obtain ⟨a₀, ha₀⟩ := e6Isogeny_surjective (GaloisField 2 f) j⁻¹
  have ha₀val : ((e6Isogeny (GaloisField 2 f) a₀ : adjointGroup Tag.E6 (GaloisField 2 f)) :
      ModGL Tag.E6 (GaloisField 2 f)) = (j : ModGL Tag.E6 (GaloisField 2 f))⁻¹ := by
    rw [ha₀]
    rfl
  set c : MulAut (GGKb .E6 n f) := ggConjAut (ggIota .E6 n f hf) hinj ⟨m, hmN⟩ with hc_def
  have hodd : Odd (Nat.card (e6Isogeny (GaloisField 2 f)).ker) := by
    have h := CFSG.ClassicalInvolution.ModelFacts.ChevAut.e6Isogeny_not_dvd_card_ker
      (GaloisField 2 f) (p := 2)
    exact Nat.not_even_iff_odd.mp fun he => h (even_iff_two_dvd.mp he)
  have hc : c ∈ Subgroup.normalizer ((ggPsiU .E6 n f).range : Set (GGAutU .E6 n f)) := by
    rw [ggPsiU_range_eq_conj .E6 n f]
    rw [Subgroup.normalizer_eq_top_iff.mpr (g4bConj_range_normal (GGKb .E6 n f))]
    exact Subgroup.mem_top c
  have hact : ∀ y y' : (ggU .E6 n f).K,
      ggPsiU .E6 n f y' = c⁻¹ * ggPsiU .E6 n f y * c →
      ((e6Isogeny (GaloisField 2 f) y' : adjointGroup Tag.E6 (GaloisField 2 f)) :
          ModGL Tag.E6 (GaloisField 2 f)) =
        ((e6Isogeny (GaloisField 2 f) a₀ : adjointGroup Tag.E6 (GaloisField 2 f)) :
            ModGL Tag.E6 (GaloisField 2 f)) *
          rootDiagUnit Tag.E6 a⁻¹ *
          ((e6Isogeny (GaloisField 2 f) y : adjointGroup Tag.E6 (GaloisField 2 f)) :
            ModGL Tag.E6 (GaloisField 2 f)) *
            (rootDiagUnit Tag.E6 a⁻¹)⁻¹ *
              ((e6Isogeny (GaloisField 2 f) a₀ : adjointGroup Tag.E6 (GaloisField 2 f)) :
                ModGL Tag.E6 (GaloisField 2 f))⁻¹ := by
    intro y y' h
    have hcenter : Subgroup.center (GGKb .E6 n f) = ⊥ := g4bE6Center hf hinj
    have hconj : MulAut.conj (QuotientGroup.mk' (Subgroup.center (ggU .E6 n f).K) y') =
        MulAut.conj (c⁻¹ (QuotientGroup.mk' (Subgroup.center (ggU .E6 n f).K) y)) := by
      have h' := h
      simp only [ggPsiU, MonoidHom.comp_apply] at h'
      have hstep := g4bMulAut_conj_conj c⁻¹
        (QuotientGroup.mk' (Subgroup.center (ggU .E6 n f).K) y)
      rw [inv_inv] at hstep
      rw [h']
      exact hstep
    have hmky : QuotientGroup.mk' (Subgroup.center (ggU .E6 n f).K) y' =
        c⁻¹ (QuotientGroup.mk' (Subgroup.center (ggU .E6 n f).K) y) :=
      g4bMulAut_conj_injective_of_center_bot hcenter hconj
    have hcmy : c (QuotientGroup.mk' (Subgroup.center (ggU .E6 n f).K) y') =
        QuotientGroup.mk' (Subgroup.center (ggU .E6 n f).K) y := by
      rw [hmky]
      exact MulAut.apply_inv_self (GGKb .E6 n f) c
        (QuotientGroup.mk' (Subgroup.center (ggU .E6 n f).K) y)
    let iso : (ggU .E6 n f).K →* adjointGroup Tag.E6 (GaloisField 2 f) :=
      (e6Isogeny (GaloisField 2 f)).comp (MonoidHom.id ((ggU .E6 n f).K))
    have hιy' : ggIota .E6 n f hf (QuotientGroup.mk' (Subgroup.center (ggU .E6 n f).K) y') =
        baseChangeGL (ggRatEmb f) (iso y' : ModGL Tag.E6 (GaloisField 2 f)) := by
      rw [QuotientGroup.mk'_apply, ggIota_E6_mk]
      rfl
    have hιy : ggIota .E6 n f hf (QuotientGroup.mk' (Subgroup.center (ggU .E6 n f).K) y) =
        baseChangeGL (ggRatEmb f) (iso y : ModGL Tag.E6 (GaloisField 2 f)) := by
      rw [QuotientGroup.mk'_apply, ggIota_E6_mk]
      rfl
    have h5 : ggIota .E6 n f hf (QuotientGroup.mk' (Subgroup.center (ggU .E6 n f).K) y') =
        m⁻¹ * ggIota .E6 n f hf (QuotientGroup.mk' (Subgroup.center (ggU .E6 n f).K) y) * m := by
      have h4 : m * ggIota .E6 n f hf (QuotientGroup.mk' (Subgroup.center (ggU .E6 n f).K) y') *
          m⁻¹ = ggIota .E6 n f hf (QuotientGroup.mk' (Subgroup.center (ggU .E6 n f).K) y) := by
        rw [← hcmy]
        rw [hc_def]
        rw [ggConjAut_apply]
      rw [← h4]
      group
    have h5b : baseChangeGL (ggRatEmb f) (iso y' : ModGL Tag.E6 (GaloisField 2 f)) =
        (baseChangeGL (ggRatEmb f) x)⁻¹ *
          baseChangeGL (ggRatEmb f) (iso y : ModGL Tag.E6 (GaloisField 2 f)) *
          baseChangeGL (ggRatEmb f) x := by
      rw [← hιy', ← hιy, ← hmjx]
      exact h5
    rw [← map_inv, ← map_mul, ← map_mul] at h5b
    have h6 : (e6Isogeny (GaloisField 2 f) y' : ModGL Tag.E6 (GaloisField 2 f)) =
        x⁻¹ * (e6Isogeny (GaloisField 2 f) y : ModGL Tag.E6 (GaloisField 2 f)) * x := by
      change (iso y' : ModGL Tag.E6 (GaloisField 2 f)) =
        x⁻¹ * (iso y : ModGL Tag.E6 (GaloisField 2 f)) * x
      exact CFSG.LieType.Chevalley.baseChangeGL_injective (ggRatEmb f) h5b
    rw [h6, ha₀val]
    rw [← MpStdE6.rootDiagUnit_inv (t := Tag.E6) a]
    rw [hx]
    group
  refine MpStdE6.ggPsiInnerDiag_of_conj_diag (Δ := (ggU .E6 n f).D)
    (CFSG.ClassicalInvolution.ModelFacts.ChevAut.e6Isogeny_ker_le_center (GaloisField 2 f))
    hodd g4bE6RootInv a⁻¹ (fun δ hδ => RootDetectExc.hdiag_E6 (GaloisField 2 f) δ hδ a⁻¹)
    hc a₀ hact

end CFSG.StandardType.GGFinModel
