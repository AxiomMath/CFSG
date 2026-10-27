module

public import CFSG.LocalAnalysis.StandardType.GGLieCoreBridge
public import CFSG.LocalAnalysis.StandardType.GGInterfaceFive
public import CFSG.LocalAnalysis.StandardType.GGFinModelRootCompatDefs
public import CFSG.LocalAnalysis.StandardType.GGFinModelInput
public import CFSG.LocalAnalysis.StandardType.GGFinModelAdj
public import CFSG.LocalAnalysis.StandardType.GGFinModelTw
public import CFSG.LocalAnalysis.StandardType.GGFinModelRat
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpRest
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeTypeA

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Exceptional
open CFSG.Open (StatedLieTag)

private theorem l10b3_datum
    {t : StatedLieTag} (ht : GGExcFive t) {f : ℕ} (hf : 1 ≤ f) :
    ∃ D : LangDatum (langTag t) GGL, D.Φ = ggPhi t f := by
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨D, hΦ, -, -⟩ := ggDatumExists hf (1 : CFSG.LieType.Chevalley.WeylGroup Tag.F4)
    exact ⟨D, hΦ⟩
  · obtain ⟨D, hΦ, -, -⟩ := ggDatumExists hf (1 : CFSG.LieType.Chevalley.WeylGroup Tag.E6)
    exact ⟨D, hΦ⟩
  · obtain ⟨D, hΦ, -, -⟩ := ggDatumExists hf (1 : CFSG.LieType.Chevalley.WeylGroup Tag.E7)
    exact ⟨D, hΦ⟩
  · obtain ⟨D, hΦ, -, -⟩ := ggDatumExists hf (1 : CFSG.LieType.Chevalley.WeylGroup Tag.E8)
    exact ⟨D, hΦ⟩
  · obtain ⟨D, hΦ, -, -⟩ := ggDatumExistsTw hf
      (1 : CFSG.LieType.Chevalley.WeylGroup TwistTag.E6.tag)
    exact ⟨D, hΦ⟩

private theorem l10b3_langPkg
    {t : StatedLieTag} (n f : ℕ) (ht : GGExcFive t) (hf : 1 ≤ f)
    (D : LangDatum (langTag t) GGL) (hΦ : D.Φ = ggPhi t f) :
    GGLangPkg D (ggIota t n f hf) := by
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · exact (ggLangPkg_adjoint (Or.inl rfl) hf D hΦ).of_equiv (ggKbEquivF4 n f)
  · exact (ggLangPkg_adjoint (Or.inr (Or.inl rfl)) hf D hΦ).of_equiv (ggKbEquivE6 n f)
  · exact (ggLangPkg_adjoint (Or.inr (Or.inr (Or.inl rfl))) hf D hΦ).of_equiv (ggKbEquivE7 n f)
  · exact (ggLangPkg_adjoint (Or.inr (Or.inr (Or.inr rfl))) hf D hΦ).of_equiv (ggKbEquivE8 n f)
  · exact (ggLangPkg_twE6_adjoint hf D hΦ).of_equiv (ggKbEquivTwE6 n f hf)

private theorem l10b3_theta_abs {K G Y : Type} [Group K] [Group G] [Group Y] {ψ : K →* G}
    {G₀ : Subgroup G} (hrange : ψ.range = G₀) {ι : K →* Y} (hker : ψ.ker ≤ ι.ker) :
    ∃ θ : ↥G₀ →* Y, (∀ (k : K) (h : ψ k ∈ G₀), θ ⟨ψ k, h⟩ = ι k) ∧ θ.range = ι.range := by
  subst hrange
  let e : K ⧸ ψ.ker ≃* ↥ψ.range := QuotientGroup.quotientKerEquivRange ψ
  let ι' : K ⧸ ψ.ker →* Y := QuotientGroup.lift ψ.ker ι hker
  refine ⟨ι'.comp e.symm.toMonoidHom, ?_, ?_⟩
  · intro k h
    have h1 : e (QuotientGroup.mk k) = ⟨ψ k, h⟩ := rfl
    have h2 : e.symm.toMonoidHom (e (QuotientGroup.mk k)) = QuotientGroup.mk k := by
      simpa using e.symm_apply_apply (e (QuotientGroup.mk k))
    rw [MonoidHom.comp_apply, ← h1, h2]
    exact QuotientGroup.lift_mk ψ.ker hker k
  · rw [MonoidHom.range_comp,
      show e.symm.toMonoidHom.range = ⊤ from MonoidHom.range_eq_top.2 e.symm.surjective,
      Subgroup.map_top]
    ext y
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨x, (QuotientGroup.lift_mk ψ.ker hker x).symm⟩
    · rintro ⟨x, rfl⟩
      exact ⟨QuotientGroup.mk x, QuotientGroup.lift_mk ψ.ker hker x⟩

private theorem l10b3_ker_abs {K G Y : Type} [Group K] [Group G] [Group Y] {ψ : K →* G}
    {G₀ : Subgroup G} (hrange : ψ.range = G₀) {ι : K →* Y} (hperf : commutator K = ⊤)
    (hkψ : ψ.ker ≤ Subgroup.center K) (hkι : ι.ker = Subgroup.center K) {θ : ↥G₀ →* Y}
    (hθ : ∀ (k : K) (h : ψ k ∈ G₀), θ ⟨ψ k, h⟩ = ι k) : θ.ker = Subgroup.center ↥G₀ := by
  subst hrange
  ext x
  obtain ⟨k, rfl⟩ := MonoidHom.rangeRestrict_surjective ψ x
  have hθk : θ (ψ.rangeRestrict k) = ι k := hθ k (ψ.rangeRestrict k).2
  rw [MonoidHom.mem_ker, hθk, ← MonoidHom.mem_ker (f := ι), hkι]
  constructor
  · intro hk
    rw [Subgroup.mem_center_iff] at hk ⊢
    intro y
    obtain ⟨k', rfl⟩ := MonoidHom.rangeRestrict_surjective ψ y
    show ψ.rangeRestrict k' * ψ.rangeRestrict k = ψ.rangeRestrict k * ψ.rangeRestrict k'
    rw [← map_mul, ← map_mul, hk k']
  · intro hk
    exact InnerDiagA.mem_center_of_rangeRestrict_mem_center hperf ψ hkψ hk

private theorem l10b3_iotaK_ker
    {t : StatedLieTag} {n f : ℕ} (hf : 1 ≤ f) (hinj : Function.Injective (ggIota t n f hf)) :
    (ggIotaK t n f hf).ker = Subgroup.center (ggU t n f).K := by
  rw [ggIotaK,
    ← MonoidHom.comap_ker (g := ggIota t n f hf)
      (f := QuotientGroup.mk' (Subgroup.center (ggU t n f).K)),
    (MonoidHom.ker_eq_bot_iff (ggIota t n f hf)).2 hinj, MonoidHom.comap_bot,
    QuotientGroup.ker_mk']

private theorem l10b3_iotaK_range
    {t : StatedLieTag} {n f : ℕ} (hf : 1 ≤ f) :
    (ggIotaK t n f hf).range = (ggIota t n f hf).range := by
  rw [ggIotaK, MonoidHom.range_comp,
    MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective _), Subgroup.map_top]

private theorem l10b3_perfect_range {K G : Type} [Group K] [Group G] (ψ : K →* G)
    (hK : commutator K = ⊤) : commutator ↥ψ.range = ⊤ := by
  have hsurj : Function.Surjective ψ.rangeRestrict := MonoidHom.rangeRestrict_surjective ψ
  have h1 : Subgroup.map ψ.rangeRestrict (commutator K) = commutator ↥ψ.range := by
    rw [commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ hsurj, commutator_def]
  rw [hK, Subgroup.map_top_of_surjective _ hsurj] at h1
  exact h1.symm

private theorem l10b3_rank
    {t : StatedLieTag} (ht : GGExcFive t) (n f : ℕ) :
    2 ≤ (ggU t n f).D.rank := by
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · rw [ggRank_untw (Or.inl rfl) n f]; decide
  · rw [ggRank_untw (Or.inr (Or.inl rfl)) n f]; decide
  · rw [ggRank_untw (Or.inr (Or.inr (Or.inl rfl))) n f]; decide
  · rw [ggRank_untw (Or.inr (Or.inr (Or.inr rfl))) n f]; decide
  · show 2 ≤ 4
    decide

theorem ggPresentsG0_of_bridgeHyp
    {t : StatedLieTag} {n f p : ℕ} (ht : GGExcFive t)
    {G : Type} [Group G] {ψ : (ggU t n f).K →* G} {G₀ D : Subgroup G}
    (h : GGLieBridgeHyp t n f p ψ G₀ D) :
    GGPresentsG0 G₀ (ggU t n f).D t n f ψ := by
  have hadm := LieModel.admissible h.2.2.1
  have hrk : 2 ≤ (ggU t n f).D.rank := l10b3_rank ht n f
  have h1 : ψ.range = G₀ := h.1
  refine ⟨⟨hadm, hrk⟩, ⟨h.1, h.2.1⟩, ?_, h.2.2.1⟩
  have hperf := l10b3_perfect_range ψ (ggU_perfect_lieModel hadm hrk).1
  rw [← h1]
  exact hperf

theorem ggLieBridge_theta
    {t : StatedLieTag} {n f : ℕ} (ht : GGExcFive t) (hf : 1 ≤ f)
    {G : Type} [Group G] {ψ : (ggU t n f).K →* G} {G₀ : Subgroup G}
    (hpres : GGPresentsG0 G₀ (ggU t n f).D t n f ψ) :
    ∃ θ : ↥G₀ →* ModGL (langTag t) GGL,
      (∀ (k : (ggU t n f).K) (h : ψ k ∈ G₀), θ ⟨ψ k, h⟩ = ggIotaK t n f hf k) ∧
      θ.ker = Subgroup.center ↥G₀ ∧ θ.range = ⁅ggFixGp t f, ggFixGp t f⁆ ∧
      ∀ z ∈ ggFixGp t f, (∀ x : ↥G₀, z * θ x = θ x * z) → z = 1 := by
  obtain ⟨D, hΦ⟩ := l10b3_datum ht hf
  have pkg := l10b3_langPkg n f ht hf D hΦ
  have hfix : D.fix = ggFixGp t f := ggFixGp_eq_fix D hΦ
  have hker := l10b3_iotaK_ker hf pkg.inj
  have hperf := (ggU_perfect_lieModel hpres.1.1 hpres.1.2).1
  obtain ⟨θ, hθ, hrange⟩ := l10b3_theta_abs hpres.2.1.1 (hpres.2.1.2.trans hker.ge)
  refine ⟨θ, hθ, l10b3_ker_abs hpres.2.1.1 hperf hpres.2.1.2 hker hθ, ?_, ?_⟩
  · rw [hrange, l10b3_iotaK_range, ← pkg.desc.derived, hfix]
  · intro z hz hc
    refine pkg.cent_triv z hz.1 fun x => ?_
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
    have hk : ψ k ∈ G₀ := by rw [← hpres.2.1.1]; exact ⟨k, rfl⟩
    have := hc ⟨ψ k, hk⟩
    rw [hθ k hk] at this
    exact this

end CFSG.StandardType.LieCore
