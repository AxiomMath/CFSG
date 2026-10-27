module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LemmaHTwE6
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IRootLine
public import CFSG.LieType.Steinberg.Exceptional.Fields
public import CFSG.LieType.Steinberg.TwistedE6.Datum
public import CFSG.LieType.Steinberg.TwistedE6.Generation
public import CFSG.Timmesfeld.LieEmbed.FieldEmbed

public section

namespace CFSG.StandardType.RCKK1I

open CFSG.Assembly CFSG.LieType.Universal CFSG.StandardType
open CFSG.Open (StatedLieTag StatedLieAdmissible)
open CFSG.Blueprint.Chevalley CFSG.LieType.RootSystem
open CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedE6
open CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Steinberg.Minuscule
open CFSG.Timmesfeld.LieEmbed

private def rckRLtwe6_alpha0 : Fin (Tag.rank .E6) → ℤ := ![1, 2, 2, 3, 2, 1]

private theorem rckRLtwe6_alpha0_mem : rckRLtwe6_alpha0 ∈ rootFinset Tag.E6 := by decide +kernel

private theorem rckRLtwe6_alpha0_rho : rho rckRLtwe6_alpha0 = rckRLtwe6_alpha0 := by
  decide +kernel

private theorem rckRLtwe6_proj_alpha0 : proj rckRLtwe6_alpha0 = CFSG.StandardType.RCKC1.rckHTwE6_high := by
  decide +kernel

private theorem rckRLtwe6_toWeight_alpha0 :
    MinData.toWeight rckRLtwe6_alpha0 (nd 1) = 1 := by
  rw [MinData.toWeight_apply]
  decide +kernel

private theorem rckRLtwe6_high_line
    {f : ℕ} (hf : 1 ≤ f) :
    ∃ ε : Multiplicative (GaloisField 2 f) ≃*
        twistedRootGroup (GaloisField 2 (2 * f)) (frobQ 2 f) CFSG.StandardType.RCKC1.rckHTwE6_high,
      RCKRootLineScalars (twistedRootGroup (GaloisField 2 (2 * f)) (frobQ 2 f) CFSG.StandardType.RCKC1.rckHTwE6_high)
        (GaloisField 2 f) ε := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hα₀ : IsRoot .E6 rckRLtwe6_alpha0 := mem_rootFinset.1 rckRLtwe6_alpha0_mem
  have hp : proj rckRLtwe6_alpha0 = CFSG.StandardType.RCKC1.rckHTwE6_high := rckRLtwe6_proj_alpha0
  have hfix : rho rckRLtwe6_alpha0 = rckRLtwe6_alpha0 := rckRLtwe6_alpha0_rho
  let φ : Multiplicative (GaloisField 2 f) →*
      twistedRootGroup (GaloisField 2 (2 * f)) (frobQ 2 f) CFSG.StandardType.RCKC1.rckHTwE6_high :=
    { toFun := fun a => ⟨xFixed (frobQ 2 f) hα₀ hfix (gfEmbed 2 f hf a.toAdd)
          (frobQ_gfEmbed 2 f hf a.toAdd), by
        rw [← hp]; exact xFixed_mem (frobQ 2 f) hα₀ hfix _ _⟩
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        change e6Data_valid.xm (GaloisField 2 (2 * f)) rckRLtwe6_alpha0
            (gfEmbed 2 f hf (Multiplicative.toAdd 1)) = 1
        rw [show Multiplicative.toAdd (1 : Multiplicative (GaloisField 2 f)) = 0 from rfl,
          map_zero, e6Data_valid.xm_zero]
      map_mul' := fun a b => by
        apply Subtype.ext
        apply Subtype.ext
        change e6Data_valid.xm (GaloisField 2 (2 * f)) rckRLtwe6_alpha0
            (gfEmbed 2 f hf (Multiplicative.toAdd (a * b))) =
          e6Data_valid.xm (GaloisField 2 (2 * f)) rckRLtwe6_alpha0
              (gfEmbed 2 f hf (Multiplicative.toAdd a)) *
            e6Data_valid.xm (GaloisField 2 (2 * f)) rckRLtwe6_alpha0
              (gfEmbed 2 f hf (Multiplicative.toAdd b))
        rw [toAdd_mul, map_add, e6Data_valid.xm_add] }
  have hφinj : Function.Injective φ := by
    intro a b hab
    have h2 := congrArg (fun z : twistedRootGroup (GaloisField 2 (2 * f)) (frobQ 2 f)
        CFSG.StandardType.RCKC1.rckHTwE6_high => (z : e6Data_valid.minGroup (GaloisField 2 (2 * f)))) hab
    change e6Data_valid.xm (GaloisField 2 (2 * f)) rckRLtwe6_alpha0
        (gfEmbed 2 f hf (Multiplicative.toAdd a)) =
      e6Data_valid.xm (GaloisField 2 (2 * f)) rckRLtwe6_alpha0
        (gfEmbed 2 f hf (Multiplicative.toAdd b)) at h2
    exact Multiplicative.toAdd.injective
      (gfEmbed_injective 2 f hf (e6Data_valid.xm_injective (GaloisField 2 (2 * f)) hα₀ h2))
  have hφsurj : Function.Surjective φ := by
    intro y
    obtain ⟨c, hc, hyc⟩ :=
      (mem_twistedRootGroup_iff_of_fixed (frobQ 2 f) hα₀ hp hfix
        (y : fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f))).1 y.2
    obtain ⟨l, hl⟩ := (frobQ_eq_iff_mem_range 2 f hf c).1 hc
    refine ⟨Multiplicative.ofAdd l, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change e6Data_valid.xm (GaloisField 2 (2 * f)) rckRLtwe6_alpha0
        (gfEmbed 2 f hf l) = (y : e6Data_valid.minGroup (GaloisField 2 (2 * f)))
    rw [hl, hyc]
  let ε : Multiplicative (GaloisField 2 f) ≃*
      twistedRootGroup (GaloisField 2 (2 * f)) (frobQ 2 f) CFSG.StandardType.RCKC1.rckHTwE6_high :=
    MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  have hεval : ∀ c : GaloisField 2 f,
      ((ε (Multiplicative.ofAdd c) : twistedRootGroup (GaloisField 2 (2 * f)) (frobQ 2 f)
          CFSG.StandardType.RCKC1.rckHTwE6_high) : e6Data_valid.minGroup (GaloisField 2 (2 * f))) =
        e6Data_valid.xm (GaloisField 2 (2 * f)) rckRLtwe6_alpha0 (gfEmbed 2 f hf c) :=
    fun _ => rfl
  refine ⟨ε, fun l hl => ?_⟩
  have hl0 : gfEmbed 2 f hf l ≠ 0 := by
    intro h
    exact hl (gfEmbed_injective 2 f hf (h.trans (map_zero (gfEmbed 2 f hf)).symm))
  let s : (GaloisField 2 (2 * f))ˣ := Units.mk0 (gfEmbed 2 f hf l) hl0
  have hsfix : frobQ 2 f (s : GaloisField 2 (2 * f)) = (s : GaloisField 2 (2 * f)) := by
    rw [Units.val_mk0]; exact frobQ_gfEmbed 2 f hf l
  obtain ⟨g, -, hgval⟩ := exists_hm_fixed (θ := frobQ 2 f) (a := nd 1) (t := s)
    (by decide) hsfix
  refine ⟨g, fun c => ?_⟩
  apply Subtype.ext
  change (g : e6Data_valid.minGroup (GaloisField 2 (2 * f))) *
      ((ε (Multiplicative.ofAdd c) : twistedRootGroup (GaloisField 2 (2 * f)) (frobQ 2 f)
        CFSG.StandardType.RCKC1.rckHTwE6_high) : e6Data_valid.minGroup (GaloisField 2 (2 * f))) *
      (g : e6Data_valid.minGroup (GaloisField 2 (2 * f)))⁻¹ =
    ((ε (Multiplicative.ofAdd (l * c)) : twistedRootGroup (GaloisField 2 (2 * f)) (frobQ 2 f)
        CFSG.StandardType.RCKC1.rckHTwE6_high) : e6Data_valid.minGroup (GaloisField 2 (2 * f)))
  rw [hεval c, hεval (l * c), hgval,
    e6Data_valid.hm_conj_xm (GaloisField 2 (2 * f)) hα₀ (nd 1) s (gfEmbed 2 f hf c),
    rckRLtwe6_toWeight_alpha0, zpow_one, Units.val_mk0]
  rw [map_mul]

private theorem rckRLtwe6_scalars_map_conj {U : Type*} [Group U] {R R' : Subgroup U} {g : U}
    (hg : R.map (MulAut.conj g).toMonoidHom = R') {F : Type} [Field F]
    {ε : Multiplicative F ≃* R} (hsc : RCKRootLineScalars R F ε) :
    ∃ ε' : Multiplicative F ≃* R', RCKRootLineScalars R' F ε' := by
  let φ : R →* R' :=
    { toFun := fun x => ⟨g * (x : U) * g⁻¹, by
        have hx : g * (x : U) * g⁻¹ ∈ R.map (MulAut.conj g).toMonoidHom :=
          ⟨x, x.2, by simp [MulAut.conj_apply]⟩
        rwa [hg] at hx⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        calc g * (↑(x * y) : U) * g⁻¹ = g * (↑x * ↑y) * g⁻¹ := rfl
          _ = (g * ↑x * g⁻¹) * (g * ↑y * g⁻¹) := by group) }
  have hφinj : Function.Injective φ := by
    intro x y hxy
    apply Subtype.ext
    have h := congrArg (fun z : R' => g⁻¹ * (z : U) * g) hxy
    simpa [φ, mul_assoc] using h
  have hφsurj : Function.Surjective φ := by
    intro y
    have hy : (y : U) ∈ R.map (MulAut.conj g).toMonoidHom := by rw [hg]; exact y.2
    obtain ⟨x, hxR, hxy⟩ := hy
    exact ⟨⟨x, hxR⟩, Subtype.ext (by simpa [φ, MulAut.conj_apply] using hxy)⟩
  let φe : R ≃* R' := MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  refine ⟨ε.trans φe, fun l hl => ?_⟩
  obtain ⟨h, hh⟩ := hsc l hl
  refine ⟨g * h * g⁻¹, fun t => ?_⟩
  change (g * h * g⁻¹) * ((φe (ε (Multiplicative.ofAdd t)) : R') : U) * (g * h * g⁻¹)⁻¹ =
    ((φe (ε (Multiplicative.ofAdd (l * t))) : R') : U)
  rw [show ((φe (ε (Multiplicative.ofAdd t)) : R') : U) =
        g * (ε (Multiplicative.ofAdd t) : U) * g⁻¹ from rfl,
      show ((φe (ε (Multiplicative.ofAdd (l * t))) : R') : U) =
        g * (ε (Multiplicative.ofAdd (l * t)) : U) * g⁻¹ from rfl,
      ← hh t]
  group

theorem rckK1I_rootLine_twistedE6
    {n f : ℕ} (hadm : StatedLieAdmissible .twistedE6 n 2 f) :
    0 < (ggU .twistedE6 n f).D.rank ∧ RCKRootLineAll (ggU .twistedE6 n f) f := by
  haveI : Fact (Nat.Prime 2) := ⟨hadm.1⟩
  have hf : 1 ≤ f := hadm.2.1
  have hrank : 0 < (ggU .twistedE6 n f).D.rank := by
    change 0 < 4
    norm_num
  refine ⟨hrank, ?_⟩
  change RCKRootLineAll (⟨twistedE6Group 2 f, twistedE6Datum 2 f⟩ : LieUniversal) f
  intro β hβ hlong
  obtain ⟨hε0, hsc0⟩ := rckRLtwe6_high_line (f := f) hf
  obtain ⟨w, γ₀, hγ₀, hmax, hβeq⟩ := hlong
  have hγ₀' : IsRoot .F4 γ₀ := isRoot_of_mem_twistedDatum_roots (frobQ 2 f) hγ₀
  have hhigh_mem : CFSG.StandardType.RCKC1.rckHTwE6_high ∈
      (twistedDatum (GaloisField 2 (2 * f)) (frobQ 2 f)).roots := by
    rw [twistedDatum_roots]
    exact mem_rootFinset.1 CFSG.StandardType.RCKC1.rckHTwE6_high_mem_rootFinset
  have hle1 : (∑ i, CFSG.StandardType.RCKC1.rckHTwE6_high i) ≤ ∑ i, γ₀ i := hmax CFSG.StandardType.RCKC1.rckHTwE6_high hhigh_mem
  have hle2 : (∑ i, γ₀ i) ≤ 11 := CFSG.StandardType.RCKC1.rckHTwE6_height_le γ₀ (mem_rootFinset.2 hγ₀')
  have hsumγ : (∑ i, γ₀ i) = 11 := by
    have := CFSG.StandardType.RCKC1.rckHTwE6_high_sum
    omega
  have hγ₀eq : γ₀ = CFSG.StandardType.RCKC1.rckHTwE6_high :=
    CFSG.StandardType.RCKC1.rckHTwE6_height_eleven_eq γ₀ (mem_rootFinset.2 hγ₀') hsumγ
  have hβeq' : β = weylAction (twistedDatum (GaloisField 2 (2 * f)) (frobQ 2 f)).isFiniteType w
      CFSG.StandardType.RCKC1.rckHTwE6_high := by rw [hβeq, hγ₀eq]
  have hθ : ∀ c, frobQ 2 f (frobQ 2 f c) = c := frobQ_frobQ 2 f hf
  have htop := iSup_twistedDatum_rootGroup (k := GaloisField 2 (2 * f)) (θ := frobQ 2 f) hθ
  have hct := twistedDatum_isCTGroupDatum (k := GaloisField 2 (2 * f)) (θ := frobQ 2 f) hθ htop
  let g := nrep (D := twistedDatum (GaloisField 2 (2 * f)) (frobQ 2 f))
    (n := nHat (frobQ 2 f)) (H := hHat (GaloisField 2 (2 * f)) (frobQ 2 f)) hct w
  have hg : ((twistedDatum (GaloisField 2 (2 * f)) (frobQ 2 f)).rootGroup CFSG.StandardType.RCKC1.rckHTwE6_high).map
      (MulAut.conj g).toMonoidHom =
      (twistedDatum (GaloisField 2 (2 * f)) (frobQ 2 f)).rootGroup β := by
    have h := (actsAs_nrep (D := twistedDatum (GaloisField 2 (2 * f)) (frobQ 2 f))
      (n := nHat (frobQ 2 f)) (H := hHat (GaloisField 2 (2 * f)) (frobQ 2 f)) hct w)
      CFSG.StandardType.RCKC1.rckHTwE6_high hhigh_mem
    exact h.trans (congrArg
      (fun γ => (twistedDatum (GaloisField 2 (2 * f)) (frobQ 2 f)).rootGroup γ)
      hβeq').symm
  obtain ⟨ε', hsc'⟩ := rckRLtwe6_scalars_map_conj hg hsc0
  exact ⟨GaloisField 2 f, inferInstance, inferInstance, ε',
    GaloisField.card 2 f (by omega), hsc'⟩

end CFSG.StandardType.RCKK1I
