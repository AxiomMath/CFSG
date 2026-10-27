module

public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5RC0Input
public import CFSG.LocalAnalysis.StandardType.GGLieBridgeHolds
public import CFSG.LocalAnalysis.StandardType.GGLieCoreSmallSetup
public import CFSG.LocalAnalysis.StandardType.GGLieCoreA3DictPhi
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.FrobeniusOnRoots
public import Certificates.Certificate1952
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate3951
public import Certificates.Certificate8033
public import Certificates.Certificate8064
public import Certificates.Certificate13659
public import Certificates.Certificate13660
public import Certificates.Certificate13604
public import Certificates.Certificate13605
public import Certificates.Certificate13691
public import Certificates.Certificate13720
public import Certificates.Certificate13721
public import Certificates.Certificate13722
public import Certificates.Certificate13723
public import Certificates.Certificate13724
import CFSG.LocalAnalysis.StandardType.GGLangAlgebraic
import CFSG.LocalAnalysis.StandardType.GGA6GlueTransport

public section

namespace CFSG.StandardType.A6Red

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open (StatedLieTag)
open scoped commutatorElement
open CFSG.StandardType.LieCore
open CFSG.StandardType.ExcFramesHalf (IsToralSubgroup)

private theorem a6core_nontoral_of_steinbergEnd
    (hRC0 : CFSG.StandardType.TableCRes.LangNontoralCompField)
    {f : ℕ} (hf : 1 ≤ f)
    {Φ : ModGL Tag.E6 GGL →* ModGL Tag.E6 GGL} (hΦ : IsSteinbergEnd Tag.E6 GGL (2 ^ f) Φ)
    {A K : Subgroup (ModGL Tag.E6 GGL)} (hA : A ≤ ratPoints Φ) (hel : IsElemAbelian 3 A)
    (hcard : Nat.card A = 3 ^ 2) (hnt : ¬ IsToralSubgroup Tag.E6 GGL A)
    (hK : IsComponentOf K (⁅ratPoints Φ, ratPoints Φ⁆ ⊓
      Subgroup.centralizer (A : Set (ModGL Tag.E6 GGL)))) :
    CFSG.StandardType.GGCompFieldAt (2 ^ f) K ∨
      (f = 1 ∧ Nat.card K = 6048 ∧ Nat.card (↥K ⧸ Subgroup.center ↥K) = 6048) := by
  classical
  have hbot : IsElemAbelian 3 (⊥ : Subgroup (ModGL Tag.E6 GGL)) :=
    ⟨⟨⟨fun u v => Subtype.ext (by
        show (u : ModGL Tag.E6 GGL) * v = v * u
        simp [Subgroup.mem_bot.mp u.2, Subgroup.mem_bot.mp v.2])⟩⟩,
      fun z hz => by rw [Subgroup.mem_bot.mp hz, one_pow]⟩
  have hbotcard : Nat.card (⊥ : Subgroup (ModGL Tag.E6 GGL)) ≤ 3 ^ 2 := by
    rw [Subgroup.card_bot]
    norm_num
  have hbottoral : IsToralSubgroup Tag.E6 GGL (⊥ : Subgroup (ModGL Tag.E6 GGL)) :=
    ⟨1, one_mem _, fun x hx => by
      rw [Subgroup.mem_bot.mp hx]
      simp⟩
  obtain ⟨w, g, hg, hlang, a₁, a₂, hmodelRaw, htorus1, htorus2, hp1, hp2, hmapRaw⟩ :=
    ggLieFrame_le_sq (τ := Tag.E6) (L := GGL) hf hΦ Nat.prime_three (by norm_num)
      (A := ⊥) bot_le hbot hbotcard hbottoral
  let c : ModGL Tag.E6 GGL →* ModGL Tag.E6 GGL := (MulAut.conj g⁻¹).toMonoidHom
  let D : LangDatum Tag.E6 GGL := langDatumOfPosition hΦ w g hg hlang
  have hmodel : (ratPoints Φ).map c = D.model := hmodelRaw
  have hDq : D.q = 2 ^ f := rfl
  have hfinΦ : Finite ↥(ratPoints Φ) :=
    finite_ratPoints (q := 2 ^ f)
      (Nat.one_lt_pow (n := f) (by omega) (by norm_num : (1 : ℕ) < 2))
      (isSteinbergEndZ_of_isSteinbergEnd hΦ)
  have hfinD : Finite ↥D.model := by
    have : Finite ↥(ratPoints Φ) := hfinΦ
    have hsurj : Function.Surjective (fun x : ↥(ratPoints Φ) =>
        (⟨c x, Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩⟩ :
          ↥((ratPoints Φ).map c))) := by
      rintro ⟨y, hy⟩
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      exact ⟨⟨x, hx⟩, rfl⟩
    have hfinMap : Finite ↥((ratPoints Φ).map c) := Finite.of_surjective _ hsurj
    rwa [hmodel] at hfinMap
  obtain ⟨ρ, hρ⟩ := frobeniusOnRoots_proved Tag.E6 GGL D
  obtain ⟨S, hSD, _hSρ⟩ := exists_langSetup_of_datum D ρ hρ hfinD hf hDq
  have hSq : S.D.q = 2 ^ f := by rw [hSD, hDq]
  have hSAlg : S.IsAlgebraic :=
    CFSG.StandardType.langSetup_isAlgebraic_of_zmod_two S hSq
  have hSDΓ : S.Γ = D.Γ := by rw [LangSetup.Γ, hSD]
  have hAmap : A.map c ≤ S.D.model := by
    rw [hSD]
    exact (Subgroup.map_mono hA).trans (le_of_eq hmodel)
  have hAel' : IsElemAbelian 3 (A.map c) := isElemAbelian_map_hom hel c
  have hAcard' : Nat.card (A.map c) = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective (K := A) (f := c) (MulAut.conj g⁻¹).injective,
      hcard]
  have hAnt' : ¬ ∃ h ∈ adjointGroup Tag.E6 GGL,
      ∀ x ∈ A.map c, h⁻¹ * x * h ∈ torusGroup Tag.E6 GGL := by
    rintro ⟨h, hh, hhA⟩
    apply hnt
    refine ⟨g * h, Subgroup.mul_mem _ hg hh, fun x hx => ?_⟩
    have hxc : c x ∈ A.map c := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    have hconj := hhA (c x) hxc
    have heq : (g * h)⁻¹ * x * (g * h) = h⁻¹ * c x * h := by
      change (g * h)⁻¹ * x * (g * h) = h⁻¹ * (g⁻¹ * x * g) * h
      group
    rw [heq]
    exact hconj
  have hΓmap : (⁅ratPoints Φ, ratPoints Φ⁆ : Subgroup (ModGL Tag.E6 GGL)).map c = D.Γ := by
    rw [Subgroup.map_commutator, hmodel]
    rfl
  have hXmap : ((⁅ratPoints Φ, ratPoints Φ⁆ ⊓
        Subgroup.centralizer (A : Set (ModGL Tag.E6 GGL)))).map c =
      S.Γ ⊓ Subgroup.centralizer (A.map c : Set (ModGL Tag.E6 GGL)) := by
    rw [Subgroup.map_inf (⁅ratPoints Φ, ratPoints Φ⁆)
      (Subgroup.centralizer (A : Set (ModGL Tag.E6 GGL))) c (MulAut.conj g⁻¹).injective,
      hΓmap, a6glue_map_centralizer (MulAut.conj g⁻¹) A, hSDΓ]
  have hK' : CFSG.Open.IsComponentOf (K.map c)
      (S.Γ ⊓ Subgroup.centralizer (A.map c : Set (ModGL Tag.E6 GGL))) := by
    have h := a6glue_isComponentOf_map_mulEquiv (MulAut.conj g⁻¹) hK
    rw [hXmap] at h
    exact (CFSG.Assembly.isComponentOf_iff_open).1 h
  have hres := hRC0 GGL 5 S hSAlg (A.map c) hAmap hAel' hAcard' hAnt' (K.map c) hK'
  have hiso : ↥K ≃* ↥(K.map c) :=
    Subgroup.equivMapOfInjective K c (MulAut.conj g⁻¹).injective
  rcases hres with hfield | ⟨hSq2, _hA9, hKc, hQc⟩
  · left
    have hfield' := hfield
    rw [hSq] at hfield'
    exact a6glue_ggCompFieldAt_congr hfield' hiso.symm
  · right
    refine ⟨?_, ?_, ?_⟩
    · have hpow : 2 ^ f = 2 ^ 1 := by
        rw [← hSq]
        simpa using hSq2
      exact Nat.pow_right_injective (by norm_num) hpow
    · rw [← Subgroup.card_map_of_injective (K := K) (f := c)
        (MulAut.conj g⁻¹).injective]
      exact hKc
    · have hqcard : Nat.card (↥K ⧸ Subgroup.center ↥K) =
          Nat.card (↥(K.map c) ⧸ Subgroup.center ↥(K.map c)) :=
        Nat.card_congr (QuotientGroup.congr (Subgroup.center K)
          (Subgroup.center (K.map c)) hiso (Subgroup.map_center_eq hiso)).toEquiv
      exact hqcard.trans hQc

theorem a6core_nontoral_E6
    (hRC0 : CFSG.StandardType.TableCRes.LangNontoralCompField)
    {t : StatedLieTag} (ht : t = .E6 ∨ t = .twistedE6)
    {f : ℕ} (hf : 1 ≤ f)
    {A K : Subgroup (ModGL (langTag t) GGL)} (hA : A ≤ ggFixGp t f) (hel : IsElemAbelian 3 A)
    (hcard : Nat.card A = 3 ^ 2) (hnt : ¬ IsToralSubgroup (langTag t) GGL A)
    (hK : IsComponentOf K (⁅ggFixGp t f, ggFixGp t f⁆ ⊓
      Subgroup.centralizer (A : Set (ModGL (langTag t) GGL)))) :
    CFSG.StandardType.GGCompFieldAt (2 ^ f) K ∨
      (f = 1 ∧ Nat.card K = 6048 ∧ Nat.card (↥K ⧸ Subgroup.center ↥K) = 6048) := by
  rcases ht with rfl | rfl
  · exact a6core_nontoral_of_steinbergEnd hRC0 hf
      (isSteinbergEnd_ggPhi (t := .E6)
        (by unfold GGExcFive; exact Or.inr (Or.inl rfl)) f)
      hA hel hcard hnt hK
  · exact a6core_nontoral_of_steinbergEnd hRC0 hf
      (isSteinbergEnd_ggPhi (t := .twistedE6)
        (by unfold GGExcFive; exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))) f)
      hA hel hcard hnt hK

end CFSG.StandardType.A6Red

end
