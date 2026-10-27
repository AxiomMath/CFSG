module

public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane
public import CFSG.LocalAnalysis.StandardType.GGFamF4Assembly
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

theorem a6core_toral_F4
    {t : StatedLieTag} (ht : t = .F4)
    {f : ℕ} (hf : 1 ≤ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A K : Subgroup (ModGL (langTag t) GGL)} (hA : A ≤ ggFixGp t f) (hel : IsElemAbelian p A)
    (hcard : Nat.card A ≤ p ^ 2) (hT : IsToralSubgroup (langTag t) GGL A)
    (hK : IsComponentOf K (⁅ggFixGp t f, ggFixGp t f⁆ ⊓
      Subgroup.centralizer (A : Set (ModGL (langTag t) GGL)))) :
    ∃ s : ℕ, 1 ≤ s ∧ (CFSG.StandardType.GGCompFieldAt (2 ^ (f * s)) K ∨
      (f = 1 ∧ s = 1 ∧ Nat.card K = 360 ∧ Nat.card (↥K ⧸ Subgroup.center ↥K) = 360)) := by
  subst t
  have hΦ : IsSteinbergEnd (langTag .F4) GGL (2 ^ f) (ggPhi .F4 f) :=
    isSteinbergEnd_ggPhi (by unfold GGExcFive; exact Or.inl rfl) f
  obtain ⟨w, g, hg, hlang, a₁, a₂, hmodelRaw, htorus1, htorus2, hp1, hp2T, hmapRaw⟩ :=
    ggLieFrame_le_sq (τ := langTag .F4) (L := GGL) hf hΦ hp hp2 hA hel hcard hT
  let c : ModGL (langTag .F4) GGL →* ModGL (langTag .F4) GGL := (MulAut.conj g⁻¹).toMonoidHom
  let D : LangDatum (langTag .F4) GGL := langDatumOfPosition hΦ w g hg hlang
  have hmodel : (ratPoints (ggPhi .F4 f)).map c = D.model := hmodelRaw
  have hmap : A.map c = Subgroup.closure
      {rootDiagUnit (langTag .F4) a₁, rootDiagUnit (langTag .F4) a₂} := hmapRaw
  obtain ⟨ρ, hρ⟩ := frobeniusOnRoots_proved (langTag .F4) GGL D
  have hfinΦ : Finite ↥(ratPoints (ggPhi .F4 f)) :=
    finite_ratPoints (q := 2 ^ f)
      (Nat.one_lt_pow (n := f) (by omega) (by norm_num : (1 : ℕ) < 2))
      (isSteinbergEndZ_of_isSteinbergEnd hΦ)
  have hfinD : Finite ↥D.model := by
    have : Finite ↥(ratPoints (ggPhi .F4 f)) := hfinΦ
    have hsurj : Function.Surjective (fun x : ↥(ratPoints (ggPhi .F4 f)) =>
        (⟨c x, Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩⟩ :
          ↥((ratPoints (ggPhi .F4 f)).map c))) := by
      rintro ⟨y, hy⟩
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      exact ⟨⟨x, hx⟩, rfl⟩
    have hfinMap : Finite ↥((ratPoints (ggPhi .F4 f)).map c) := Finite.of_surjective _ hsurj
    rwa [hmodel] at hfinMap
  have hDq : D.q = 2 ^ f := rfl
  have hΓmap : (⁅ggFixGp .F4 f, ggFixGp .F4 f⁆ :
      Subgroup (ModGL (langTag .F4) GGL)).map c = D.Γ := by
    rw [Subgroup.map_commutator]
    have h1 : Subgroup.map c (ggFixGp .F4 f) = D.model := by
      change Subgroup.map c (ratPoints (ggPhi .F4 f)) = D.model
      exact hmodel
    rw [h1]
    rfl
  have hXmap : (⁅ggFixGp .F4 f, ggFixGp .F4 f⁆ ⊓
        Subgroup.centralizer (A : Set (ModGL (langTag .F4) GGL))).map c =
      D.Γ ⊓ Subgroup.centralizer
        (Subgroup.closure {rootDiagUnit (langTag .F4) a₁, rootDiagUnit (langTag .F4) a₂} :
          Set (ModGL (langTag .F4) GGL)) := by
    rw [Subgroup.map_inf (⁅ggFixGp .F4 f, ggFixGp .F4 f⁆)
      (Subgroup.centralizer (A : Set (ModGL (langTag .F4) GGL))) c (MulAut.conj g⁻¹).injective]
    rw [hΓmap, a6glue_map_centralizer (MulAut.conj g⁻¹) A, hmap]
  have hK' : IsComponentOf (K.map c)
      (D.Γ ⊓ Subgroup.centralizer
        (Subgroup.closure {rootDiagUnit (langTag .F4) a₁, rootDiagUnit (langTag .F4) a₂} :
          Set (ModGL (langTag .F4) GGL))) := by
    have h := a6glue_isComponentOf_map_mulEquiv (MulAut.conj g⁻¹) hK
    rwa [hXmap] at h
  obtain ⟨S, hSD, _hSρ⟩ := exists_langSetup_of_datum D ρ hρ hfinD hf hDq
  have hT_fam : ∀ u : Fin 2, rootDiagUnit (langTag .F4)
      ((![a₁, a₂] : Fin 2 → Fin (langTag .F4).rank → GGLˣ) u) ∈ S.D.torus := by
    intro u
    fin_cases u
    · simpa [hSD] using htorus1
    · simpa [hSD] using htorus2
  have hap_fam : ∀ u j, ((![a₁, a₂] : Fin 2 → Fin (langTag .F4).rank → GGLˣ) u) j ^ p = 1 := by
    intro u
    fin_cases u
    · exact pow_eq_one_of_rootDiagUnit_pow (a := a₁) (by simpa using hp1)
    · exact pow_eq_one_of_rootDiagUnit_pow (a := a₂) (by simpa using hp2T)
  have hrange : Set.range (fun u : Fin 2 => rootDiagUnit (langTag .F4)
      ((![a₁, a₂] : Fin 2 → Fin (langTag .F4).rank → GGLˣ) u)) =
      ({rootDiagUnit (langTag .F4) a₁, rootDiagUnit (langTag .F4) a₂} :
        Set (ModGL (langTag .F4) GGL)) := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      fin_cases u <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
  have hK'' : CFSG.Open.IsComponentOf (K.map c) (S.Γ ⊓ Subgroup.centralizer
      (Set.range fun u : Fin 2 => rootDiagUnit (langTag .F4)
        ((![a₁, a₂] : Fin 2 → Fin (langTag .F4).rank → GGLˣ) u))) := by
    rw [← CFSG.Assembly.isComponentOf_iff_open]
    have hΓD : S.Γ = D.Γ := by
      rw [LangSetup.Γ, hSD]
    rw [hΓD, ← Subgroup.centralizer_closure, hrange]
    exact hK'
  obtain ⟨i, -, hfield⟩ :=
    CFSG.StandardType.TableCRes.langFamilyCompFieldF4_holds (L := GGL) (p₀ := 5) (p := p)
      (S := S) (ι := Fin 2) (a := ![a₁, a₂]) hp hp2 hT_fam hap_fam (K.map c) hK''
  refine ⟨componentOrbitLength S.ρ
      (componentRoots (CFSG.StandardType.TableCRes.famCharHom
        (![a₁, a₂] : Fin 2 → Fin (langTag .F4).rank → GGLˣ)) i), ?_, ?_⟩
  · have h := CFSG.StandardType.TableCRes.componentOrbitLength_pos S
        (Ψ := componentRoots (CFSG.StandardType.TableCRes.famCharHom
          (![a₁, a₂] : Fin 2 → Fin (langTag .F4).rank → GGLˣ)) i)
        (fun γ hγ => hγ.1.1)
    omega
  · rcases hfield with hfd | ⟨hq2, hs1, hcard1, hcardZ1⟩
    · left
      have hQ : S.D.q ^ componentOrbitLength S.ρ
          (componentRoots (CFSG.StandardType.TableCRes.famCharHom
            (![a₁, a₂] : Fin 2 → Fin (langTag .F4).rank → GGLˣ)) i) =
          2 ^ (f * componentOrbitLength S.ρ
            (componentRoots (CFSG.StandardType.TableCRes.famCharHom
              (![a₁, a₂] : Fin 2 → Fin (langTag .F4).rank → GGLˣ)) i)) := by
        rw [show S.D.q = 2 ^ f by rw [hSD, hDq], pow_mul]
      rw [← hQ]
      exact a6glue_ggCompFieldAt_congr hfd
        (Subgroup.equivMapOfInjective K c (MulAut.conj g⁻¹).injective).symm
    · right
      refine ⟨?_, hs1, ?_, ?_⟩
      · have hqD : D.q = 2 := by rw [← hSD]; exact hq2
        have h2f : 2 ^ f = 2 ^ 1 := by rw [← hDq, hqD, pow_one]
        exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) h2f
      · rw [← Subgroup.card_map_of_injective (f := c) (MulAut.conj g⁻¹).injective]
        exact hcard1
      · have eK : ↥K ≃* ↥(K.map c) :=
          Subgroup.equivMapOfInjective K c (MulAut.conj g⁻¹).injective
        have hZ : ↥K ⧸ Subgroup.center ↥K ≃*
            ↥(K.map c) ⧸ Subgroup.center ↥(K.map c) :=
          QuotientGroup.congr _ _ eK (Subgroup.map_center_eq eK)
        rw [Nat.card_congr hZ.toEquiv]
        exact hcardZ1

end CFSG.StandardType.A6Red
