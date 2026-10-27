module

public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane
public import CFSG.LocalAnalysis.StandardType.GGFamAssembly
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

theorem a6core_toral_SL
    {t : StatedLieTag} (ht : t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6)
    {f : ℕ} (hf : 1 ≤ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A K : Subgroup (ModGL (langTag t) GGL)} (hA : A ≤ ggFixGp t f) (hel : IsElemAbelian p A)
    (hcard : Nat.card A ≤ p ^ 2) (hT : IsToralSubgroup (langTag t) GGL A)
    (hK : IsComponentOf K (⁅ggFixGp t f, ggFixGp t f⁆ ⊓
      Subgroup.centralizer (A : Set (ModGL (langTag t) GGL)))) :
    ∃ s : ℕ, 1 ≤ s ∧ CFSG.StandardType.GGCompFieldAtSL (2 ^ (f * s)) K := by
  classical
  have hΦ : IsSteinbergEnd (langTag t) GGL (2 ^ f) (ggPhi t f) := by
    rcases ht with rfl | rfl | rfl | rfl
    · exact isSteinbergEnd_ggPhi
        (by unfold GGExcFive; exact Or.inr (Or.inl rfl)) f
    · exact isSteinbergEnd_ggPhi
        (by unfold GGExcFive; exact Or.inr (Or.inr (Or.inl rfl))) f
    · exact isSteinbergEnd_ggPhi
        (by unfold GGExcFive; exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))) f
    · exact isSteinbergEnd_ggPhi
        (by unfold GGExcFive; exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))) f
  have hAr : A ≤ ratPoints (ggPhi t f) := hA
  obtain ⟨w, g, hg, hlang, a₁, a₂, hmodelRaw, htorus1, htorus2, hd1p, hd2p, hmapRaw⟩ :=
    ggLieFrame_le_sq (τ := langTag t) hf hΦ hp hp2 hAr hel hcard hT
  let c : ModGL (langTag t) GGL →* ModGL (langTag t) GGL := (MulAut.conj g⁻¹).toMonoidHom
  let D : LangDatum (langTag t) GGL := langDatumOfPosition hΦ w g hg hlang
  have hmodel : (ratPoints (ggPhi t f)).map c = D.model := hmodelRaw
  have hmap : A.map c = Subgroup.closure
      {rootDiagUnit (langTag t) a₁, rootDiagUnit (langTag t) a₂} := hmapRaw
  obtain ⟨ρ, hρ⟩ := frobeniusOnRoots_proved (langTag t) GGL D
  have hfinΦ : Finite ↥(ratPoints (ggPhi t f)) :=
    finite_ratPoints (q := 2 ^ f)
      (Nat.one_lt_pow (n := f) (by omega) (by norm_num : (1 : ℕ) < 2))
      (isSteinbergEndZ_of_isSteinbergEnd hΦ)
  have hfinD : Finite ↥D.model := by
    have : Finite ↥(ratPoints (ggPhi t f)) := hfinΦ
    have hsurj : Function.Surjective (fun x : ↥(ratPoints (ggPhi t f)) =>
        (⟨c x, Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩⟩ :
          ↥((ratPoints (ggPhi t f)).map c))) := by
      rintro ⟨y, hy⟩
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      exact ⟨⟨x, hx⟩, rfl⟩
    have hfinMap : Finite ↥((ratPoints (ggPhi t f)).map c) := Finite.of_surjective _ hsurj
    rwa [hmodel] at hfinMap
  have hDq : D.q = 2 ^ f := rfl
  obtain ⟨S, hD, -⟩ := exists_langSetup_of_datum D ρ hρ hfinD hf hDq
  have hDqS : S.D.q = 2 ^ f := by
    rw [hD]
    exact hDq
  have hSΓ : S.Γ = D.Γ := by
    show S.D.Γ = D.Γ
    rw [hD]
  have hΓmap : (⁅ggFixGp t f, ggFixGp t f⁆ : Subgroup (ModGL (langTag t) GGL)).map c = D.Γ := by
    rw [Subgroup.map_commutator]
    have h1 : Subgroup.map c (ggFixGp t f) = D.model := by
      change Subgroup.map c (ratPoints (ggPhi t f)) = D.model
      exact hmodel
    rw [h1]
    rfl
  have hXmap : (⁅ggFixGp t f, ggFixGp t f⁆ ⊓
        Subgroup.centralizer (A : Set (ModGL (langTag t) GGL))).map c =
      D.Γ ⊓ Subgroup.centralizer
        (Subgroup.closure {rootDiagUnit (langTag t) a₁, rootDiagUnit (langTag t) a₂} :
          Set (ModGL (langTag t) GGL)) := by
    rw [Subgroup.map_inf (⁅ggFixGp t f, ggFixGp t f⁆)
      (Subgroup.centralizer (A : Set (ModGL (langTag t) GGL))) c (MulAut.conj g⁻¹).injective]
    rw [hΓmap, a6glue_map_centralizer (MulAut.conj g⁻¹) A, hmap]
  have hK' : IsComponentOf (K.map c)
      (D.Γ ⊓ Subgroup.centralizer
        (Subgroup.closure {rootDiagUnit (langTag t) a₁, rootDiagUnit (langTag t) a₂} :
          Set (ModGL (langTag t) GGL))) := by
    have h := a6glue_isComponentOf_map_mulEquiv (MulAut.conj g⁻¹) hK
    rwa [hXmap] at h
  let a : Fin 2 → Fin (langTag t).rank → GGLˣ := ![a₁, a₂]
  have hTa : ∀ u : Fin 2, rootDiagUnit (langTag t) (a u) ∈ S.D.torus := by
    intro u
    fin_cases u
    · change rootDiagUnit (langTag t) a₁ ∈ S.D.torus
      rw [hD]
      exact htorus1
    · change rootDiagUnit (langTag t) a₂ ∈ S.D.torus
      rw [hD]
      exact htorus2
  have hpa : ∀ u : Fin 2, ∀ j, a u j ^ p = 1 := by
    intro u j
    fin_cases u
    · exact pow_eq_one_of_rootDiagUnit_pow hd1p j
    · exact pow_eq_one_of_rootDiagUnit_pow hd2p j
  have hrange : Set.range (fun u : Fin 2 => rootDiagUnit (langTag t) (a u)) =
      {rootDiagUnit (langTag t) a₁, rootDiagUnit (langTag t) a₂} := by
    ext z
    constructor
    · rintro ⟨u, rfl⟩
      fin_cases u <;> simp [a]
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  have hK'' : CFSG.Open.IsComponentOf (K.map c)
      (S.Γ ⊓ Subgroup.centralizer
        (Set.range fun u : Fin 2 => rootDiagUnit (langTag t) (a u))) := by
    rw [hSΓ, hrange, ← Subgroup.centralizer_closure
      ({rootDiagUnit (langTag t) a₁, rootDiagUnit (langTag t) a₂} :
        Set (ModGL (langTag t) GGL))]
    exact CFSG.Assembly.isComponentOf_iff_open.mp hK'
  obtain ⟨i, -, hfield⟩ :=
    CFSG.StandardType.TableCRes.langFamilyCompFieldSL_holds (langTag t) GGL 5 p S
      (by rcases ht with rfl | rfl | rfl | rfl <;> simp [langTag]) hp hp2 (Fin 2) a hTa hpa
      (K.map c) hK''
  have hker : ∀ γ ∈ kernelRoots (Pi.monoidHom fun u : Fin 2 => rootCharHom (a u)),
      S.ρ γ ∈ kernelRoots (Pi.monoidHom fun u : Fin 2 => rootCharHom (a u)) :=
    fun γ hγ => CFSG.StandardType.TableCRes.rho_mem_kernelRoots_famChar S a hTa hγ
  let s : ℕ := componentOrbitLength S.ρ
    (componentRoots (Pi.monoidHom fun u : Fin 2 => rootCharHom (a u)) i)
  have hs : 1 ≤ s := by
    obtain ⟨hpos, -⟩ := CFSG.StandardType.TableCRes.fam_componentOrbitLength_spec S hker i
    exact Nat.succ_le_of_lt hpos
  refine ⟨s, hs, ?_⟩
  have hfield2 : CFSG.StandardType.GGCompFieldAtSL (2 ^ (f * s)) (K.map c) := by
    rw [pow_mul, ← hDqS]
    exact hfield
  exact CFSG.StandardType.GGCompFieldAtSL.congr hfield2
    (Subgroup.equivMapOfInjective K c (MulAut.conj g⁻¹).injective).symm

end CFSG.StandardType.A6Red
