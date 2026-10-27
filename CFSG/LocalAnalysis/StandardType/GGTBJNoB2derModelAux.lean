module

public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derModelDefs
public import CFSG.LocalAnalysis.StandardType.GGTBJConfigFacts
import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derExistsY
import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derYComp
import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherAutomorphismData
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnSympRed

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l48mA_ker_comp {L : Type*} [Group L] {R : Type*} [Group R]
    (θ : L ⧸ Subgroup.center L ≃* R) :
    (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))).ker =
      Subgroup.center L := by
  ext l
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
  constructor
  · intro h
    have h1 : QuotientGroup.mk' (Subgroup.center L) l = 1 := by
      apply θ.injective
      simpa using h
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  · intro h
    have hq : QuotientGroup.mk' (Subgroup.center L) l = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact h
    simp [hq]

open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag in
private lemma l48mA_lift {K : Type} [Field K] [Finite K] [CharP K 2] {r : ℕ} [NeZero r]
    {φ : MulAut (LargeEvenProj (LargeEvenSpGroup K r))}
    (hφ : φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K r))
      (LargeEvenGSpSet K r)) :
    ∃ g : LargeEvenProj (LargeEvenSpGroup K r), MulAut.conj g = φ := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  obtain ⟨A, hA, hgraph⟩ := hφ
  have hgsp : A ∈ gsp r K := by
    obtain ⟨μ, hμ, h⟩ := hA
    refine mem_gsp.mpr ⟨Units.mk0 μ hμ, ?_⟩
    simpa [largeEvenSpForm_def, formJ] using h
  have hconj : conjAut r K ⟨A, hgsp⟩ = φ := by
    ext x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    have hy : (↑y : CFSG.Open.StatedProj (CFSG.Open.StatedSp r K)) = proj r K y := rfl
    rw [hy, conjAut_proj]
    exact (hgraph y (conjSp r K ⟨A, hgsp⟩ y) (coe_conjSp _ y)).symm
  obtain ⟨x, hx⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnSympRed.exists_conjAut_eq_conj (m := r) (K := K) h2
      ⟨A, hgsp⟩
  exact ⟨CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj r K x, hx.symm.trans hconj⟩

theorem ggB2der_model_aux {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hA1 : GGB2derSympKnown) (hcfg : GGConfig 3 B Bs x L D J)
    (hJ : GGHasLabel (⟨.B2der, 0, 1⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J))
    (hBL : B ≤ Subgroup.normalizer (L : Set G)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (r : ℕ) (_ : NeZero r),
      Nat.card K = 2 ∧ 3 ≤ r ∧
      ∃ ψ : ↥L →* LargeEvenProj (LargeEvenSpGroup K r),
        Function.Surjective ψ ∧ ψ.ker = Subgroup.center ↥L ∧
        ∀ b : ↥B, ∃ g : LargeEvenProj (LargeEvenSpGroup K r), ∀ l : ↥L,
          ψ ((L.normalizerMonoidHom (Subgroup.inclusion hBL b)) l) = g * ψ l * g⁻¹ := by
  classical
  have hS : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hst : LargeEvenStandardType 3 B x L := hcfg.1.2.2.2.2.2.2.2
  have hpre : LargeEvenStdSubPre 3 B x L D J := hcfg.2.2.1
  have hB : IsElemAbelian 3 B := hS.1.1
  have hx1 : x ≠ 1 := hS.2.2.1
  obtain ⟨hxL, -, hx3, hperf⟩ := GGConfig.data_L hcfg
  have hDB : D ≤ B := hpre.1
  have hDcard : Nat.card D = 3 ^ 2 := hpre.2.2.1
  have hxD : x ∈ D := hpre.2.2.2.1
  obtain ⟨y, hyD, hyx, hgen⟩ := ggB2der_exists_y hB hDB hDcard hxD hx1
  obtain ⟨he1, he3, hcomp, hlabJ⟩ := ggB2der_y_component hcfg hJ hBL hyD hyx
  let eY : MulAut ↥L := L.normalizerMonoidHom (Subgroup.inclusion hBL y)
  let q : ↥L →* ↥L ⧸ Subgroup.center ↥L := QuotientGroup.mk' (Subgroup.center ↥L)
  obtain ⟨hLperf, lab, hlab2, hraw⟩ := hst.1
  have hrawA1 := (hA1.1 lab hlab2) _ hraw
  obtain ⟨R₀, _, I₀, F₀, hQ₀, hA1b⟩ := largeEvenRawDatum_exists hrawA1
  obtain ⟨hRsimple, hRna, θ₀, hP₀⟩ := hQ₀
  have hsurj₀ : Function.Surjective (θ₀.toMonoidHom.comp q) :=
    θ₀.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center ↥L))
  have hker₀ : (θ₀.toMonoidHom.comp q).ker = Subgroup.center ↥L := l48mA_ker_comp θ₀
  have hφy : ∃ φ ∈ I₀, ∀ l : ↥L, φ (θ₀ (QuotientGroup.mk' (Subgroup.center ↥L) l)) =
      θ₀ (QuotientGroup.mk' (Subgroup.center ↥L) (eY l)) := by
    obtain ⟨φ, hφI, hφind⟩ := hP₀.2.2 ((y : G)⁻¹) (B.inv_mem y.2)
    refine ⟨φ, hφI, fun l => ?_⟩
    have hrel : ((eY l : ↥L) : G) = ((y : G)⁻¹)⁻¹ * (l : G) * ((y : G)⁻¹) := by
      change ((L.normalizerMonoidHom (Subgroup.inclusion hBL y) l : ↥L) : G) = _
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      simp
    simpa using hφind l (eY l) hrel
  have hA1concl := hA1b ↥L (θ₀.toMonoidHom.comp q) hsurj₀ (by rw [hker₀]) hperf eY
    (by show eY ≠ 1; exact he1) (by show eY ^ 3 = 1; exact he3) hφy
    (J.subgroupOf L) hcomp hlabJ
  obtain ⟨htagC, hn1, hr3⟩ := hA1concl
  have hrawK : ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ∧
      ∃ θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (LargeEvenSpGroup K lab.rank),
        LargeEvenSplit 3 lab ∧
          B ≤ Subgroup.normalizer (L : Set G) ∧
          ∀ b ∈ B, ∃ φ ∈ LargeEvenMatConjImage
              (LargeEvenProjMk (LargeEvenSpGroup K lab.rank)) (LargeEvenGSpSet K lab.rank),
            LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ := by
    rcases htagC with htag | htag
    · have h := hraw
      dsimp only [CFSG.Assembly.LargeEvenRawDatumLegacy] at h
      rw [htag] at h
      obtain ⟨K, hKf, hKfin, hKcard, hcont⟩ := h
      obtain ⟨-, -, θ, hPθ⟩ := hcont
      exact ⟨K, hKf, hKfin, by rw [hn1] at hKcard; simpa using hKcard, θ, hPθ⟩
    · have h := hraw
      dsimp only [CFSG.Assembly.LargeEvenRawDatumLegacy] at h
      rw [htag] at h
      obtain ⟨K, hKf, hKfin, hKcard, hcont⟩ := h
      obtain ⟨-, -, θ, hPθ⟩ := hcont
      exact ⟨K, hKf, hKfin, by rw [hn1] at hKcard; simpa using hKcard, θ, hPθ⟩
  obtain ⟨K, hKf, hKfin, hKcard, θ, hPθ⟩ := hrawK
  letI : Field K := hKf
  letI : Finite K := hKfin
  haveI hCharP : CharP K 2 :=
    CFSG.RankThree.PartOne.charP_two_of_card_eq_pow (f := 1) (by simpa using hKcard)
  haveI hNeZero : NeZero lab.rank := ⟨by omega⟩
  let ψ : ↥L →* LargeEvenProj (LargeEvenSpGroup K lab.rank) := θ.toMonoidHom.comp q
  have hsurj : Function.Surjective ψ :=
    θ.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center ↥L))
  have hker : ψ.ker = Subgroup.center ↥L := l48mA_ker_comp θ
  refine ⟨K, hKf, hKfin, hCharP, lab.rank, hNeZero, hKcard, hr3, ψ, hsurj, hker, ?_⟩
  intro b
  obtain ⟨φ, hφI, hφind⟩ := hPθ.2.2 ((b : G)⁻¹) (B.inv_mem b.2)
  obtain ⟨g, hg⟩ := l48mA_lift hφI
  refine ⟨g, fun l => ?_⟩
  have hrel : ((L.normalizerMonoidHom (Subgroup.inclusion hBL b)) l : G) =
      ((b : G)⁻¹)⁻¹ * (l : G) * ((b : G)⁻¹) := by
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    simp
  have h := hφind l ((L.normalizerMonoidHom (Subgroup.inclusion hBL b)) l) hrel
  rw [← hg] at h
  rw [MulAut.conj_apply] at h
  exact h.symm

end CFSG.StandardType
