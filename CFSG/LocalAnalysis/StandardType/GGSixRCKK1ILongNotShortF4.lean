module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IDefs
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviRootSL2
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotAutD
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcBruhat

public section

namespace CFSG.StandardType.RCKK1I

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
open CFSG.Open (StatedLieTag StatedLieAdmissible)
open CFSG.StandardType.RCKSmall (RCKSmallTag)
open CFSG.LieType.Steinberg
open CFSG.LieType.Universal.Symplectic
open CFSG.LieType.Universal.Symplectic.SpExtras
open TauCeti.GLSymplecticFin
open CFSG.StandardType.GGRootSp
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
open CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction.F4Pilot

private abbrev rckK1Ilnsf4_conj {K : Type*} [Group K] (a b : K) : Prop :=
  ∃ g : K, g * a * g⁻¹ = b

private theorem rckK1Ilnsf4_conj.symm {K : Type*} [Group K] {a b : K}
    (h : rckK1Ilnsf4_conj a b) : rckK1Ilnsf4_conj b a := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g⁻¹, by rw [← hg]; group⟩

private theorem rckK1Ilnsf4_conj.trans {K : Type*} [Group K] {a b c : K}
    (hab : rckK1Ilnsf4_conj a b) (hbc : rckK1Ilnsf4_conj b c) : rckK1Ilnsf4_conj a c := by
  obtain ⟨g, hg⟩ := hab
  obtain ⟨h, hh⟩ := hbc
  refine ⟨h * g, ?_⟩
  rw [show (h * g) * a * (h * g)⁻¹ = h * (g * a * g⁻¹) * h⁻¹ by group, hg, hh]

private theorem rckK1Ilnsf4_sum_le_rootR :
    ∀ δ ∈ rootFinset .F4, (∑ i, δ i) ≤ ∑ i, rootR i := by
  decide +kernel

private theorem rckK1Ilnsf4_eq_rootR_of_maxSum :
    ∀ γ ∈ rootFinset .F4,
      (∀ δ ∈ rootFinset .F4, (∑ i, δ i) ≤ (∑ i, γ i)) → γ = rootR := by
  decide +kernel

private theorem rckK1Ilnsf4_rootR_eq : rootR = orbitCertRoot .F4 47 := by
  decide +kernel

private theorem rckK1Ilnsf4_rootS_eq : rootS = orbitCertRoot .F4 44 := by
  decide +kernel

private theorem rckK1Ilnsf4_pair_rootR :
    ∃ i : Fin (Tag.rank .F4),
      (∑ j, Tag.cartan .F4 i j * rootR j) = 1 ∨
      (∑ j, Tag.cartan .F4 i j * rootR j) = -1 ∨
      (∑ j, Tag.cartan .F4 i j * rootR j) = 2 ∨
      (∑ j, Tag.cartan .F4 i j * rootR j) = -2 := by
  decide +kernel

private theorem rckK1Ilnsf4_pair_rootS :
    ∃ i : Fin (Tag.rank .F4),
      (∑ j, Tag.cartan .F4 i j * rootS j) = 1 ∨
      (∑ j, Tag.cartan .F4 i j * rootS j) = -1 ∨
      (∑ j, Tag.cartan .F4 i j * rootS j) = 2 ∨
      (∑ j, Tag.cartan .F4 i j * rootS j) = -2 := by
  decide +kernel

private theorem rckK1Ilnsf4_isConj_scalar
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (θ : Fin (Tag.rank .F4) → ℤ) (hθ : IsRoot .F4 θ) (i : Fin (Tag.rank .F4))
    (hc : (∑ j, Tag.cartan .F4 i j * θ j) = 1 ∨
          (∑ j, Tag.cartan .F4 i j * θ j) = -1 ∨
          (∑ j, Tag.cartan .F4 i j * θ j) = 2 ∨
          (∑ j, Tag.cartan .F4 i j * θ j) = -2)
    {c : K} (hc0 : c ≠ 0) :
    rckK1Ilnsf4_conj (⟨pinnedX .F4 K θ c, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .F4 K)
      ⟨pinnedX .F4 K θ 1, pinnedX_mem_adjointGroup _ _⟩ := by
  have hsqrt : ∀ l : K, ∃ s : K, s ^ 2 = l := fun l =>
    (Function.Injective.bijective_of_finite (CharTwo.sq_injective (R := K))).2 l
  have hpow : ∃ t : Kˣ, (((t ^ (∑ j, Tag.cartan .F4 i j * θ j) : Kˣ) : K)) = c := by
    rcases hc with h | h | h | h
    · exact ⟨Units.mk0 c hc0, by rw [h]; simp⟩
    · exact ⟨(Units.mk0 c hc0)⁻¹, by rw [h]; simp⟩
    · obtain ⟨s, hs⟩ := hsqrt c
      have hs0 : s ≠ 0 := by
        rintro rfl
        rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hs
        exact hc0 hs.symm
      exact ⟨Units.mk0 s hs0, by rw [h]; simpa using hs⟩
    · obtain ⟨s, hs⟩ := hsqrt c
      have hs0 : s ≠ 0 := by
        rintro rfl
        rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hs
        exact hc0 hs.symm
      exact ⟨(Units.mk0 s hs0)⁻¹, by rw [h]; simpa using hs⟩
  obtain ⟨t, ht⟩ := hpow
  refine rckK1Ilnsf4_conj.symm ?_
  refine ⟨(⟨torusElt .F4 K i t, torusElt_mem_adjointGroup i t⟩ : adjointGroup .F4 K), ?_⟩
  refine Subtype.ext ?_
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  have hhom : RootCentExc.torusHom .F4 K (Pi.mulSingle i t) = torusElt .F4 K i t :=
    RootCentExc.torusHom_mulSingle i t
  rw [← hhom]
  rw [RootCentExc.torusHom_conj_pinnedX (K := K) hθ (Pi.mulSingle i t) 1, mul_one]
  congr 1
  have hprod : (∏ j, (Pi.mulSingle i t) j ^ (∑ k, Tag.cartan .F4 j k * θ k)) =
      t ^ (∑ k, Tag.cartan .F4 i k * θ k) := by
    rw [Finset.prod_eq_single i
      (fun j _ hj => by rw [Pi.mulSingle_eq_of_ne hj, one_zpow])
      (fun h => absurd (Finset.mem_univ i) h), Pi.mulSingle_eq_same]
  rw [hprod]
  exact ht

private theorem rckK1Ilnsf4_isConj_long_of_mem
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {β : Fin (Tag.rank .F4) → ℤ} (hβ : IsRoot .F4 β)
    (hlong : GGLongRoot (f4Datum K) β)
    {x : adjointGroup .F4 K} (hx : x ∈ (f4Datum K).rootGroup β) (hx1 : x ≠ 1) :
    rckK1Ilnsf4_conj x ⟨f4x K 47 1, pinnedX_mem_adjointGroup _ _⟩ := by
  obtain ⟨w, γ₀, hγ₀, hmax, hβeq⟩ := hlong
  have hγ₀R : γ₀ = rootR :=
    rckK1Ilnsf4_eq_rootR_of_maxSum γ₀ (mem_rootFinset.2 (mem_adjDatum_roots.mp hγ₀))
      (fun δ hδ => hmax δ (mem_adjDatum_roots.mpr (mem_rootFinset.1 hδ)))
  have hwβ : w⁻¹ • β = rootR := by
    rw [hβeq, hγ₀R]
    exact inv_smul_smul w rootR
  set g₁ : adjointGroup .F4 K := weylRepC K w⁻¹ with hg₁def
  have hmap := map_conj_weylRepC_rootGroup (K := K) w⁻¹ hβ
  rw [hwβ] at hmap
  have hx' : g₁ * x * g₁⁻¹ ∈ (f4Datum K).rootGroup rootR := by
    rw [← hmap]
    exact ⟨x, hx, rfl⟩
  have hrootR : IsRoot .F4 rootR := isRoot_rootR
  obtain ⟨c, hc⟩ := (mem_rootGroup_iff_pinnedX hrootR).1 hx'
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [pinnedX_zero] at hc
    apply hx1
    have h1 : g₁ * x * g₁⁻¹ = 1 := Subtype.ext hc.symm
    calc x = g₁⁻¹ * (g₁ * x * g₁⁻¹) * g₁ := by group
      _ = 1 := by rw [h1]; group
  obtain ⟨i, hi⟩ := rckK1Ilnsf4_pair_rootR
  have hsc := rckK1Ilnsf4_isConj_scalar rootR hrootR i hi hc0
  have hf4x : (⟨pinnedX .F4 K rootR 1, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .F4 K) =
      ⟨f4x K 47 1, pinnedX_mem_adjointGroup _ _⟩ := by
    rw [rckK1Ilnsf4_rootR_eq]
    rfl
  rw [hf4x] at hsc
  have hmid : rckK1Ilnsf4_conj x
      (⟨pinnedX .F4 K rootR c, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .F4 K) := by
    exact ⟨g₁, Subtype.ext (by simpa using hc.symm)⟩
  exact hmid.trans hsc

private theorem rckK1Ilnsf4_iform_two_of_not_long
    {K : Type} [Field K]
    {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ)
    (hshort : ¬ GGLongRoot (f4Datum K) γ) : iform γ γ = 2 := by
  rcases iform_self_eq_two_or_four hγ with h | h4
  · exact h
  · exfalso
    apply hshort
    obtain ⟨w, hw⟩ := exists_smul_eq_rootR hγ h4
    refine ⟨w⁻¹, rootR, mem_adjDatum_roots.mpr isRoot_rootR, ?_, ?_⟩
    · intro δ hδ
      exact rckK1Ilnsf4_sum_le_rootR δ (mem_rootFinset.2 (mem_adjDatum_roots.mp hδ))
    · rw [← hw]
      exact (inv_smul_smul w γ).symm

private theorem rckK1Ilnsf4_isConj_short_of_mem
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ)
    (hshort : ¬ GGLongRoot (f4Datum K) γ)
    {y : adjointGroup .F4 K} (hy : y ∈ (f4Datum K).rootGroup γ) (hy1 : y ≠ 1) :
    rckK1Ilnsf4_conj y ⟨f4x K 44 1, pinnedX_mem_adjointGroup _ _⟩ := by
  have h2 := rckK1Ilnsf4_iform_two_of_not_long hγ hshort
  obtain ⟨w, hw⟩ := exists_smul_eq_rootS hγ h2
  set g₂ : adjointGroup .F4 K := weylRepC K w with hg₂def
  have hmap := map_conj_weylRepC_rootGroup (K := K) w hγ
  rw [hw] at hmap
  have hy' : g₂ * y * g₂⁻¹ ∈ (f4Datum K).rootGroup rootS := by
    rw [← hmap]
    exact ⟨y, hy, rfl⟩
  have hrootS : IsRoot .F4 rootS := isRoot_rootS
  obtain ⟨d, hd⟩ := (mem_rootGroup_iff_pinnedX hrootS).1 hy'
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [pinnedX_zero] at hd
    apply hy1
    have h1 : g₂ * y * g₂⁻¹ = 1 := Subtype.ext hd.symm
    calc y = g₂⁻¹ * (g₂ * y * g₂⁻¹) * g₂ := by group
      _ = 1 := by rw [h1]; group
  obtain ⟨i, hi⟩ := rckK1Ilnsf4_pair_rootS
  have hsc := rckK1Ilnsf4_isConj_scalar rootS hrootS i hi hd0
  have hf4x : (⟨pinnedX .F4 K rootS 1, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .F4 K) =
      ⟨f4x K 44 1, pinnedX_mem_adjointGroup _ _⟩ := by
    rw [rckK1Ilnsf4_rootS_eq]
    rfl
  rw [hf4x] at hsc
  have hmid : rckK1Ilnsf4_conj y
      (⟨pinnedX .F4 K rootS d, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .F4 K) := by
    exact ⟨g₂, Subtype.ext (by simpa using hd.symm)⟩
  exact hmid.trans hsc

theorem rckK1I_longNotShort_F4
    {n f : ℕ} (hadm : StatedLieAdmissible .F4 n 2 f)
    {β γ : Fin (ggU .F4 n f).D.rank → ℤ} (hβ : β ∈ (ggU .F4 n f).D.roots)
    (hlong : GGLongRoot (ggU .F4 n f).D β)
    (hγ : γ ∈ (ggU .F4 n f).D.roots) (hshort : ¬ GGLongRoot (ggU .F4 n f).D γ)
    (h2γ : 2 • γ ∉ (ggU .F4 n f).D.roots) (u : (ggU .F4 n f).K) :
    (ggU .F4 n f).D.rootGroup β ⊓
      ((ggU .F4 n f).D.rootGroup γ).map (MulAut.conj u).toMonoidHom = ⊥ := by
  change (f4Datum (GaloisField 2 f)).rootGroup β ⊓
    ((f4Datum (GaloisField 2 f)).rootGroup γ).map (MulAut.conj u).toMonoidHom = ⊥
  change β ∈ (f4Datum (GaloisField 2 f)).roots at hβ
  change γ ∈ (f4Datum (GaloisField 2 f)).roots at hγ
  change GGLongRoot (f4Datum (GaloisField 2 f)) β at hlong
  change ¬ GGLongRoot (f4Datum (GaloisField 2 f)) γ at hshort
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxβ, hxγ⟩ := hx
  by_contra hx1
  have hβroot : IsRoot .F4 β := mem_adjDatum_roots.mp hβ
  have hγroot : IsRoot .F4 γ := mem_adjDatum_roots.mp hγ
  have hconjβ : rckK1Ilnsf4_conj x
      (⟨f4x (GaloisField 2 f) 47 1, pinnedX_mem_adjointGroup _ _⟩ :
        adjointGroup .F4 (GaloisField 2 f)) :=
    rckK1Ilnsf4_isConj_long_of_mem hβroot hlong hxβ hx1
  obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.1 hxγ
  have hy1 : y ≠ 1 := by
    intro hy1'
    apply hx1
    rw [← hyeq, hy1']
    exact map_one _
  have hconjγ : rckK1Ilnsf4_conj y
      (⟨f4x (GaloisField 2 f) 44 1, pinnedX_mem_adjointGroup _ _⟩ :
        adjointGroup .F4 (GaloisField 2 f)) :=
    rckK1Ilnsf4_isConj_short_of_mem hγroot hshort hy hy1
  have hyx : rckK1Ilnsf4_conj y x := by
    refine ⟨u, ?_⟩
    change u * y * u⁻¹ = x
    rw [← MulAut.conj_apply]
    exact hyeq
  have hfull : rckK1Ilnsf4_conj
      (⟨f4x (GaloisField 2 f) 47 1, pinnedX_mem_adjointGroup _ _⟩ :
        adjointGroup .F4 (GaloisField 2 f))
      (⟨f4x (GaloisField 2 f) 44 1, pinnedX_mem_adjointGroup _ _⟩ :
        adjointGroup .F4 (GaloisField 2 f)) :=
    hconjβ.symm.trans (hyx.symm.trans hconjγ)
  obtain ⟨g, hg⟩ := hfull
  have hg' : (g : ModGL .F4 (GaloisField 2 f)) * f4x (GaloisField 2 f) 47 1 *
      (g : ModGL .F4 (GaloisField 2 f))⁻¹ = f4x (GaloisField 2 f) 44 1 := by
    have h := congrArg Subtype.val hg
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h
  exact CFSG.SeitzReduction.conj_f4x_47_ne_f4x_44 (K := GaloisField 2 f) g.2 hg'

end CFSG.StandardType.RCKK1I
