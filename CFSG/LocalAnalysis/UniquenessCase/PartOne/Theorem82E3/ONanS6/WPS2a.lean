module

public import CFSG.GroupTheory.ConjActionModPCore
public import CFSG.GroupTheory.CoprimeActionSupport.CentralizerOnQuotientMembership
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CComponents
public import CFSG.RankThree.PartTwo.Sec17.Item17Res15ProofAut
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanK8K9
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanK2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WS6

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor IsAlt)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
open CFSG.Blueprint (LieModel)
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}

theorem card_range_dvd {H K : Type*} [Group H] [Finite H] [Group K] (f : H →* K) :
    Nat.card f.range ∣ Nat.card H := by
  have h1 : Nat.card f.range = Nat.card (H ⧸ f.ker) :=
    (Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv).symm
  rw [h1]
  exact Subgroup.card_quotient_dvd_card f.ker

theorem exists_normal_simple_quotient (H : Type*) [Group H] [Finite H] [Nontrivial H] :
    ∃ (N : Subgroup H) (_ : N.Normal), N ≠ ⊤ ∧ IsSimpleGroup (H ⧸ N) := by
  classical
  obtain ⟨N, -, hmax⟩ := Finite.exists_le_maximal
    (p := fun N : Subgroup H => N.Normal ∧ N ≠ ⊤) (a := ⊥) ⟨inferInstance, bot_ne_top⟩
  have hNnorm : N.Normal := hmax.prop.1
  have hNne : N ≠ ⊤ := hmax.prop.2
  refine ⟨N, hNnorm, hNne, ?_⟩
  haveI : N.Normal := hNnorm
  haveI : Nontrivial (H ⧸ N) := QuotientGroup.nontrivial_iff.mpr hNne
  refine IsSimpleGroup.mk ?_
  intro K hK
  have hK'norm : (K.comap (QuotientGroup.mk' N)).Normal := Subgroup.normal_comap _
  have hNle : N ≤ K.comap (QuotientGroup.mk' N) := QuotientGroup.le_comap_mk' N K
  by_cases htop : K.comap (QuotientGroup.mk' N) = ⊤
  · right
    rw [← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) K, htop,
      Subgroup.map_top_of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)]
  · left
    have hK'eq : K.comap (QuotientGroup.mk' N) = N :=
      le_antisymm (hmax.2 ⟨hK'norm, htop⟩ hNle) hNle
    have h1 : K = Subgroup.map (QuotientGroup.mk' N) N := by
      rw [← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) K, hK'eq]
    have h2 : Subgroup.map (QuotientGroup.mk' N) N = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk' N]
    rw [h1, h2]

theorem normalizer_pCoreOf_le {L M : Subgroup G}
    (h : M ≤ Subgroup.normalizer (L : Set G)) :
    M ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 L : Set G) := by
  have key : ∀ (m : G), m ∈ Subgroup.normalizer (L : Set G) →
      ∀ x ∈ CFSG.Open.pCoreOf 2 L, m * x * m⁻¹ ∈ CFSG.Open.pCoreOf 2 L := by
    intro m hm x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have hfix := Subgroup.characteristic_iff_map_eq.mp
      (CFSG.pCore_characteristic (p := 2) (G := ↥L))
      (Subgroup.normalizerMonoidHom (H := L) ⟨m, hm⟩)
    have hmem : (Subgroup.normalizerMonoidHom (H := L) ⟨m, hm⟩) y ∈
        CFSG.Open.pCore 2 ↥L := by
      rw [← hfix]
      exact Subgroup.mem_map_of_mem
        (MulEquiv.toMonoidHom (Subgroup.normalizerMonoidHom (H := L) ⟨m, hm⟩)) hy
    rw [CFSG.Open.pCoreOf, Subgroup.mem_map]
    refine ⟨_, hmem, ?_⟩
    change ((Subgroup.normalizerMonoidHom (H := L) ⟨m, hm⟩) y : G) = m * y * m⁻¹
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key m (h hm) x
  · intro hx
    have hm' : m⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
      (Subgroup.normalizer (L : Set G)).inv_mem (h hm)
    have hthis := key m⁻¹ hm' (m * x * m⁻¹) hx
    simp only [inv_inv] at hthis
    have heq : m⁻¹ * (m * x * m⁻¹) * m = x := by group
    rwa [heq] at hthis

theorem map_ker_conjModPCore_eq_centralizerOnQuotient (c : Ctx82E3 D) :
    (CFSG.GroupTheory.conjModPCore 2 c.L D.M c.le_normalizer_L).ker.map D.M.subtype =
      CFSG.LocalAnalysis.RankThreeUC.centralizerOnQuotient D.M
        (CFSG.Open.pCoreOf 2 c.L) c.L := by
  ext m
  rw [CFSG.GroupTheory.mem_map_ker_conjModPCore_iff,
    CFSG.GroupTheory.CoprimeActionSupport.CentralizerOnQuotientMembership.mem_centralizerOnQuotient]
  constructor
  · rintro ⟨hmM, hcomm⟩
    exact ⟨hmM, c.le_normalizer_L hmM, normalizer_pCoreOf_le c.le_normalizer_L hmM, hcomm⟩
  · rintro ⟨hmM, -, -, hcomm⟩
    exact ⟨hmM, hcomm⟩

theorem noSzSection_mulAut_Lbar
    (c : Ctx82E3 D) (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) :
    CFSG.RankThree.PartTwo.Sec16.Steps166.NoSzSection (MulAut c.Lbar) := by
  haveI : Group.IsPerfect c.Lbar := Group.isPerfect_def.2 hON.1.1
  have hT : IsTripleCover c.Lbar CFSG.Blueprint.NativeSporadic.ON := ⟨hON.2.1, hON.2.2⟩
  exact CFSG.RankThree.PartTwo.Sec17.Proof17Res15.noSzSection_mulAut_of_isTripleCover hT
    CFSG.RankThree.PartTwo.Sec17.Proof17Res15.noSzSection_mulAut_on

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor IsAlt)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
open CFSG.Blueprint (LieModel)
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}
variable (c : Ctx82E3 D) {P A : Subgroup G} {a : G}

theorem perfect_threePrime_le_centralizerOnQuotient'
    (hPSz : CFSG.RankThree.PartTwo.KFacts.KPSz) (hK8 : K8Cat)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) :
    ∀ W : Subgroup G, W ≤ D.M → Group.IsPerfect ↥W → ¬ 3 ∣ Nat.card W →
      W ≤ CFSG.LocalAnalysis.RankThreeUC.centralizerOnQuotient D.M
        (CFSG.Open.pCoreOf 2 c.L) c.L := by
  intro W hWM hperf h3
  have hMtop : D.M ≠ ⊤ := by
    obtain ⟨p, hp⟩ := c.sig_nonempty
    exact (c.sig1_sp p (c.sigma_subset_sigmaOne hp)).1
  intro w hwW
  by_contra hwC
  let ρ : ↥W →* MulAut c.Lbar :=
    (CFSG.GroupTheory.conjModPCore 2 c.L D.M c.le_normalizer_L).comp (Subgroup.inclusion hWM)
  have hρne : ρ ≠ 1 := by
    intro h1
    apply hwC
    have hker : (⟨w, hWM hwW⟩ : ↥D.M) ∈
        (CFSG.GroupTheory.conjModPCore 2 c.L D.M c.le_normalizer_L).ker := by
      rw [MonoidHom.mem_ker]
      have hval : ρ ⟨w, hwW⟩ =
          CFSG.GroupTheory.conjModPCore 2 c.L D.M c.le_normalizer_L ⟨w, hWM hwW⟩ := rfl
      have hx1 : ρ ⟨w, hwW⟩ = 1 := by rw [h1]; rfl
      rw [hval] at hx1
      exact hx1
    have hmem : w ∈ (CFSG.GroupTheory.conjModPCore 2 c.L D.M c.le_normalizer_L).ker.map
        D.M.subtype := Subgroup.mem_map.mpr ⟨⟨w, hWM hwW⟩, hker, rfl⟩
    rw [map_ker_conjModPCore_eq_centralizerOnQuotient] at hmem
    exact hmem
  haveI : Group.IsPerfect ↥W := hperf
  haveI : Group.IsPerfect ↥ρ.range := Group.IsPerfect.range (f := ρ)
  have hrange : ρ.range ≠ ⊥ := by
    intro hbot
    exact hρne (MonoidHom.range_eq_bot_iff.mp hbot)
  haveI : Nontrivial ↥ρ.range := (Subgroup.nontrivial_iff_ne_bot ρ.range).mpr hrange
  obtain ⟨N, hNnorm, hNne, hsimple⟩ :=
    exists_normal_simple_quotient ↥ρ.range
  haveI : N.Normal := hNnorm
  haveI : IsSimpleGroup (↥ρ.range ⧸ N) := hsimple
  haveI : Nontrivial (↥ρ.range ⧸ N) := QuotientGroup.nontrivial_iff.mpr hNne
  haveI : Group.IsPerfect (↥ρ.range ⧸ N) := inferInstance
  have hnonab : ∃ x y : (↥ρ.range ⧸ N), x * y ≠ y * x := by
    by_contra h
    push Not at h
    exact Group.IsPerfect.not_isSolvable (G := ↥ρ.range ⧸ N)
      (IsSimpleGroup.comm_iff_isSolvable.mp h)
  have h3S : ¬ 3 ∣ Nat.card (↥ρ.range ⧸ N) := by
    intro hdvd
    exact h3 (hdvd.trans ((Subgroup.card_quotient_dvd_card N).trans (card_range_dvd ρ)))
  have hcat : CFSG.Assembly.InCatalog (↥ρ.range ⧸ N) := by
    have hWtop : W ≠ ⊤ := fun h => hMtop (top_unique (h ▸ hWM))
    exact CFSG.KCore.KProperNonab.catalogue_of_surjective
      (C := CFSG.Open.IsCatalogGroup) CFSG.Open.isCatalogGroup_isoInvariant c.kProper
      W hWtop hnonab ((QuotientGroup.mk' N).comp ρ.rangeRestrict) (by
        intro s
        obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N s
        obtain ⟨x, hx⟩ := ρ.rangeRestrict_surjective g
        exact ⟨x, by rw [MonoidHom.comp_apply, hx]⟩)
  obtain ⟨f, hf⟩ := hPSz (↥ρ.range ⧸ N) hnonab hcat h3S
  exact noSzSection_mulAut_Lbar c hON ρ.range N 2 f hf

@[expose] def F9PerfectCore (c : Ctx82E3 D) (P : Subgroup G) (a : G) : Prop :=
  IsTripleCover (perfectCoreL c a ⧸ CFSG.Open.pCore 2 ↥(perfectCoreL c a))
      (alternatingGroup (Fin 6)) ∧
    zSub P c.L ≤ perfectCoreL c a ∧
    ⁅perfectCoreL c a, zSub P c.L⁆ ≤ CFSG.Open.pCoreOf 2 (perfectCoreL c a)

@[expose] def PerfectCoreGeneration (c : Ctx82E3 D) (A : Subgroup G) (a : G) : Prop :=
  A ≤ Subgroup.closure ({a} : Set G) ⊔ perfectCoreL c a

theorem perfectCoreL_structure'
    (hF9 : F9PerfectCore c P a) (hgen : PerfectCoreGeneration c A a)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    (hA : CFSG.Open.IsElemAbelian 3 A) (hA27 : Nat.card A = 27)
    (hAPL : A ≤ P ⊓ c.L) (ha : a ∈ A) (haZ : a ∉ zSub P c.L) :
    IsTripleCover (perfectCoreL c a ⧸ CFSG.Open.pCore 2 ↥(perfectCoreL c a))
        (alternatingGroup (Fin 6)) ∧
      zSub P c.L ≤ perfectCoreL c a ∧
      ⁅perfectCoreL c a, zSub P c.L⁆ ≤
        CFSG.Open.pCoreOf 2 (perfectCoreL c a) ∧
      A ≤ Subgroup.closure ({a} : Set G) ⊔ perfectCoreL c a :=
  ⟨hF9.1, hF9.2.1, hF9.2.2, hgen⟩

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
