module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Nine92Bar
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Nine92StepAux
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Nine92BarComp
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Nine92BarType
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Nine92BarCJ
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Nine92Pump
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Nine92SylCat
public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.ExclBridge
public import CFSG.GroupTheory.PCore.FixedSubgroupCore
public import CFSG.GroupTheory.CenterlessInnerCentralizer

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.SignalizerFunctorTheorem
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.HardMathSupport.Dickson.Sec6

attribute [local instance] gLAPPrimeCoreOf_normal

theorem isKGroup_top_barCentralizerBTwo {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdTwD5 b₀ K E) (hKproper : KProper InCatalog G)
    {B : Basis3 G (5 + 1)} (hB : Adapted B b₀ K E) :
    CFSG.IsKGroup ↥(⊤ : Subgroup (barCentralizerBTwo (B.b 2))) := by
  have hproper : CFSG.IsKProper G :=
    CFSG.ComponentClassification.CatalogueKProper.isKProper_iff_kProper.mpr hKproper
  have hH : CFSG.IsKGroup ↥(centralizerBTwo (B.b 2)) :=
    hproper (centralizerBTwo (B.b 2)) (centralizer_b_two_ne_top hstd hB)
  have hbar : CFSG.IsKGroup (barCentralizerBTwo (B.b 2)) :=
    hH.of_surjective (twD5BarMap (B.b 2)) (QuotientGroup.mk'_surjective _)
  exact hbar.subgroup ⊤

theorem primeCore_twD5BarNineJ_eq_bot {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdTwD5 b₀ K E) {B : Basis3 G (5 + 1)}
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD5 B b₀) :
    GLAPPrimeCore 3 ↥(twD5BarNineJ (B.b 2) K) = ⊥ := by
  have hJH : nineJ K (B.b 2) ≤ centralizerBTwo (B.b 2) :=
    (Subgroup.commutator_le_self _).trans inf_le_right
  obtain ⟨e⟩ := twD5BarSub_mulEquiv_of_inf_eq_bot (b₂ := B.b 2) hJH
    (nineJ_inf_primeCoreCentralizerBTwo_eq_bot hstd hB hrec)
  have hmap := CFSG.pPrimeCore_map_iso 3 e
  have hbot : pPrimeCore 3 ↥(nineJ K (B.b 2)) = ⊥ := nineJ_primeCore_eq_bot hstd hB hrec
  rw [hbot] at hmap
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hmap

theorem isCatalogLieIso_quotient_primeCore_of_eq_bot {Q : Type*} [Group Q] (p : ℕ)
    {P : TauCeti.LieTypeIndex → Prop} (h : IsCatalogLieIso Q P)
    (hbot : GLAPPrimeCore p Q = ⊥) : IsCatalogLieIso (Q ⧸ GLAPPrimeCore p Q) P :=
  IsCatalogLieIso.of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot).symm h

theorem primeCoreOf_twD5BarLbar_eq_bot {G : Type} [Group G] [Finite G] {b₂ : G}
    {L : Subgroup G} (hL : GLAPComponent 3 (centralizerBTwo b₂) L) :
    GLAPPrimeCoreOf 3 (twD5BarLbar (b₂ := b₂) L) = ⊥ := by
  have hO : GLAPPrimeCore 3 (barCentralizerBTwo b₂) = ⊥ :=
    glaPPrimeCore_barCentralizerBTwo_eq_bot b₂
  have hLbar : GLAPComponent 3 ⊤ (twD5BarLbar (b₂ := b₂) L) :=
    glaPComponent_twD5BarSub_of_glaPComponent hL
  exact CFSG.gLAPPrimeCoreOf_eq_bot_iff_pPrimeCore.mpr
    (upD42_core_eq_bot (twD5BarLbar (b₂ := b₂) L) hO hLbar)

theorem not_mem_dQ_twD5BarSub {G : Type} [Group G] [Finite G] {b₀ b₂ : G}
    {L : Subgroup G} (hLH : L ≤ centralizerBTwo b₂)
    (hb0 : b₀ ∈ centralizerBTwo b₂) (hb0N : b₀ ∈ Subgroup.normalizer (L : Set G))
    (hnot : b₀ ∉ dQ L)
    (hcore : GLAPPrimeCoreOf 3 (twD5BarLbar (b₂ := b₂) L) = ⊥) :
    twD5BarBZero b₂ b₀ hb0 ∉ dQ (twD5BarLbar (b₂ := b₂) L) := by
  obtain ⟨y, hy, hyb⟩ := exists_bar_mem_not_commute_of_not_mem_dQ hLH hb0 hb0N hnot
  intro hmem
  rw [mem_dQ] at hmem
  obtain ⟨-, -, htriv⟩ := hmem
  have h1 : y * twD5BarBZero b₂ b₀ hb0 * y⁻¹ * (twD5BarBZero b₂ b₀ hb0)⁻¹ = 1 := by
    have h := htriv y hy
    rwa [hcore, Subgroup.mem_bot] at h
  have h2 : y * twD5BarBZero b₂ b₀ hb0 = twD5BarBZero b₂ b₀ hb0 * y :=
    mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)
  exact hyb h2

theorem isCatalogLieIso_twD5BarNineJ {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdTwD5 b₀ K E) {B : Basis3 G (5 + 1)}
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD5 B b₀) :
    IsCatalogLieIso ↥(twD5BarNineJ (B.b 2) K) IsD42Index := by
  have hJH : nineJ K (B.b 2) ≤ centralizerBTwo (B.b 2) :=
    (Subgroup.commutator_le_self _).trans inf_le_right
  have hJO : nineJ K (B.b 2) ⊓ primeCoreCentralizerBTwo (B.b 2) = ⊥ :=
    nineJ_inf_gLAPPrimeCoreOf_eq_bot hstd hB hrec
  exact isCatalogLieIso_twD5BarSub_of_inf_eq_bot hJH hJO
    (isCatalogLieIso_isD42_of_statedClassicalModel
      (nineJ_statedClassicalModel_two_and_center hstd hB hrec).1)

theorem upD42Concl_twD5BarLbar (hcen : UpD42Statement) {G : Type} [Group G] [Finite G]
    {b₀ : G} {K E : Subgroup G} (hstd : StdTwD5 b₀ K E) (hKproper : KProper InCatalog G)
    {B : Basis3 G (5 + 1)} (hB : Adapted B b₀ K E) (hrec : RecOutTwD5 B b₀)
    {L : Subgroup G} (hL : GLAPComponent 3 (Subgroup.centralizer ({B.b 2} : Set G)) L)
    (hbN : b₀ ∈ Subgroup.normalizer (L : Set G))
    (hJ : GLAPComponent 3 (L ⊓ Subgroup.centralizer ({b₀} : Set G)) (nineJ K (B.b 2)))
    (hnot : b₀ ∉ dQ L) (hb0 : b₀ ∈ centralizerBTwo (B.b 2)) (h3b0 : b₀ ^ 3 = 1) :
    UpD42Concl (barOf 3 (twD5BarLbar (b₂ := B.b 2) L)) := by
  have hLH : L ≤ centralizerBTwo (B.b 2) := hL.1
  exact hcen (barCentralizerBTwo (B.b 2)) ⊤ (twD5BarLbar (b₂ := B.b 2) L)
    (isKGroup_top_barCentralizerBTwo hstd hKproper hB)
    (glaPComponent_twD5BarSub_of_glaPComponent hL) (twD5BarBZero (B.b 2) b₀ hb0)
    (Subgroup.mem_top _) (twD5BarBZero_mem_normalizer_twD5BarSub hLH hb0 hbN)
    (bar_pow_three_eq_one h3b0 hb0)
    (not_mem_dQ_twD5BarSub hLH hb0 hbN hnot (primeCoreOf_twD5BarLbar_eq_bot hL))
    (twD5BarNineJ (B.b 2) K)
    (glaPComponent_twD5BarSub_inf_centralizer hLH hb0 hbN hstd.2.1.1 hJ)
    (isCatalogLieIso_quotient_primeCore_of_eq_bot 3 (isCatalogLieIso_twD5BarNineJ hstd hB hrec)
      (primeCore_twD5BarNineJ_eq_bot hstd hB hrec))

theorem mem_dQ_of_census
    (hcen : UpD42Statement) (hΩ : UpD42ExclInnAt IsOmegaTwoBigIndex)
    {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G} (hstd : StdTwD5 b₀ K E)
    (hKproper : KProper InCatalog G) {B : Basis3 G (5 + 1)} (hB : Adapted B b₀ K E)
    (hrec : RecOutTwD5 B b₀) (hfus : Fus42 B b₀)
    {L : Subgroup G} (hL : GLAPComponent 3 (Subgroup.centralizer ({B.b 2} : Set G)) L)
    (hbN : b₀ ∈ Subgroup.normalizer (L : Set G))
    (hJ : GLAPComponent 3 (L ⊓ Subgroup.centralizer ({b₀} : Set G)) (nineJ K (B.b 2))) :
    b₀ ∈ dQ L := by
  by_contra hnot
  have hb0 : b₀ ∈ centralizerBTwo (B.b 2) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    simpa [hB.2.1] using (B.comm 0 2).eq
  have hLH : L ≤ centralizerBTwo (B.b 2) := hL.1
  have h3b0 : b₀ ^ 3 = 1 := by
    rw [← hstd.2.1.1]
    exact pow_orderOf_eq_one b₀
  obtain ⟨-, -, -, -, -, -, -, -, hEmax, -, -, -⟩ := hstd.2.1
  exact false_of_upD42Concl_of_weaklyClosed hΩ (twD5BarLbar (b₂ := B.b 2) L)
    (twD5BarNineJ (B.b 2) K)
    (twD5BarSub (B.b 2) ((E ⊓ nineJ K (B.b 2)).subgroupOf (centralizerBTwo (B.b 2))))
    (twD5BarBZero (B.b 2) b₀ hb0) (twD5BarBTwo (B.b 2))
    (glaPPrimeCore_barCentralizerBTwo_eq_bot (B.b 2))
    (glaPComponent_twD5BarSub_of_glaPComponent hL)
    (twD5BarBZero_mem_normalizer_twD5BarSub hLH hb0 hbN) (bar_pow_three_eq_one h3b0 hb0)
    (exists_bar_mem_not_commute_of_not_mem_dQ hLH hb0 hbN hnot) bar_b₂_mem_center
    (glaPComponent_twD5BarSub_inf_centralizer hLH hb0 hbN hstd.2.1.1 hJ)
    (isCatalogLieIso_twD5BarNineJ hstd hB hrec) twD5BarSub_inf_le
    (isElemAbelian_twD5BarSub_inf hEmax.2.1) (card_twD5BarSub_inf_nineJ hstd hB hrec)
    (twD5Bar_centralizer_inf_centralizer_le_zpowers_sup hstd hB hrec hfus hb0)
    (fun _ hy => conj_mem_zpowers_sup_zpowers_of_mem_sup_barA hstd hB hrec hb0 hy)
    (fun _ hP => card_le_of_isPGroup_of_surjective hstd hB hrec hfus (le_refl _)
      (twD5BarMap (B.b 2)) (QuotientGroup.mk'_surjective _) hP)
    (upD42Concl_twD5BarLbar hcen hstd hKproper hB hrec hL hbN hJ hnot hb0 h3b0)

end CFSG.StandardType.FrameRoute.FS81

end
