module

public import CFSG.LocalAnalysis.StandardType.GGRawAutRestCore
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangSz
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldCyclicLabels
public import CFSG.LocalAnalysis.ComponentInitial.InvolutionFixedFourGroupTransport
public import CFSG.RankThree.SteinbergR3ESuzukiFieldSplitting
public import CFSG.RankThree.PartTwo.KFacts.AutSz

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut coe_szFieldAut)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

namespace RawAutSz

variable {a : ℕ} {K : Type} [Field K]

theorem congr_field_eq_sz (hZ : Subgroup.center (suzukiGroup a K) = ⊥)
    {f : MulAut (LargeEvenCenterQuot (suzukiGroup a K))}
    (hf : f ∈ LargeEvenMatFieldImage (LargeEvenCenterMk (suzukiGroup a K))) :
    ∃ σ : K ≃+* K, MulAut.congr (centerQuotEquivOfBot hZ) f = szFieldAut a K σ := by
  obtain ⟨σ, hσ⟩ := hf
  refine ⟨σ, MulEquiv.ext fun x => ?_⟩
  have e1 := hσ x (szFieldAut a K σ x) (coe_szFieldAut σ x)
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, centerQuotEquivOfBot_symm,
    e1, centerQuotEquivOfBot_mk]

theorem symm_szFieldAut_mem (hZ : Subgroup.center (suzukiGroup a K) = ⊥) (σ : K ≃+* K) :
    (MulAut.congr (centerQuotEquivOfBot hZ)).symm (szFieldAut a K σ) ∈
      LargeEvenMatFieldImage (LargeEvenCenterMk (suzukiGroup a K)) := by
  refine ⟨σ, fun h h' hh' => ?_⟩
  rw [RecipeExcLang.congr_symm_apply_mk hZ]
  congr 1
  exact Subtype.ext (Units.ext (by rw [coe_szFieldAut]; exact hh'.symm))

variable [Finite K]

theorem ggRawInnField_suzuki (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p ≠ 1) :
    GGRawInnField p (LargeEvenCenterQuot (LargeEvenSzGroup a K)) (LargeEvenInnSet _)
      (LargeEvenMatFieldImage (LargeEvenCenterMk (LargeEvenSzGroup a K))) := by
  suffices key : ∀ H : Subgroup (GL (Fin 4) K), H = suzukiGroup a K →
      GGRawInnField p (LargeEvenCenterQuot H) (LargeEvenInnSet _)
        (LargeEvenMatFieldImage (LargeEvenCenterMk H)) from key _ (largeEvenSzGroup_eq a K)
  rintro H rfl
  have hZ := CFSG.RankThree.PartOne.KE.suzuki_center_eq_bot ha hK
  refine ggRawInnField_of_subgroup hp (MulAut.conj : _ →* MulAut _).range (MonoidHom.coe_range _)
    (fun r => ⟨r, rfl⟩) fun f hf hfI => ?_
  obtain ⟨σ, hσ⟩ := congr_field_eq_sz hZ hf
  have hin : szFieldAut a K σ ∈ inner (suzukiGroup a K) := by
    rw [← hσ]
    exact (CFSG.LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff _ f).mpr hfI
  have h1 := CFSG.RankThree.Automorphisms.eq_one_of_szFieldAut_mem_inner ha hK hin
  rw [h1, map_one] at hσ
  exact (MulAut.congr (centerQuotEquivOfBot hZ)).injective (hσ.trans (map_one _).symm)

theorem ggRawPCyclic_suzuki (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} :
    GGRawPCyclic p (LargeEvenCenterQuot (LargeEvenSzGroup a K)) (LargeEvenInnSet _)
      (LargeEvenMatFieldImage (LargeEvenCenterMk (LargeEvenSzGroup a K))) := by
  suffices key : ∀ H : Subgroup (GL (Fin 4) K), H = suzukiGroup a K →
      GGRawPCyclic p (LargeEvenCenterQuot H) (LargeEvenInnSet _)
        (LargeEvenMatFieldImage (LargeEvenCenterMk H)) from key _ (largeEvenSzGroup_eq a K)
  rintro H rfl
  have hZ := CFSG.RankThree.PartOne.KE.suzuki_center_eq_bot ha hK
  have := (CFSG.LieType.Suzuki.suzukiGroup_outer_isCyclic_card_dvd ha hK).1
  have hO : GGOutCyclic (suzukiGroup a K) :=
    ggOutCyclic_of_hom (QuotientGroup.mk' (inner _)) (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _)
  exact ggRawPCyclic_of_outCyclic (MulAut.conj : _ →* MulAut _).range (MonoidHom.coe_range _)
    (fun r => ⟨r, rfl⟩) (hO.of_mulEquiv (centerQuotEquivOfBot hZ))

theorem exists_conj_mul_field_suzuki (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (φ : MulAut (LargeEvenCenterQuot (LargeEvenSzGroup a K))) :
    ∃ u ∈ LargeEvenInnSet (LargeEvenCenterQuot (LargeEvenSzGroup a K)),
      ∃ f ∈ Subgroup.closure (LargeEvenMatFieldImage (LargeEvenCenterMk (LargeEvenSzGroup a K))),
        φ = u * f := by
  suffices key : ∀ H : Subgroup (GL (Fin 4) K), H = suzukiGroup a K →
      ∀ φ : MulAut (LargeEvenCenterQuot H), ∃ u ∈ LargeEvenInnSet (LargeEvenCenterQuot H),
        ∃ f ∈ Subgroup.closure (LargeEvenMatFieldImage (LargeEvenCenterMk H)), φ = u * f from
    key _ (largeEvenSzGroup_eq a K) φ
  rintro H rfl φ
  have hZ := CFSG.RankThree.PartOne.KE.suzuki_center_eq_bot ha hK
  obtain ⟨g, σ, hgσ⟩ := CFSG.RankThree.PartTwo.KFacts.exists_conj_mul_szFieldAut ha hK
    (MulAut.congr (centerQuotEquivOfBot hZ) φ)
  refine ⟨MulAut.conj ((centerQuotEquivOfBot hZ).symm g), ⟨_, rfl⟩,
    (MulAut.congr (centerQuotEquivOfBot hZ)).symm (szFieldAut a K σ),
    Subgroup.subset_closure (symm_szFieldAut_mem hZ σ), ?_⟩
  apply (MulAut.congr (centerQuotEquivOfBot hZ)).injective
  rw [map_mul, MulEquiv.apply_symm_apply, mulAut_congr_conj, MulEquiv.apply_symm_apply]
  exact hgσ

end RawAutSz

open RawAutSz

theorem ggRawInnFieldOn_twB2 :
    GGRawInnFieldOn fun lab => lab.tag = .twB2 := by
  intro p hp _ lab hlab ht Q h
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht
  subst ht
  have hn3 : 3 ≤ n := hlab.2.2.2
  dsimp only [LargeEvenRawDatum] at h ⊢
  obtain ⟨K, _, _, hK, hQ⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, hQ, ggRawInnField_suzuki (by omega) hK hp.one_lt.ne'⟩

theorem ggRawPCyclicOn_twB2 :
    GGRawPCyclicOn fun _ lab => lab.tag = .twB2 := by
  intro p _ _ lab hlab ht Q h
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht
  subst ht
  have hn3 : 3 ≤ n := hlab.2.2.2
  dsimp only [LargeEvenRawDatum] at h ⊢
  obtain ⟨K, _, _, hK, hQ⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, hQ, ggRawPCyclic_suzuki (by omega) hK⟩

theorem ggOddAutOn_twB2 : GGOddAutOn fun lab => lab.tag = .twB2 := by
  intro p lab _ _ hlab ht _ Q h
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht
  subst ht
  have hn3 : 3 ≤ n := hlab.2.2.2
  dsimp only [LargeEvenRawDatum] at h ⊢
  obtain ⟨K, _, _, hK, hQ⟩ := h
  try dsimp only at hK hQ ⊢
  exact ⟨K, inferInstance, inferInstance, hK, hQ, fun _ _ =>
    RawAut.ggOddAutInnField_of_forall (exists_conj_mul_field_suzuki (by omega) hK)⟩

end CFSG.StandardType

end
