module

public import CFSG.LocalAnalysis.StandardType.GGFieldFiveE8Action
public import CFSG.LocalAnalysis.StandardType.GGFieldFiveE8Centralizer
public import CFSG.LocalAnalysis.StandardType.GGFieldFiveE8Marking
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerAdj
public import CFSG.LocalAnalysis.StandardType.GGSixFieldFiveProof
public import CFSG.LocalAnalysis.StandardType.GGSixFieldFiveTagsOm
public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDivOmega
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitExcCore
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGOmSpin

public section

namespace CFSG.StandardType

namespace FieldFiveE8

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley LayerFacts FieldFiveOm
  CFSG.ComponentClassification
open CFSG.LocalAnalysis.ComponentInitial (isComponentOf_map_iff)

section Main

theorem isComponentOf_top : IsComponentOf (⊤ : Subgroup E8Two) ⊤ := by
  refine ⟨le_rfl, IsSubnormal.refl _, ?_⟩
  rw [AssemblyBPredicates.isQuasisimple_iff_native]
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm
    (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_e8 (GaloisField 2 1))

theorem isComponentOf_range {G : Type} [Group G] {ψ : E8Two →* G} (hψ : Function.Injective ψ) :
    IsComponentOf ψ.range ψ.range := by
  have h := (isComponentOf_map_iff hψ).mpr isComponentOf_top
  rwa [← MonoidHom.range_eq_map] at h

theorem five_dvd_natCard_of_pow_eq_one {H : Type} [Group H] [Finite H] {s : H} (hs5 : s ^ 5 = 1)
    (hs1 : s ≠ 1) : 5 ∣ Nat.card H := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact (orderOf_eq_prime hs5 hs1) ▸ orderOf_dvd_natCard s

theorem false_of_ggConjPairs_one {G : Type} [Group G] [Finite G] {ψ : E8Two →* G}
    (hψ : Function.Injective ψ)
    (hX : LieModel (↥ψ.range ⧸ Subgroup.center ↥ψ.range) .E8 0 2 1) {x : G}
    (hsx : (x, (1 : E8Two)) ∈ ggConjPairs ψ) {L : Subgroup G}
    (hL : IsComponentOf L (ψ.range ⊓ Subgroup.centralizer {x}))
    (hLmark : GGNbrClauseFiveMarking 5 x L) : False := by
  have hcomm : ∀ u, x * ψ u = ψ u * x := fun u => by
    have h := inv_mul_map_mul_eq hsx u
    simp only [inv_one, one_mul, mul_one] at h
    calc x * ψ u = x * (x⁻¹ * ψ u * x) := by rw [h]
      _ = ψ u * x := by group
  have hCx : ψ.range ⊓ Subgroup.centralizer {x} = ψ.range := by
    refine inf_eq_left.mpr fun g hg => ?_
    obtain ⟨u, rfl⟩ := hg
    exact Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff.mp hh]
      exact hcomm u
  rw [hCx] at hL
  have hLq : CFSG.IsQuasisimple L := (AssemblyBPredicates.isQuasisimple_iff_native L).mp hL.2.2
  obtain rfl : L = ψ.range :=
    OmNonsplit.eq_of_isComponentOf_of_le hL (isComponentOf_range hψ) hLq le_rfl hL.1
  refine not_ggNbrClauseFiveMarking_of_lieModel_E8 le_rfl hX (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) ⟨1, one_mem _, ?_⟩ hLmark
  rintro _ ⟨u, rfl⟩
  rw [inv_mul_map_mul_eq hsx u]
  simp

theorem false_of_isFiveB {G : Type} [Group G] [Finite G] {ψ : E8Two →* G}
    (hψ : Function.Injective ψ) {x : G} {s : E8Two} (hs : (x, s) ∈ ggConjPairs ψ)
    {K₀ : Subgroup E8Two} (hK₀ : IsFiveB s K₀) {L : Subgroup G}
    (hL : IsComponentOf L (ψ.range ⊓ Subgroup.centralizer {x}))
    (hLmark : GGNbrClauseFiveMarking 5 x L) : False := by
  haveI : Finite E8Two := Finite.of_injective ψ hψ
  rw [ExcNonsplit.range_inf_centralizer_eq_map_centralizer hψ hs] at hL
  have hLr : L ≤ ψ.range := hL.1.trans (by rintro _ ⟨u, -, rfl⟩; exact ⟨u, rfl⟩)
  have hQ : IsComponentOf (L.comap ψ) (Subgroup.centralizer {s}) := by
    refine (isComponentOf_map_iff hψ).mp ?_
    rwa [Subgroup.map_comap_eq_self hLr]
  obtain rfl : L = K₀.map ψ := by
    rw [← Subgroup.map_comap_eq_self hLr, eq_of_isComponentOf_of_isFiveB hK₀ hQ]
  obtain ⟨k₀, hk₀, hin⟩ := exists_inner_of_isFiveB hK₀ (b := s)
    (Subgroup.mem_centralizer_iff.mpr fun h hh => by rw [Set.mem_singleton_iff.mp hh])
  exact not_ggNbrClauseFiveMarking_of_isFiveB hψ hK₀ (exists_inner_map hs hk₀ hin) hLmark

theorem exists_of_ggConjPairs_one {G : Type} [Group G] [Finite G] {ψ : E8Two →* G}
    (hψ : Function.Injective ψ)
    (hX : LieModel (↥ψ.range ⧸ Subgroup.center ↥ψ.range) .E8 0 2 1) {D : Subgroup G} {y : G}
    (hyD : y ∈ D) (hy1 : y ≠ 1) (hy : (y, (1 : E8Two)) ∈ ggConjPairs ψ) {x : G} {s : E8Two}
    (hs : (x, s) ∈ ggConjPairs ψ) (hs1 : s ≠ 1) (hs5 : s ^ 5 = 1) {J : Subgroup G}
    (hJr : J ≤ ψ.range) :
    ∃ y ∈ D, y ≠ 1 ∧ ∃ K : Subgroup G,
      IsComponentOf K (ψ.range ⊓ Subgroup.centralizer {y}) ∧ J ≤ K ∧ 5 ∣ Nat.card K ∧
      x ∉ Subgroup.centralizer (K : Set G) ∧ ¬ GGNbrClauseFiveMarking 5 x K := by
  haveI : Finite E8Two := Finite.of_injective ψ hψ
  have hZ : Subgroup.center E8Two = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .E8) (K := GaloisField 2 1)
  have hcomm : ∀ u, y * ψ u = ψ u * y := fun u => by
    have h := inv_mul_map_mul_eq hy u
    simp only [inv_one, one_mul, mul_one] at h
    calc y * ψ u = y * (y⁻¹ * ψ u * y) := by rw [h]
      _ = ψ u * y := by group
  have hCy : ψ.range ⊓ Subgroup.centralizer {y} = ψ.range := by
    refine inf_eq_left.mpr fun g hg => ?_
    obtain ⟨u, rfl⟩ := hg
    exact Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff.mp hh]
      exact hcomm u
  refine ⟨y, hyD, hy1, ψ.range, ?_, hJr, ?_, ?_, ?_⟩
  · rw [hCy]
    exact isComponentOf_range hψ
  · rw [← Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv]
    exact five_dvd_natCard_of_pow_eq_one hs5 hs1
  · intro hxc
    refine hs1 (eq_of_mem_ggConjPairs hψ hZ hs ?_)
    intro u
    have h := Subgroup.mem_centralizer_iff.mp hxc (ψ u) ⟨u, rfl⟩
    simp only [one_mul, inv_one, mul_one]
    rw [← h]
    group
  · refine not_ggNbrClauseFiveMarking_of_lieModel_E8 le_rfl hX (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ⟨ψ s, ⟨s, rfl⟩, ?_⟩
    rintro _ ⟨u, rfl⟩
    rw [inv_mul_map_mul_eq hs u]
    simp

theorem exists_of_plane (h5 : E8TwoFiveCentInput) (hpl : E8TwoFivePlaneCentInput)
    {G : Type} [Group G] [Finite G] {ψ : E8Two →* G}
    (hψ : Function.Injective ψ) {D : Subgroup G} (hDel : IsElemAbelian 5 D)
    (hDcard : Nat.card D = 5 ^ 2) (hDs : ∀ e ∈ D, ∃ s, (e, s) ∈ ggConjPairs ψ)
    (hfree : ∀ y ∈ D, y ≠ 1 → (y, (1 : E8Two)) ∉ ggConjPairs ψ) {x : G} (hxD : x ∈ D)
    {sx : E8Two} (hsx : (x, sx) ∈ ggConjPairs ψ) (hs1 : sx ≠ 1)
    (h5B : ¬ ∃ K₀ : Subgroup E8Two, IsFiveB sx K₀) {J : Subgroup G} (hJq : CFSG.IsQuasisimple J)
    (hJr : J ≤ ψ.range) (hJD : J ≤ Subgroup.centralizer (D : Set G)) :
    ∃ y ∈ D, y ≠ 1 ∧ ∃ K : Subgroup G,
      IsComponentOf K (ψ.range ⊓ Subgroup.centralizer {y}) ∧ J ≤ K ∧ 5 ∣ Nat.card K ∧
      x ∉ Subgroup.centralizer (K : Set G) ∧ ¬ GGNbrClauseFiveMarking 5 x K := by
  haveI : Finite E8Two := Finite.of_injective ψ hψ
  have hZ : Subgroup.center E8Two = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .E8) (K := GaloisField 2 1)
  have hAel := isElemAbelian_conjOf hψ hZ hDel hDs
  have hAcard : Nat.card (conjOf ψ D) = 5 ^ 2 :=
    (card_conjOf_of_no_centralizing hψ hZ hDs hfree).trans hDcard
  have hnc := not_isMulCommutative_centralizer_conjOf hψ hDs hJq (le_inf hJr hJD)
  obtain ⟨y', hy'A, hy'1, K₀, hK₀⟩ :=
    exists_isFiveB_of_noncomm_centralizer_plane h5 hpl _ hAel hAcard hnc
  obtain ⟨y, hyD, hyy'⟩ := mem_conjOf.mp hy'A
  have hy1 : y ≠ 1 := by
    rintro rfl
    exact hy'1 (eq_of_mem_ggConjPairs hψ hZ hyy' (one_mem _))
  have hy'5 : y' ^ 5 = 1 := hAel.2 y' hy'A
  have hCy := ExcNonsplit.range_inf_centralizer_eq_map_centralizer hψ hyy'
  have hJC : J ≤ (Subgroup.centralizer {y'}).map ψ := by
    rw [← hCy]
    exact le_inf hJr (hJD.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hyD)))
  have hJK : J ≤ K₀.map ψ := by
    let e1 : ↥(J.comap ψ) ≃* ↥J := ((J.comap ψ).equivMapOfInjective ψ hψ).trans
      (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hJr))
    have hq' : CFSG.IsQuasisimple (J.comap ψ) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv e1.symm hJq
    have hle : J.comap ψ ≤ Subgroup.centralizer {y'} := by
      have := Subgroup.comap_mono (f := ψ) hJC
      rwa [Subgroup.comap_map_eq_self_of_injective hψ] at this
    have := Subgroup.map_mono (f := ψ) (le_of_isFiveB_of_isQuasisimple hK₀ hle hq')
    rwa [Subgroup.map_comap_eq_self hJr] at this
  have hee : x * y = y * x :=
    congrArg Subtype.val (hDel.1.is_comm.comm (⟨x, hxD⟩ : ↥D) ⟨y, hyD⟩)
  have hsy' : sx * y' = y' * sx := mul_comm_of_mem_ggConjPairs hψ hZ hsx hyy' hee
  have hsxC : sx ∈ Subgroup.centralizer {y'} :=
    Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff.mp hh]
      exact hsy'.symm
  refine ⟨y, hyD, hy1, K₀.map ψ, ?_, hJK, ?_, ?_, ?_⟩
  · rw [hCy]
    exact (isComponentOf_map_iff hψ).mpr hK₀.1
  · rw [Subgroup.card_map_of_injective hψ]
    exact hK₀.2.2.2.1
  · intro hxc
    have hsxK : sx ∈ Subgroup.centralizer (K₀ : Set E8Two) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have h1 := Subgroup.mem_centralizer_iff.mp hxc (ψ u) ⟨u, hu, rfl⟩
      have h3 : x⁻¹ * ψ u * x = ψ u := by rw [mul_assoc, h1, inv_mul_cancel_left]
      have h4 : sx⁻¹ * u * sx = u := hψ ((inv_mul_map_mul_eq hsx u).symm.trans h3)
      calc u * sx = sx * (sx⁻¹ * u * sx) := by group
        _ = sx * u := by rw [h4]
    have hmem : sx ∈ Subgroup.zpowers y' :=
      mem_zpowers_of_mem_centralizer_of_isFiveB hK₀ hsxC hsxK
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hsx5 : sx ^ 5 = 1 := pow_eq_one_of_mem_ggConjPairs hψ hZ hsx (hDel.2 x hxD)
    have ho1 : orderOf sx = 5 := orderOf_eq_prime hsx5 hs1
    have ho2 : orderOf y' = 5 := orderOf_eq_prime hy'5 hy'1
    have hzp : Subgroup.zpowers sx = Subgroup.zpowers y' :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hmem)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, ho1, ho2])
    exact h5B ⟨K₀, IsFiveB.of_zpowers_eq hK₀ hzp.symm⟩
  · obtain ⟨k₀, hk₀, hin⟩ := exists_inner_of_isFiveB hK₀ hsxC
    exact not_ggNbrClauseFiveMarking_of_isFiveB hψ hK₀ (exists_inner_map hsx hk₀ hin)

theorem fieldFive_e8 (h5 : E8TwoFiveCentInput) (hpl : E8TwoFivePlaneCentInput)
    {G : Type} [Group G] [Finite G] {ψ : E8Two →* G} (hψ : Function.Injective ψ)
    (hX : LieModel (↥ψ.range ⧸ Subgroup.center ↥ψ.range) .E8 0 2 1) {D : Subgroup G}
    (hDel : IsElemAbelian 5 D) (hDcard : Nat.card D = 5 ^ 2)
    (hDs : ∀ e ∈ D, ∃ s, (e, s) ∈ ggConjPairs ψ) {x : G} (hxD : x ∈ D) {L : Subgroup G}
    (hL : IsComponentOf L (ψ.range ⊓ Subgroup.centralizer {x}))
    (hLmark : GGNbrClauseFiveMarking 5 x L) {J : Subgroup G}
    (hJ : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G))) :
    ∃ y ∈ D, y ≠ 1 ∧ ∃ K : Subgroup G,
      IsComponentOf K (ψ.range ⊓ Subgroup.centralizer {y}) ∧ J ≤ K ∧ 5 ∣ Nat.card K ∧
      x ∉ Subgroup.centralizer (K : Set G) ∧ ¬ GGNbrClauseFiveMarking 5 x K := by
  classical
  haveI : Finite E8Two := Finite.of_injective ψ hψ
  have hZ : Subgroup.center E8Two = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .E8) (K := GaloisField 2 1)
  have hJq : CFSG.IsQuasisimple J := (AssemblyBPredicates.isQuasisimple_iff_native J).mp hJ.2.2
  have hJr : J ≤ ψ.range := (hJ.1.trans inf_le_left).trans (hL.1.trans inf_le_left)
  have hJD : J ≤ Subgroup.centralizer (D : Set G) := hJ.1.trans inf_le_right
  obtain ⟨sx, hsx⟩ := hDs x hxD
  have hsx5 : sx ^ 5 = 1 := pow_eq_one_of_mem_ggConjPairs hψ hZ hsx (hDel.2 x hxD)
  by_cases hs1 : sx = 1
  · subst hs1
    exact (false_of_ggConjPairs_one hψ hX hsx hL hLmark).elim
  by_cases h5B : ∃ K₀ : Subgroup E8Two, IsFiveB sx K₀
  · obtain ⟨K₀, hK₀⟩ := h5B
    exact (false_of_isFiveB hψ hsx hK₀ hL hLmark).elim
  by_cases hc : ∃ y ∈ D, y ≠ 1 ∧ (y, (1 : E8Two)) ∈ ggConjPairs ψ
  · obtain ⟨y, hyD, hy1, hy⟩ := hc
    exact exists_of_ggConjPairs_one hψ hX hyD hy1 hy hsx hs1 hsx5 hJr
  · push Not at hc
    exact exists_of_plane h5 hpl hψ hDel hDcard hDs hc hxD hsx hs1 h5B hJq hJr hJD

theorem ggFieldFiveNbrTag_E8_of_classes (h5 : E8TwoFiveCentInput)
    (hpl : E8TwoFivePlaneCentInput) : GGFieldFiveNbrTag .E8 := by
  intro G _ _ n ψ G₀ hpres D hDel hDcard hDN hDdiag x hxD L hL hLmark J hJ
  obtain ⟨⟨hadm, -⟩, ⟨hrange, hker⟩, -, hLie⟩ := id hpres
  obtain rfl : n = 0 := hadm.2.2
  subst hrange
  have hZ : Subgroup.center E8Two = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .E8) (K := GaloisField 2 1)
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans hZ.le
  exact fieldFive_e8 h5 hpl (ψ := ψ) hinj hLie hDel hDcard
    (fun d hd => LayerPDiv.exists_mem_ggConjPairs_of_inner
      (ggPsiDiagInner_E8 G 0 1 ψ _ hpres d (hDN hd) (hDdiag d hd))) hxD hL hLmark hJ

end Main

end FieldFiveE8

end CFSG.StandardType
