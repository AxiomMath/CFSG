module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerTagsExcToral
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixEMain

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE8F CFSG.RankThree.PartOne LayerExc LayerSixE
open scoped commutatorElement

namespace TagsExc

section Model

variable {L C : Type*} [Group L] [Group C] {G : Type*} [Group G]

theorem isPGroup_zpowers_of_pow_eq_one {H : Type*} [Group H] {g : H} {p : ℕ} (hg : g ^ p = 1) :
    IsPGroup p (Subgroup.zpowers g) ∧
      ∀ a ∈ Subgroup.zpowers g, ∀ b ∈ Subgroup.zpowers g, a * b = b * a := by
  refine ⟨?_, ?_⟩
  · rintro ⟨_, k, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    change ((fun k : ℤ => g ^ k) k) ^ p ^ 1 = 1
    simp only [pow_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg, one_zpow]
  · rintro _ ⟨k, rfl⟩ _ ⟨l, rfl⟩
    exact zpow_mul_comm g k l

theorem mem_autFix_zpowers {α : MulAut C} {x : C} :
    x ∈ autFix (Subgroup.zpowers α) ↔ α x = x := by
  refine ⟨fun h => h α (Subgroup.mem_zpowers α), fun h β hβ => ?_⟩
  have hst : Subgroup.zpowers α ≤ MulAction.stabilizer (MulAut C) x := by
    rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff, MulAut.smul_def]
    exact h
  have := hst hβ
  rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at this

theorem ggNotExcThree_of_isComponentOf_model [Finite L] [Finite G] {π : L →* C}
    (hπ : Function.Surjective π) (hπker : π.ker ≤ Subgroup.center L)
    (hodd : Odd (Nat.card π.ker)) {ψ : L →* G} (hker : ψ.ker ≤ π.ker) {y : G}
    (hyN : y ∈ Subgroup.normalizer (ψ.range : Set G)) {α : MulAut C}
    (hα : GGInduces π ψ y α) {β : Type} {S : β → Subgroup C}
    (hS : LayerCores.IsSubCoreFamily (autFix (Subgroup.zpowers α)) S)
    (hcomp : ∀ X : Subgroup C, IsComponentOf X (autFix (Subgroup.zpowers α)) →
      GGNotExcThreeOrder (ggCQ X))
    {K : Subgroup G} (hK : IsComponentOf K (ψ.range ⊓ Subgroup.centralizer {y})) :
    GGNotExcThreeOrder (ggCQ K) := by
  set M := (autFix (Subgroup.zpowers α)).comap π with hM
  have hψker : ψ.ker ≤ Subgroup.center L := hker.trans hπker
  set H := ψ.range ⊓ Subgroup.centralizer ({y} : Set G) with hH
  have hHM : H ≤ M.map ψ := by
    rintro _ ⟨⟨u, rfl⟩, hu⟩
    refine ⟨u, ?_, rfl⟩
    change π u ∈ autFix (Subgroup.zpowers α)
    rw [mem_autFix_zpowers]
    refine (hα u u ?_).symm
    rw [← Subgroup.mem_centralizer_singleton_iff.mp hu]
    group
  have hMH : ⁅M, M⁆ ≤ H.comap ψ := by
    rw [Subgroup.commutator_le]
    intro y₁ hy₁ y₂ hy₂
    refine ⟨⟨_, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have hz : ∀ {u u' : L}, u ∈ M → ψ u' = y * ψ u * y⁻¹ → u⁻¹ * u' ∈ Subgroup.center L := by
      intro u u' hu hu'
      refine hπker ?_
      have hfix : α (π u) = π u := mem_autFix_zpowers.mp hu
      rw [MonoidHom.mem_ker, map_mul, map_inv, hα u u' hu', hfix, inv_mul_cancel]
    obtain ⟨y₁', hy₁'⟩ := exists_conj_eq hyN y₁
    obtain ⟨y₂', hy₂'⟩ := exists_conj_eq hyN y₂
    have hconj : ψ ⁅y₁', y₂'⁆ = y * ψ ⁅y₁, y₂⁆ * y⁻¹ := by
      rw [map_commutatorElement, map_commutatorElement, hy₁', hy₂']
      simp only [commutatorElement_def]
      group
    have hc : ⁅y₁', y₂'⁆ = ⁅y₁, y₂⁆ := by
      calc ⁅y₁', y₂'⁆ = ⁅y₁ * (y₁⁻¹ * y₁'), y₂ * (y₂⁻¹ * y₂')⁆ := by
            rw [mul_inv_cancel_left, mul_inv_cancel_left]
        _ = ⁅y₁, y₂⁆ := by
            rw [commutatorElement_mul_central_left (hz hy₁ hy₁'),
              commutatorElement_mul_central_right (hz hy₂ hy₂')]
    rw [hc] at hconj
    calc ψ ⁅y₁, y₂⁆ * y = y * ψ ⁅y₁, y₂⁆ * y⁻¹ * y := by rw [← hconj]
      _ = y * ψ ⁅y₁, y₂⁆ := by group
  have hS' := isSubCoreFamily_comap_of_central π hπ hπker hodd hS
  have hS'' : LayerCores.IsSubCoreFamily ⁅M, M⁆ (fun c => derivedPreimage π (S c)) := by
    have h := hS'.inf_of_commutator_le (N := ⁅M, M⁆) le_rfl
    rwa [inf_eq_right.mpr (Subgroup.commutator_le_self M)] at h
  have hC₀H : (⁅M, M⁆).map ψ ≤ H := Subgroup.map_le_iff_le_comap.mpr hMH
  have hnorm : (((⁅M, M⁆).map ψ).subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hC₀H]
    rintro _ k ⟨s, hs, rfl⟩ hk
    obtain ⟨u, hu, rfl⟩ := hHM hk
    exact ⟨u * s * u⁻¹, LayerSixE.conj_mem_commutator_self hu hs,
      by rw [map_mul, map_mul, map_inv]⟩
  have hcommH : ⁅H, H⁆ ≤ (⁅M, M⁆).map ψ := by
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono hHM hHM
  obtain ⟨c, rfl⟩ := LayerPDiv.exists_eq_map_of_isComponentOf_sub ψ hψker hC₀H hnorm hcommH
    hS'' hK
  have hq := hS.2.2.1 c
  have hperf : Group.IsPerfect ↥(derivedPreimage π (S c)) :=
    (isQuasisimple_derivedPreimage hπ hπker hq).1
  rw [ggCQ_map_of_perfect ψ hψker hperf, ← ggCQ_map_of_perfect π hπker hperf,
    map_derivedPreimage_of_perfect hπ hq.1]
  exact hcomp (S c) ⟨hS.1 c, hS.2.1 c,
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hq⟩

end Model

section Toral


variable {τ : Tag} {K : Type} [Field K]

theorem isSubCoreFamily_famCentralizer [Finite K] [CharP K 2]
    (F : Set (Fin τ.rank → Kˣ)) {t : Kˣ} (ht : (t : K) ^ 2 ≠ 1)
    (hW : ∃ k, LayerFacts.ggDer (famStabilizerSubgroup F) k ≤ famReflectionGroup F) :
    LayerCores.IsSubCoreFamily (famCentralizer F)
      (fun i => (componentRootSpan K (famChar F) i).comap (adjointGroup τ K).subtype) := by
  classical
  obtain ⟨k, hk⟩ := hW
  have hHQM := torus_sup_rootSpan_le_map_famCentralizer (K := K) F
  have hYN := map_famWeylReps_le_normalizer (K := K) F
  have hMle := map_famCentralizer_le_sup (K := K) F
  have hMN : (famCentralizer F).map (adjointGroup τ K).subtype ≤ Subgroup.normalizer
      ((torusGroup τ K ⊔ rootSpan τ K (famKernel F) : Subgroup (ModGL τ K)) :
        Set (ModGL τ K)) :=
    hMle.trans (sup_le Subgroup.le_normalizer hYN)
  have hder : LayerFacts.ggDer ((famCentralizer F).map (adjointGroup τ K).subtype) (k + 1) ≤
      rootSpan τ K (famKernel F) := by
    rw [LayerFacts.ggDer_succ]
    have h1 := (LayerFacts.ggDer_mono hMle k).trans ((ggDer_sup_le_of_le_normalizer hYN k).trans
      (sup_le le_rfl (ggDer_map_famWeylReps_le hk)))
    exact (Subgroup.commutator_mono h1 h1).trans
      (commutator_torus_sup_rootSpan_le fun α hα => hα.1)
  have hsup : ⨆ i, componentRootSpan K (famChar F) i = rootSpan τ K (famKernel F) := by
    rw [iSup_componentRootSpan, kernelRoots_famChar]
  have hfam := isSubCoreFamily_of_le_of_normal (isSubCoreFamily_torus_sup_rootSpan F ht) hHQM
    (fun u hu s hs => (Subgroup.mem_normalizer_iff.1 (hMN hu) s).1 hs)
    ⟨k + 1, by rw [hsup]; exact hder⟩
  have h := hfam.comap (adjointGroup τ K).subtype (adjointGroup τ K).subtype_injective (by
    rintro _ ⟨g, -, rfl⟩
    exact ⟨g, rfl⟩)
  rwa [Subgroup.comap_map_eq_self_of_injective (adjointGroup τ K).subtype_injective] at h

theorem ggNotExcThree_of_isComponentOf_autFix_toral [Finite K] [CharP K 2]
    (hK4 : 4 ≤ Nat.card K) (hW : GGWeylFamQuotSolvInput τ) (hsmall : GGExcSmallCompOrderInput)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {α : MulAut ↥(adjointGroup τ K)} (hαp : α ^ p = 1)
    (ht : GGInndiagToral τ K (Subgroup.zpowers α)) {X : Subgroup ↥(adjointGroup τ K)}
    (hX : IsComponentOf X (autFix (Subgroup.zpowers α))) : GGNotExcThreeOrder (ggCQ X) := by
  obtain ⟨c, hc⟩ := ht
  set e : MulAut ↥(adjointGroup τ K) := MulAut.conj c with he
  set F := conjTuples (Subgroup.zpowers α) c with hF
  rw [autFix_eq_comap_famCentralizer _ c hc, Subgroup.comap_equiv_eq_map_symm'] at hX
  have hX' := isComponentOf_comap e.symm.toMonoidHom e.symm.injective hX
  rw [← ggCQ_comap_of_injective e.symm.toMonoidHom e.symm.injective (by
    rw [MonoidHom.range_eq_top.mpr e.symm.surjective]; exact le_top)]
  have hpow : ∀ a ∈ F, ∃ n : ℕ, a ^ p ^ n = 1 := by
    rintro a ⟨β, hβ, hβa⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hβ
    have hβp : (α ^ k) ^ p = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hαp, one_zpow]
    refine ⟨1, rootDiagAutHom_injective ?_⟩
    rw [pow_one, map_pow, hβa, map_one, conj_pow, hβp, mul_one, mul_inv_cancel]
  have hWF : ∃ k, LayerFacts.ggDer (famStabilizerSubgroup F) k ≤ famReflectionGroup F := by
    by_cases hdvd : p ∣ Nat.card (famStabilizerSubgroup F)
    · exact hW K p hp hp2 _ hpow hdvd
    · exact ⟨0, famStabilizer_subset_closure_of_coprime hp _ hpow hdvd⟩
  obtain ⟨t, htt⟩ := exists_unit_sq_ne_one hK4
  have hfam := isSubCoreFamily_famCentralizer F htt hWF
  rw [← Subgroup.map_id (famCentralizer F)] at hX'
  obtain ⟨i, hi⟩ := LayerPDiv.exists_eq_map_of_isComponentOf_sub (MonoidHom.id _)
    (by rw [MonoidHom.ker_id]; exact bot_le) le_rfl
    (by rw [Subgroup.subgroupOf_self]; infer_instance) (LayerFacts.ggCommutator_self_le _) hfam hX'
  rw [hi, Subgroup.map_id, ggCQ_comap_of_injective _ (adjointGroup τ K).subtype_injective (by
    rw [Subgroup.range_subtype]; exact rootSpan_le_adjointGroup K _)]
  exact ggNotExcThree_componentRootSpan hK4 fun hr hs => hsmall τ K _ _ _ hr hs

end Toral

end TagsExc

section Tags

open CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny

@[expose] def GGE6InndiagCompNonToralInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ α ∈ LayerSixE.inndiagAut .E6 K, α ^ p = 1 →
      ¬ LayerSixE.GGInndiagToral .E6 K (Subgroup.zpowers α) →
      ∀ X : Subgroup ↥(adjointGroup .E6 K),
        IsComponentOf X (LayerSixE.autFix (Subgroup.zpowers α)) → GGNotExcThreeOrder (ggCQ X)

theorem ggLayerNotExcThreeTag_E6_of_inputs (hW : GGWeylFamQuotSolvInput .E6)
    (hcore : GGE6InndiagCoreInput) (hsmall : GGExcSmallCompOrderInput)
    (hN : GGE6InndiagCompNonToralInput) : GGLayerNotExcThreeTag .E6 := by
  intro G _ _ n f ψ G₀ hpres hf p hp hp2 y hy hyN hdiag C hC
  obtain ⟨-, ⟨hrange, hker⟩, -, -⟩ := hpres
  subst hrange
  have : Finite ↥(e6Data_valid.minGroup (GaloisField 2 f)) :=
    CFSG.LieType.Steinberg.CentralExt.FieldFour.finite_minGroup' e6Data_valid
  have hK4 := TagsExc.four_le_card_galoisField hf
  have hodd : Odd (Nat.card (e6Isogeny (GaloisField 2 f)).ker) := by
    have h2 := CFSG.ClassicalInvolution.ModelFacts.ChevAut.e6Isogeny_not_dvd_card_ker
      (GaloisField 2 f) (p := 2)
    exact Nat.not_even_iff_odd.mp fun he => h2 (even_iff_two_dvd.mp he)
  have hkπ := LayerSixE.ker_le_ker_e6Isogeny hker
  obtain ⟨α, hαD, hα⟩ := LayerSixE.exists_induces_E6 ψ hker hyN hdiag
  have hαp : α ^ p = 1 := by
    have h1 := hα.pow hkπ hyN p
    rw [hy] at h1
    exact GGInduces.unique (e6Isogeny_surjective (GaloisField 2 f)) (Subgroup.one_mem _) h1
      (GGInduces.one hkπ)
  obtain ⟨hAp, hAc⟩ := TagsExc.isPGroup_zpowers_of_pow_eq_one hαp
  obtain ⟨β, S, hS⟩ := hcore (GaloisField 2 f) p hp hp2 _ hAp hAc
    ((Subgroup.zpowers_le).mpr hαD)
  refine TagsExc.ggNotExcThree_of_isComponentOf_model (e6Isogeny_surjective (GaloisField 2 f))
    (CFSG.ClassicalInvolution.ModelFacts.ChevAut.e6Isogeny_ker_le_center (GaloisField 2 f))
    hodd hkπ hyN hα hS (fun X hX => ?_) hC
  by_cases ht : LayerSixE.GGInndiagToral .E6 (GaloisField 2 f) (Subgroup.zpowers α)
  · exact TagsExc.ggNotExcThree_of_isComponentOf_autFix_toral hK4 hW hsmall hp hp2 hαp ht hX
  · exact hN _ hK4 p hp hp2 α hαD hαp ht X hX

end Tags

end CFSG.StandardType
