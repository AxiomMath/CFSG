module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerTagsExcBasic
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcPilotRest
public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDivOmega
public import CFSG.RankThree.Chevalley.EvenPinnedRootSL2
import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE8F LayerExc

namespace TagsExc

variable {τ : Tag} {K : Type} [Field K]

section Family


theorem isSubCoreFamily_centralizer_toral [Finite K] [CharP K 2]
    (A : Subgroup ↥(adjointGroup τ K)) (hA : ∀ x ∈ A, (x : ModGL τ K) ∈ torusGroup τ K)
    {t : Kˣ} (ht : (t : K) ^ 2 ≠ 1)
    (hW : ∃ k, LayerFacts.ggDer (famStabilizerSubgroup (torusTuples A)) k ≤
      famReflectionGroup (torusTuples A)) :
    LayerCores.IsSubCoreFamily (Subgroup.centralizer (A : Set ↥(adjointGroup τ K)))
      (fun i => (componentRootSpan K (famChar (torusTuples A)) i).comap
        (adjointGroup τ K).subtype) := by
  classical
  obtain ⟨k, hk⟩ := hW
  have hHQM := torus_sup_rootSpan_le_map_centralizer A hA
  have hYN := map_famWeylReps_le_normalizer (K := K) (torusTuples A)
  have hMle := map_centralizer_le_sup A
  have hMN : (Subgroup.centralizer (A : Set ↥(adjointGroup τ K))).map
      (adjointGroup τ K).subtype ≤ Subgroup.normalizer
        ((torusGroup τ K ⊔ rootSpan τ K (famKernel (torusTuples A)) :
          Subgroup (ModGL τ K)) : Set (ModGL τ K)) :=
    hMle.trans (sup_le Subgroup.le_normalizer hYN)
  have hder : LayerFacts.ggDer ((Subgroup.centralizer (A : Set ↥(adjointGroup τ K))).map
      (adjointGroup τ K).subtype) (k + 1) ≤ rootSpan τ K (famKernel (torusTuples A)) := by
    rw [LayerFacts.ggDer_succ]
    have h1 := (LayerFacts.ggDer_mono hMle k).trans ((ggDer_sup_le_of_le_normalizer hYN k).trans
      (sup_le le_rfl (ggDer_map_famWeylReps_le hk)))
    exact (Subgroup.commutator_mono h1 h1).trans
      (commutator_torus_sup_rootSpan_le fun α hα => hα.1)
  have hsup : ⨆ i, componentRootSpan K (famChar (torusTuples A)) i =
      rootSpan τ K (famKernel (torusTuples A)) := by
    rw [iSup_componentRootSpan, kernelRoots_famChar]
  have hfam := isSubCoreFamily_of_le_of_normal (isSubCoreFamily_torus_sup_rootSpan _ ht) hHQM
    (fun u hu s hs => (Subgroup.mem_normalizer_iff.1 (hMN hu) s).1 hs)
    ⟨k + 1, by rw [hsup]; exact hder⟩
  have h := hfam.comap (adjointGroup τ K).subtype (adjointGroup τ K).subtype_injective (by
    rintro _ ⟨g, -, rfl⟩
    exact ⟨g, rfl⟩)
  rwa [Subgroup.comap_map_eq_self_of_injective (adjointGroup τ K).subtype_injective] at h

end Family

theorem small_of_dvd {a N n : ℕ} (ha : 2 ≤ a) (hN : 1 ≤ N) (h2 : 2 ^ (a * N) ∣ n)
    (hSL : 2 ^ a * ((2 ^ a) ^ 2 - 1) ∣ n) (hn : n = 174182400 ∨ n = 25920 ∨ n = 360) :
    (a = 2 ∧ N ≤ 6) ∨ (a = 3 ∧ N ≤ 4) := by
  have h2' : 2 ^ (a * N) ∣ n * 1 := by rwa [mul_one]
  obtain ⟨hb1, hb2, hb3⟩ := ggAKFG_le_of_dvd (z := 1) odd_one h2'
  have hb : a * N ≤ 12 := by
    rcases hn with rfl | rfl | rfl
    · exact hb1 rfl
    · exact (hb2 rfl).trans (by norm_num)
    · exact (hb3 rfl).trans (by norm_num)
  have ha12 : a ≤ 12 := le_trans (Nat.le_mul_of_pos_right a hN) hb
  interval_cases a
  · left; omega
  · right; omega
  all_goals exfalso; rcases hn with rfl | rfl | rfl <;> revert hSL <;> decide

section Orders


variable {M : Type} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
  {i : KernelComponent χ}

theorem odd_card_center_componentRootSpan [Finite K] [CharP K 2] :
    Odd (Nat.card (Subgroup.center ↥(componentRootSpan K χ i))) := by
  refine odd_card_center_of fun z hz hzc hz2 => ?_
  have hzZ : (⟨z, hz⟩ : componentRootSpan K χ i) ∈
      Subgroup.center (componentRootSpan K χ i) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hzc g g.2).symm
  have hT := componentTorus_le_torusGroup K χ i
    (CFSG.LieType.HighestRoot.coe_mem_componentTorus_of_mem_center hzZ)
  have hm := pow_eq_one_of_mem_torusGroup hT
  obtain ⟨k, hk⟩ := odd_card_units (K := K)
  rw [hk, pow_succ, pow_mul, hz2, one_pow, one_mul] at hm
  exact hm

theorem two_pow_dvd_ggCQ_componentRootSpan [Finite K] [CharP K 2] {a : ℕ}
    (ha : Nat.card K = 2 ^ a) :
    2 ^ (a * (posRoots (componentRoots χ i)).ncard) ∣ ggCQ (componentRootSpan K χ i) := by
  have hU : Nat.card (componentUnipotent K χ i) =
      Nat.card K ^ (posRoots (componentRoots χ i)).ncard :=
    card_rootSpan (fun _ h => isRoot_height_pos_of_mem_posRoots h)
      fun _ hα _ hβ a b ha hb hr => mem_posRoots_of_nsmul_add hα hβ a b ha hb hr
  have hdvd := Subgroup.card_dvd_of_le
    (componentUnipotent_le_componentRootSpan (K := K) (χ := χ) (i := i))
  rw [hU, ha, ← pow_mul, card_eq_ggCQ_mul] at hdvd
  exact (Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr
    odd_card_center_componentRootSpan)).dvd_of_dvd_mul_right hdvd

theorem card_sl2_dvd_ggCQ_componentRootSpan [Finite K] [CharP K 2] (hK4 : 4 ≤ Nat.card K)
    {α : Fin τ.rank → ℤ} (hα : α ∈ componentRoots χ i) :
    Nat.card K * (Nat.card K ^ 2 - 1) ∣ ggCQ (componentRootSpan K χ i) := by
  have hΨ := isRootComponent_componentRoots (χ := χ) i
  have hαr : IsRoot τ α := hΨ.isRoot α hα
  have hnα : -α ∈ componentRoots χ i := hΨ.neg_mem α hα
  obtain ⟨-, -, ⟨e, -⟩, -, -, -, -, -, -, -, -, hsimp⟩ :=
    CFSG.RankThree.Chevalley.even_Chevalley_pinned_root_SL2_maps τ K hαr
  obtain ⟨hQs, -, x, y, hxy⟩ := hsimp ‹_› hK4
  have hQS : rootSubgroup τ K α ⊔ rootSubgroup τ K (-α) ≤ componentRootSpan K χ i :=
    sup_le (le_iSup₂_of_le α hα le_rfl) (le_iSup₂_of_le (-α) hnα le_rfl)
  set f : ↥(rootSubgroup τ K α ⊔ rootSubgroup τ K (-α)) →*
      ↥(componentRootSpan K χ i) ⧸ Subgroup.center ↥(componentRootSpan K χ i) :=
    (QuotientGroup.mk' _).comp (Subgroup.inclusion hQS) with hf
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with h | h
    · exact h
    · exfalso
      apply hxy
      have hx : x ∈ f.ker := by rw [h]; trivial
      have hxZ : Subgroup.inclusion hQS x ∈ Subgroup.center ↥(componentRootSpan K χ i) :=
        (QuotientGroup.eq_one_iff _).mp hx
      have hc := Subgroup.mem_center_iff.mp hxZ (Subgroup.inclusion hQS y)
      apply Subtype.ext
      have hc' := congrArg Subtype.val hc
      simp only [Subgroup.coe_mul, Subgroup.coe_inclusion] at hc'
      simp only [Subgroup.coe_mul]
      exact hc'.symm
  have h1 := Subgroup.card_dvd_of_injective f hinj
  rw [← Nat.card_congr e.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two] at h1
  exact h1

theorem ggNotExcThree_componentRootSpan [Finite K] [CharP K 2] (hK4 : 4 ≤ Nat.card K)
    (hsmall : 2 < (componentRoots χ i).ncard →
      (Nat.card K = 4 ∧ (posRoots (componentRoots χ i)).ncard ≤ 6 ∨
        Nat.card K = 8 ∧ (posRoots (componentRoots χ i)).ncard ≤ 4) →
      GGNotExcThreeOrder (ggCQ (componentRootSpan K χ i))) :
    GGNotExcThreeOrder (ggCQ (componentRootSpan K χ i)) := by
  obtain ⟨a, -, ha⟩ := LayerExcThree.exists_card_eq_two_pow K
  have ha2 : 2 ≤ a := by
    by_contra h
    push Not at h
    interval_cases a <;> rw [ha] at hK4 <;> norm_num at hK4
  have hΨ := isRootComponent_componentRoots (χ := χ) i
  obtain ⟨⟨α, hαk⟩, hαi⟩ := Quotient.exists_rep i
  have hαΨ : α ∈ componentRoots χ i := ⟨hαk, hαi⟩
  by_cases hr : 2 < (componentRoots χ i).ncard
  · by_cases hs : Nat.card K = 4 ∧ (posRoots (componentRoots χ i)).ncard ≤ 6 ∨
        Nat.card K = 8 ∧ (posRoots (componentRoots χ i)).ncard ≤ 4
    · exact hsmall hr hs
    · refine (ggNotExcThreeOrder_iff _).mpr fun N₀ hN₀ heq => hs ?_
      have hN : 1 ≤ (posRoots (componentRoots χ i)).ncard := by
        have hfin : (posRoots (componentRoots χ i)).Finite :=
          (finite_setOf_isRoot τ).subset fun β hβ => hΨ.isRoot β hβ.1
        rcases mem_posRoots_or_mem_negRoots hΨ hαΨ with hp | hn
        · exact (Set.ncard_pos hfin).mpr ⟨α, hp⟩
        · exact (Set.ncard_pos hfin).mpr ⟨-α, hn⟩
      have h2 := two_pow_dvd_ggCQ_componentRootSpan (χ := χ) (i := i) ha
      have hSL := card_sl2_dvd_ggCQ_componentRootSpan hK4 hαΨ
      rw [ha] at hSL
      have hn : ggCQ (componentRootSpan K χ i) = 174182400 ∨
          ggCQ (componentRootSpan K χ i) = 25920 ∨ ggCQ (componentRootSpan K χ i) = 360 := by
        rcases hN₀ with rfl | rfl | rfl
        · exact Or.inl heq
        · exact Or.inr (Or.inl heq)
        · exact Or.inr (Or.inr heq)
      rcases small_of_dvd ha2 hN h2 hSL hn with ⟨rfl, h6⟩ | ⟨rfl, h4⟩
      · exact Or.inl ⟨by rw [ha]; norm_num, h6⟩
      · exact Or.inr ⟨by rw [ha]; norm_num, h4⟩
  ·
    push Not at hr
    have hsub : ({α, -α} : Set (Fin τ.rank → ℤ)) ⊆ componentRoots χ i :=
      Set.insert_subset hαΨ (Set.singleton_subset_iff.2 (hΨ.neg_mem α hαΨ))
    have hfin : (componentRoots χ i).Finite :=
      (finite_setOf_isRoot τ).subset fun β hβ => hΨ.isRoot β hβ
    have hne : α ≠ -α := by
      intro h
      refine (hΨ.isRoot α hαΨ).ne_zero (funext fun k => ?_)
      have h2 := congrFun h k
      simp only [Pi.neg_apply] at h2
      simp only [Pi.zero_apply]
      omega
    have hcard : ({α, -α} : Set (Fin τ.rank → ℤ)).ncard = 2 := Set.ncard_pair hne
    have heq : componentRoots χ i = {α, -α} :=
      (Set.eq_of_subset_of_ncard_le hsub (by rw [hcard]; omega) hfin).symm
    have hS : componentRootSpan K χ i = rootSubgroup τ K α ⊔ rootSubgroup τ K (-α) := by
      change rootSpan τ K (componentRoots χ i) = _
      rw [heq, rootSpan, iSup_insert, iSup_singleton]
    obtain ⟨-, -, ⟨e, -⟩, -⟩ :=
      CFSG.RankThree.Chevalley.even_Chevalley_pinned_root_SL2_maps τ K (hΨ.isRoot α hαΨ)
    exact LayerExcThree.ggNotExcThree_of_mulEquiv_SL le_rfl
      ((e.trans (MulEquiv.subgroupCongr hS.symm)).symm)

end Orders

theorem exists_unit_sq_ne_one [Finite K] [CharP K 2] (hK4 : 4 ≤ Nat.card K) :
    ∃ t : Kˣ, (t : K) ^ 2 ≠ 1 := by
  by_contra h
  push Not at h
  have h01 : ∀ x : K, x = 0 ∨ x = 1 := by
    intro x
    by_cases hx : x = 0
    · exact Or.inl hx
    · right
      have h1 : x ^ 2 = 1 := by simpa using h (Units.mk0 x hx)
      have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
      have h3 : (x - 1) ^ 2 = 0 := by linear_combination h1 + (1 - x) * h2
      exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h3)
  have hle : Nat.card K ≤ 2 := by
    have hsub : (Set.univ : Set K) ⊆ {0, 1} := fun x _ => by
      rcases h01 x with rfl | rfl <;> simp
    calc Nat.card K = (Set.univ : Set K).ncard := (Set.ncard_univ K).symm
      _ ≤ ({0, 1} : Set K).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ 2 := (Set.ncard_insert_le 0 {1}).trans (by rw [Set.ncard_singleton])
  omega

end TagsExc

section Inputs


@[expose] def GGExcSmallCompOrderInput : Prop :=
  ∀ (τ : Tag) (K : Type) [Field K] [Finite K] [CharP K 2] (M : Type) [CommGroup M]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (i : KernelComponent χ),
    2 < (componentRoots χ i).ncard →
    (Nat.card K = 4 ∧ (posRoots (componentRoots χ i)).ncard ≤ 6 ∨
      Nat.card K = 8 ∧ (posRoots (componentRoots χ i)).ncard ≤ 4) →
    GGNotExcThreeOrder (ggCQ (componentRootSpan K χ i))

@[expose] def GGExcCentCompNonToralInput (τ : Tag) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ s : ↥(adjointGroup τ K), s ^ p = 1 →
      ¬ GGExcToral τ K (Subgroup.zpowers s) →
      ∀ C : Subgroup ↥(adjointGroup τ K),
        IsComponentOf C (Subgroup.centralizer ({s} : Set ↥(adjointGroup τ K))) →
          GGNotExcThreeOrder (ggCQ C)

end Inputs

section Toral


variable {τ : Tag} {K : Type} [Field K]

theorem TagsExc.ggNotExcThree_of_isComponentOf_toral [Finite K] [CharP K 2]
    (hK4 : 4 ≤ Nat.card K) (hsmall : GGExcSmallCompOrderInput)
    (A : Subgroup ↥(adjointGroup τ K)) (hA : ∀ x ∈ A, (x : ModGL τ K) ∈ torusGroup τ K)
    (hW : ∃ k, LayerFacts.ggDer (famStabilizerSubgroup (torusTuples A)) k ≤
      famReflectionGroup (torusTuples A))
    {C : Subgroup ↥(adjointGroup τ K)}
    (hC : IsComponentOf C (Subgroup.centralizer (A : Set ↥(adjointGroup τ K)))) :
    GGNotExcThreeOrder (ggCQ C) := by
  obtain ⟨t, ht⟩ := TagsExc.exists_unit_sq_ne_one hK4
  have hfam := TagsExc.isSubCoreFamily_centralizer_toral A hA ht hW
  rw [← Subgroup.map_id (Subgroup.centralizer (A : Set ↥(adjointGroup τ K)))] at hC
  obtain ⟨c, rfl⟩ := LayerPDiv.exists_eq_map_of_isComponentOf_sub (MonoidHom.id _)
    (by rw [MonoidHom.ker_id]; exact bot_le) le_rfl
    (by rw [Subgroup.subgroupOf_self]; infer_instance) (LayerFacts.ggCommutator_self_le _) hfam hC
  change GGNotExcThreeOrder (ggCQ (((componentRootSpan K (famChar (torusTuples A)) c).comap
    (adjointGroup τ K).subtype).map (MonoidHom.id _)))
  rw [Subgroup.map_id, ggCQ_comap_of_injective _ (adjointGroup τ K).subtype_injective (by
    rw [Subgroup.range_subtype]; exact rootSpan_le_adjointGroup K _)]
  exact TagsExc.ggNotExcThree_componentRootSpan hK4 fun hr hs => hsmall τ K _ _ _ hr hs

theorem ggCentCompNotExcThree_of_inputs (hW : GGWeylFamQuotSolvInput τ)
    (hsmall : GGExcSmallCompOrderInput) (hN : GGExcCentCompNonToralInput τ) [Finite K]
    [CharP K 2] (hK4 : 4 ≤ Nat.card K) : GGCentCompNotExcThree ↥(adjointGroup τ K) := by
  intro p hp hp2 s hs C hC
  by_cases ht : GGExcToral τ K (Subgroup.zpowers s)
  · obtain ⟨g, hg⟩ := ht
    set e : ↥(adjointGroup τ K) ≃* ↥(adjointGroup τ K) := MulAut.conj g with he
    set A := (Subgroup.zpowers s).map e.toMonoidHom with hAdef
    have hcent : Subgroup.centralizer ({s} : Set ↥(adjointGroup τ K)) =
        (Subgroup.centralizer (A : Set ↥(adjointGroup τ K))).map e.symm.toMonoidHom := by
      rw [← Subgroup.comap_equiv_eq_map_symm', hAdef,
        ← LayerFacts.centralizer_eq_comap_map e (Subgroup.zpowers s),
        Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    rw [hcent] at hC
    have hC' := TagsExc.isComponentOf_comap e.symm.toMonoidHom e.symm.injective hC
    have hA : ∀ x ∈ A, (x : ModGL τ K) ∈ torusGroup τ K := by
      rintro _ ⟨x, hx, rfl⟩
      exact hg x hx
    have hpow : ∀ a ∈ torusTuples A, ∃ n : ℕ, a ^ p ^ n = 1 := by
      rintro a ⟨_, ⟨x, hx, rfl⟩, hxa⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      refine ⟨1, LayerExc.pow_eq_one_of_coe_eq_rootDiagUnit hxa ?_⟩
      rw [pow_one, ← map_pow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hs,
        one_zpow, map_one]
    have hWA : ∃ k, LayerFacts.ggDer (famStabilizerSubgroup (torusTuples A)) k ≤
        famReflectionGroup (torusTuples A) := by
      by_cases hcase : p ∣ Nat.card (famStabilizerSubgroup (torusTuples A))
      · exact hW K p hp hp2 _ hpow hcase
      · exact ⟨0, famStabilizer_subset_closure_of_coprime hp _ hpow hcase⟩
    have h1 := TagsExc.ggNotExcThree_of_isComponentOf_toral hK4 hsmall A hA hWA hC'
    rwa [ggCQ_comap_of_injective _ e.symm.injective (by
      rw [MonoidHom.range_eq_top.mpr e.symm.surjective]; exact le_top)] at h1
  · exact hN K hK4 p hp hp2 s hs ht C hC

end Toral

end CFSG.StandardType
