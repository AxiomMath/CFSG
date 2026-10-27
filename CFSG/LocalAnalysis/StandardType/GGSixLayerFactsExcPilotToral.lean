module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcToral
public import CFSG.LieType.Chevalley.ToralCentralizerQuotient

public section

namespace CFSG.StandardType

namespace LayerExc

section Normal

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem commutator_sup_le_of_le_normalizer {N Y : Subgroup G}
    (hY : Y ≤ Subgroup.normalizer (N : Set G)) : ⁅N ⊔ Y, N ⊔ Y⁆ ≤ N ⊔ ⁅Y, Y⁆ := by
  have hdec : ∀ g ∈ N ⊔ Y, ∃ n ∈ N, ∃ y ∈ Y, g = n * y := by
    intro g hg
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left N Y hY] at hg
    obtain ⟨n, hn, y, hy, rfl⟩ := hg
    exact ⟨n, hn, y, hy, rfl⟩
  have hconj : ∀ y ∈ Y, ∀ n ∈ N, y * n * y⁻¹ ∈ N := fun y hy n hn =>
    (Subgroup.mem_normalizer_iff.1 (hY hy) n).1 hn
  rw [Subgroup.commutator_le]
  intro g₁ h₁ g₂ h₂
  obtain ⟨n₁, hn₁, y₁, hy₁, rfl⟩ := hdec g₁ h₁
  obtain ⟨n₂, hn₂, y₂, hy₂, rfl⟩ := hdec g₂ h₂
  have hc : ⁅y₁, y₂⁆ ∈ ⁅Y, Y⁆ := Subgroup.commutator_mem_commutator hy₁ hy₂
  have hcY : ⁅y₁, y₂⁆ ∈ Y := Subgroup.commutator_le_self Y hc
  have hm₁ : n₁ * (y₁ * n₂ * y₁⁻¹) ∈ N := mul_mem hn₁ (hconj y₁ hy₁ n₂ hn₂)
  have hm₂ : n₂ * (y₂ * n₁ * y₂⁻¹) ∈ N := mul_mem hn₂ (hconj y₂ hy₂ n₁ hn₁)
  have e : ⁅n₁ * y₁, n₂ * y₂⁆ = n₁ * (y₁ * n₂ * y₁⁻¹) *
      (⁅y₁, y₂⁆ * (n₂ * (y₂ * n₁ * y₂⁻¹))⁻¹ * ⁅y₁, y₂⁆⁻¹) * ⁅y₁, y₂⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact mul_mem (Subgroup.mem_sup_left (mul_mem hm₁ (hconj _ hcY _ (inv_mem hm₂))))
    (Subgroup.mem_sup_right hc)

theorem ggDer_le_self (Y : Subgroup G) (k : ℕ) : LayerFacts.ggDer Y k ≤ Y := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [LayerFacts.ggDer_succ]
    exact (Subgroup.commutator_le_self _).trans ih

theorem ggDer_sup_le_of_le_normalizer {N Y : Subgroup G}
    (hY : Y ≤ Subgroup.normalizer (N : Set G)) (k : ℕ) :
    LayerFacts.ggDer (N ⊔ Y) k ≤ N ⊔ LayerFacts.ggDer Y k := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [LayerFacts.ggDer_succ, LayerFacts.ggDer_succ]
    exact (Subgroup.commutator_mono ih ih).trans
      (commutator_sup_le_of_le_normalizer ((ggDer_le_self Y k).trans hY))

theorem isSubCoreFamily_of_le_of_normal {H₀ H : Subgroup G} {β : Type} {S : β → Subgroup G}
    (h : LayerCores.IsSubCoreFamily H₀ S) (hle : H₀ ≤ H)
    (hn : ∀ u ∈ H, ∀ s ∈ H₀, u * s * u⁻¹ ∈ H₀) (hk : ∃ k, LayerFacts.ggDer H k ≤ ⨆ c, S c) :
    LayerCores.IsSubCoreFamily H S := by
  obtain ⟨hS, hsn, hq, -, hz⟩ := h
  exact ⟨fun c => (hS c).trans hle, fun c => LayerCores.ggSubnormal_trans (hsn c)
    (LayerCores.ggSubnormal_of_normal hle hn), hq, hk, hz⟩

end Normal

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE8F

variable {τ : Tag} {K : Type} [Field K]

section Weyl

@[expose] def famStabilizerSubgroup (F : Set (Fin τ.rank → Kˣ)) : Subgroup (WeylGroup τ) where
  carrier := famStabilizer F
  one_mem' _ _ v := by rw [one_smul]
  mul_mem' {w w'} hw hw' a ha v := by rw [mul_smul, hw a ha, hw' a ha]
  inv_mem' {w} hw a ha v := by rw [← hw a ha (w⁻¹ • v), smul_inv_smul]

@[expose] def famReflectionGroup (F : Set (Fin τ.rank → Kˣ)) : Subgroup (WeylGroup τ) :=
  Subgroup.closure {s | ∃ α ∈ famKernel F, s = rootReflection α}

@[expose] def torusTuples (A : Subgroup ↥(adjointGroup τ K)) : Set (Fin τ.rank → Kˣ) :=
  {a | ∃ x ∈ A, (x : ModGL τ K) = rootDiagUnit τ a}

theorem image_famKernel {F : Set (Fin τ.rank → Kˣ)} {w : WeylGroup τ}
    (hw : w ∈ famStabilizer F) : (fun α => w • α) '' famKernel F = famKernel F := by
  have hw' : w⁻¹ ∈ famStabilizer F := (famStabilizerSubgroup F).inv_mem hw
  ext β
  constructor
  · rintro ⟨α, ⟨hα, hαa⟩, rfl⟩
    exact ⟨IsRoot.smul hα w, fun a ha => (hw a ha α).trans (hαa a ha)⟩
  · rintro ⟨hβ, hβa⟩
    exact ⟨w⁻¹ • β, ⟨IsRoot.smul hβ w⁻¹, fun a ha => (hw' a ha β).trans (hβa a ha)⟩,
      smul_inv_smul w β⟩

end Weyl

section Toral


@[expose] noncomputable def famWeylReps (F : Set (Fin τ.rank → Kˣ)) :
    Subgroup ↥(monomialSubgroup τ K) :=
  Subgroup.closure {n | ∃ w ∈ famStabilizer F,
    (n : ModGL τ K) = canonicalRep (coxeterSystem τ) K w}

theorem canonicalRep_mem_normalizer_torus_sup {F : Set (Fin τ.rank → Kˣ)} {w : WeylGroup τ}
    (hw : w ∈ famStabilizer F) :
    canonicalRep (coxeterSystem τ) K w ∈ Subgroup.normalizer
      ((torusGroup τ K ⊔ rootSpan τ K (famKernel F) : Subgroup (ModGL τ K)) :
        Set (ModGL τ K)) := by
  have hT := map_conj_eq_of_mem_normalizer (canonicalRep_mem_normalizer (R := K) w)
  have hS := (canonical_weyl_root_transport τ K).1 w (famKernel F) fun α hα => hα.1
  rw [image_famKernel hw] at hS
  have hmap : (torusGroup τ K ⊔ rootSpan τ K (famKernel F)).map
      (MulAut.conj (canonicalRep (coxeterSystem τ) K w)).toMonoidHom =
        torusGroup τ K ⊔ rootSpan τ K (famKernel F) := by
    rw [Subgroup.map_sup, hT, hS]
  rw [Subgroup.mem_normalizer_iff_conj_image_eq]
  have h := congrArg SetLike.coe hmap
  rw [Subgroup.coe_map] at h
  exact h

theorem map_weylQuotientHom_famWeylReps_le (F : Set (Fin τ.rank → Kˣ)) :
    (famWeylReps (K := K) F).map (weylQuotientHom τ K) ≤ famStabilizerSubgroup F := by
  rw [famWeylReps, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨n, ⟨w, hw, hn⟩, rfl⟩
  have h : weylQuotientHom τ K n = w :=
    weylQuotientHom_eq (by rw [hn]; exact mapsRootLines_canonicalRep (R := K) w)
  rw [SetLike.mem_coe, h]
  exact hw

theorem coe_mem_torus_sup_rootSpan_of_mem {F : Set (Fin τ.rank → Kˣ)}
    {n : ↥(monomialSubgroup τ K)} (hn : weylQuotientHom τ K n ∈ famReflectionGroup F) :
    (n : ModGL τ K) ∈ torusGroup τ K ⊔ rootSpan τ K (famKernel F) := by
  obtain ⟨w, k, hk, hnk⟩ := monomialSubgroup_le_torusWeylCosets n.2
  have hmaps : MapsRootLines (n : (Module.End K (RootModule τ K))ˣ) w := by
    rw [hnk]
    simpa using (mapsRootLines_of_mem_torusGroup hk).mul (mapsRootLines_canonicalRep (R := K) w)
  rw [weylQuotientHom_eq hmaps] at hn
  have hnw : canonicalRep (coxeterSystem τ) K w ∈ torusGroup τ K ⊔ rootSpan τ K (famKernel F) :=
    canonicalRep_mem_sup_of_mem_closure (fun α hα => hα.1) (fun α hα => neg_mem_famKernel hα) hn
  change (n : (Module.End K (RootModule τ K))ˣ) ∈ _
  rw [hnk]
  exact mul_mem (Subgroup.mem_sup_left hk) hnw

theorem map_famWeylReps_le_normalizer (F : Set (Fin τ.rank → Kˣ)) :
    (famWeylReps (K := K) F).map (monomialSubgroup τ K).subtype ≤
      Subgroup.normalizer ((torusGroup τ K ⊔ rootSpan τ K (famKernel F) :
        Subgroup (ModGL τ K)) : Set (ModGL τ K)) := by
  rw [famWeylReps, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨n, ⟨w, hw, hn⟩, rfl⟩
  change (n : ModGL τ K) ∈ _
  rw [hn]
  exact canonicalRep_mem_normalizer_torus_sup hw

theorem ggDer_map_famWeylReps_le {F : Set (Fin τ.rank → Kˣ)} {k : ℕ}
    (hk : LayerFacts.ggDer (famStabilizerSubgroup F) k ≤ famReflectionGroup F) :
    LayerFacts.ggDer ((famWeylReps (K := K) F).map (monomialSubgroup τ K).subtype) k ≤
      torusGroup τ K ⊔ rootSpan τ K (famKernel F) := by
  rw [← LayerFacts.map_ggDer]
  rintro _ ⟨n, hn, rfl⟩
  have h1 : weylQuotientHom τ K n ∈ LayerFacts.ggDer (famStabilizerSubgroup F) k := by
    have h2 := LayerFacts.ggDer_mono (map_weylQuotientHom_famWeylReps_le (K := K) F) k
    rw [← LayerFacts.map_ggDer] at h2
    exact h2 ⟨n, hn, rfl⟩
  exact coe_mem_torus_sup_rootSpan_of_mem (hk h1)

theorem torus_sup_rootSpan_le_map_centralizer (A : Subgroup ↥(adjointGroup τ K))
    (hA : ∀ x ∈ A, (x : ModGL τ K) ∈ torusGroup τ K) :
    torusGroup τ K ⊔ rootSpan τ K (famKernel (torusTuples A)) ≤
      (Subgroup.centralizer (A : Set ↥(adjointGroup τ K))).map (adjointGroup τ K).subtype := by
  intro x hx
  have hxL : x ∈ adjointGroup τ K :=
    (sup_le CFSG.RankThree.PartOne.KE.torusGroup_le_adjointGroup'
      (rootSpan_le_adjointGroup K _)) hx
  refine ⟨⟨x, hxL⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hA y hy)
  have hlF : l ∈ torusTuples A := ⟨y, hy, hl⟩
  have hle : torusGroup τ K ⊔ rootSpan τ K (famKernel (torusTuples A)) ≤
      Subgroup.centralizer ({rootDiagUnit τ l} : Set (ModGL τ K)) := by
    refine sup_le (fun h hh => ?_) ?_
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (rootDiagUnit_mul_comm_of_mem_torusGroup l hh).symm
    · refine iSup₂_le fun α hα => (Subgroup.closure_le _).2 ?_
      rintro _ ⟨c, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      have h1 := rootDiagUnit_conj_pinnedX l hα.1 c
      rw [hα.2 l hlF, Units.val_one, one_mul] at h1
      calc pinnedX τ K α c * rootDiagUnit τ l =
            rootDiagUnit τ l * pinnedX τ K α c * (rootDiagUnit τ l)⁻¹ * rootDiagUnit τ l := by
            rw [h1]
        _ = rootDiagUnit τ l * pinnedX τ K α c := by group
  have hc := hle hx
  refine Subtype.ext ?_
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hl]
  exact (Subgroup.mem_centralizer_singleton_iff.1 hc).symm

theorem map_famWeylReps_le_map_centralizer (A : Subgroup ↥(adjointGroup τ K))
    (hA : ∀ x ∈ A, (x : ModGL τ K) ∈ torusGroup τ K) :
    (famWeylReps (torusTuples A)).map (monomialSubgroup τ K).subtype ≤
      (Subgroup.centralizer (A : Set ↥(adjointGroup τ K))).map (adjointGroup τ K).subtype := by
  rw [famWeylReps, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨n, ⟨w, hw, hn⟩, rfl⟩
  change (n : ModGL τ K) ∈ _
  rw [hn]
  refine ⟨⟨_, canonicalRep_mem_adjointGroup _ K w⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hA y hy)
  have h1 := (conj_canonicalRep_eq_iff l w).2 (hw l ⟨y, hy, hl⟩)
  refine Subtype.ext ?_
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hl]
  calc rootDiagUnit τ l * canonicalRep (coxeterSystem τ) K w =
        rootDiagUnit τ l * canonicalRep (coxeterSystem τ) K w * (rootDiagUnit τ l)⁻¹ *
          rootDiagUnit τ l := by group
    _ = canonicalRep (coxeterSystem τ) K w * rootDiagUnit τ l := by rw [h1]

theorem map_centralizer_le_sup (A : Subgroup ↥(adjointGroup τ K)) :
    (Subgroup.centralizer (A : Set ↥(adjointGroup τ K))).map (adjointGroup τ K).subtype ≤
      (torusGroup τ K ⊔ rootSpan τ K (famKernel (torusTuples A))) ⊔
        (famWeylReps (torusTuples A)).map (monomialSubgroup τ K).subtype := by
  rintro _ ⟨g, hg, rfl⟩
  have hcomm : ∀ a ∈ torusTuples A,
      rootDiagUnit τ a * (g : ModGL τ K) * (rootDiagUnit τ a)⁻¹ = g := by
    rintro a ⟨x, hx, hxa⟩
    rw [← hxa]
    have h' := congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hg x hx)
    rw [Subgroup.coe_mul, Subgroup.coe_mul] at h'
    rw [h']
    group
  obtain ⟨w, hw, h, hh, u, hu, v, hv, hg'⟩ := fam_factor (torusTuples A) g.2 hcomm
  have hQ : ∀ {S : Set (Fin τ.rank → ℤ)}, S ⊆ famKernel (torusTuples A) →
      rootSpan τ K S ≤ torusGroup τ K ⊔ rootSpan τ K (famKernel (torusTuples A)) := fun hS =>
    (rootSpan_mono hS).trans le_sup_right
  have hn : canonicalRep (coxeterSystem τ) K w ∈
      (famWeylReps (torusTuples A)).map (monomialSubgroup τ K).subtype :=
    ⟨⟨_, canonicalRep_mem_monomialSubgroup K w⟩, Subgroup.subset_closure ⟨w, hw, rfl⟩, rfl⟩
  change (g : ModGL τ K) ∈ _
  rw [hg']
  exact mul_mem (mul_mem (mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_left hh))
    (Subgroup.mem_sup_left (hQ Set.inter_subset_left hu))) (Subgroup.mem_sup_right hn))
    (Subgroup.mem_sup_left (hQ Set.inter_subset_left hv))

theorem exists_subCoreFamily_centralizer_of_toral [Finite K] [CharP K 2]
    (A : Subgroup ↥(adjointGroup τ K)) (hA : ∀ x ∈ A, (x : ModGL τ K) ∈ torusGroup τ K)
    (hA1 : A ≠ ⊥)
    (hW : ∃ k, LayerFacts.ggDer (famStabilizerSubgroup (torusTuples A)) k ≤
      famReflectionGroup (torusTuples A)) :
    ∃ (β : Type) (S : β → Subgroup ↥(adjointGroup τ K)),
      LayerCores.IsSubCoreFamily (Subgroup.centralizer (A : Set ↥(adjointGroup τ K))) S := by
  classical
  obtain ⟨k, hk⟩ := hW
  obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hA1
  obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hA _ x.2)
  obtain ⟨j, hj⟩ : ∃ j, l j ≠ 1 := by
    by_contra h
    push Not at h
    apply hx1
    have hl1 : l = 1 := funext h
    rw [hl1, rootDiagUnit_one] at hl
    exact Subtype.ext (Subtype.ext hl)
  have ht : ((l j : Kˣ) : K) ^ 2 ≠ 1 := by
    intro h
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    have h3 : ((l j : K) - 1) ^ 2 = 0 := by linear_combination h + (1 - (l j : K)) * h2
    exact hj (Units.ext (by simpa [sub_eq_zero] using h3))
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
  rw [Subgroup.comap_map_eq_self_of_injective (adjointGroup τ K).subtype_injective] at h
  exact ⟨_, _, h⟩

end Toral

end LayerExc

end CFSG.StandardType
