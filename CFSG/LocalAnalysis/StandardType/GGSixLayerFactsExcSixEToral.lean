module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixEReduce
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcPilotRest

public section

namespace CFSG.StandardType

namespace LayerSixE

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE8F LayerExc

variable {τ : Tag} {K : Type} [Field K]

section FamDef

@[expose] def famCentralizer (F : Set (Fin τ.rank → Kˣ)) : Subgroup ↥(adjointGroup τ K) where
  carrier := {g | ∀ a ∈ F, rootDiagUnit τ a * (g : ModGL τ K) * (rootDiagUnit τ a)⁻¹ = g}
  one_mem' := fun a _ => by
    rw [OneMemClass.coe_one, mul_one, mul_inv_cancel]
  mul_mem' := fun {g h} hg hh a ha => by
    rw [Subgroup.coe_mul]
    calc rootDiagUnit τ a * ((g : ModGL τ K) * h) * (rootDiagUnit τ a)⁻¹ =
          (rootDiagUnit τ a * g * (rootDiagUnit τ a)⁻¹) *
            (rootDiagUnit τ a * h * (rootDiagUnit τ a)⁻¹) := by group
      _ = g * h := by rw [hg a ha, hh a ha]
  inv_mem' := fun {g} hg a ha => by
    rw [Subgroup.coe_inv]
    calc rootDiagUnit τ a * (g : ModGL τ K)⁻¹ * (rootDiagUnit τ a)⁻¹ =
          (rootDiagUnit τ a * g * (rootDiagUnit τ a)⁻¹)⁻¹ := by group
      _ = (g : ModGL τ K)⁻¹ := by rw [hg a ha]

theorem mem_famCentralizer {F : Set (Fin τ.rank → Kˣ)} {g : ↥(adjointGroup τ K)} :
    g ∈ famCentralizer F ↔
      ∀ a ∈ F, rootDiagUnit τ a * (g : ModGL τ K) * (rootDiagUnit τ a)⁻¹ = g :=
  Iff.rfl

end FamDef

section Family


theorem torus_sup_rootSpan_le_map_famCentralizer (F : Set (Fin τ.rank → Kˣ)) :
    torusGroup τ K ⊔ rootSpan τ K (famKernel F) ≤
      (famCentralizer F).map (adjointGroup τ K).subtype := by
  intro x hx
  have hxL : x ∈ adjointGroup τ K :=
    (sup_le CFSG.RankThree.PartOne.KE.torusGroup_le_adjointGroup'
      (rootSpan_le_adjointGroup K _)) hx
  refine ⟨⟨x, hxL⟩, fun l hlF => ?_, rfl⟩
  have hle : torusGroup τ K ⊔ rootSpan τ K (famKernel F) ≤
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
  have hc := Subgroup.mem_centralizer_singleton_iff.1 (hle hx)
  change rootDiagUnit τ l * x * (rootDiagUnit τ l)⁻¹ = x
  rw [← hc, mul_inv_cancel_right]

theorem map_famWeylReps_le_map_famCentralizer (F : Set (Fin τ.rank → Kˣ)) :
    (famWeylReps F).map (monomialSubgroup τ K).subtype ≤
      (famCentralizer F).map (adjointGroup τ K).subtype := by
  rw [famWeylReps, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨n, ⟨w, hw, hn⟩, rfl⟩
  change (n : ModGL τ K) ∈ _
  rw [hn]
  exact ⟨⟨_, canonicalRep_mem_adjointGroup _ K w⟩,
    fun l hl => (conj_canonicalRep_eq_iff l w).2 (hw l hl), rfl⟩

theorem map_famCentralizer_le_sup (F : Set (Fin τ.rank → Kˣ)) :
    (famCentralizer F).map (adjointGroup τ K).subtype ≤
      (torusGroup τ K ⊔ rootSpan τ K (famKernel F)) ⊔
        (famWeylReps F).map (monomialSubgroup τ K).subtype := by
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨w, hw, h, hh, u, hu, v, hv, hg'⟩ := fam_factor F g.2 hg
  have hQ : ∀ {S : Set (Fin τ.rank → ℤ)}, S ⊆ famKernel F →
      rootSpan τ K S ≤ torusGroup τ K ⊔ rootSpan τ K (famKernel F) := fun hS =>
    (rootSpan_mono hS).trans le_sup_right
  have hn : canonicalRep (coxeterSystem τ) K w ∈
      (famWeylReps F).map (monomialSubgroup τ K).subtype :=
    ⟨⟨_, canonicalRep_mem_monomialSubgroup K w⟩, Subgroup.subset_closure ⟨w, hw, rfl⟩, rfl⟩
  change (g : ModGL τ K) ∈ _
  rw [hg']
  exact mul_mem (mul_mem (mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_left hh))
    (Subgroup.mem_sup_left (hQ Set.inter_subset_left hu))) (Subgroup.mem_sup_right hn))
    (Subgroup.mem_sup_left (hQ Set.inter_subset_left hv))

theorem exists_subCoreFamily_famCentralizer [Finite K] [CharP K 2]
    (F : Set (Fin τ.rank → Kˣ)) {t : Kˣ} (ht : (t : K) ^ 2 ≠ 1)
    (hW : ∃ k, LayerFacts.ggDer (famStabilizerSubgroup F) k ≤ famReflectionGroup F) :
    ∃ (β : Type) (S : β → Subgroup ↥(adjointGroup τ K)),
      LayerCores.IsSubCoreFamily (famCentralizer F) S := by
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
  rw [Subgroup.comap_map_eq_self_of_injective (adjointGroup τ K).subtype_injective] at h
  exact ⟨_, _, h⟩

end Family

section Toral


@[expose] def GGInndiagToral (τ : Tag) (K : Type) [Field K]
    (A : Subgroup (MulAut ↥(adjointGroup τ K))) : Prop :=
  ∃ c : ↥(adjointGroup τ K), ∀ α ∈ A,
    MulAut.conj c * α * (MulAut.conj c)⁻¹ ∈ (rootDiagAutHom τ K).range

@[expose] def conjTuples (A : Subgroup (MulAut ↥(adjointGroup τ K))) (c : ↥(adjointGroup τ K)) :
    Set (Fin τ.rank → Kˣ) :=
  {a | ∃ α ∈ A, rootDiagAutHom τ K a = MulAut.conj c * α * (MulAut.conj c)⁻¹}

theorem conj_mul_apply_conj (α : MulAut ↥(adjointGroup τ K)) (c x : ↥(adjointGroup τ K)) :
    (MulAut.conj c * α * (MulAut.conj c)⁻¹) (c * x * c⁻¹) = c * α x * c⁻¹ := by
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_inv_apply, MulAut.conj_apply]
  congr 2
  group

theorem autFix_eq_comap_famCentralizer (A : Subgroup (MulAut ↥(adjointGroup τ K)))
    (c : ↥(adjointGroup τ K))
    (hc : ∀ α ∈ A, MulAut.conj c * α * (MulAut.conj c)⁻¹ ∈ (rootDiagAutHom τ K).range) :
    autFix A = (famCentralizer (conjTuples A c)).comap (MulAut.conj c).toMonoidHom := by
  ext x
  rw [Subgroup.mem_comap, mem_autFix, mem_famCentralizer]
  constructor
  · rintro hx a ⟨α, hα, hαa⟩
    have h := congrArg (fun φ : MulAut ↥(adjointGroup τ K) =>
      ((φ (c * x * c⁻¹) : ↥(adjointGroup τ K)) : ModGL τ K)) hαa
    rw [conj_mul_apply_conj, hx α hα] at h
    exact h
  · intro hx α hα
    obtain ⟨a, ha⟩ := hc α hα
    have h1 := hx a ⟨α, hα, ha⟩
    have h2 : (MulAut.conj c * α * (MulAut.conj c)⁻¹) (c * x * c⁻¹) = c * x * c⁻¹ := by
      rw [← ha]
      exact Subtype.ext h1
    rw [conj_mul_apply_conj] at h2
    simpa using h2

end Toral

section ToralCore


theorem exists_subCoreFamily_autFix_of_toral [Finite K] [CharP K 2]
    (hq : CFSG.IsQuasisimple ↥(adjointGroup τ K)) (hW : GGWeylFamQuotSolvInput τ) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (A : Subgroup (MulAut ↥(adjointGroup τ K)))
    (hA : IsPGroup p A) (ht : GGInndiagToral τ K A) :
    ∃ (β : Type) (S : β → Subgroup ↥(adjointGroup τ K)), LayerCores.IsSubCoreFamily (autFix A) S := by
  obtain ⟨c, hc⟩ := ht
  rw [autFix_eq_comap_famCentralizer A c hc]
  suffices h : ∃ (β : Type) (S : β → Subgroup ↥(adjointGroup τ K)),
      LayerCores.IsSubCoreFamily (famCentralizer (conjTuples A c)) S by
    obtain ⟨β, S, hS⟩ := h
    refine ⟨β, fun i => (S i).comap (MulAut.conj c).toMonoidHom, ?_⟩
    exact hS.comap _ (MulAut.conj c).injective (by
      rw [MonoidHom.range_eq_top.mpr (MulAut.conj c).surjective]
      exact le_top)
  have hpow : ∀ a ∈ conjTuples A c, ∃ n : ℕ, a ^ p ^ n = 1 := by
    rintro a ⟨α, hα, hαa⟩
    obtain ⟨n, hn⟩ := hA ⟨α, hα⟩
    have hαn : α ^ p ^ n = 1 := by simpa using congrArg Subtype.val hn
    refine ⟨n, rootDiagAutHom_injective ?_⟩
    rw [map_pow, hαa, map_one, conj_pow, hαn, mul_one, mul_inv_cancel]
  by_cases hF : ∃ a ∈ conjTuples A c, a ≠ 1
  · obtain ⟨a₀, -, ha₀1⟩ := hF
    obtain ⟨j, hj⟩ : ∃ j, a₀ j ≠ 1 := by
      by_contra h
      push Not at h
      exact ha₀1 (funext h)
    have ht : ((a₀ j : Kˣ) : K) ^ 2 ≠ 1 := by
      intro h
      have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
      have h3 : ((a₀ j : K) - 1) ^ 2 = 0 := by linear_combination h + (1 - (a₀ j : K)) * h2
      exact hj (Units.ext (by simpa [sub_eq_zero] using h3))
    by_cases hdvd : p ∣ Nat.card (famStabilizerSubgroup (conjTuples A c))
    · exact exists_subCoreFamily_famCentralizer _ ht (hW K p hp hp2 _ hpow hdvd)
    · exact exists_subCoreFamily_famCentralizer _ ht
        ⟨0, famStabilizer_subset_closure_of_coprime hp _ hpow hdvd⟩
  · push Not at hF
    have htop : famCentralizer (conjTuples A c) =
        Subgroup.centralizer ((⊥ : Subgroup ↥(adjointGroup τ K)) : Set ↥(adjointGroup τ K)) := by
      ext g
      rw [mem_famCentralizer, Subgroup.mem_centralizer_iff]
      constructor
      · intro _ y hy
        rw [SetLike.mem_coe, Subgroup.mem_bot] at hy
        rw [hy, one_mul, mul_one]
      · intro _ a ha
        rw [hF a ha, rootDiagUnit_one, one_mul, inv_one, mul_one]
    rw [htop]
    exact exists_subCoreFamily_centralizer_bot hq center_adjointGroup_eq_bot

end ToralCore

end LayerSixE

end CFSG.StandardType
