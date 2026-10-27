module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL4Rel
public import CFSG.Quasithin.Background.F6GoldschmidtList

public section

namespace CFSG.Quasithin.F6.GoldAmL4

variable {D E : Type*} [Group D] [Group E]

theorem closure_range_union {a b s : D} (hT : TRel a b s) (y : D) :
    Subgroup.closure ((hT.emb.range : Set D) ∪ {y}) = Subgroup.closure ({a, b, s, y} : Set D) := by
  rw [Subgroup.closure_union, Subgroup.closure_eq, hT.emb_range]
  rw [← Subgroup.closure_union]
  congr 1
  ext g
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

theorem exists_vertex_isos {a b s x y : D} {a' b' s' x' y' : E}
    (hA : ARel a b s x) (hB : BRel a b s y) (hA' : ARel a' b' s' x') (hB' : BRel a' b' s' y')
    (hcard : Nat.card (Subgroup.closure ({a, b, s} : Set D)) = 32)
    (hcard' : Nat.card (Subgroup.closure ({a', b', s'} : Set E)) = 32) :
    ∃ (φ₁ : ↥(Subgroup.closure ({a, b, s, y} : Set D)) ≃*
        ↥(Subgroup.closure ({a', b', s', y'} : Set E)))
      (φ₂ : ↥(Subgroup.closure ({a, b, s, x} : Set D)) ≃*
        ↥(Subgroup.closure ({a', b', s', x'} : Set E))),
      (∀ w : Tc, ∀ hg : hA.toTRel.emb w ∈ Subgroup.closure ({a, b, s, y} : Set D),
        ((φ₁ ⟨hA.toTRel.emb w, hg⟩ : ↥(Subgroup.closure ({a', b', s', y'} : Set E))) : E) =
          hA'.toTRel.emb w) ∧
      (∀ w : Tc, ∀ hg : hA.toTRel.emb w ∈ Subgroup.closure ({a, b, s, x} : Set D),
        ((φ₂ ⟨hA.toTRel.emb w, hg⟩ : ↥(Subgroup.closure ({a', b', s', x'} : Set E))) : E) =
          hA'.toTRel.emb w) ∧
      ((φ₁ ⟨y, Subgroup.subset_closure (by simp)⟩ :
        ↥(Subgroup.closure ({a', b', s', y'} : Set E))) : E) = y' ∧
      ((φ₂ ⟨x, Subgroup.subset_closure (by simp)⟩ :
        ↥(Subgroup.closure ({a', b', s', x'} : Set E))) : E) = x' := by
  have hT := hA.toTRel
  have hT' := hA'.toTRel
  have hinj := hT.emb_injective hcard
  have hinj' := hT'.emb_injective hcard'
  have hvA := hA.vertexSpec hinj
  have hvA' := hA'.vertexSpec hinj'
  have hvB : VertexSpec hT m2Sub tT0 y (Fu alpha0) tT0 tT0 := hB.vertexSpec hinj
  have hvB' : VertexSpec hT' m2Sub tT0 y' (Fu alpha0) tT0 tT0 := hB'.vertexSpec hinj'
  obtain ⟨φA, hφA, hφAx⟩ := hvA.vertex_iso hinj hinj' base_or hvA'
  obtain ⟨φB, hφB, hφBy⟩ := hvB.vertex_iso hinj hinj' m2_or hvB'
  have eA := closure_range_union hT x
  have eB := closure_range_union hT y
  have eA' := closure_range_union hT' x'
  have eB' := closure_range_union hT' y'
  exact ⟨(MulEquiv.subgroupCongr eB.symm).trans (φB.trans (MulEquiv.subgroupCongr eB')),
    (MulEquiv.subgroupCongr eA.symm).trans (φA.trans (MulEquiv.subgroupCongr eA')),
    fun w hg => hφB w, fun w hg => hφA w, hφBy, hφAx⟩

theorem isAmalgamIso_of_tuples {a b s x y : D} {a' b' s' x' y' : E}
    (hA : ARel a b s x) (hB : BRel a b s y) (hA' : ARel a' b' s' x') (hB' : BRel a' b' s' y')
    (hcard : Nat.card (Subgroup.closure ({a, b, s} : Set D)) = 32)
    (hcard' : Nat.card (Subgroup.closure ({a', b', s'} : Set E)) = 32)
    (hinf : Subgroup.closure ({a, b, s, y} : Set D) ⊓ Subgroup.closure ({a, b, s, x} : Set D) =
      Subgroup.closure ({a, b, s} : Set D))
    (hinf' : Subgroup.closure ({a', b', s', y'} : Set E) ⊓
      Subgroup.closure ({a', b', s', x'} : Set E) = Subgroup.closure ({a', b', s'} : Set E)) :
    CFSG.Quasithin.F6.IsAmalgamIso (Subgroup.closure ({a, b, s, y} : Set D))
      (Subgroup.closure ({a, b, s, x} : Set D)) (Subgroup.closure ({a', b', s', y'} : Set E))
      (Subgroup.closure ({a', b', s', x'} : Set E)) := by
  have hT := hA.toTRel
  have hT' := hA'.toTRel
  have eA := closure_range_union hT x
  have eB := closure_range_union hT y
  have eA' := closure_range_union hT' x'
  have eB' := closure_range_union hT' y'
  obtain ⟨φ₁, φ₂, hv₁, hv₂, -, -⟩ := exists_vertex_isos hA hB hA' hB' hcard hcard'
  have hT1 : Subgroup.closure ({a, b, s} : Set D) = hT.emb.range := hT.emb_range.symm
  have hT1' : Subgroup.closure ({a', b', s'} : Set E) = hT'.emb.range := hT'.emb_range.symm
  refine ⟨φ₁, φ₂, ?_, ?_⟩
  · intro g hg₁ hg₂
    have hgT : g ∈ Subgroup.closure ({a, b, s} : Set D) := by
      rw [← hinf]; exact ⟨hg₁, hg₂⟩
    rw [hT1] at hgT
    obtain ⟨w, rfl⟩ := hgT
    rw [hv₁ w hg₁, hv₂ w hg₂]
  · intro g hg₁ hg₂
    have hgT : g ∈ Subgroup.closure ({a', b', s'} : Set E) := by
      rw [← hinf']; exact ⟨hg₁, hg₂⟩
    rw [hT1'] at hgT
    obtain ⟨w, rfl⟩ := hgT
    have hm₁ : hT.emb w ∈ Subgroup.closure ({a, b, s, y} : Set D) := by
      rw [← eB]; exact Subgroup.subset_closure (Or.inl ⟨w, rfl⟩)
    have hm₂ : hT.emb w ∈ Subgroup.closure ({a, b, s, x} : Set D) := by
      rw [← eA]; exact Subgroup.subset_closure (Or.inl ⟨w, rfl⟩)
    have e₁ : φ₁.symm ⟨hT'.emb w, hg₁⟩ = ⟨hT.emb w, hm₁⟩ := by
      rw [MulEquiv.symm_apply_eq]
      exact Subtype.ext (hv₁ w hm₁).symm
    have e₂ : φ₂.symm ⟨hT'.emb w, hg₂⟩ = ⟨hT.emb w, hm₂⟩ := by
      rw [MulEquiv.symm_apply_eq]
      exact Subtype.ext (hv₂ w hm₂).symm
    rw [e₁, e₂]

end CFSG.Quasithin.F6.GoldAmL4
