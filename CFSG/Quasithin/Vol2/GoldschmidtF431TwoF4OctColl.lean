module

public import CFSG.LieType.Ree.LargeReeBlockCollection
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.Quasithin.H13.F431.TwoF4

open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.Blueprint.Chevalley


section Closed

variable {τ : Tag} {K : Type} [Field K]

theorem bijOn_list_prod_rootSpan_of_closed {n : ℕ} {S : Set (Fin τ.rank → ℤ)}
    {Q : Fin n → Set (Fin τ.rank → ℤ)} {L : Fin n → List (Fin τ.rank → ℤ)}
    (hSpos : ∀ α ∈ S, IsRoot τ α ∧ 0 < height α)
    (hScl : ∀ α ∈ S, ∀ β ∈ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • α + b • β) →
      a • α + b • β ∈ S)
    (hQ : ∀ k, ∀ α ∈ Q k, IsRoot τ α ∧ 0 < height α)
    (hcl : ∀ k, ∀ α ∈ Q k, ∀ β ∈ Q k, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • α + b • β) →
      a • α + b • β ∈ Q k)
    (hL : ∀ k, (L k).Nodup) (hLQ : ∀ k, {x | x ∈ L k} = Q k)
    (hdisj : ∀ k k', k ≠ k' → Disjoint (Q k) (Q k'))
    (hcover : ∀ α, α ∈ S ↔ ∃ k, α ∈ Q k) :
    Set.BijOn (fun u : Fin n → ModGL τ K => (List.ofFn u).prod)
      (Set.univ.pi fun k => (rootSpan τ K (Q k) : Set (ModGL τ K)))
      (rootSpan τ K S : Set (ModGL τ K)) := by
  classical
  have hmemQ : ∀ k x, x ∈ L k ↔ x ∈ Q k := fun k x => by
    rw [← hLQ k]
    rfl
  have hmemL : ∀ x, x ∈ (List.ofFn L).flatten ↔ ∃ k, x ∈ L k := by
    intro x
    rw [List.mem_flatten]
    constructor
    · rintro ⟨l, hl, hx⟩
      obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hl
      exact ⟨k, hx⟩
    · rintro ⟨k, hx⟩
      exact ⟨L k, List.mem_ofFn.2 ⟨k, rfl⟩, hx⟩
  have huniq : ∀ k k' x, x ∈ L k → x ∈ L k' → k = k' := by
    intro k k' x h h'
    by_contra hne
    exact Set.disjoint_left.1 (hdisj k k' hne) ((hmemQ k x).1 h) ((hmemQ k' x).1 h')
  have hnd : ((List.ofFn L).flatten).Nodup := by
    refine List.nodup_flatten.2 ⟨fun l hl => ?_, List.pairwise_ofFn.2 fun k k' hkk' => ?_⟩
    · obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hl
      exact hL k
    · exact fun x h h' => (ne_of_lt hkk') (huniq k k' x h h')
  have hset : {x | x ∈ (List.ofFn L).flatten} = S := by
    ext x
    change x ∈ (List.ofFn L).flatten ↔ x ∈ S
    rw [hmemL, hcover]
    constructor
    · rintro ⟨k, hx⟩
      exact ⟨k, (hmemQ k x).1 hx⟩
    · rintro ⟨k, hx⟩
      exact ⟨k, (hmemQ k x).2 hx⟩
  have hsub : ∀ k, Q k ⊆ S := fun k α hα => (hcover α).2 ⟨k, hα⟩
  have hT := list_prod_pinnedX_bijective (K := K) hSpos hScl hnd hset
  have hB := fun k => list_prod_pinnedX_bijective (K := K) (hQ k) (hcl k) (hL k) (hLQ k)
  let glue : ((k : Fin n) → (Fin τ.rank → ℤ) → K) → (Fin τ.rank → ℤ) → K := fun c x =>
    if hx : ∃ k, x ∈ L k then c hx.choose x else 0
  have hglue : ∀ c k, ∀ x ∈ L k, glue c x = c k x := by
    intro c k x hx
    have hex : ∃ k, x ∈ L k := ⟨k, hx⟩
    change (if hx : ∃ k, x ∈ L k then c hx.choose x else 0) = c k x
    rw [dite_eq_left hex, huniq _ _ x hex.choose_spec hx]
  have hsplit : ∀ c : (Fin τ.rank → ℤ) → K,
      (((List.ofFn L).flatten).map fun α => pinnedX τ K α (c α)).prod =
        (List.ofFn fun k => ((L k).map fun α => pinnedX τ K α (c α)).prod).prod :=
    fun c => CFSG.LieType.Ree.prod_map_flatten_ofFn L _
  have hblock : ∀ (c : (k : Fin n) → (Fin τ.rank → ℤ) → K) k,
      ((L k).map fun α => pinnedX τ K α (glue c α)).prod =
        ((L k).map fun α => pinnedX τ K α (c k α)).prod := fun c k => by
    rw [List.map_congr_left fun x hx => by rw [hglue c k x hx]]
  refine ⟨fun u hu => ?_, fun u hu v hv h => ?_, fun g hg => ?_⟩
  · refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
    exact rootSpan_mono (hsub k) (hu k (Set.mem_univ k))
  · choose cu hcu using fun k => (hB k).2.1 (u k) (hu k (Set.mem_univ k))
    choose cv hcv using fun k => (hB k).2.1 (v k) (hv k (Set.mem_univ k))
    have hu' : (List.ofFn u).prod =
        (((List.ofFn L).flatten).map fun α => pinnedX τ K α (glue cu α)).prod := by
      rw [hsplit]
      exact congrArg List.prod (List.ofFn_inj.2 (funext fun k => by rw [hblock, hcu]))
    have hv' : (List.ofFn v).prod =
        (((List.ofFn L).flatten).map fun α => pinnedX τ K α (glue cv α)).prod := by
      rw [hsplit]
      exact congrArg List.prod (List.ofFn_inj.2 (funext fun k => by rw [hblock, hcv]))
    have heq := hT.2.2 _ _ (hu'.symm.trans (h.trans hv'))
    funext k
    rw [← hcu k, ← hcv k]
    refine congrArg List.prod (List.map_congr_left fun x hx => ?_)
    have hx' := heq x ((hmemL x).2 ⟨k, hx⟩)
    rw [hglue cu k x hx, hglue cv k x hx] at hx'
    rw [hx']
  · obtain ⟨c, rfl⟩ := hT.2.1 g hg
    exact ⟨fun k => ((L k).map fun α => pinnedX τ K α (c α)).prod, fun k _ => (hB k).1 c,
      (hsplit c).symm⟩

end Closed

section Groups

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem octColl_bijOn {n : ℕ} (S : Set (Fin F4.tag.rank → ℤ))
    (Q : Fin n → Set (Fin F4.tag.rank → ℤ)) (hQinj : Function.Injective Q)
    (hQ : ∀ k, Q k ∈ largeReePosBlocks) (hS : ∀ α, α ∈ S ↔ ∃ k, α ∈ Q k)
    (hcl : ∀ α ∈ S, ∀ β ∈ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot F4.tag (a • α + b • β) →
      a • α + b • β ∈ S) :
    Set.BijOn (fun x : Fin n → ModGL F4.tag K => (List.ofFn x).prod)
      (Set.univ.pi fun k => (largeReeBlockGroup K a (Q k) : Set (ModGL F4.tag K)))
      ((rootSpan F4.tag K S ⊓ F4.reeGamma K a : Subgroup (ModGL F4.tag K)) :
        Set (ModGL F4.tag K)) := by
  classical
  have hQB : ∀ k, Q k ∈ largeReeBlocks := fun k => (hQ k).1
  have hQpos : ∀ k, ∀ α ∈ Q k, IsRoot F4.tag α ∧ 0 < height α := fun k _ hα => (hQ k).2 hα
  have hL : ∀ k, ∃ i : Fin 16, {x | x ∈ largeReeBlockTable i} = Q k := fun k => by
    have h := hQB k
    rw [largeReeBlocks_eq_range] at h
    exact h
  choose ι hι using hL
  have hdisj : ∀ k k', k ≠ k' → Disjoint (Q k) (Q k') := fun k k' h =>
    largeReeBlocks_disjoint (hQB k) (hQB k') (hQinj.ne h)
  have hSpos : ∀ α ∈ S, IsRoot F4.tag α ∧ 0 < height α := fun α hα => by
    obtain ⟨k, hk⟩ := (hS α).1 hα
    exact hQpos k α hk
  have hBij := bijOn_list_prod_rootSpan_of_closed (K := K) (Q := Q)
    (L := fun k => largeReeBlockTable (ι k)) hSpos hcl hQpos
    (fun k _ hα _ hβ _ _ ha hb hr => nsmul_add_nsmul_mem_largeReeBlocks (hQB k) hα hβ ha hb hr)
    (fun k => (largeReeBlockTable_ne_nil_nodup (ι k)).2) hι hdisj hS
  refine ⟨fun x hx => ?_, fun x hx y hy h => ?_, fun g hg => ?_⟩
  · refine Subgroup.mem_inf.2 ⟨hBij.1 fun k _ => (hx k (Set.mem_univ k)).1,
      Subgroup.list_prod_mem _ fun y hy => ?_⟩
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hy
    exact (hx k (Set.mem_univ k)).2
  · exact hBij.2.1 (fun k _ => (hx k (Set.mem_univ k)).1) (fun k _ => (hy k (Set.mem_univ k)).1) h
  · obtain ⟨u, hu, rfl⟩ := hBij.2.2 (Subgroup.mem_inf.1 hg).1
    have hga : ∀ k, u k ∈ adjointGroup F4.tag K := fun k =>
      rootSpan_le_adjointGroup _ (hu k (Set.mem_univ k))
    set ũ : Fin n → adjointGroup F4.tag K := fun k => ⟨u k, hga k⟩ with hũ
    set v : Fin n → ModGL F4.tag K :=
      fun k => ((F4.finiteReeAut K a (ũ k) : adjointGroup F4.tag K) : ModGL F4.tag K) with hv
    have hvQ : ∀ k, v k ∈ rootSpan F4.tag K (Q k) := fun k =>
      finiteReeAut_mem_of_map_le (map_finiteReeAut_rootSpan_le fun α hα =>
        ⟨(hQpos k α hα).1, dualRoot_mem_largeReeBlocks (hQB k) hα⟩) (hu k (Set.mem_univ k))
        (hga k)
    have hprod : (List.ofFn v).prod = (List.ofFn u).prod := by
      have hga' : (List.ofFn u).prod ∈ adjointGroup F4.tag K :=
        Subgroup.list_prod_mem _ fun y hy => by
          obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hy
          exact hga k
      have e : (⟨(List.ofFn u).prod, hga'⟩ : adjointGroup F4.tag K) = (List.ofFn ũ).prod := by
        refine Subtype.ext ?_
        rw [Subgroup.val_list_prod, List.map_ofFn]
        rfl
      have hF := finiteReeAut_eq_of_mem_reeGamma (Subgroup.mem_inf.1 hg).2 hga'
      rw [e, map_list_prod, List.map_ofFn, Subgroup.val_list_prod, List.map_ofFn] at hF
      exact hF
    have hvu : v = u := hBij.2.1 (fun k _ => hvQ k) hu hprod
    refine ⟨u, fun k _ => Subgroup.mem_inf.2 ⟨hu k (Set.mem_univ k),
      mem_reeGamma_of_fixed (hga k) (congrFun hvu k)⟩, rfl⟩

end Groups

end CFSG.Quasithin.H13.F431.TwoF4
