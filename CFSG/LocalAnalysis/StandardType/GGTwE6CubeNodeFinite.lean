module

public import CFSG.LocalAnalysis.StandardType.GGTwE6CubeNodeFiniteCheck

public section

namespace CFSG.StandardType.TwE6Cube

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.StandardType.TwE6EndNode3

theorem ofFn_getD {r : List ℤ} (hr : r.length = 6) :
    List.ofFn (fun i : Fin 6 => r.getD i 0) = r := by
  refine List.ext_getElem (by rw [List.length_ofFn, hr]) fun n h1 h2 => ?_
  rw [List.getElem_ofFn, List.getD_eq_getElem _ _ h2]

theorem getD_ofFn (α : Fin 6 → ℤ) (i : Fin 6) : (List.ofFn α).getD i 0 = α i := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact i.2), List.getElem_ofFn]

@[expose] def CubeSplit (v : Fin 6 → ZMod 3) : Prop :=
  ∃ g b : Fin 6 → ℤ, IsRoot Tag.E6 g ∧ KerP v g ∧ IsRoot Tag.E6 b ∧ KerP v b ∧
    iform (τ := Tag.E6) g b = 0 ∧ ∀ b' d : Fin 6 → ℤ, IsRoot Tag.E6 b' → KerP v b' →
      IsRoot Tag.E6 d → KerP v d → iform (τ := Tag.E6) g b' = 0 →
        iform (τ := Tag.E6) g d ≠ 0 → iform (τ := Tag.E6) b' d = 0

@[expose] def CubeAnn (v : Fin 6 → ZMod 3) : Prop :=
  ∃ u : Fin 6 → ZMod 3, u ≠ 0 ∧ u ≠ v ∧ u ≠ -v ∧
    ∀ α : Fin 6 → ℤ, IsRoot Tag.E6 α → KerP v α → KerP u α

@[expose] def CubeExcl (v : Fin 6 → ZMod 3) : Prop := CubeSplit v ∨ CubeAnn v

theorem kerP_neg {v : Fin 6 → ZMod 3} {α : Fin 6 → ℤ} : KerP (-v) α ↔ KerP v α := by
  simp [KerP]

theorem kerP_zero {α : Fin 6 → ℤ} : KerP 0 α := by
  simp [KerP]

section Roots


theorem mem_rts_iff {α : Fin 6 → ℤ} : α ∈ rts ↔ IsRoot Tag.E6 α := by
  refine Iff.trans ?_ (isRoot_iff_mem_artifactRoots (τ := Tag.E6) (v := α)).symm
  constructor
  · intro h
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h
    have hlen : r.length = 6 := length_of_mem_artifactRoots (τ := Tag.E6) hr
    have h' : List.ofFn (fun i : Fin 6 => r.getD i 0) ∈ Tag.E6.artifactRoots := by
      rw [ofFn_getD hlen]
      exact hr
    exact h'
  · intro h
    exact List.mem_map.2 ⟨List.ofFn α, h, funext fun i => getD_ofFn α i⟩

theorem nodup_rts : rts.Nodup := by
  refine (nodup_artifactRoots Tag.E6).map_on fun x hx y hy hxy => ?_
  have hx6 : x.length = 6 := length_of_mem_artifactRoots (τ := Tag.E6) hx
  have hy6 : y.length = 6 := length_of_mem_artifactRoots (τ := Tag.E6) hy
  rw [← ofFn_getD hx6, ← ofFn_getD hy6]
  exact congrArg List.ofFn hxy

theorem mem_kerL_iff {v : Fin 6 → ZMod 3} {α : Fin 6 → ℤ} :
    α ∈ kerL v ↔ IsRoot Tag.E6 α ∧ KerP v α := by
  rw [kerL, List.mem_filter, mem_rts_iff, kerB_iff]

theorem ncard_kernel_roots {v : Fin 6 → ZMod 3} (h : (kerL v).length = 40) :
    Set.ncard {α : Fin 6 → ℤ | IsRoot Tag.E6 α ∧ KerP v α} = 40 := by
  have hset : {α : Fin 6 → ℤ | IsRoot Tag.E6 α ∧ KerP v α} = ((kerL v).toFinset : Set _) := by
    ext α
    simp [mem_kerL_iff]
  have hnd : (kerL v).Nodup := nodup_rts.filter _
  rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd, h]

theorem cube_dichotomy {v : Fin 6 → ZMod 3} (hv : v ≠ 0) :
    (∃ γ : Fin 6 → ℤ, IsRoot Tag.E6 γ ∧ corootVec γ = v) ∨
      Set.ncard {α : Fin 6 → ℤ | IsRoot Tag.E6 α ∧ KerP v α} = 40 ∨ CubeExcl v := by
  rcases dichotomy_rts hv with ⟨γ, hγ, h⟩ | h | ⟨g, hg, b, hb, hgb, hall⟩ |
    ⟨u, hu0, hu1, hu2, hK⟩
  · exact Or.inl ⟨γ, mem_rts_iff.1 hγ, h⟩
  · exact Or.inr (Or.inl (ncard_kernel_roots h))
  · obtain ⟨hg1, hg2⟩ := mem_kerL_iff.1 hg
    obtain ⟨hb1, hb2⟩ := mem_kerL_iff.1 hb
    exact Or.inr (Or.inr (Or.inl ⟨g, b, hg1, hg2, hb1, hb2, hgb, fun b' d h1 h2 h3 h4 =>
      hall b' (mem_kerL_iff.2 ⟨h1, h2⟩) d (mem_kerL_iff.2 ⟨h3, h4⟩)⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨u, hu0, hu1, hu2, fun α hα hk =>
      hK α (mem_kerL_iff.2 ⟨hα, hk⟩)⟩))

theorem corootVec_ne_of_ker {v : Fin 6 → ZMod 3} {γ : Fin 6 → ℤ} (hγ : IsRoot Tag.E6 γ)
    (hk : KerP v γ) : corootVec γ ≠ 0 ∧ corootVec γ ≠ v ∧ corootVec γ ≠ -v := by
  have hnk : ¬ KerP (corootVec γ) γ := fun h => by
    have h2 := cor_not_ker γ (mem_rts_iff.2 hγ)
    rw [← corootVec_eq] at h2
    exact absurd ((kerB_iff _ _).2 h) (by rw [h2]; decide)
  exact ⟨fun h => hnk (h ▸ kerP_zero), fun h => hnk (h ▸ hk), fun h => hnk (h ▸ kerP_neg.2 hk)⟩

end Roots

end CFSG.StandardType.TwE6Cube

end
