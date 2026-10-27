module

public import CFSG.Quasithin.Background.G93ApplyRestrict
public import CFSG.Quasithin.Background.G9StmtsModels
public import CFSG.Quasithin.Background.G116IIIFStar

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem isComponentOf_map_conj {Γ L : Subgroup (GLV V)} (hL : IsComponentOf L Γ) {γ : GLV V}
    (hγ : γ ∈ Γ) : IsComponentOf (L.map (MulAut.conj γ).toMonoidHom) Γ := by
  have hLΓ : L ≤ Γ := hL.1
  set A : Subgroup ↥Γ := L.subgroupOf Γ with hAdef
  set γ' : ↥Γ := ⟨γ, hγ⟩ with hγ'
  have hA : IsComponentOf A ⊤ := (isComponentOf_iff_subgroupOf.1 hL).2
  have hB : IsComponentOf (A.map (MulAut.conj γ').toMonoidHom) ⊤ :=
    open_isComponentOf_top_map_conj hA γ'
  have hAmap : A.map Γ.subtype = L := Subgroup.map_subgroupOf_eq_of_le hLΓ
  have hBmap : (A.map (MulAut.conj γ').toMonoidHom).map Γ.subtype =
      L.map (MulAut.conj γ).toMonoidHom := by
    rw [Subgroup.map_map, ← hAmap, Subgroup.map_map]
    rfl
  have hle : L.map (MulAut.conj γ).toMonoidHom ≤ Γ := by
    rw [← hBmap]
    exact Subgroup.map_subtype_le _
  refine isComponentOf_iff_subgroupOf.2 ⟨hle, ?_⟩
  have : (L.map (MulAut.conj γ).toMonoidHom).subgroupOf Γ =
      A.map (MulAut.conj γ').toMonoidHom := by
    rw [← hBmap]
    exact Subgroup.comap_map_eq_self_of_injective Γ.subtype_injective _
  rwa [this]

theorem normalClosure_eq_of_conj_eq {Γ L : Subgroup (GLV V)}
    (h : ∀ γ ∈ Γ, L.map (MulAut.conj γ).toMonoidHom = L) : normalClosure Γ L = L := by
  refine le_antisymm ?_ (le_normalClosure Γ L)
  rw [normalClosure, Subgroup.closure_le]
  rintro _ ⟨γ, hγ, l, hl, rfl⟩
  rw [← h γ hγ]
  exact ⟨l, hl, rfl⟩

theorem mem_map_conj_of_mem {L : Subgroup (V ≃ₗ[ZMod 2] V)} {γ l : V ≃ₗ[ZMod 2] V} (hl : l ∈ L) :
    γ * l * γ⁻¹ ∈ L.map (MulAut.conj γ).toMonoidHom :=
  ⟨l, hl, rfl⟩

variable [Finite V]

theorem normalClosure_eq_sup_of_numConjugates_le_two {Γ L : Subgroup (GLV V)}
    (hnum : numConjugates Γ L ≤ 2) {γ : GLV V} (hγ : γ ∈ Γ)
    (hne : L.map (MulAut.conj γ).toMonoidHom ≠ L) :
    normalClosure Γ L = L ⊔ L.map (MulAut.conj γ).toMonoidHom := by
  set L₂ : Subgroup (GLV V) := L.map (MulAut.conj γ).toMonoidHom with hL₂
  set S : Set (Subgroup (GLV V)) :=
    {M | ∃ δ ∈ Γ, M = L.map (MulAut.conj δ).toMonoidHom} with hS
  have hSfin : S.Finite := Set.toFinite S
  have hsub : ({L, L₂} : Set (Subgroup (GLV V))) ⊆ S := by
    intro M hM
    rcases hM with rfl | rfl
    · refine ⟨1, Γ.one_mem, ?_⟩
      ext x
      simp
    · exact ⟨γ, hγ, rfl⟩
  have hcard : ({L, L₂} : Set (Subgroup (GLV V))).ncard = 2 :=
    Set.ncard_pair (Ne.symm hne)
  have hS2 : S.ncard ≤ 2 := hnum
  have heq : ({L, L₂} : Set (Subgroup (GLV V))) = S :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hcard]; exact hS2) hSfin
  apply le_antisymm
  · rw [normalClosure, Subgroup.closure_le]
    rintro _ ⟨δ, hδ, l, hl, rfl⟩
    have hmem : L.map (MulAut.conj δ).toMonoidHom ∈ S := ⟨δ, hδ, rfl⟩
    rw [← heq] at hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    have hg : δ * l * δ⁻¹ ∈ L.map (MulAut.conj δ).toMonoidHom := mem_map_conj_of_mem hl
    rcases hmem with h | h
    · rw [h] at hg
      exact Subgroup.mem_sup_left hg
    · rw [h] at hg
      exact Subgroup.mem_sup_right hg
  · refine sup_le (le_normalClosure Γ L) ?_
    rintro _ ⟨l, hl, rfl⟩
    exact Subgroup.subset_closure ⟨γ, hγ, l, hl, rfl⟩

omit [Finite V] in
theorem map_conj_le_normalClosure {Γ L : Subgroup (GLV V)} {γ : GLV V} (hγ : γ ∈ Γ) :
    L.map (MulAut.conj γ).toMonoidHom ≤ normalClosure Γ L := by
  rintro _ ⟨l, hl, rfl⟩
  exact Subgroup.subset_closure ⟨γ, hγ, l, hl, rfl⟩

@[expose] def conjEquivMap (L : Subgroup (GLV V)) (γ : GLV V) :
    ↥L ≃* ↥(L.map (MulAut.conj γ).toMonoidHom) where
  toFun l := ⟨γ * (l : GLV V) * γ⁻¹, mem_map_conj_of_mem l.2⟩
  invFun m := ⟨γ⁻¹ * (m : GLV V) * γ, by
    obtain ⟨l, hl, hlm⟩ := m.2
    have : γ⁻¹ * (m : GLV V) * γ = l := by
      rw [← hlm]
      show γ⁻¹ * (γ * l * γ⁻¹) * γ = l
      group
    rw [this]
    exact hl⟩
  left_inv l := by
    apply Subtype.ext
    show γ⁻¹ * (γ * (l : GLV V) * γ⁻¹) * γ = l
    group
  right_inv m := by
    apply Subtype.ext
    show γ * (γ⁻¹ * (m : GLV V) * γ) * γ⁻¹ = m
    group
  map_mul' a b := by
    apply Subtype.ext
    show γ * ((a : GLV V) * (b : GLV V)) * γ⁻¹ =
      (γ * (a : GLV V) * γ⁻¹) * (γ * (b : GLV V) * γ⁻¹)
    group

omit [Finite V] in
theorem quasiEquivalent_map_conj {Γ L : Subgroup (GLV V)}
    (hfix : fixedSpace (normalClosure Γ L) = ⊥) (hhom : Homogeneous (normalClosure Γ L))
    {I : Submodule (ZMod 2) V} (hI : IrrPlus (normalClosure Γ L) I)
    (hf : FaithfulOn (normalClosure Γ L) I) {γ : GLV V} (hγ : γ ∈ Γ)
    (hLI : Invariant L I) (hL₂I : Invariant (L.map (MulAut.conj γ).toMonoidHom) I) :
    QuasiEquivalent (restrictRange L I hLI)
      (restrictRange (L.map (MulAut.conj γ).toMonoidHom) I hL₂I) := by
  set H := normalClosure Γ L with hH
  set L₂ := L.map (MulAut.conj γ).toMonoidHom with hL₂
  have hLH : L ≤ H := le_normalClosure Γ L
  have hL₂H : L₂ ≤ H := map_conj_le_normalClosure hγ
  have hfL : FaithfulOn L I := faithfulOn_of_le hLH hf
  have hfL₂ : FaithfulOn L₂ I := faithfulOn_of_le hL₂H hf
  have hconjI : IrrPlus H (conjSub γ I) :=
    ((hI.isIrr hfix).conj_of_normal (normalClosure_normal Γ L) hγ).irrPlus hfix
  obtain ⟨θ, hθ⟩ := hhom (conjSub γ I) I hconjI hI
  let e : ↥I ≃ₗ[ZMod 2] ↥(conjSub γ I) :=
    Submodule.equivMapOfInjective (γ : V →ₗ[ZMod 2] V) γ.injective I
  have he : ∀ v : ↥I, ((e v : ↥(conjSub γ I)) : V) = γ (v : V) := fun v => rfl
  let ψ : ↥I ≃ₗ[ZMod 2] ↥I := e.trans θ
  let φ : ↥(restrictRange L I hLI) ≃* ↥(restrictRange L₂ I hL₂I) :=
    (restrictRangeEquiv hLI hfL).symm.trans ((conjEquivMap L γ).trans (restrictRangeEquiv hL₂I hfL₂))
  refine ⟨φ, Or.inl ⟨ψ, fun g v => ?_⟩⟩
  set l₀ : ↥L := (restrictRangeEquiv hLI hfL).symm g with hl₀
  have hg : g = restrictRangeEquiv hLI hfL l₀ := by rw [hl₀]; simp
  have hgv : (((g : GLV ↥I) v : ↥I) : V) = (l₀ : GLV V) (v : V) := by
    rw [hg]
    rfl
  have hφg : (((φ g : ↥(restrictRange L₂ I hL₂I)) : GLV ↥I)) =
      restrictHom L₂ I hL₂I (conjEquivMap L γ l₀) := by
    show ((restrictRangeEquiv hL₂I hfL₂ (conjEquivMap L γ ((restrictRangeEquiv hLI hfL).symm g)) :
      ↥(restrictRange L₂ I hL₂I)) : GLV ↥I) = _
    rfl
  have hk : γ * (l₀ : GLV V) * γ⁻¹ ∈ H := by
    have := H.mul_mem (H.mul_mem (hL₂H (mem_map_conj_of_mem l₀.2)) H.one_mem) H.one_mem
    simpa using this
  have key := hθ (γ * (l₀ : GLV V) * γ⁻¹) hk (e v) (e ((g : GLV ↥I) v)) (by
    rw [he, he, hgv]
    simp)
  apply Subtype.ext
  rw [hφg]
  show ((ψ ((g : GLV ↥I) v) : ↥I) : V) =
    (γ * (l₀ : GLV V) * γ⁻¹) ((ψ v : ↥I) : V)
  exact key.symm

theorem g118_hEq {Γ L : Subgroup (GLV V)} (hL : IsComponentOf L Γ)
    (hnum : numConjugates Γ L ≤ 2) (hfix : fixedSpace (normalClosure Γ L) = ⊥)
    (hhom : Homogeneous (normalClosure Γ L)) {I : Submodule (ZMod 2) V}
    (hI : IrrPlus (normalClosure Γ L) I) (hf : FaithfulOn (normalClosure Γ L) I) :
    normalClosure Γ L = L ∨ ∃ L₂ : Subgroup (GLV V), IsComponentOf L₂ Γ ∧ L₂ ≠ L ∧
      normalClosure Γ L = L ⊔ L₂ ∧ ∃ (hLI : Invariant L I) (hL₂I : Invariant L₂ I),
        QuasiEquivalent (restrictRange L I hLI) (restrictRange L₂ I hL₂I) := by
  by_cases hall : ∀ γ ∈ Γ, L.map (MulAut.conj γ).toMonoidHom = L
  · exact Or.inl (normalClosure_eq_of_conj_eq hall)
  · right
    push Not at hall
    obtain ⟨γ, hγ, hne⟩ := hall
    have hLI : Invariant L I := hI.1.mono (le_normalClosure Γ L)
    have hL₂I : Invariant (L.map (MulAut.conj γ).toMonoidHom) I :=
      hI.1.mono (map_conj_le_normalClosure hγ)
    exact ⟨L.map (MulAut.conj γ).toMonoidHom, isComponentOf_map_conj hL hγ, hne,
      normalClosure_eq_sup_of_numConjugates_le_two hnum hγ hne, hLI, hL₂I,
      quasiEquivalent_map_conj hfix hhom hI hf hγ hLI hL₂I⟩

end G11

end CFSG.Quasithin
