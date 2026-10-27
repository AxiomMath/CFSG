module

public import CFSG.RankThree.GroupTheory.SteinbergCETwoCoreAlpha

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBY

open CFSG CFSG.RankThree.GroupTheory

variable {G H : Type*} [Group G] [Group H]

theorem map_centralizer_singleton_mulEquiv (f : G ≃* H) (b : G) :
    (Subgroup.centralizer ({b} : Set G)).map f.toMonoidHom =
      Subgroup.centralizer ({f b} : Set H) := by
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have := congrArg f h
    simpa using this
  · intro h
    apply f.injective
    simpa using h

theorem map_inSubgroup_pCore_of_injective (p : ℕ) (f : G →* H) (hf : Function.Injective f)
    (K : Subgroup G) :
    (inSubgroup (pCore p) K).map f = inSubgroup (pCore p) (K.map f) := by
  rw [inSubgroup, inSubgroup, ← pCore_map_iso p (K.equivMapOfInjective f hf), Subgroup.map_map,
    Subgroup.map_map]
  rfl

theorem map_inSubgroup_pCore (p : ℕ) (f : G ≃* H) (K : Subgroup G) :
    (inSubgroup (pCore p) K).map f.toMonoidHom =
      inSubgroup (pCore p) (K.map f.toMonoidHom) :=
  map_inSubgroup_pCore_of_injective p f.toMonoidHom f.injective K

theorem map_conj_eq_of_mem_normalizer {K : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) : K.map (MulAut.conj g).toMonoidHom = K := by
  ext x
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  exact (Subgroup.mem_normalizer_iff''.mp hg x).symm

theorem mem_normalizer_of_map_conj_eq {K : Subgroup G} {g : G}
    (hg : K.map (MulAut.conj g).toMonoidHom = K) : g ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← hg]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← hg, Subgroup.mem_map_equiv, MulAut.conj_symm_apply] at hx
    simpa [mul_assoc] using hx

theorem map_inSubgroup_pCore_centralizer (p : ℕ) (f : G ≃* H) (b : G) :
    (inSubgroup (pCore p) (Subgroup.centralizer ({b} : Set G))).map f.toMonoidHom =
      inSubgroup (pCore p) (Subgroup.centralizer ({f b} : Set H)) := by
  rw [map_inSubgroup_pCore, map_centralizer_singleton_mulEquiv]

theorem map_twoCoreX (f : G ≃* H) (B : Subgroup G) :
    (twoCoreX B).map f.toMonoidHom = twoCoreX (B.map f.toMonoidHom) := by
  ext y
  rw [Subgroup.mem_map_equiv, mem_twoCoreX_iff, mem_twoCoreX_iff]
  constructor
  · intro h b' hb' hb'1
    rw [Subgroup.mem_map_equiv] at hb'
    have hne : f.symm b' ≠ 1 := fun h1 => hb'1 (by simpa using congrArg f h1)
    have hmem := Subgroup.mem_map_of_mem f.toMonoidHom (h _ hb' hne)
    rw [map_inSubgroup_pCore_centralizer] at hmem
    simpa using hmem
  · intro h b hb hb1
    have hne : f b ≠ 1 := fun h1 => hb1 (f.injective (by simpa using h1))
    have hmem := h (f b) (Subgroup.mem_map_of_mem f.toMonoidHom hb) hne
    rw [← map_inSubgroup_pCore_centralizer, Subgroup.mem_map_equiv] at hmem
    exact hmem

theorem map_twoCoreJ (f : G ≃* H) (B : Subgroup G) :
    (twoCoreJ B).map f.toMonoidHom = twoCoreJ (B.map f.toMonoidHom) := by
  rw [twoCoreJ, twoCoreJ]
  simp only [Subgroup.map_iSup, Subgroup.map_commutator, map_inSubgroup_pCore_centralizer]
  apply le_antisymm
  · refine iSup₂_le fun b hb => iSup_le fun hb1 => ?_
    have hne : f b ≠ 1 := fun h1 => hb1 (f.injective (by simpa using h1))
    exact le_iSup₂_of_le (f b) (Subgroup.mem_map_of_mem f.toMonoidHom hb)
      (le_iSup_of_le hne le_rfl)
  · refine iSup₂_le fun b' hb' => iSup_le fun hb'1 => ?_
    have hb'' : f.symm b' ∈ B := (Subgroup.mem_map_equiv).mp hb'
    have hne : f.symm b' ≠ 1 := fun h1 => hb'1 (by simpa using congrArg f h1)
    refine le_iSup₂_of_le (f.symm b') hb'' (le_iSup_of_le hne ?_)
    rw [MulEquiv.apply_symm_apply]

theorem map_twoCoreAlpha (f : G ≃* H) (B : Subgroup G) :
    (twoCoreAlpha B).map f.toMonoidHom = twoCoreAlpha (B.map f.toMonoidHom) := by
  rw [twoCoreAlpha, twoCoreAlpha, Subgroup.map_sup, map_twoCoreJ, map_twoCoreX]

theorem alpha_isomorphism_transport (f : G ≃* H) (B : Subgroup G) :
    (twoCoreX B).map f.toMonoidHom = twoCoreX (B.map f.toMonoidHom) ∧
      (twoCoreJ B).map f.toMonoidHom = twoCoreJ (B.map f.toMonoidHom) ∧
      (twoCoreAlpha B).map f.toMonoidHom = twoCoreAlpha (B.map f.toMonoidHom) ∧
      (∀ g : G, conjugate (twoCoreAlpha B) g = twoCoreAlpha (conjugate B g)) ∧
      Subgroup.normalizer (B : Set G) ≤ Subgroup.normalizer (twoCoreAlpha B : Set G) := by
  have hconj : ∀ g : G, conjugate (twoCoreAlpha B) g = twoCoreAlpha (conjugate B g) :=
    fun g => map_twoCoreAlpha (MulAut.conj g⁻¹) B
  refine ⟨map_twoCoreX f B, map_twoCoreJ f B, map_twoCoreAlpha f B, hconj, fun g hg => ?_⟩
  have hB : B.map (MulAut.conj g⁻¹).toMonoidHom = B := map_conj_eq_of_mem_normalizer (inv_mem hg)
  have hA : (twoCoreAlpha B).map (MulAut.conj g⁻¹).toMonoidHom = twoCoreAlpha B := by
    rw [map_twoCoreAlpha, hB]
  simpa using inv_mem (mem_normalizer_of_map_conj_eq hA)

end CFSG.RankThree.GroupTheory.SteinbergBY
