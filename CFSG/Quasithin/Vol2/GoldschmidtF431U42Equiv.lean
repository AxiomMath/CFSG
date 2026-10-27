module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.Quasithin.H13.F431.U42

theorem isSylowTwoOf_top_map' {G H : Type*} [Group G] [Group H] (φ : G ≃* H)
    {S : Subgroup G} (h : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) :
    CFSG.QuasithinUnique.IsSylowTwoOf (S.map φ.toMonoidHom) ⊤ := by
  obtain ⟨-, hp, hidx⟩ := h
  refine ⟨le_top, hp.map _, ?_⟩
  have e1 : (S.subgroupOf ⊤).index = S.index := Subgroup.relIndex_top_right S
  have e2 : ((S.map φ.toMonoidHom).subgroupOf ⊤).index = (S.map φ.toMonoidHom).index :=
    Subgroup.relIndex_top_right _
  have e3 : (S.map φ.toMonoidHom).index = S.index := Subgroup.index_map_equiv S φ
  rw [e2, e3]
  rwa [e1] at hidx

theorem centralizer_map {G H : Type*} [Group G] [Group H] (e : G ≃* H) (a : G) :
    Subgroup.centralizer ({e a} : Set H) =
      (Subgroup.centralizer ({a} : Set G)).map e.toMonoidHom := by
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_map]
  constructor
  · intro h
    refine ⟨e.symm g, ?_, by simp⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply e.injective
    simpa using h
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    simpa using congrArg e hx

theorem isConj_map_iff {G H : Type*} [Group G] [Group H] (e : G ≃* H) {a b : G} :
    IsConj (e a) (e b) ↔ IsConj a b := by
  refine ⟨fun h => ?_, fun h => e.toMonoidHom.map_isConj h⟩
  simpa using e.symm.toMonoidHom.map_isConj h

theorem map_mem_normalizer {G H : Type*} [Group G] [Group H] (e : G ≃* H) {D : Subgroup H}
    {n : H} (hn : n ∈ Subgroup.normalizer (D : Set H)) :
    e.symm n ∈ Subgroup.normalizer ((D.comap e.toMonoidHom : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hn ⊢
  intro h
  have := hn (e h)
  simpa [Subgroup.mem_comap] using this

theorem exists_conj_isSylowTwoOf_top {G : Type*} [Group G] [Finite G] {S₁ S₂ : Subgroup G}
    (h₁ : CFSG.QuasithinUnique.IsSylowTwoOf S₁ ⊤) (h₂ : CFSG.QuasithinUnique.IsSylowTwoOf S₂ ⊤) :
    ∃ c : G, S₁.map (MulAut.conj c).toMonoidHom = S₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hi₁ : ¬ 2 ∣ S₁.index := by
    have e1 : (S₁.subgroupOf ⊤).index = S₁.index := Subgroup.relIndex_top_right S₁
    have := h₁.2.2
    rwa [e1] at this
  have hi₂ : ¬ 2 ∣ S₂.index := by
    have e1 : (S₂.subgroupOf ⊤).index = S₂.index := Subgroup.relIndex_top_right S₂
    have := h₂.2.2
    rwa [e1] at this
  let P₁ : Sylow 2 G := h₁.2.1.toSylow hi₁
  let P₂ : Sylow 2 G := h₂.2.1.toSylow hi₂
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P₁ P₂
  refine ⟨g, ?_⟩
  have h := congrArg (fun P : Sylow 2 G => (P : Subgroup G)) hg
  simp only [Sylow.coe_subgroup_smul] at h
  have e1 : (P₁ : Subgroup G) = S₁ := rfl
  have e2 : (P₂ : Subgroup G) = S₂ := rfl
  rw [e1, e2] at h
  rw [← h]
  ext x
  simp [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_map, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro hx
    exact ⟨g⁻¹ * x * g, hx, by group⟩

end CFSG.Quasithin.H13.F431.U42
