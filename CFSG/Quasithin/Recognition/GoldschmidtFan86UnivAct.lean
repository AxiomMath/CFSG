module

public import CFSG.Quasithin.Recognition.GoldschmidtTreeAcyclic

public section

namespace CFSG.Quasithin.Fan86.Univ

open CFSG.Quasithin

section CosetGraph

variable {D : Type*} [Group D] (P R : Subgroup D)

theorem adj_smul_of_adj (g : D) {u v : (D ⧸ P) ⊕ (D ⧸ R)} (h : (goldCosetGraph P R).Adj u v) :
    (goldCosetGraph P R).Adj (g • u) (g • v) := by
  rcases u with x | x <;> rcases v with y | y
  · simp [goldCosetGraph, SimpleGraph.fromRel_adj, goldCosetRel] at h
  · obtain ⟨z, rfl, rfl⟩ := (goldCosetGraph_adj_inl_inr P R x y).1 h
    exact (goldCosetGraph_adj_inl_inr P R _ _).2 ⟨g * z, rfl, rfl⟩
  · obtain ⟨z, rfl, rfl⟩ := (goldCosetGraph_adj_inl_inr P R y x).1 h.symm
    exact ((goldCosetGraph_adj_inl_inr P R _ _).2 ⟨g * z, rfl, rfl⟩).symm
  · simp [goldCosetGraph, SimpleGraph.fromRel_adj, goldCosetRel] at h

theorem goldCosetGraph_adj_smul (g : D) (u v : (D ⧸ P) ⊕ (D ⧸ R)) :
    (goldCosetGraph P R).Adj (g • u) (g • v) ↔ (goldCosetGraph P R).Adj u v := by
  refine ⟨fun h => ?_, adj_smul_of_adj P R g⟩
  have := adj_smul_of_adj P R g⁻¹ h
  rwa [inv_smul_smul, inv_smul_smul] at this

end CosetGraph

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

abbrev Vtx : Type _ := (X.Universal ⧸ X.ofA.range) ⊕ (X.Universal ⧸ X.ofB.range)

@[expose] def baseA : (X.Universal ⧸ X.ofA.range) ⊕ (X.Universal ⧸ X.ofB.range) := X.vtx true 1

@[expose] def baseB : (X.Universal ⧸ X.ofA.range) ⊕ (X.Universal ⧸ X.ofB.range) := X.vtx false 1

theorem adj_smul (g : X.Universal) (u v : Vtx X) :
    X.treeGraph.Adj (g • u) (g • v) ↔ X.treeGraph.Adj u v :=
  goldCosetGraph_adj_smul X.ofA.range X.ofB.range g u v

theorem smul_baseA (g : X.Universal) : g • baseA X = X.vtx true g := by
  show Sum.inl (((g * 1 : X.Universal)) : X.Universal ⧸ X.ofA.range) = _
  rw [mul_one]
  rfl

theorem smul_baseB (g : X.Universal) : g • baseB X = X.vtx false g := by
  show Sum.inr (((g * 1 : X.Universal)) : X.Universal ⧸ X.ofB.range) = _
  rw [mul_one]
  rfl

theorem adj_baseA_baseB : X.treeGraph.Adj (baseA X) (baseB X) := X.adj_vtx_not true 1

theorem stabilizer_baseA : MulAction.stabilizer X.Universal (baseA X) = X.ofA.range := by
  have h := MulAction.stabilizer_quotient X.ofA.range
  ext g
  have hg : g ∈ MulAction.stabilizer X.Universal ((1 : X.Universal) : X.Universal ⧸ X.ofA.range) ↔
      g ∈ X.ofA.range := by rw [h]
  rw [MulAction.mem_stabilizer_iff] at hg ⊢
  rw [← hg]
  exact Sum.inl_injective.eq_iff

theorem stabilizer_baseB : MulAction.stabilizer X.Universal (baseB X) = X.ofB.range := by
  have h := MulAction.stabilizer_quotient X.ofB.range
  ext g
  have hg : g ∈ MulAction.stabilizer X.Universal ((1 : X.Universal) : X.Universal ⧸ X.ofB.range) ↔
      g ∈ X.ofB.range := by rw [h]
  rw [MulAction.mem_stabilizer_iff] at hg ⊢
  rw [← hg]
  exact Sum.inr_injective.eq_iff

theorem exists_smul_base (w : (X.Universal ⧸ X.ofA.range) ⊕ (X.Universal ⧸ X.ofB.range)) :
    (∃ g : X.Universal, w = g • baseA X) ∨ (∃ g : X.Universal, w = g • baseB X) := by
  rcases w with q | q
  · obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    exact Or.inl ⟨g, (smul_baseA X g).symm⟩
  · obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    exact Or.inr ⟨g, (smul_baseB X g).symm⟩

theorem exists_smul_edge {u w : (X.Universal ⧸ X.ofA.range) ⊕ (X.Universal ⧸ X.ofB.range)}
    (h : X.treeGraph.Adj u w) :
    ∃ g : X.Universal,
      (u = g • baseA X ∧ w = g • baseB X) ∨ (u = g • baseB X ∧ w = g • baseA X) := by
  rcases u with x | x <;> rcases w with y | y
  · simp [GoldAmalgam.treeGraph, goldCosetGraph, SimpleGraph.fromRel_adj, goldCosetRel] at h
  · obtain ⟨z, rfl, rfl⟩ := (goldCosetGraph_adj_inl_inr _ _ x y).1 h
    exact ⟨z, Or.inl ⟨(smul_baseA X z).symm, (smul_baseB X z).symm⟩⟩
  · obtain ⟨z, rfl, rfl⟩ := (goldCosetGraph_adj_inl_inr _ _ y x).1 h.symm
    exact ⟨z, Or.inr ⟨(smul_baseB X z).symm, (smul_baseA X z).symm⟩⟩
  · simp [GoldAmalgam.treeGraph, goldCosetGraph, SimpleGraph.fromRel_adj, goldCosetRel] at h

theorem ofA_mem_ofB_range_iff (a : A) : X.ofA a ∈ X.ofB.range ↔ a ∈ X.edgeA := by
  constructor
  · intro h
    have h1 : X.ofA a ∈ X.ofA.range ⊓ X.ofB.range := ⟨⟨a, rfl⟩, h⟩
    rw [X.ofA_range_inf_ofB_range] at h1
    obtain ⟨c, hc⟩ := h1
    have : X.ofA (X.toA c) = X.ofA a := by rw [X.ofA_toA]; exact hc
    exact ⟨c, X.ofA_injective this⟩
  · rintro ⟨c, rfl⟩
    exact ⟨X.toB c, by rw [X.ofA_toA, X.ofB_toB]⟩

theorem ofB_mem_ofA_range_iff (b : B) : X.ofB b ∈ X.ofA.range ↔ b ∈ X.edgeB := by
  constructor
  · intro h
    have h1 : X.ofB b ∈ X.ofA.range ⊓ X.ofB.range := ⟨h, ⟨b, rfl⟩⟩
    rw [X.ofA_range_inf_ofB_range] at h1
    obtain ⟨c, hc⟩ := h1
    have : X.ofB (X.toB c) = X.ofB b := by rw [X.ofB_toB]; exact hc
    exact ⟨c, X.ofB_injective this⟩
  · rintro ⟨c, rfl⟩
    exact ⟨X.toA c, by rw [X.ofA_toA, X.ofB_toB]⟩

theorem adj_baseA_iff (w : (X.Universal ⧸ X.ofA.range) ⊕ (X.Universal ⧸ X.ofB.range)) :
    X.treeGraph.Adj (baseA X) w ↔
      ∃ a : A, w = Sum.inr ((X.ofA a : X.Universal) : X.Universal ⧸ X.ofB.range) := by
  rw [baseA, X.adj_vtx_iff true 1 w]
  constructor
  · rintro ⟨y, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, by simp [GoldAmalgam.vtx]⟩
  · rintro ⟨a, rfl⟩
    exact ⟨X.ofA a, ⟨a, rfl⟩, by simp [GoldAmalgam.vtx]⟩

theorem adj_baseB_iff (w : (X.Universal ⧸ X.ofA.range) ⊕ (X.Universal ⧸ X.ofB.range)) :
    X.treeGraph.Adj (baseB X) w ↔
      ∃ b : B, w = Sum.inl ((X.ofB b : X.Universal) : X.Universal ⧸ X.ofA.range) := by
  rw [baseB, X.adj_vtx_iff false 1 w]
  constructor
  · rintro ⟨y, ⟨b, rfl⟩, rfl⟩
    exact ⟨b, by simp [GoldAmalgam.vtx]⟩
  · rintro ⟨b, rfl⟩
    exact ⟨X.ofB b, ⟨b, rfl⟩, by simp [GoldAmalgam.vtx]⟩

theorem inr_ofA_eq_iff (a a' : A) :
    (Sum.inr ((X.ofA a : X.Universal) : X.Universal ⧸ X.ofB.range) :
        (X.Universal ⧸ X.ofA.range) ⊕ (X.Universal ⧸ X.ofB.range)) =
      Sum.inr ((X.ofA a' : X.Universal) : X.Universal ⧸ X.ofB.range) ↔ a⁻¹ * a' ∈ X.edgeA := by
  rw [Sum.inr.injEq, QuotientGroup.eq, ← map_inv, ← map_mul, ofA_mem_ofB_range_iff]

theorem inl_ofB_eq_iff (b b' : B) :
    (Sum.inl ((X.ofB b : X.Universal) : X.Universal ⧸ X.ofA.range) :
        (X.Universal ⧸ X.ofA.range) ⊕ (X.Universal ⧸ X.ofB.range)) =
      Sum.inl ((X.ofB b' : X.Universal) : X.Universal ⧸ X.ofA.range) ↔ b⁻¹ * b' ∈ X.edgeB := by
  rw [Sum.inl.injEq, QuotientGroup.eq, ← map_inv, ← map_mul, ofB_mem_ofA_range_iff]

theorem ofA_smul_inr (h a : A) :
    X.ofA h • (Sum.inr ((X.ofA a : X.Universal) : X.Universal ⧸ X.ofB.range) :
        (X.Universal ⧸ X.ofA.range) ⊕ (X.Universal ⧸ X.ofB.range)) =
      Sum.inr ((X.ofA (h * a) : X.Universal) : X.Universal ⧸ X.ofB.range) := by
  show Sum.inr (((X.ofA h * X.ofA a : X.Universal)) : X.Universal ⧸ X.ofB.range) = _
  rw [map_mul]

theorem ofB_smul_inl (h b : B) :
    X.ofB h • (Sum.inl ((X.ofB b : X.Universal) : X.Universal ⧸ X.ofA.range) :
        (X.Universal ⧸ X.ofA.range) ⊕ (X.Universal ⧸ X.ofB.range)) =
      Sum.inl ((X.ofB (h * b) : X.Universal) : X.Universal ⧸ X.ofA.range) := by
  show Sum.inl (((X.ofB h * X.ofB b : X.Universal)) : X.Universal ⧸ X.ofA.range) = _
  rw [map_mul]

end CFSG.Quasithin.Fan86.Univ
