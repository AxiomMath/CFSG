module

public import CFSG.Quasithin.Recognition.UniquenessSystemDefs

public section

namespace CFSG.Quasithin.Asc94

open scoped Pointwise

universe u v

variable {G : Type v} [Group G] {X : Type u} [MulAction G X]

@[expose] def orbitSubgraph (Γ : SimpleGraph X) [CFSG.Quasithin.GraphAction G Γ]
    (I : Subgroup G) (x y : X) (hxy : Γ.Adj x y) (hy : ∃ t ∈ I, t • x = y) : Γ.Subgraph where
  verts := (fun i : G => i • x) '' (I : Set G)
  Adj a b := ∃ i ∈ I, (a = i • x ∧ b = i • y) ∨ (a = i • y ∧ b = i • x)
  adj_sub := by
    rintro a b ⟨i, -, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact (CFSG.Quasithin.GraphAction.adj_smul i x y).mpr hxy
    · exact (CFSG.Quasithin.GraphAction.adj_smul i y x).mpr hxy.symm
  edge_vert := by
    rintro a b ⟨i, hi, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ⟨i, hi, rfl⟩
    · obtain ⟨t, ht, rfl⟩ := hy
      exact ⟨i * t, I.mul_mem hi ht, mul_smul i t x⟩
  symm := ⟨by
    rintro a b ⟨i, hi, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ⟨i, hi, Or.inr ⟨rfl, rfl⟩⟩
    · exact ⟨i, hi, Or.inl ⟨rfl, rfl⟩⟩⟩

theorem orbitSubgraph_edgeSet (Γ : SimpleGraph X) [CFSG.Quasithin.GraphAction G Γ]
    (I : Subgroup G) (x y : X) (hxy : Γ.Adj x y) (hy : ∃ t ∈ I, t • x = y) :
    (orbitSubgraph Γ I x y hxy hy).edgeSet = (fun i : G => s(i • x, i • y)) '' (I : Set G) := by
  ext e
  induction e using Sym2.ind with
  | _ a b =>
    simp only [SimpleGraph.Subgraph.mem_edgeSet, Set.mem_image, SetLike.mem_coe]
    constructor
    · rintro ⟨i, hi, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact ⟨i, hi, rfl⟩
      · exact ⟨i, hi, Sym2.eq_swap⟩
    · rintro ⟨i, hi, he⟩
      rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨i, hi, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨i, hi, Or.inr ⟨rfl, rfl⟩⟩

theorem isUniquenessSystem_of (Γ : SimpleGraph X) [hΓ : CFSG.Quasithin.GraphAction G Γ]
    (I : Subgroup G) (x y : X) (hxy : Γ.Adj x y)
    (htrans : ∀ w : X, ∃ g : G, g • x = w)
    (hedge : Γ.edgeSet = Set.range fun g : G => s(g • x, g • y))
    (hswap : ∃ t ∈ I, t • x = y ∧ t • y = x)
    (hsup : MulAction.stabilizer G x ⊔ I = ⊤)
    (hstab : MulAction.stabilizer G x =
      MulAction.stabilizer G x ⊓ MulAction.stabilizer G y ⊔ I ⊓ MulAction.stabilizer G x)
    (hI : I = I ⊓ MulAction.stabilizer G x ⊔ I ⊓ MulAction.stabilizer G ({x, y} : Set X)) :
    IsUniquenessSystem Γ I
      (orbitSubgraph Γ I x y hxy (by obtain ⟨t, ht, h1, -⟩ := hswap; exact ⟨t, ht, h1⟩)) x y where
  graphAction := hΓ
  trans := htrans
  edgeSet_eq := hedge
  swap := hswap
  verts_eq := rfl
  edgeSet_I_eq := orbitSubgraph_edgeSet Γ I x y hxy _
  sup_eq_top := hsup
  stab_eq := hstab
  I_eq := hI

end CFSG.Quasithin.Asc94
