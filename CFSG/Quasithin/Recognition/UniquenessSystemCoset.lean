module

public import CFSG.Quasithin.Recognition.UniquenessSystemPairs

public section

namespace CFSG.Quasithin.Asc94

open MulAction
open scoped Pointwise

universe v

variable {G : Type v} [Group G]

@[expose] def cosetGraph (A : Subgroup G) (t : G) : SimpleGraph (G ⧸ A) :=
  SimpleGraph.fromRel fun q₁ q₂ => ∃ g : G, q₁ = (g : G ⧸ A) ∧ q₂ = ((g * t : G) : G ⧸ A)

instance (A : Subgroup G) (t : G) : GraphAction G (cosetGraph A t) where
  adj_smul g u v := by
    have key : ∀ (g : G) (u v : G ⧸ A), (cosetGraph A t).Adj u v →
        (cosetGraph A t).Adj (g • u) (g • v) := by
      intro g u v ⟨hne, h⟩
      refine ⟨fun e => hne (smul_left_cancel g e), ?_⟩
      rcases h with ⟨k, rfl, rfl⟩ | ⟨k, rfl, rfl⟩
      · left; refine ⟨g * k, ?_, ?_⟩
        · rw [MulAction.Quotient.smul_mk]; rfl
        · rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_assoc]
      · right; refine ⟨g * k, ?_, ?_⟩
        · rw [MulAction.Quotient.smul_mk]; rfl
        · rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_assoc]
    exact ⟨fun h => by simpa using key g⁻¹ _ _ h, key g u v⟩

theorem stabilizer_mk_one (A : Subgroup G) : stabilizer G ((1 : G) : G ⧸ A) = A :=
  MulAction.stabilizer_quotient A

theorem cosetGraph_adj_mk {A : Subgroup G} {t : G} (htA : t ∉ A) :
    (cosetGraph A t).Adj ((1 : G) : G ⧸ A) (t : G ⧸ A) := by
  refine ⟨fun h => htA ?_, Or.inl ⟨1, rfl, by rw [one_mul]⟩⟩
  have := QuotientGroup.eq.mp h
  simpa using this

@[expose] def cosetSubgraph (A I : Subgroup G) (t : G) (htA : t ∉ A) :
    (cosetGraph A t).Subgraph :=
  stdSubgraph (cosetGraph A t) I ((1 : G) : G ⧸ A) (t : G ⧸ A) (cosetGraph_adj_mk htA)

theorem cosetSystem_isUniquenessSystem {A I : Subgroup G} {t : G} (htI : t ∈ I) (htA : t ∉ A)
    (htt : t * t ∈ A) (hgen : A ⊔ I = ⊤)
    (hA : A ≤ A ⊓ stabilizer G ((t : G) : G ⧸ A) ⊔ I ⊓ A)
    (hI : I ≤ I ⊓ A ⊔ Subgroup.zpowers t) :
    IsUniquenessSystem (cosetGraph A t) I (cosetSubgraph A I t htA) ((1 : G) : G ⧸ A)
      (t : G ⧸ A) := by
  have htx : t • ((1 : G) : G ⧸ A) = (t : G ⧸ A) := by
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
  have hty : t • ((t : G) : G ⧸ A) = ((1 : G) : G ⧸ A) := by
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
    simpa using A.inv_mem htt
  have hadj := cosetGraph_adj_mk htA
  refine ⟨inferInstance, ?_, ?_, ⟨t, htI, htx, hty⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro w
    induction w using QuotientGroup.induction_on with
    | H g => exact ⟨g, by rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]⟩
  · ext e
    induction e using Sym2.ind with
    | _ u v =>
      rw [SimpleGraph.mem_edgeSet]
      constructor
      · rintro ⟨-, ⟨g, rfl, rfl⟩ | ⟨g, rfl, rfl⟩⟩
        · refine ⟨g, ?_⟩
          simp only [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
        · refine ⟨g, ?_⟩
          simp only [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
          exact Sym2.eq_swap
      · rintro ⟨g, hg⟩
        have h' := (GraphAction.adj_smul g _ _).mpr hadj
        rcases Sym2.eq_iff.mp hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [← h1, ← h2]; exact h'
        · rw [← h1, ← h2]; exact h'.symm
  · exact stdSubgraph_verts_eq hadj htI htx
  · exact stdSubgraph_edgeSet_eq hadj
  · rw [stabilizer_mk_one]; exact hgen
  · rw [stabilizer_mk_one]
    exact le_antisymm hA (sup_le inf_le_left inf_le_right)
  · rw [stabilizer_mk_one]
    refine le_antisymm (hI.trans (sup_le_sup_left ?_ _)) (sup_le inf_le_left inf_le_left)
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_inf.mpr ⟨htI, ?_⟩
    rw [mem_stabilizer_iff, Set.smul_set_insert, Set.smul_set_singleton, htx, hty,
      Set.pair_comm]

end CFSG.Quasithin.Asc94
