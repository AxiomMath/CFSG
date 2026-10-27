module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86UnivAct
public import CFSG.Quasithin.Recognition.GoldschmidtFan86ModelCore

public section

namespace CFSG.Quasithin.Fan86.Univ

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique

section CharTwo

variable {K G : Type*} [Group K] [Group G]

theorem pCoreOf_range (f : K →* G) (hf : Function.Injective f) :
    pCoreOf 2 f.range = (Open.pCore 2 K).map f := by
  unfold pCoreOf
  let e : K ≃* f.range := MonoidHom.ofInjective hf
  rw [← CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 e, Subgroup.map_map]
  congr 1

theorem charTwo_range (f : K →* G) (hf : Function.Injective f) (h : CharTwo (⊤ : Subgroup K)) :
    CharTwo f.range := by
  intro x hx
  obtain ⟨k, rfl⟩ := hx.1
  rw [pCoreOf_range f hf]
  have hxc := hx.2
  rw [pCoreOf_range f hf] at hxc
  have hk : k ∈ (⊤ : Subgroup K) ⊓ Subgroup.centralizer (pCoreOf 2 (⊤ : Subgroup K) : Set K) := by
    refine ⟨trivial, ?_⟩
    rw [Model.pCoreOf_top_eq]
    intro z hz
    have := Subgroup.mem_centralizer_iff.1 hxc (f z) ⟨z, hz, rfl⟩
    exact hf (by rw [map_mul, map_mul]; exact this)
  have := h hk
  rw [Model.pCoreOf_top_eq] at this
  exact ⟨k, this, rfl⟩

end CharTwo

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

@[expose] def stabHomA (g : X.Universal) : A →* X.Universal :=
  (MulAut.conj g).toMonoidHom.comp X.ofA

@[expose] def stabHomB (g : X.Universal) : B →* X.Universal :=
  (MulAut.conj g).toMonoidHom.comp X.ofB

theorem stabHomA_injective (g : X.Universal) : Function.Injective (stabHomA X g) :=
  (MulAut.conj g).injective.comp X.ofA_injective

theorem stabHomB_injective (g : X.Universal) : Function.Injective (stabHomB X g) :=
  (MulAut.conj g).injective.comp X.ofB_injective

theorem stabilizer_smul_baseA (g : X.Universal) :
    MulAction.stabilizer X.Universal (g • baseA X) = (stabHomA X g).range := by
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj, stabilizer_baseA, stabHomA,
    MonoidHom.range_comp]

theorem stabilizer_smul_baseB (g : X.Universal) :
    MulAction.stabilizer X.Universal (g • baseB X) = (stabHomB X g).range := by
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj, stabilizer_baseB, stabHomB,
    MonoidHom.range_comp]

theorem finite_stabilizer [Finite A] [Finite B] (v : Vtx X) :
    Finite ↥(MulAction.stabilizer X.Universal v) := by
  rcases exists_smul_base X v with ⟨g, rfl⟩ | ⟨g, rfl⟩
  · rw [stabilizer_smul_baseA]
    exact Finite.of_surjective _ (stabHomA X g).rangeRestrict_surjective
  · rw [stabilizer_smul_baseB]
    exact Finite.of_surjective _ (stabHomB X g).rangeRestrict_surjective

theorem charTwo_stabilizer (hA : CharTwo (⊤ : Subgroup A)) (hB : CharTwo (⊤ : Subgroup B))
    (v : Vtx X) : CharTwo (MulAction.stabilizer X.Universal v) := by
  rcases exists_smul_base X v with ⟨g, rfl⟩ | ⟨g, rfl⟩
  · rw [stabilizer_smul_baseA]
    exact charTwo_range _ (stabHomA_injective X g) hA
  · rw [stabilizer_smul_baseB]
    exact charTwo_range _ (stabHomB_injective X g) hB

theorem stabilizer_inf_smul (g : X.Universal) :
    MulAction.stabilizer X.Universal (g • baseA X) ⊓
        MulAction.stabilizer X.Universal (g • baseB X) =
      ((MulAut.conj g).toMonoidHom.comp (Monoid.PushoutI.base X.diagram)).range := by
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj,
    MulAction.stabilizer_smul_eq_stabilizer_map_conj, stabilizer_baseA, stabilizer_baseB,
    ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective, X.ofA_range_inf_ofB_range,
    MonoidHom.range_comp]

theorem isPGroup_stabilizer_inf (hC : IsPGroup 2 C) {u w : Vtx X} (h : X.treeGraph.Adj u w) :
    IsPGroup 2 ↥(MulAction.stabilizer X.Universal u ⊓ MulAction.stabilizer X.Universal w) := by
  have key : ∀ g : X.Universal, IsPGroup 2 ↥(MulAction.stabilizer X.Universal (g • baseA X) ⊓
      MulAction.stabilizer X.Universal (g • baseB X)) := fun g => by
    rw [stabilizer_inf_smul]
    refine hC.of_equiv (MonoidHom.ofInjective ?_)
    exact (MulAut.conj g).injective.comp (Monoid.PushoutI.base_injective X.diagram_injective)
  obtain ⟨g, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := exists_smul_edge X h
  · exact key g
  · rw [inf_comm]
    exact key g

theorem ncard_neighborSet_inl (g : X.Universal) :
    (X.treeGraph.neighborSet (Sum.inl (g : X.Universal ⧸ X.ofA.range))).ncard =
      X.edgeA.index :=
  (goldCosetGraph_ncard_neighborSet_inl X.ofA.range X.ofB.range g).trans
    X.universalCompletion.relIndex_range_eq_edgeA_index

theorem ncard_neighborSet_inr (g : X.Universal) :
    (X.treeGraph.neighborSet (Sum.inr (g : X.Universal ⧸ X.ofB.range))).ncard =
      X.edgeB.index :=
  (goldCosetGraph_ncard_neighborSet_inr X.ofA.range X.ofB.range g).trans
    X.universalCompletion.relIndex_range_eq_edgeB_index

end CFSG.Quasithin.Fan86.Univ
