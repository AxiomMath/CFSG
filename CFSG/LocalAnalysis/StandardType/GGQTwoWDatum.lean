module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabel

public section

namespace CFSG.StandardType

open Module

structure GGQ2WDatum (p : ℕ) [Fact p.Prime] where
  Λ : Type
  [instFintype : Fintype Λ]
  [instDecEq : DecidableEq Λ]
  coxeter : CoxeterMatrix Λ
  cartan : Matrix Λ Λ ℤ
  V : Type
  [instAddCommGroup : AddCommGroup V]
  [instModule : Module (ZMod p) V]
  coroot : Λ → V
  root : Λ → Dual (ZMod p) V
  isWeyl : GGIsWeylMatrix coxeter
  isCartan : GGIntCartan coxeter cartan
  pairing : ∀ i j, root i (coroot j) = (cartan i j : ZMod p)

attribute [instance] GGQ2WDatum.instFintype GGQ2WDatum.instDecEq GGQ2WDatum.instAddCommGroup
  GGQ2WDatum.instModule

namespace GGQ2WDatum

theorem root_coroot_self {p : ℕ} [Fact p.Prime] (D : GGQ2WDatum p) (i : D.Λ) :
    D.root i (D.coroot i) = 2 := by
  rw [D.pairing, D.isCartan.1]; norm_num

@[expose] noncomputable def simpleRefl {p : ℕ} [Fact p.Prime] (D : GGQ2WDatum p) (k : D.Λ) :
    D.V ≃ₗ[ZMod p] D.V :=
  Module.reflection (D.root_coroot_self k)

@[expose] noncomputable def weyl {p : ℕ} [Fact p.Prime] (D : GGQ2WDatum p) :
    Subgroup (D.V ≃ₗ[ZMod p] D.V) :=
  Subgroup.closure (Set.range D.simpleRefl)

theorem simpleRefl_apply {p : ℕ} [Fact p.Prime] (D : GGQ2WDatum p) (k : D.Λ) (v : D.V) :
    D.simpleRefl k v = v - D.root k v • D.coroot k :=
  Module.reflection_apply v (D.root_coroot_self k)

theorem simpleRefl_mem_weyl {p : ℕ} [Fact p.Prime] (D : GGQ2WDatum p) (k : D.Λ) :
    D.simpleRefl k ∈ D.weyl :=
  Subgroup.subset_closure ⟨k, rfl⟩

theorem nonempty {p : ℕ} [Fact p.Prime] (D : GGQ2WDatum p) : Nonempty D.Λ := by
  rcases D.isWeyl with ⟨n, e, hn, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩
  · exact ⟨e ⟨0, hn⟩⟩
  all_goals exact ⟨e 0⟩

end GGQ2WDatum

end CFSG.StandardType

end
