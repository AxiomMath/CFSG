module

public import CFSG.LinearAlgebra.RootGroupSL.RankOneGraph
public import CFSG.LocalAnalysis.StandardType.GGRootNormInner
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LinearAlgebra.RootGroupSL.NoOuter
public import CFSG.LinearAlgebra.RootGroupSL.NormalizerX
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt

public section

namespace CFSG.StandardType

open CFSG.LinearAlgebra.RootGroupSL
open CFSG.Open

theorem ggRootNormInner_rootSL_rankOne {k : Type} [Field k] [Finite k] [CharP k 2]
    (hk : 4 ≤ Nat.card k) : GGRootNormInner (rootSL k k k) := by
  classical
  intro α h2 hR hC
  have hX : 0 < Module.finrank k k := by
    rw [Module.finrank_self]
    exact Nat.zero_lt_one
  have hV : 3 ≤ Module.finrank k (DSpace k k) := by
    have h : Module.finrank k (DSpace k k) = 3 := by
      simp [DSpace, Module.finrank_prod, Module.finrank_self]
    omega
  have hcore : pCoreOf 2 (Subgroup.normalizer
        (rootSL k k k : Set (SpecialLinearGroup k (DSpace k k)))) = QK k k k :=
    pCoreOf_normalizer_rootSL (k := k) (E := k) (X := k) hX
  have hCQ : ∀ h ∈ Subgroup.normalizer
        (rootSL k k k : Set (SpecialLinearGroup k (DSpace k k))),
      α h * h⁻¹ ∈ QK k k k := by
    intro h hh
    rw [← hcore]
    exact hC h hh
  obtain ⟨σ, hform⟩ :=
    exists_semilinear_form_of_mulAut_sl (F := k) (V := DSpace k k) hV α
  rcases hform with ⟨T, hT, hα⟩ | ⟨T, hT, hα⟩
  ·
    have hσ : σ = RingEquiv.refl k :=
      field_form_eq_refl (k := k) (E := k) (X := k) hX α hR
        (fun h hh => Subgroup.mem_sup_left (hCQ h hh)) σ T hT hα
    have hTlin : ∀ (c : k) (v : DSpace k k), T (c • v) = c • T v := by
      intro c v
      rw [hT c v, hσ]
      rfl
    exact exists_conj_of_linear_form (k := k) (V := DSpace k k) α T hTlin hα h2
  ·
    exact False.elim (false_of_graph_form_rankOne (k := k) (by omega) α hR hCQ σ T hT hα)

end CFSG.StandardType
