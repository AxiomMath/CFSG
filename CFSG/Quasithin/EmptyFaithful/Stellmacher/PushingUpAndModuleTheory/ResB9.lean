module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ResB8
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.Hss113
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ResB2

public section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.F53

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CosetGeom Equiv CFSG.Quasithin.F53Mod
open CFSG.Quasithin.F53Push
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace ConfR

variable {δ μ : Geo H M} {U : Subgroup G}

theorem not_Zv_le_Qv (hA : F53Amalgam H M S) (h : ConfR δ μ U) {i j : Geo H M}
    (hi : i ∈ nbrs μ) (hj : j ∈ nbrs μ) (hij : i ≠ j) : ¬ Zv i ≤ Qv j := by
  have hδ : δ ∈ nbrs μ := h.sig.adj.symm
  obtain ⟨n, hn, hnδ, hZn⟩ := h.exists_not_Zv_le hA
  obtain ⟨g, hg, hgn, hgδ⟩ := h.two_transitive hA hn hδ hi hj hnδ hij
  intro hle
  apply hZn
  have h2 : conjSub (g : G) (Zv n) ≤ conjSub (g : G) (Qv δ) := by
    rw [← Zv_smul, ← Qv_smul, hgn, hgδ]; exact hle
  exact (conjSub_le_conjSub_iff _).mp h2

theorem dist_nbrs {i j : Geo H M} (hi : i ∈ nbrs μ) (hj : j ∈ nbrs μ) :
    dist i j ≤ 2 := by
  have h1 : dist i μ = 1 := dist_eq_one_iff_adj.mpr (show (graph (H ⊔ M) H M).Adj μ i from hi).symm
  have h2 : dist μ j = 1 := dist_eq_one_iff_adj.mpr (show (graph (H ⊔ M) H M).Adj μ j from hj)
  have := dist_triangle_of_adj (show (graph (H ⊔ M) H M).Adj i μ from
    (show (graph (H ⊔ M) H M).Adj μ i from hi).symm) j
  omega

theorem isCritPair (hA : F53Amalgam H M S) (h : ConfR δ μ U) {i j : Geo H M}
    (hi : i ∈ nbrs μ) (hj : j ∈ nbrs μ) (hij : i ≠ j) :
    IsCritPair₁ i j ∧ bMin H M = 2 := by
  have hn := h.not_Zv_le_Qv hA hi hj hij
  have h1 : bAt i ≤ dist i j := Nat.sInf_le ⟨j, rfl, hn⟩
  have h2 := dist_nbrs hi hj
  have h3 := bMin_le_bAt (H := H) (M := M) i
  have h4 := h.b
  have hb : bMin H M = 2 := by omega
  exact ⟨⟨hn, by omega⟩, hb⟩

theorem Zv_le_Qv_mu (h : ConfR δ μ U) {j : Geo H M} (hj : j ∈ nbrs μ) : Zv j ≤ Qv μ :=
  Zv_le_Qv_of_dist_lt (by
    have h1 : dist j μ = 1 :=
      dist_eq_one_iff_adj.mpr (show (graph (H ⊔ M) H M).Adj μ j from hj).symm
    have h2 := bMin_le_bAt (H := H) (M := M) j
    have := h.b
    omega)

theorem centralizer_Zv (hA : F53Amalgam H M S) (h : ConfR δ μ U) {i j : Geo H M}
    (hi : i ∈ nbrs μ) (hj : j ∈ nbrs μ) (hij : i ≠ j) :
    stab i ⊓ Subgroup.centralizer (Zv i : Set G) = Qv i :=
  centralizer_Zv_eq_Qv_of_bAt hA (bAt_eq_of_crit (h.isCritPair hA hi hj hij).1)

theorem comm_ne (hA : F53Amalgam H M S) (h : ConfR δ μ U) {i j : Geo H M}
    (hi : i ∈ nbrs μ) (hj : j ∈ nbrs μ) (hij : i ≠ j) : ⁅Zv i, Zv j⁆ ≠ ⊥ := by
  intro hc
  have hle : Zv j ≤ Subgroup.centralizer (Zv i : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hc
  have hjs : Zv j ≤ stab i :=
    (h.Zv_le_Qv_mu hj).trans (Qv_le_stab_of_mem_nbrs hA hi)
  exact h.not_Zv_le_Qv hA hj hi hij.symm (by
    rw [← h.centralizer_Zv hA hi hj hij]
    exact le_inf hjs hle)

theorem a_eq (hA : F53Amalgam H M S) (h : ConfR δ μ U) {i j : Geo H M}
    (hi : i ∈ nbrs μ) (hj : j ∈ nbrs μ) (hij : i ≠ j) :
    (Zv i ⊓ Qv j).relIndex (Zv i) = (Zv j ⊓ Qv i).relIndex (Zv j) :=
  F53.Stellmacher.hss113aAt_of hA i j (h.isCritPair hA hi hj hij).1 (h.comm_ne hA hi hj hij)

end ConfR

end CFSG.Quasithin.F53
