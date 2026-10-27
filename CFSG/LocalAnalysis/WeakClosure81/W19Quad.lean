module

public import CFSG.LocalAnalysis.WeakClosure81.W19Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace MinCex193

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {X : Subgroup G}

theorem conjSubgroup_M_eq (c : MinCex193 D V₀ V p X) (g : G) :
    conjSubgroup D.M g = normalizer (conjSubgroup V g : Set G) := by
  rw [← E3.conjSubgroup_normalizer, c.setting.normalizer_eq]

theorem quadratic_of_inf_ne_bot (c : MinCex193 D V₀ V p X) {g : G} {E : Subgroup G}
    (hE : IsMulCommutative ↥E) (hEA : conjSubgroup V g ≤ normalizer (E : Set G))
    (hne : E ⊓ conjSubgroup V₀ g ≠ ⊥) :
    E ≤ conjSubgroup D.M g ∧ ⁅E, conjSubgroup V g⁆ ≤ E ⊓ conjSubgroup V g ∧
      ⁅⁅E, conjSubgroup V g⁆, conjSubgroup V g⁆ = ⊥ := by
  obtain ⟨w, hw⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have hwE : (w : G) ∈ E := (Subgroup.mem_inf.1 w.2).1
  have hwV : (w : G) ∈ conjSubgroup V₀ g := (Subgroup.mem_inf.1 w.2).2
  have hw1 : (w : G) ≠ 1 := fun h => hw (Subtype.ext h)
  have hEM : E ≤ conjSubgroup D.M g := by
    refine le_trans ?_ (centralizer_le_conj_M c.setting c.ne_bot g hwV hw1)
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact Subtype.ext_iff.1 (hE.is_comm.comm ⟨_, hwE⟩ ⟨e, he⟩)
  have hEN : E ≤ normalizer (conjSubgroup V g : Set G) := by
    rw [← c.conjSubgroup_M_eq g]
    exact hEM
  have hcomm : ⁅E, conjSubgroup V g⁆ ≤ E ⊓ conjSubgroup V g := by
    rw [Subgroup.commutator_le]
    intro e he a ha
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    ·
      have h1 : a * e⁻¹ * a⁻¹ ∈ E :=
        (Subgroup.mem_normalizer_iff.1 (hEA ha) e⁻¹).1 (E.inv_mem he)
      have : ⁅e, a⁆ = e * (a * e⁻¹ * a⁻¹) := by
        rw [commutatorElement_def]; group
      rw [this]
      exact E.mul_mem he h1
    ·
      have h1 : e * a * e⁻¹ ∈ conjSubgroup V g :=
        (Subgroup.mem_normalizer_iff.1 (hEN he) a).1 ha
      have : ⁅e, a⁆ = (e * a * e⁻¹) * a⁻¹ := by
        rw [commutatorElement_def]
      rw [this]
      exact (conjSubgroup V g).mul_mem h1 ((conjSubgroup V g).inv_mem ha)
  refine ⟨hEM, hcomm, ?_⟩
  have hVg : IsElemAbelian 2 (conjSubgroup V g) :=
    E3.isElemAbelian_conjSubgroup c.setting.isElemAbelian g
  have hAA : ⁅conjSubgroup V g, conjSubgroup V g⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subtype.ext_iff.1 (hVg.1.is_comm.comm ⟨_, hy⟩ ⟨x, hx⟩)
  exact le_bot_iff.1 ((Subgroup.commutator_mono (hcomm.trans inf_le_right) le_rfl).trans hAA.le)

end MinCex193

end CFSG.LocalAnalysis.WeakClosure81
