module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec7.T73.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec7.T73.Inf

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}
  {r : ℕ} {S : Subgroup G}

theorem theorem_7_3
    (h : Counterexample p A θ) (hr : InPiTheta A θ r) (hS : IsSr p A θ r S)
    {E K : Subgroup G} (hB : TypeBCore p A θ E K) {a : G} (ha : a ∈ A) (haE : a ∉ E) :
    zOf (S ⊓ Subgroup.centralizer {a}) = zOf S ⊓ Subgroup.centralizer {a} := by
  have ha1 : a ≠ 1 := fun h1 => haE (h1 ▸ one_mem E)
  have hF := h.zpowers_mem_E1 ha ha1
  have hFE : Subgroup.zpowers a ≠ E := fun heq => haE (heq ▸ Subgroup.mem_zpowers a)
  rw [← centralizer_zpowers_eq_singleton a]
  refine le_antisymm ?_ ?_
  · refine (zOf_le_sup h hr hS hB hF hFE).trans (sup_le le_rfl (le_inf ?_ ?_))
    · exact (le_inf (zOf_inf_centralizer_le h hr hS hB hF hFE) inf_le_left).trans
        (inf_zOf_le h hr hS hB hF hFE)
    · exact inf_le_left.trans ((zOf_le _).trans inf_le_right)
  · intro x hx
    exact mem_zOf_iff.mpr ⟨⟨zOf_le S hx.1, hx.2⟩, fun w hw => (mem_zOf_iff.mp hx.1).2 w hw.1⟩

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
