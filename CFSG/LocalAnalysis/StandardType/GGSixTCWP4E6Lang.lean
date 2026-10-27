module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4E6Frame

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

def tcOfL (l : List ℤ) : Fin Tag.E6.rank → ℤ := fun i => l.getD i.val 0

theorem tcOfL_ofFn (γ : Fin Tag.E6.rank → ℤ) : tcOfL (List.ofFn γ) = γ := by
  funext i
  simp [tcOfL]

theorem ofFn_ofL {l : List ℤ} (h : l.length = 6) : List.ofFn (tcOfL l) = l := by
  apply List.ext_getElem
  · simp [h]
    rfl
  · intro i h1 h2
    simp [tcOfL, List.getElem?_eq_getElem h2]

theorem ofFn_add (α β : Fin Tag.E6.rank → ℤ) :
    List.ofFn (α + β) = tcAddL (List.ofFn α) (List.ofFn β) := by
  apply List.ext_getElem
  · simp [tcAddL]
  · intro i h1 h2
    simp [tcAddL]

private theorem ofFn_neg (α : Fin Tag.E6.rank → ℤ) : List.ofFn (-α) = tcNegL (List.ofFn α) := by
  apply List.ext_getElem
  · simp [tcNegL]
  · intro i h1 h2
    simp [tcNegL]

theorem mem_tcA2Set_iff (α β γ : Fin Tag.E6.rank → ℤ) :
    γ ∈ tcA2Set α β ↔ List.ofFn γ ∈ tcA2L (List.ofFn α) (List.ofFn β) := by
  simp only [tcA2Set, tcA2L, Set.mem_insert_iff, Set.mem_singleton_iff, List.mem_cons,
    List.not_mem_nil, or_false, ← ofFn_add, ← ofFn_neg]
  simp only [List.ofFn_inj]

end CFSG.StandardType.TableCRes

end
