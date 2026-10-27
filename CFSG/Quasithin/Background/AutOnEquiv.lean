module

public import CFSG.Quasithin.Background.InternalSecISec

public section

namespace CFSG.Quasithin.InternalSec

variable {G : Type} [Group G]

theorem nonempty_autOn_equiv {L V W : Subgroup G} (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (h : L ⊓ Subgroup.centralizer (V : Set G) = L ⊓ Subgroup.centralizer (W : Set G)) :
    Nonempty (↥(autOn L V) ≃* ↥(autOn L W)) := by
  have hker : (InternalSec.autOnHom hLV).ker = (InternalSec.autOnHom hLW).ker := by
    ext l
    rw [InternalSec.mem_ker_autOnHom, InternalSec.mem_ker_autOnHom]
    constructor
    · intro hl
      have h2 : (l : G) ∈ L ⊓ Subgroup.centralizer (V : Set G) := ⟨l.2, hl⟩
      rw [h] at h2
      exact h2.2
    · intro hl
      have h2 : (l : G) ∈ L ⊓ Subgroup.centralizer (W : Set G) := ⟨l.2, hl⟩
      rw [← h] at h2
      exact h2.2
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective _
      (InternalSec.autOnHom_surjective hLV)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ (InternalSec.autOnHom_surjective hLW)))⟩

end CFSG.Quasithin.InternalSec
